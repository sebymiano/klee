/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- ktest-dehavoc.cpp ---------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExprBuilder.h"
#include "klee/perf-contracts.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include <dlfcn.h>
#include <expr/Parser.h>
#include <fstream>
#include <iostream>
#include <klee/Constraints.h>
#include <klee/Solver.h>
#include <vector>

#define DEBUG

namespace {
llvm::cl::opt<std::string> SenderCallPathFile(llvm::cl::desc("<sender call path>"),
                                         llvm::cl::Positional,
                                         llvm::cl::Required);

llvm::cl::opt<std::string> ReceiverCallPathFile(llvm::cl::desc("<receiver call path>"),
                                         llvm::cl::Positional,
                                         llvm::cl::Required);
}

typedef struct {
  std::string function_name;
  std::map<std::string, std::pair<klee::ref<klee::Expr>, klee::ref<klee::Expr>>>
      extra_vars;
} call_t;

typedef struct {
  klee::ConstraintManager constraints;
  std::vector<call_t> calls;
  std::map<std::string, const klee::Array *> arrays;
  std::map<std::string, klee::ref<klee::Expr>> initial_extra_vars;
} call_path_t;

std::map<std::pair<std::string, int>, klee::ref<klee::Expr>>
    subcontract_constraints;

call_path_t *load_call_path(std::string file_name) {
  std::ifstream call_path_file(file_name);
  assert(call_path_file.is_open() && "Unable to open call path file.");

  call_path_t *call_path = new call_path_t;

  enum {
    STATE_INIT,
    STATE_KQUERY,
    STATE_CALLS,
    STATE_CALLS_MULTILINE,
    STATE_DONE
  } state = STATE_INIT;

  std::string kQuery;
  std::vector<klee::ref<klee::Expr>> exprs;
  std::set<std::string> declared_arrays;

  int parenthesis_level = 0;

  while (!call_path_file.eof()) {
    std::string line;
    std::getline(call_path_file, line);

    switch (state) {
    case STATE_INIT: {
      if (line == ";;-- kQuery --") {
        state = STATE_KQUERY;
      }
    } break;

    case STATE_KQUERY: {
      if (line == ";;-- Calls --") {
        auto MB = llvm::MemoryBuffer::getMemBuffer(kQuery);
        klee::ExprBuilder *Builder = klee::createDefaultExprBuilder();
        klee::expr::Parser *P =
            klee::expr::Parser::Create("", MB.get(), Builder, false);
        while (klee::expr::Decl *D = P->ParseTopLevelDecl()) {
          assert(!P->GetNumErrors() &&
                 "Error parsing kquery in call path file.");
          if (klee::expr::ArrayDecl *AD = dyn_cast<klee::expr::ArrayDecl>(D)) {
            call_path->arrays[AD->Root->name] = AD->Root;
          } else if (klee::expr::QueryCommand *QC =
                         dyn_cast<klee::expr::QueryCommand>(D)) {
            call_path->constraints = klee::ConstraintManager(QC->Constraints);
            exprs = QC->Values;
            break;
          }
        }

        state = STATE_CALLS;
      } else {
        kQuery += "\n" + line;

        if (line.substr(0, sizeof("array ") - 1) == "array ") {
          std::string array_name = line.substr(sizeof("array "));
          size_t delim = array_name.find("[");
          assert(delim != std::string::npos);
          array_name = array_name.substr(0, delim);
          declared_arrays.insert(array_name);
        }
      }
      break;

    case STATE_CALLS:
      if (line == ";;-- Constraints --") {
        assert(exprs.empty() && "Too many expressions in kQuery.");

        state = STATE_DONE;
      } else {
        size_t delim = line.find(":");
        assert(delim != std::string::npos);
        std::string preamble = line.substr(0, delim);
        line = line.substr(delim + 1);

        if (preamble == "extra") {
          while (line[0] == ' ') {
            line = line.substr(1);
          }

          delim = line.find("&");
          assert(delim != std::string::npos);
          std::string name = line.substr(0, delim);

          assert(exprs.size() >= 2 && "Not enough expression in kQuery.");
          call_path->calls.back().extra_vars[name] =
              std::make_pair(exprs[0], exprs[1]);
          if (!call_path->initial_extra_vars.count(name)) {
            call_path->initial_extra_vars[name] = exprs[0];
          }
          exprs.erase(exprs.begin(), exprs.begin() + 2);
        } else {
          call_path->calls.emplace_back();

          delim = line.find("(");
          assert(delim != std::string::npos);
          call_path->calls.back().function_name = line.substr(0, delim);
        }

        for (char c : line) {
          if (c == '(') {
            parenthesis_level++;
          } else if (c == ')') {
            parenthesis_level--;
            assert(parenthesis_level >= 0);
          }
        }

        if (parenthesis_level > 0) {
          state = STATE_CALLS_MULTILINE;
        }
      }
    } break;

    case STATE_CALLS_MULTILINE: {
      for (char c : line) {
        if (c == '(') {
          parenthesis_level++;
        } else if (c == ')') {
          parenthesis_level--;
          assert(parenthesis_level >= 0);
        }
      }

      if (parenthesis_level == 0) {
        state = STATE_CALLS;
      }

      continue;
    } break;

    case STATE_DONE: {
      continue;
    } break;

    default: { assert(false && "Invalid call path file."); } break;
    }
  }

  return call_path;
}

int main(int argc, char **argv, char **envp) {
  llvm::cl::ParseCommandLineOptions(argc, argv);

  call_path_t *sender_call_path = load_call_path(SenderCallPathFile);
  call_path_t *receiver_call_path = load_call_path(ReceiverCallPathFile);

  klee::Solver *solver = klee::createCoreSolver(klee::Z3_SOLVER);
  assert(solver);
  solver = createCexCachingSolver(solver);
  solver = createCachingSolver(solver);
  solver = createIndependentSolver(solver);

  klee::ExprBuilder *exprBuilder = klee::createDefaultExprBuilder();

  klee::ConstraintManager constraints;

  for (auto c : sender_call_path->constraints) {
    constraints.addConstraint(c);
  }
  for (auto c : receiver_call_path->constraints) {
    constraints.addConstraint(c);
  }

  klee::ref<klee::Expr> tx_expr;
  for (auto call : sender_call_path->calls) {
    if (call.function_name == "stub_core_trace_tx") {
      assert(call.extra_vars.count("user_buf_addr"));
      tx_expr = call.extra_vars["user_buf_addr"].first;
    }
  }
  if (tx_expr.isNull()) {
    std::cout << "Sender doesn't send." << std::endl;
    std::cout << "Call paths incompatible." << std::endl;
    return 1;
  }

  klee::ref<klee::Expr> rx_expr;
  for (auto call : receiver_call_path->calls) {
    if (call.function_name == "stub_core_trace_rx") {
      assert(call.extra_vars.count("user_buf_addr"));
      rx_expr = call.extra_vars["user_buf_addr"].first;
    }
  }
  if (rx_expr.isNull()) {
    std::cout << "Receiver doesn't receive." << std::endl;
    std::cout << "Call paths incompatible." << std::endl;
    return 1;
  }

  klee::ref<klee::Expr> eq_expr = exprBuilder->Eq(rx_expr, tx_expr);

  klee::Query sat_query(constraints, eq_expr);
  bool result = false;
  bool success = solver->mayBeTrue(sat_query, result);
  assert(success);

  if (result) {
    std::cout << "Call paths compatible." << std::endl;
    return 0;
  } else {
    std::cout << "Call paths incompatible." << std::endl;
    return 1;
  }
}
