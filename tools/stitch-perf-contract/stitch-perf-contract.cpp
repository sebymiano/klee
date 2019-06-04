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
#include <deque>

#define DEBUG

namespace {
llvm::cl::opt<std::string>
    ContractLib("contract",
                llvm::cl::desc("A performance contract library to load that "
                               "describes the data structure performance."),
                llvm::cl::Required);

llvm::cl::opt<std::string> UserVariables(
    "user-vars",
    llvm::cl::desc("Sets the value of user variables (var1=val1,var2=val2)."));

llvm::cl::opt<std::string> InputCallPathFile(llvm::cl::desc("<call path>"),
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
  std::map<std::string, std::string> tags;
} call_path_t;

std::map<std::pair<std::string, int>, klee::ref<klee::Expr>>
    subcontract_constraints;

call_path_t *load_call_path(std::string file_name,
                            std::set<std::string> symbols,
                            std::vector<std::string> expressions_str,
                            std::deque<klee::ref<klee::Expr>> &expressions) {
  std::ifstream call_path_file(file_name);
  assert(call_path_file.is_open() && "Unable to open call path file.");

  call_path_t *call_path = new call_path_t;

  enum {
    STATE_INIT,
    STATE_KQUERY,
    STATE_CALLS,
    STATE_CALLS_MULTILINE,
    STATE_CONSTRAINTS,
    STATE_TAGS,
  } state = STATE_INIT;

  std::string kQuery;
  std::vector<klee::ref<klee::Expr>> exprs;
  std::set<std::string> declared_arrays;

  int parenthesis_level = 0;

  while (!call_path_file.eof()) {
    std::string line;
    std::getline(call_path_file, line);

    if (line.empty()) {
      continue;
    }

    switch (state) {
    case STATE_INIT: {
      if (line == ";;-- kQuery --") {
        state = STATE_KQUERY;
      }
    } break;

    case STATE_KQUERY: {
      if (line == ";;-- Calls --") {
        for (auto ait : symbols) {
          std::string array_name = ait.substr(sizeof("array "));
          size_t delim = array_name.find("[");
          assert(delim != std::string::npos);
          array_name = array_name.substr(0, delim);

          if (!declared_arrays.count(array_name)) {
            kQuery = ait + "\n" + kQuery;
          }
        }

        if (! expressions_str.empty()) {
          if (kQuery.substr(kQuery.length() - 2) == "])") {
            kQuery = kQuery.substr(0, kQuery.length() - 2) + "\n";

            for (auto eit : expressions_str) {
              kQuery += "\n         " + eit;
            }
            kQuery += "])";
          } else if (kQuery.substr(kQuery.length() - 6) == "false)") {
            kQuery = kQuery.substr(0, kQuery.length() - 1) + "\n[\n";

            for (auto eit : expressions_str) {
              kQuery += "\n         " + eit;
            }
            kQuery += "])";
          } else {
            assert(false && "Mal-formed kQuery.");
          }
        }

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
        for (size_t i = 0; i < expressions_str.size(); i++) {
          assert(!exprs.empty() && "Too few expressions in kQuery.");
          expressions.push_back(exprs.front());
          exprs.erase(exprs.begin());
        }

        assert(exprs.empty() && "Too many expressions in kQuery.");

        state = STATE_CONSTRAINTS;
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

    case STATE_CONSTRAINTS : {
      if (line == ";;-- Tags --") {
        state = STATE_TAGS;
      }
    } break;

    case STATE_TAGS : {
      auto delim = line.find(" = ");
      assert(delim != std::string::npos && "Invalid Tag.");
      std::string name = line.substr(0, delim);
      std::string value = line.substr(delim + sizeof(" = ") - 1);

      call_path->tags[name] = value;
    } break;

    default: { assert(false && "Invalid call path file."); } break;
    }
  }

  return call_path;
}

std::map<std::string, long>
process_candidate(call_path_t *call_path, void *contract,
                  std::map<std::string, klee::ref<klee::Expr>> vars, std::map<std::string,std::map<std::string, std::set<int>>> &cstate) { 
  LOAD_SYMBOL(contract, contract_get_metrics);
  LOAD_SYMBOL(contract, contract_has_contract);
  LOAD_SYMBOL(contract, contract_num_sub_contracts);
  LOAD_SYMBOL(contract, contract_get_subcontract_constraints);
  LOAD_SYMBOL(contract, contract_get_sub_contract_performance);
  LOAD_SYMBOL(contract, contract_get_concrete_state);

#ifdef DEBUG
  std::cerr << std::endl;
  std::cerr << "Debug: Trying candidate with variables:" << std::endl;
  for (auto vit : vars) {
    std::cerr << "Debug:   " << vit.first << " = " << std::flush;
    vit.second->print(llvm::errs());
    llvm::errs().flush();
    std::cerr << std::endl;
  }
#endif

  klee::Solver *solver = klee::createCoreSolver(klee::Z3_SOLVER);
  assert(solver);
  solver = createCexCachingSolver(solver);
  solver = createCachingSolver(solver);
  solver = createIndependentSolver(solver);

  klee::ConstraintManager constraints = call_path->constraints;

  klee::ExprBuilder *exprBuilder = klee::createDefaultExprBuilder();
  for (auto extra_var : call_path->initial_extra_vars) {
    std::string initial_name = "initial_" + extra_var.first;

    assert(call_path->arrays.count(initial_name));
    const klee::Array *array = call_path->arrays[initial_name];
    assert(array && "Initial variable not found");
    klee::UpdateList ul(array, 0);
    klee::ref<klee::Expr> read_expr =
        exprBuilder->Read(ul, exprBuilder->Constant(0, klee::Expr::Int32));
    for (unsigned offset = 1; offset < array->getSize(); offset++) {
      read_expr = exprBuilder->Concat(
          exprBuilder->Read(ul,
                            exprBuilder->Constant(offset, klee::Expr::Int32)),
          read_expr);
    }
    klee::ref<klee::Expr> eq_expr =
        exprBuilder->Eq(read_expr, extra_var.second);

    constraints.addConstraint(eq_expr);
  }

  for (auto var : vars) {
    if (call_path->initial_extra_vars.count(var.first)) {
      klee::ref<klee::Expr> eq_expr =
          exprBuilder->Eq(var.second, call_path->initial_extra_vars[var.first]);

      klee::Query sat_query(constraints, eq_expr);
      bool result = false;
      bool success = solver->mayBeTrue(sat_query, result);
      assert(success);

      if (!result) {
#ifdef DEBUG
        std::cerr << "Debug: Candidate is trivially UNSAT." << std::endl;
        eq_expr->print(llvm::errs());
        llvm::errs().flush();
        std::cerr << std::endl;
#endif
        return {};
      }

      constraints.addConstraint(eq_expr);
    } else {
      std::cerr << "Warning: ignoring variable: " << var.first << std::endl;
    }
  }

#ifdef DEBUG
  std::cerr << "Debug: Using candidate with variables:" << std::endl;
  for (auto vit : vars) {
    std::cerr << "Debug:   " << vit.first << " = " << std::flush;
    vit.second->print(llvm::errs());
    llvm::errs().flush();
    std::cerr << std::endl;
  }
#endif

  std::map<std::string, long> total_performance;
  int calls_processed = 0; /*To give the cstate a unique ID*/
  for (auto cit : call_path->calls) {
#ifdef DEBUG
    std::cerr << "Debug: Processing call to " << cit.function_name << std::endl;
#endif

    if (!contract_has_contract(cit.function_name)) {
      std::cerr << "Warning: No contract for function: " << cit.function_name
                << ". Ignoring." << std::endl;
      continue;
    }

    klee::ConstraintManager call_constraints = constraints;

    for (auto extra_var : cit.extra_vars) {
      std::string current_name = "current_" + extra_var.first;

      assert(call_path->arrays.count(current_name));
      const klee::Array *array = call_path->arrays[current_name];
      klee::UpdateList ul(array, 0);
      klee::ref<klee::Expr> read_expr =
          exprBuilder->Read(ul, exprBuilder->Constant(0, klee::Expr::Int32));
      for (unsigned offset = 1; offset < array->getSize(); offset++) {
        read_expr = exprBuilder->Concat(
            exprBuilder->Read(ul,
                              exprBuilder->Constant(offset, klee::Expr::Int32)),
            read_expr);
      }
      klee::ref<klee::Expr> eq_expr =
          exprBuilder->Eq(read_expr, extra_var.second.first);

      call_constraints.addConstraint(eq_expr);
    }

    bool found_subcontract = false;
    for (int sub_contract_idx = 0;
         sub_contract_idx < contract_num_sub_contracts(cit.function_name);
         sub_contract_idx++) {
      klee::Query sat_query(call_constraints,
                            subcontract_constraints[std::make_pair(
                                cit.function_name, sub_contract_idx)]);
      bool result = false;
      bool success = solver->mayBeTrue(sat_query, result);
      assert(success);

      if (result) {
        assert(!found_subcontract && "Multiple subcontracts match.");
        found_subcontract = true;

        std::map<std::string, long> variables;
        for (auto extra_var : cit.extra_vars) {
          klee::Query expr_query(constraints, extra_var.second.first);
          klee::ref<klee::ConstantExpr> result;
          success = solver->getValue(expr_query, result);
          assert(success);

          variables[extra_var.first] = result->getLimitedValue();

          bool check = true;
          success = solver->mayBeFalse(expr_query.withExpr(exprBuilder->Eq(
                                           extra_var.second.first, result)),
                                       check);
          assert(success);
          assert((!check) && "Candidate allows multiple variable assignments.");
        }
#ifdef DEBUG
        std::cerr << "Debug: Calling " << cit.function_name
                  << " with variables:" << std::endl;
        for (auto vit : variables) {
          std::cerr << "Debug:   " << vit.first << " = " << vit.second
                    << std::endl;
        }
#endif

        std::set<std::string> metrics = contract_get_metrics();
        for (auto metric : metrics) {
          long performance = contract_get_sub_contract_performance(
              cit.function_name, sub_contract_idx, metric, variables);
          assert(performance >= 0);
          total_performance[metric] += performance;
        }
        
	calls_processed ++;
	std::string unique_fn_id = "LibVig Call #" + std::to_string(calls_processed) + ":" + cit.function_name;
	cstate[unique_fn_id] = contract_get_concrete_state(
		       cit.function_name, sub_contract_idx,variables);	
    
      }
    }
    if (!found_subcontract) {
#ifdef DEBUG
      std::cerr << "Debug: No subcontract for " << cit.function_name
                << " is SAT." << std::endl;
#endif
      return {};
    }
  }

  if (total_performance.empty()) {
    for (auto metric : contract_get_metrics()) {
      total_performance[metric] = 0;
    }
  }

#ifdef DEBUG
  std::cerr << "Debug: Candidate performance:" << std::endl;
  for (auto metric : total_performance) {
    std::cerr << "Debug:   " << metric.first << ": " << metric.second
              << std::endl;
  }
#endif
  return total_performance;
}

int main(int argc, char **argv, char **envp) {
  llvm::cl::ParseCommandLineOptions(argc, argv);

  dlerror();
  const char *err = NULL;
  void *contract = dlopen(ContractLib.c_str(), RTLD_NOW);
  if ((err = dlerror())) {
    std::cerr << "Error: Unable to load contract plugin " << ContractLib << ": "
              << err << std::endl;
    exit(-1);
  }
  assert(contract);

  // Get contract symbols
  LOAD_SYMBOL(contract, contract_init);
  LOAD_SYMBOL(contract, contract_get_user_variables);
  LOAD_SYMBOL(contract, contract_get_optimization_variables);
  LOAD_SYMBOL(contract, contract_get_symbols);
  LOAD_SYMBOL(contract, contract_get_contracts);
  LOAD_SYMBOL(contract, contract_has_contract);
  LOAD_SYMBOL(contract, contract_num_sub_contracts);
  LOAD_SYMBOL(contract, contract_get_subcontract_constraints);
  LOAD_SYMBOL(contract, contract_get_sub_contract_performance);

  contract_init();

  std::map<std::string, std::string> user_variables_str =
      contract_get_user_variables();
  std::set<std::string> overriden_user_variables;

  std::string user_variables_param = UserVariables;
  while (!user_variables_param.empty()) {
    std::string user_variable_string =
        user_variables_param.substr(0, user_variables_param.find(","));
    user_variables_param =
        user_variable_string.size() == user_variables_param.size()
            ? ""
            : user_variables_param.substr(user_variable_string.size() + 1);

    std::string user_var =
        user_variable_string.substr(0, user_variable_string.find("="));
    std::string user_val =
        user_variable_string.substr(user_variable_string.find("=") + 1);

    if (!user_variables_str.count(user_var)) {
      std::cerr << "Error: User variable " << user_var
                << " not defined in contract." << std::endl
                << "Error: Valid user variables:" << std::endl;
      for (auto it : user_variables_str) {
        std::cerr << "Error:   " << it.first << std::endl;
      }
      exit(-1);
    }

    user_variables_str[user_var] = user_val;
    overriden_user_variables.insert(user_var);
  }

  std::map<std::string, std::set<std::string>> optimization_variables_str =
      contract_get_optimization_variables();

  std::map<std::pair<std::string, int>, std::string>
      subcontract_constraints_str;
  for (auto function_name : contract_get_contracts()) {
    for (int sub_contract_idx = 0;
         sub_contract_idx < contract_num_sub_contracts(function_name);
         sub_contract_idx++) {
      subcontract_constraints_str[std::make_pair(function_name,
                                                 sub_contract_idx)] =
          contract_get_subcontract_constraints(function_name, sub_contract_idx);
    }
  }

  std::vector<std::string> expressions_str;
  for (auto vit : user_variables_str) {
    expressions_str.push_back(vit.second);
  }
  for (auto vit : optimization_variables_str) {
    for (auto cit : vit.second) {
      expressions_str.push_back(cit);
    }
  }
  for (auto cit : subcontract_constraints_str) {
    expressions_str.push_back(cit.second);
  }

  std::deque<klee::ref<klee::Expr>> expressions;
  call_path_t *call_path = load_call_path(
      InputCallPathFile, contract_get_symbols(), expressions_str, expressions);

  std::map<std::string, klee::ref<klee::Expr>> user_variables;
  for (auto vit : user_variables_str) {
    assert(!expressions.empty());
    user_variables[vit.first] = expressions.front();
    expressions.pop_front();
  }
  std::map<std::string, std::set<klee::ref<klee::Expr>>> optimization_variables;
  for (auto vit : optimization_variables_str) {
    for (auto cit : vit.second) {
      assert(!expressions.empty());
      optimization_variables[vit.first].insert(expressions.front());
      expressions.pop_front();
    }
  }
  for (auto cit : subcontract_constraints_str) {
    assert(!expressions.empty());
    subcontract_constraints[cit.first] = expressions.front();
    expressions.pop_front();
  }
  assert(expressions.empty());

  std::map<std::string, std::set<klee::ref<klee::Expr>>::iterator>
      candidate_iterators;
  for (auto &it : optimization_variables) {
    if (!overriden_user_variables.count(it.first)) {
      candidate_iterators[it.first] = it.second.begin();
    }
  }

#ifdef DEBUG
  std::cerr << "Debug: Binding user variables to:" << std::endl;
  for (auto vit : user_variables) {
    std::cerr << "Debug:   " << vit.first << " = " << std::flush;
    vit.second->print(llvm::errs());
    llvm::errs().flush();
    std::cerr << std::endl;
  }
#endif
  
  std::map<std::string, long> max_performance;
  std::map<std::string,std::map<std::string, std::set<int>>> final_cstate;
  std::map<std::string, std::set<klee::ref<klee::Expr>>::iterator>::iterator
      pos;
  do {
    std::map<std::string, klee::ref<klee::Expr>> vars = user_variables;

    for (auto it : candidate_iterators) {
      vars[it.first] = *it.second;
    }

    std::map<std::string,std::map<std::string, std::set<int>>> candidate_cstate;
    std::map<std::string, long> performance =
        process_candidate(call_path, contract, vars, candidate_cstate);
    for (auto metric : performance) {
      assert(metric.second >= 0);
      if (metric.second > max_performance[metric.first]) {
	final_cstate=candidate_cstate; /*Assumption that all three metrics increase/decrease together*/
        max_performance[metric.first] = metric.second;
      }
    }

    pos = candidate_iterators.begin();
    while (++(pos->second) == optimization_variables[pos->first].end()) {
      if (++pos == candidate_iterators.end()) {
        break;
      }

      for (auto reset_pos = candidate_iterators.begin(); reset_pos != pos;
           reset_pos++) {
        reset_pos->second = optimization_variables[reset_pos->first].begin();
      }
    }
  } while (pos != candidate_iterators.end());

  if (max_performance.empty()) {
    std::cerr << "Warning: No candidate was SAT." << std::endl;
  }

  for (auto metric : max_performance) {
    std::cout << metric.first << "," << metric.second << std::endl;
  }

  if(!final_cstate.empty()) {
	for (auto cstate_it : final_cstate) {
		for(auto it : cstate_it.second) {
			std::cout<<"Concrete State:"<<cstate_it.first<<":" << it.first <<":"; 
			for(auto it1 : it.second) {
				std::cout<<" " <<it1;
	        	}
			std::cout<< std::endl;  
	        }
	}
  }

  return 0;
}
