/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FileHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/System/Time.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"
#include "klee/ExprBuilder.h"
#include "klee/util/ExprPPrinter.h"
#include "../lib/Core/Memory.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/system_error.h"
#endif

#if LLVM_VERSION_CODE >= LLVM_VERSION(4, 0)
#include <llvm/Bitcode/BitcodeReader.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>

#include <cerrno>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>
#include <list>
#include <iostream>


using namespace llvm;
using namespace klee;

namespace {
  cl::opt<std::string>
  InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

  cl::opt<std::string>
  EntryPoint("entry-point",
               cl::desc("Consider the function with the given name as the entrypoint"),
               cl::init("main"));

  cl::opt<std::string>
  RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));

  cl::opt<std::string>
  Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter,
            cl::desc("<program arguments>..."));

  cl::opt<bool>
  NoOutput("no-output",
           cl::desc("Don't generate test files"));

  cl::opt<bool>
  WarnAllExternals("warn-all-externals",
                   cl::desc("Give initial warning for all externals."));

  cl::opt<bool>
  WriteCVCs("write-cvcs",
            cl::desc("Write .cvc files for each test case"));

  cl::opt<bool>
  WriteKQueries("write-kqueries",
            cl::desc("Write .kquery files for each test case"));

  cl::opt<bool>
  WriteSMT2s("write-smt2s",
            cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));

  cl::opt<bool>
  WriteCov("write-cov",
           cl::desc("Write coverage information for each test case"));

  cl::opt<bool>
  WriteTestInfo("write-test-info",
                cl::desc("Write additional test case information"));

  cl::opt<bool>
  WritePaths("write-paths",
                cl::desc("Write .path files for each test case"));

  cl::opt<bool>
  WriteSymPaths("write-sym-paths",
                cl::desc("Write .sym.path files for each test case"));

  cl::opt<bool>
  OptExitOnError("exit-on-error",
              cl::desc("Exit if errors occur"));

  enum class LibcType { FreeStandingLibc, KleeLibc, UcLibc };

  cl::opt<LibcType> Libc(
      "libc", cl::desc("Choose libc version (none by default)."),
      cl::values(
          clEnumValN(
              LibcType::FreeStandingLibc, "none",
              "Don't link in a libc (only provide freestanding environment)"),
          clEnumValN(LibcType::KleeLibc, "klee", "Link in klee libc"),
          clEnumValN(LibcType::UcLibc, "uclibc",
                     "Link in uclibc (adapted for klee)") KLEE_LLVM_CL_VAL_END),
      cl::init(LibcType::FreeStandingLibc));

  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
		cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
		cl::init(false));

  cl::opt<bool>
  OptimizeModule("optimize",
                 cl::desc("Optimize before execution"),
		 cl::init(false));

  cl::opt<bool>
  CheckDivZero("check-div-zero",
               cl::desc("Inject checks for division-by-zero"),
               cl::init(true));

  cl::opt<bool>
  CheckOvershift("check-overshift",
               cl::desc("Inject checks for overshift"),
               cl::init(true));

  cl::opt<std::string>
  OutputDir("output-dir",
            cl::desc("Directory to write results in (defaults to klee-out-N)"),
            cl::init(""));

  cl::opt<bool>
  DumpCallTracePrefixes("dump-call-trace-prefixes",
                        cl::desc("Compute and dump all the prefixes for the call "
                                 "traces, generated according to klee_trace_*."),
                        cl::init(false));

  cl::opt<bool>
  DumpCallTraces("dump-call-traces",
                 cl::desc("Dump call traces into separate file each. The call "
                          "traces consist of function invocations with the "
                          "klee_trace_ret* intrinsic labels."),
                 cl::init(false));

  cl::opt<bool>
  CondoneUndeclaredHavocs("condone-undeclared-havocs",
                          cl::desc("Do not throw an error if a memory location changes "
                                   "its value during loop invarint analysis"),
                          cl::init(false));

  cl::opt<bool>
  ReplayKeepSymbolic("replay-keep-symbolic",
                     cl::desc("Replay the test cases only by asserting "
                              "the bytes, not necessarily making them concrete."));

  cl::list<std::string>
      ReplayKTestFile("replay-ktest-file",
                      cl::desc("Specify a ktest file to use for replay"),
                      cl::value_desc("ktest file"));

  cl::list<std::string>
      ReplayKTestDir("replay-ktest-dir",
                   cl::desc("Specify a directory to replay ktest files from"),
                   cl::value_desc("output directory"));

  cl::opt<std::string>
  ReplayPathFile("replay-path",
                 cl::desc("Specify a path file to replay"),
                 cl::value_desc("path file"));

  cl::list<std::string>
  SeedOutFile("seed-out");

  cl::list<std::string>
  SeedOutDir("seed-out-dir");

  cl::list<std::string>
  LinkLibraries("link-llvm-lib",
		cl::desc("Link the given libraries before execution"),
		cl::value_desc("library file"));

  cl::opt<unsigned>
  MakeConcreteSymbolic("make-concrete-symbolic",
                       cl::desc("Probabilistic rate at which to make concrete reads symbolic, "
				"i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  "
				"Used for testing."),
                       cl::init(0));

  cl::opt<unsigned>
  StopAfterNTests("stop-after-n-tests",
	     cl::desc("Stop execution after generating the given number of tests.  Extra tests corresponding to partially explored paths will also be dumped."),
	     cl::init(0));

  cl::opt<bool>
  Watchdog("watchdog",
           cl::desc("Use a watchdog process to enforce --max-time."),
           cl::init(0));
}

extern cl::opt<double> MaxTime;

class KleeHandler;

struct CallPathTip {
  CallInfo call;
  unsigned path_id;
};

class CallTree {
  std::vector<CallTree* > children;
  CallPathTip tip;
  std::vector<std::vector<CallPathTip*> > groupChildren();
public:
  CallTree():children(), tip(){};
  void addCallPath(std::vector<CallInfo>::const_iterator path_begin,
                   std::vector<CallInfo>::const_iterator path_end,
                   unsigned path_id);
  void dumpCallPrefixes(std::list<CallInfo> accumulated_prefix,
                        std::list<const std::vector<ref<Expr> >* >
                        accumulated_context,
                        KleeHandler* fileOpener);
  void dumpCallPrefixesSExpr(std::list<CallInfo> accumulated_prefix,
                             KleeHandler* fileOpener);

  int refCount;
};

/***/

class KleeHandler : public InterpreterHandler {
private:
  Interpreter *m_interpreter;
  TreeStreamWriter *m_pathWriter, *m_symPathWriter;
  llvm::raw_ostream *m_infoFile;

  SmallString<128> m_outputDirectory;

  unsigned m_numTotalTests;     // Number of tests received from the interpreter
  unsigned m_numGeneratedTests; // Number of tests successfully generated
  unsigned m_pathsExplored; // number of paths explored so far
  unsigned m_callPathIndex; // number of call path strings dumped so far
  unsigned m_callPathPrefixIndex; // number of call path strings dumped so far

  // used for writing .ktest files
  int m_argc;
  char **m_argv;

  CallTree m_callTree;

public:
  KleeHandler(int argc, char **argv);
  ~KleeHandler();

  llvm::raw_ostream &getInfoStream() const { return *m_infoFile; }
  /// Returns the number of test cases successfully generated so far
  unsigned getNumTestCases() { return m_numGeneratedTests; }
  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() { m_pathsExplored++; }

  void setInterpreter(Interpreter *i);

  void processTestCase(const ExecutionState  &state,
                       const char *errorMessage,
                       const char *errorSuffix);
  void processCallPath(const ExecutionState &state);

  std::string getOutputFilename(const std::string &filename);
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename);
  std::string getTestFilename(const std::string &suffix, unsigned id);
  llvm::raw_fd_ostream *openTestFile(const std::string &suffix, unsigned id);

  // load a .path file
  static void loadPathFile(std::string name,
                           std::vector<bool> &buffer);

  static void getKTestFilesInDir(std::string directoryPath,
                                 std::vector<std::string> &results);

  static std::string getRunTimeLibraryPath(const char *argv0);
  llvm::raw_fd_ostream  *openNextCallPathPrefixFile();

  void dumpCallPathPrefixes();
  void dumpCallPath(const ExecutionState &state, llvm::raw_ostream *file);
};

KleeHandler::KleeHandler(int argc, char **argv)
    : m_interpreter(0), m_pathWriter(0), m_symPathWriter(0), m_infoFile(0),
      m_outputDirectory(), m_numTotalTests(0), m_numGeneratedTests(0),
      m_pathsExplored(0), m_callPathIndex(1), m_callPathPrefixIndex(0), m_argc(argc), m_argv(argv) {

  // create output directory (OutputDir or "klee-out-<i>")
  bool dir_given = OutputDir != "";
  SmallString<128> directory(dir_given ? OutputDir : InputFile);

  if (!dir_given) sys::path::remove_filename(directory);
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
  if ((ec = sys::fs::make_absolute(directory)) != errc::success) {
#else
  if (auto ec = sys::fs::make_absolute(directory)) {
#endif
    klee_error("unable to determine absolute path: %s", ec.message().c_str());
  }

  if (dir_given) {
    // OutputDir
    if (mkdir(directory.c_str(), 0775) < 0)
      klee_error("cannot create \"%s\": %s", directory.c_str(), strerror(errno));

    m_outputDirectory = directory;
  } else {
    // "klee-out-<i>"
    int i = 0;
    for (; i <= INT_MAX; ++i) {
      SmallString<128> d(directory);
      llvm::sys::path::append(d, "klee-out-");
      raw_svector_ostream ds(d);
      ds << i;
// SmallString is always up-to-date, no need to flush. See Support/raw_ostream.h
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 8)
      ds.flush();
#endif

      // create directory and try to link klee-last
      if (mkdir(d.c_str(), 0775) == 0) {
        m_outputDirectory = d;

        SmallString<128> klee_last(directory);
        llvm::sys::path::append(klee_last, "klee-last");

        if (((unlink(klee_last.c_str()) < 0) && (errno != ENOENT)) ||
            symlink(m_outputDirectory.c_str(), klee_last.c_str()) < 0) {

          klee_warning("cannot create klee-last symlink: %s", strerror(errno));
        }

        break;
      }

      // otherwise try again or exit on error
      if (errno != EEXIST)
        klee_error("cannot create \"%s\": %s", m_outputDirectory.c_str(), strerror(errno));
    }
    if (i == INT_MAX && m_outputDirectory.str().equals(""))
        klee_error("cannot create output directory: index out of range");
  }

  klee_message("output directory is \"%s\"", m_outputDirectory.c_str());

  // open warnings.txt
  std::string file_path = getOutputFilename("warnings.txt");
  if ((klee_warning_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open messages.txt
  file_path = getOutputFilename("messages.txt");
  if ((klee_message_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open info
  m_infoFile = openOutputFile("info");
}

KleeHandler::~KleeHandler() {
  delete m_pathWriter;
  delete m_symPathWriter;
  fclose(klee_warning_file);
  fclose(klee_message_file);
  delete m_infoFile;
}

void KleeHandler::setInterpreter(Interpreter *i) {
  m_interpreter = i;

  if (WritePaths) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    m_interpreter->setPathWriter(m_pathWriter);
  }

  if (WriteSymPaths) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string KleeHandler::getOutputFilename(const std::string &filename) {
  SmallString<128> path = m_outputDirectory;
  sys::path::append(path,filename);
  return path.str();
}

llvm::raw_fd_ostream *KleeHandler::openOutputFile(const std::string &filename) {
  llvm::raw_fd_ostream *f;
  std::string Error;
  std::string path = getOutputFilename(filename);
  f = klee_open_output_file(path, Error);
  if (!Error.empty()) {
    klee_warning("error opening file \"%s\".  KLEE may have run out of file "
                 "descriptors: try to increase the maximum number of open file "
                 "descriptors by using ulimit (%s).",
                 path.c_str(), Error.c_str());
    return NULL;
  }
  return f;
}

std::string KleeHandler::getTestFilename(const std::string &suffix, unsigned id) {
  std::stringstream filename;
  filename << "test" << std::setfill('0') << std::setw(6) << id << '.' << suffix;
  return filename.str();
}

llvm::raw_fd_ostream *KleeHandler::openTestFile(const std::string &suffix,
                                                unsigned id) {
  return openOutputFile(getTestFilename(suffix, id));
}


/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
void KleeHandler::processTestCase(const ExecutionState &state,
                                  const char *errorMessage,
                                  const char *errorSuffix) {
  if (!NoOutput) {
    std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
    std::vector< HavocedLocation > havocs;
    bool success = m_interpreter->getSymbolicSolution(state, out, havocs);

    if (!success)
      klee_warning("unable to get symbolic solution, losing test case");

    double start_time = util::getWallTime();

    unsigned id = ++m_numTotalTests;

    if (success) {
      KTest b;
      b.numArgs = m_argc;
      b.args = m_argv;
      b.symArgvs = 0;
      b.symArgvLen = 0;
      b.numObjects = out.size();
      b.objects = new KTestObject[b.numObjects];
      assert(b.objects);
      std::string *names = new std::string[b.numObjects];
      for (unsigned i=0; i<b.numObjects; i++) {
        KTestObject *o = &b.objects[i];
        // Drop the '..._1' suffix
        std::string name = out[i].first;
        size_t last_underscore = out[i].first.rfind("_");
        if (last_underscore != std::string::npos) {
          bool all_digits = true;
          for (unsigned j = last_underscore + 1; j < name.size(); ++j) {
            if ('0' <= name[j] && name[j] <= '9') { //fine
            } else {
              all_digits = false;
              break;
            }
          }
          if (all_digits) {
            name = name.substr(0, last_underscore);
          }
        }
        names[i] = name;
        o->name = const_cast<char*>(names[i].c_str());
        o->numBytes = out[i].second.size();
        o->bytes = new unsigned char[o->numBytes];
        assert(o->bytes);
        std::copy(out[i].second.begin(), out[i].second.end(), o->bytes);
      }
      b.numHavocs = havocs.size();
      b.havocs = new KTestHavocedLocation[b.numHavocs];
      assert(b.havocs);
      for (unsigned i=0; i<b.numHavocs; i++) {
        KTestHavocedLocation *o = &b.havocs[i];
        o->name = const_cast<char*>(havocs[i].name.c_str());
        o->numBytes = havocs[i].value.size();
        o->bytes = new unsigned char[o->numBytes];
        assert(o->bytes);
        std::copy(havocs[i].value.begin(), havocs[i].value.end(), o->bytes);
        unsigned mask_size = (o->numBytes + 31)/32*4;
        assert(mask_size <= havocs[i].mask.size());
        o->mask = new uint32_t[mask_size/sizeof(uint32_t)];
        assert(o->mask);
        memcpy(o->mask, havocs[i].mask.get_bits(), mask_size);
        // printf("dumping mask for %s: ", o->name);
        // for (unsigned i = 0; i < mask_size/4*32; ++i) {
        //   uint32_t word = i / 32;
        //   uint32_t bit_id = (i - word * 32);
        //   uint32_t bit_mask = 1 << bit_id;
        //   printf("%s", (bit_mask & o->mask[word]) ? "1" : "0");
        // }
        // printf("\n");
        // fflush(stdout);
      }

      if (!kTest_toFile(&b, getOutputFilename(getTestFilename("ktest", id)).c_str())) {
        klee_warning("unable to write output test case, losing it");
      } else {
        ++m_numGeneratedTests;
      }

      if (DumpCallTraces) {
        llvm::raw_fd_ostream *trace_file =
          openOutputFile(getTestFilename("call_path", id));
        dumpCallPath(state, trace_file);
        delete trace_file;
      }

      for (unsigned i=0; i<b.numObjects; i++)
        delete[] b.objects[i].bytes;
      delete[] b.objects;
      delete[] names;
    }

    if (errorMessage) {
      llvm::raw_ostream *f = openTestFile(errorSuffix, id);
      *f << errorMessage;
      delete f;
    }

    if (m_pathWriter) {
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(m_interpreter->getPathStreamID(state),
                               concreteBranches);
      llvm::raw_fd_ostream *f = openTestFile("path", id);
      for (std::vector<unsigned char>::iterator I = concreteBranches.begin(),
                                                E = concreteBranches.end();
           I != E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (errorMessage || WriteKQueries) {
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
      llvm::raw_ostream *f = openTestFile("kquery", id);
      *f << constraints;
      delete f;
    }

    if (WriteCVCs) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
      llvm::raw_ostream *f = openTestFile("cvc", id);
      *f << constraints;
      delete f;
    }

    if(WriteSMT2s) {
      std::string constraints;
        m_interpreter->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
        llvm::raw_ostream *f = openTestFile("smt2", id);
        *f << constraints;
        delete f;
    }

    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(m_interpreter->getSymbolicPathStreamID(state),
                                  symbolicBranches);
      llvm::raw_fd_ostream *f = openTestFile("sym.path", id);
      for (std::vector<unsigned char>::iterator I = symbolicBranches.begin(), E = symbolicBranches.end(); I!=E; ++I) {
        *f << *I << "\n";
     }
      delete f;
    }

    if (WriteCov) {
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      llvm::raw_ostream *f = openTestFile("cov", id);
      for (std::map<const std::string*, std::set<unsigned> >::iterator
             it = cov.begin(), ie = cov.end();
           it != ie; ++it) {
        for (std::set<unsigned>::iterator
               it2 = it->second.begin(), ie = it->second.end();
             it2 != ie; ++it2)
          *f << *it->first << ":" << *it2 << "\n";
      }
      delete f;
    }

    if (m_numGeneratedTests == StopAfterNTests)
      m_interpreter->setHaltExecution(true);

    if (WriteTestInfo) {
      double elapsed_time = util::getWallTime() - start_time;
      llvm::raw_ostream *f = openTestFile("info", id);
      *f << "Time to generate test case: "
         << elapsed_time << "s\n";
      delete f;
    }
  }
  
  if (errorMessage && OptExitOnError) {
    m_interpreter->prepareForEarlyExit();
    klee_error("EXITING ON ERROR:\n%s\n", errorMessage);
  }
}

bool dumpCallInfo(const CallInfo& ci, llvm::raw_ostream& file) {
  file << ci.callPlace.getLine() <<":" <<ci.f->getName() <<"(";
  assert(ci.returned);
  for (std::vector< CallArg >::const_iterator argIter = ci.args.begin(),
         end = ci.args.end(); argIter != end; ++argIter) {
    const CallArg *arg = &*argIter;
    file <<arg->name <<":";
    file <<*arg->expr;
    if (arg->isPtr) {
      file <<"&";
      if (arg->funPtr == NULL) {
        if (arg->pointee.doTraceValueIn ||
            arg->pointee.doTraceValueOut) {
          file <<"[";
          if (arg->pointee.doTraceValueIn) {
            file <<*arg->pointee.inVal;
          }
          if (arg->pointee.doTraceValueOut &&
              arg->pointee.outVal.isNull()) return false;
          file <<"->";
          if (arg->pointee.doTraceValueOut) {
            file <<*arg->pointee.outVal;
          }
          file <<"]";
          std::map<int, FieldDescr>::const_iterator i =
            arg->pointee.fields.begin(),
            e = arg->pointee.fields.end();
          for (; i != e; ++i) {
            file <<"[" <<i->second.name <<":";
            if (i->second.doTraceValueIn ||
                i->second.doTraceValueOut) {
              if (i->second.doTraceValueIn) {
                file <<*i->second.inVal;
              }
              file << "->";
              if (i->second.doTraceValueOut &&
                  i->second.outVal.isNull()) return false;
              if (i->second.doTraceValueOut) {
                file <<*i->second.outVal;
              }
              file <<"]";
            } else {
              file <<"(...)]";
            }
          }
        } else {
          file <<"[...]";
        }
      } else {
        file <<arg->funPtr->getName();
      }
    }
    if (argIter+1 != end)
      file <<",";
  }
  file <<") -> ";
  if (ci.ret.expr.isNull()) {
    file <<"[]";
  } else {
    file <<*ci.ret.expr;
    if (ci.ret.isPtr) {
      file <<"&";
      if (ci.ret.funPtr == NULL) {
        if (ci.ret.pointee.doTraceValueOut) {
          file <<"[" <<*ci.ret.pointee.outVal <<"]";
          std::map<int, FieldDescr>::const_iterator
            i = ci.ret.pointee.fields.begin(),
            e = ci.ret.pointee.fields.end();
          for (; i != e; ++i) {
            file <<"[" <<i->second.name <<":";
            if (i->second.doTraceValueOut) {
              file <<*i->second.outVal << "]";
            } else {
              file <<"(...)]";
            }
          }
        } else {
          file <<"[...]";
        }
      } else {
        file <<ci.ret.funPtr->getName();
      }
    }
  }
  file <<"\n";
  for (std::map<size_t, CallExtraPtr>::const_iterator i = ci.extraPtrs.begin(),
         e = ci.extraPtrs.end(); i != e; ++i) {
    const CallExtraPtr *extra_ptr = &(*i).second;
    file <<"extra: " <<extra_ptr->name <<"&" <<extra_ptr->ptr <<" = &[";
    if (extra_ptr->pointee.doTraceValueIn) {
      file <<extra_ptr->pointee.inVal;
    } else {
      file <<"(...)";
    }
    if (extra_ptr->pointee.doTraceValueOut) {
      file <<" -> " <<extra_ptr->pointee.outVal;
    } else {
      file <<"-> (...)";
    }
    file <<"]\n";
  }
  return true;
}

void dumpPointeeInSExpr(const FieldDescr& pointee,
                        llvm::raw_ostream& file);

void dumpFieldsInSExpr(const std::map<int, FieldDescr>& fields,
                       llvm::raw_ostream& file) {
  file <<"(break_down (";
  std::map<int, FieldDescr>::const_iterator i = fields.begin(),
    e = fields.end();
  for (; i != e; ++i) {
    file <<"\n((fname \"" <<i->second.name <<"\") (value ";
    dumpPointeeInSExpr(i->second, file);
    file <<") (addr " <<i->second.addr <<"))";
  }
  file <<"))";
}

void dumpPointeeInSExpr(const FieldDescr& pointee,
                        llvm::raw_ostream& file) {
  file << "((full (";
  if (pointee.doTraceValueIn) {
    file <<*pointee.inVal;
  }
  file <<"))\n (sname (";
  if (!pointee.type.empty()) {
    file <<pointee.type;
  }
  file << "))\n";
  dumpFieldsInSExpr(pointee.fields, file);
  file <<")";
}

void dumpPointeeOutSExpr(const FieldDescr& pointee,
                         llvm::raw_ostream& file);

void dumpFieldsOutSExpr(const std::map<int, FieldDescr>& fields,
                        llvm::raw_ostream& file) {
  file <<"(break_down (";
  std::map<int, FieldDescr>::const_iterator i = fields.begin(),
    e = fields.end();
  for (; i != e; ++i) {
    file <<"\n((fname \"" <<i->second.name <<"\") (value ";
    dumpPointeeOutSExpr(i->second, file);
    file <<") (addr " <<i->second.addr <<" ))";
  }
  file <<"))";
}

void dumpPointeeOutSExpr(const FieldDescr& pointee,
                         llvm::raw_ostream& file) {
  file <<"((full (";
  if (pointee.doTraceValueOut) {
    file <<*pointee.outVal;
  }
  file <<"))\n (sname (";
  if (!pointee.type.empty()) {
    file <<pointee.type;
  }
  file <<"))\n";
  dumpFieldsOutSExpr(pointee.fields, file);
  file <<")";
}

bool dumpCallArgSExpr(const CallArg *arg, llvm::raw_ostream& file) {
  file <<"\n((aname \"" <<arg->name <<"\")\n";
  file <<"(value " <<*arg->expr <<")\n";
  file <<"(ptr ";
  if (arg->isPtr) {
    if (arg->funPtr == NULL) {
      if (arg->pointee.doTraceValueIn ||
          arg->pointee.doTraceValueOut) {
        file <<"(Curioptr\n";
        file <<"((before ";
        dumpPointeeInSExpr(arg->pointee, file);
        file <<")\n";
        file <<"(after ";
        dumpPointeeOutSExpr(arg->pointee, file);
        file <<")))\n";
      } else {
        file <<"Apathptr";
      }
    } else {
      file <<"(Funptr \"" <<arg->funPtr->getName() <<"\")";
    }
  } else {
    file <<"Nonptr";
  }
  file <<"))";
  return true;
}

void dumpRetSExpr(const RetVal& ret, llvm::raw_ostream& file) {
  if (ret.expr.isNull()) {
    file <<"(ret ())";
  } else {
    file <<"(ret (((value " <<*ret.expr <<")\n";
    file <<"(ptr ";
    if (ret.isPtr) {
      if (ret.funPtr == NULL) {
        if (ret.pointee.doTraceValueIn ||
            ret.pointee.doTraceValueOut) {
          file <<"(Curioptr ((before ((full ()) (break_down ()) (sname ()))) (after ";
          dumpPointeeOutSExpr(ret.pointee, file);
          file <<")))\n";
        } else {
          file <<"Apathptr";
        }
      } else {
        file <<"(Funptr \"" <<ret.funPtr->getName() <<"\")";
      }
    } else {
      file <<"Nonptr";
    }
    file <<"))))\n";
  }
}

bool dumpExtraPtrSExpr(const CallExtraPtr& cep, llvm::raw_ostream& file) {
  file <<"\n((pname \"" <<cep.name <<"\")\n";
  file <<"(value " <<cep.ptr <<")\n";
  file <<"(ptee ";
  if (cep.accessibleIn) {
    if (cep.accessibleOut) {
      file <<"(Changing (";
      dumpPointeeInSExpr(cep.pointee, file);
      file <<"\n";
      dumpPointeeOutSExpr(cep.pointee, file);
      file <<"))\n";
    } else {
      file <<"(Closing ";
      dumpPointeeInSExpr(cep.pointee, file);
      file <<")\n";
    }
  } else {
    if (cep.accessibleOut) {
      file <<"(Opening ";
      dumpPointeeOutSExpr(cep.pointee, file);
      file <<")\n";
    } else {
      llvm::errs() <<"The extra pointer must be accessible either at "
                   <<"the beginning of a function, at its end or both.\n";
      return false;
    }
  }
  file <<"))\n";
  return true;
}

bool dumpCallInfoSExpr(const CallInfo& ci, llvm::raw_ostream& file) {
  file <<"((fun_name \"" <<ci.f->getName() <<"\")\n (args (";
  assert(ci.returned);
  for (std::vector< CallArg >::const_iterator argIter = ci.args.begin(),
         end = ci.args.end(); argIter != end; ++argIter) {
    const CallArg *arg = &*argIter;
    if (!dumpCallArgSExpr(arg, file)) return false;
  }
  file <<"))\n";
  file <<"(extra_ptrs (";
  std::map<size_t, CallExtraPtr>::const_iterator i = ci.extraPtrs.begin(),
    e = ci.extraPtrs.end();
  for (; i != e; ++i) {
    dumpExtraPtrSExpr(i->second, file);
  }
  file <<"))\n";
  dumpRetSExpr(ci.ret, file);
  file <<"(call_context (";
  for (std::vector<ref<Expr> >::const_iterator cci = ci.callContext.begin(),
         cce = ci.callContext.end(); cci != cce; ++cci) {
    file <<"\n" <<**cci;
  }
  file <<"))\n";
  file <<"(ret_context (";
  for (std::vector<ref<Expr> >::const_iterator rci = ci.returnContext.begin(),
         rce = ci.returnContext.end(); rci != rce; ++rci) {
    file <<"\n" <<**rci;
  }
  file <<")))\n";
  return true;
}

void KleeHandler::processCallPath(const ExecutionState &state) {
  unsigned id = m_callPathIndex;
  if (DumpCallTracePrefixes)
    m_callTree.addCallPath(state.callPath.begin(),
                           state.callPath.end(),
                           id);

  if (!DumpCallTraces) return;

  ++m_callPathIndex;

  std::stringstream filename;
  filename << "call-path" << std::setfill('0') << std::setw(6) << id << '.' << "txt";
  llvm::raw_ostream *file = openOutputFile(filename.str());
  for (std::vector<CallInfo>::const_iterator iter = state.callPath.begin(),
         end = state.callPath.end(); iter != end; ++iter) {
    const CallInfo& ci = *iter;
    bool dumped = dumpCallInfo(ci, *file);
    if (!dumped) break;
  }
  *file <<";;-- Constraints --\n";
  for (ConstraintManager::constraint_iterator ci = state.constraints.begin(),
         cEnd = state.constraints.end(); ci != cEnd; ++ci) {
    *file <<**ci<<"\n";
  }
  delete file;
}

llvm::raw_fd_ostream *KleeHandler::openNextCallPathPrefixFile() {
  unsigned id = ++m_callPathPrefixIndex;
  std::stringstream filename;
  filename << "call-prefix" << std::setfill('0') << std::setw(6) << id << '.' << "txt";
  return openOutputFile(filename.str());
}

void KleeHandler::dumpCallPathPrefixes() {
  m_callTree.dumpCallPrefixesSExpr(std::list<CallInfo>(), this);
  //m_callTree.dumpCallPrefixes(std::list<CallInfo>(), std::list<const std::vector<ref<Expr> >* >(), this);
}

void KleeHandler::dumpCallPath(const ExecutionState &state, llvm::raw_ostream *file) {
  std::vector<klee::ref<klee::Expr> > evalExprs;
  std::vector<const klee::Array *> evalArrays;

  for (auto ci : state.callPath) {
    for (auto e : ci.extraPtrs) {
      if (e.second.pointee.doTraceValueIn) {
        evalExprs.push_back(e.second.pointee.inVal);
      }
      if (e.second.pointee.doTraceValueOut) {
        evalExprs.push_back(e.second.pointee.outVal);
      }
    }
  }

  ExprBuilder *exprBuilder = createDefaultExprBuilder();
  std::string kleaverStr;
  llvm::raw_string_ostream kleaverROS(kleaverStr);
  ExprPPrinter::printQuery(kleaverROS, state.constraints, exprBuilder->False(),
                           &evalExprs[0], &evalExprs[0] + evalExprs.size(),
                           &evalArrays[0], &evalArrays[0] + evalArrays.size(),
                           true);
  kleaverROS.flush();

  *file <<";;-- kQuery --\n";
  *file << kleaverROS.str();

  *file <<";;-- Calls --\n";
  for (std::vector<CallInfo>::const_iterator iter = state.callPath.begin(),
         end = state.callPath.end(); iter != end; ++iter) {
    const CallInfo& ci = *iter;
    bool dumped = dumpCallInfo(ci, *file);
    if (!dumped) break;
  }
  *file <<";;-- Constraints --\n";
  for (ConstraintManager::constraint_iterator ci = state.constraints.begin(),
         cEnd = state.constraints.end(); ci != cEnd; ++ci) {
    *file <<**ci<<"\n";
  }

  *file <<";;-- Tags --\n";
  for (auto it : state.symbolics) {
    if (it.second->name.compare(0, sizeof("vigor_tag_") - 1, "vigor_tag_") == 0) {
      const klee::ObjectState *addrOS = state.addressSpace.findObject(it.first);
      assert(addrOS && "Tag not set.");

      klee::ref<klee::Expr> addrExpr =
          addrOS->read(0, klee::Context::get().getPointerWidth());
      assert(isa<klee::ConstantExpr>(addrExpr) && "Tag address is symbolic.");
      klee::ref<klee::ConstantExpr> address =
          cast<klee::ConstantExpr>(addrExpr);
      klee::ObjectPair op;
      assert(state.addressSpace.resolveOne(address, op) &&
             "Tag address is not uniquely defined.");
      const klee::MemoryObject *mo = op.first;
      const klee::ObjectState *os = op.second;

      char *buf = new char[mo->size];
      unsigned ioffset = 0;
      klee::ref<klee::Expr> offset_expr =
          klee::SubExpr::create(address, op.first->getBaseExpr());
      assert(isa<klee::ConstantExpr>(offset_expr) &&
             "Tag is an invalid string.");
      klee::ref<klee::ConstantExpr> value =
          cast<klee::ConstantExpr>(offset_expr.get());
      ioffset = value.get()->getZExtValue();
      assert(ioffset < mo->size);

      unsigned i;
      for (i = 0; i < mo->size - ioffset - 1; i++) {
        klee::ref<klee::Expr> cur = os->read8(i + ioffset);
        assert(isa<klee::ConstantExpr>(cur) &&
               "Symbolic character in tag value.");
        buf[i] = cast<klee::ConstantExpr>(cur)->getZExtValue(8);
      }
      buf[i] = 0;

      *file << it.second->name.substr(sizeof("vigor_tag_") - 1) << " = " << buf << "\n";
      delete buf;
    }
  }
}


  // load a .path file
void KleeHandler::loadPathFile(std::string name,
                                     std::vector<bool> &buffer) {
  std::ifstream f(name.c_str(), std::ios::in | std::ios::binary);

  if (!f.good())
    assert(0 && "unable to open path file");

  while (f.good()) {
    unsigned value;
    f >> value;
    buffer.push_back(!!value);
    f.get();
  }
}

void KleeHandler::getKTestFilesInDir(std::string directoryPath,
                                     std::vector<std::string> &results) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
#else
  std::error_code ec;
#endif
  llvm::sys::fs::directory_iterator i(directoryPath, ec), e;
  for (; i != e && !ec; i.increment(ec)) {
    auto f = i->path();
    if (f.size() >= 6 && f.substr(f.size()-6,f.size()) == ".ktest") {
      results.push_back(f);
    }
  }

  if (ec) {
    llvm::errs() << "ERROR: unable to read output directory: " << directoryPath
                 << ": " << ec.message() << "\n";
    exit(1);
  }
}

std::string KleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env)
    return std::string(env);

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(
      llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)
      );

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  }
  else
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                       libDir.c_str() << "\n");
  return libDir.str();
}

void CallTree::addCallPath(std::vector<CallInfo>::const_iterator path_begin,
                           std::vector<CallInfo>::const_iterator path_end,
                           unsigned path_id) {
  //TODO: do we process constraints (what if they are different from the old ones?)
  //TODO: record assumptions for each item in the call-path, because, when
  // comparing two paths in the tree they may differ only by the assumptions.
  if (path_begin == path_end) return;
  std::vector<CallInfo>::const_iterator next = path_begin;
  ++next;
  std::vector<CallTree*>::iterator i = children.begin(), ie = children.end();
  for (; i != ie; ++i) {
    if ((*i)->tip.call.eq(*path_begin)) {
      (*i)->addCallPath(next, path_end, path_id);
      return;
    }
  }
  children.push_back(new CallTree());
  CallTree* n = children.back();
  n->tip.call = *path_begin;
  n->tip.path_id = path_id;
  n->addCallPath(next, path_end, path_id);
}

std::vector<std::vector<CallPathTip*> > CallTree::groupChildren() {
  std::vector<std::vector<CallPathTip*> > ret;
  for (unsigned ci = 0; ci < children.size(); ++ci) {
    CallPathTip* current = &children[ci]->tip;
    bool groupNotFound = true;
    for (unsigned gi = 0; gi < ret.size(); ++gi) {
      if (current->call.sameInvocation(&ret[gi][0]->call)) {
        ret[gi].push_back(current);
        groupNotFound = false;
        break;
      }
    }
    if (groupNotFound) {
      ret.push_back(std::vector<CallPathTip*>());
      ret.back().push_back(current);
    }
  }
  return ret;
}

void dumpCallGroup(const std::vector<CallInfo*> group, llvm::raw_ostream& file) {
  std::vector<CallInfo*>::const_iterator gi = group.begin(), ge = group.end();
  file << (**gi).f->getName() <<"(";
  for (unsigned argI = 0; argI < (**gi).args.size(); ++argI) {
    const CallArg& arg = (**gi).args[argI];
    file <<arg.name <<":";
    file <<*arg.expr;
    if (arg.isPtr) {
      file <<"&";
      if (arg.funPtr != NULL) {
        file <<arg.funPtr->getName();
      } else {
        file << "[";
        if (arg.pointee.doTraceValueIn) {
           file << arg.pointee.inVal;
        }
        file << "->";
        for (; gi != ge; ++gi) {
          file <<*(**gi).args[argI].pointee.outVal <<"; ";
        }
        file <<"]";
        gi = group.begin();
        unsigned numFields = arg.pointee.fields.size();
        for (; gi != ge; ++gi) {
          assert((**gi).args[argI].pointee.fields.size() == numFields &&
                 "Do not support variating the argument structure for different"
                 " calls of the same function.");
        }
        gi = group.begin();
        std::map<int, FieldDescr>::const_iterator
          fi = arg.pointee.fields.begin(),
          fe = arg.pointee.fields.end();
        for (; fi != fe; ++fi) {
          int fieldOffset = fi->first;
          const FieldDescr& descr = fi->second;
          file <<"[";
          if (descr.doTraceValueIn) {
            file <<descr.name <<":" <<*descr.inVal;
          }
          file << "->";
          for (; gi != ge; ++gi) {
            std::map<int, FieldDescr>::const_iterator otherDescrI =
              (**gi).args[argI].pointee.fields.find(fieldOffset);
            assert(otherDescrI != (**gi).args[argI].pointee.fields.end() &&
                   "The argument structure is different.");
            file <<*otherDescrI->second.outVal <<";";
          }
          file <<"]";
          gi = group.begin();
        }
      }
    }
  }
  file <<") ->";
  const RetVal& ret = (**gi).ret;
  if (ret.expr.isNull()) {
    for (; gi != ge; ++gi) {
      assert((**gi).ret.expr.isNull() &&
             "Do not support different return"
             " behaviours for the same function.");
    }
    gi = group.begin();
    file <<"[]";
  } else {
    if (ret.isPtr) {
      for (; gi != ge; ++gi) {
        assert((**gi).ret.isPtr &&
               "Do not support different return"
               " behaviours for the same function.");
      }
      gi = group.begin();
      file <<"&";
      if (ret.funPtr != NULL) {
        for (; gi != ge; ++gi) {
          assert((**gi).ret.funPtr != NULL &&
                 "Do not support different return"
                 " behaviours for the same function.");
          file <<(**gi).ret.funPtr->getName() <<";";
        }
        gi = group.begin();
      } else {
        for (; gi != ge; ++gi) {
          file <<*(**gi).ret.pointee.outVal <<";";
        }
        gi = group.begin();
        std::map<int, FieldDescr>::const_iterator
          fi = ret.pointee.fields.begin(),
          fe = ret.pointee.fields.end();
        for (; fi != fe; ++fi) {
          int fieldOffset = fi->first;
          const FieldDescr& descr = fi->second;
          file <<"[" <<descr.name <<":";
          for (; gi != ge; ++gi) {
            std::map<int, FieldDescr>::const_iterator otherDescrI =
              (**gi).ret.pointee.fields.find(fieldOffset);
            assert(otherDescrI != (**gi).ret.pointee.fields.end() &&
                   "The return structure is different.");
            file <<*otherDescrI->second.outVal <<";";
          }
          file <<"]";
          gi = group.begin();
        }
      }
    } else {
      for (; gi != ge; ++gi) {
        file <<(**gi).ret.expr <<";";
      }
    }
  }
  file <<"\n";
}

void CallTree::dumpCallPrefixes(std::list<CallInfo> accumulated_prefix,
                                std::list<const std::vector<ref<Expr> >* >
                                accumulated_context,
                                KleeHandler* fileOpener) {
  std::vector<std::vector<CallPathTip*> > tipCalls = groupChildren();
  std::vector<std::vector<CallPathTip*> >::iterator ti = tipCalls.begin(),
    te = tipCalls.end();
  for (; ti != te; ++ti) {
    llvm::raw_ostream* file = fileOpener->openNextCallPathPrefixFile();
    std::list<CallInfo>::iterator ai = accumulated_prefix.begin(),
      ae = accumulated_prefix.end();
    for (; ai != ae; ++ai) {
      bool dumped = dumpCallInfo(*ai, *file);
      assert(dumped);
    }
    *file <<"--- Constraints ---\n";
    for (std::list<const std::vector<ref<Expr> >* >::const_iterator
           cgi = accumulated_context.begin(),
           cge = accumulated_context.end(); cgi != cge; ++cgi) {
      for (std::vector<ref<Expr> >::const_iterator ci = (**cgi).begin(),
             ce = (**cgi).end(); ci != ce; ++ci) {
        *file <<**ci<<"\n";
      }
      *file<<"---\n";
    }
    *file <<"--- Alternatives ---\n";
    //FIXME: currently there can not be more than one alternative.
    *file <<"(or \n";
    for (std::vector<CallPathTip*>::const_iterator chi = ti->begin(),
           che = ti->end(); chi != che; ++chi) {
      *file <<"(and \n";
      bool dumped = dumpCallInfo((**chi).call, *file);
      assert(dumped);
      for (std::vector<ref<Expr> >::const_iterator ei =
             (**chi).call.callContext.begin(),
             ee = (**chi).call.callContext.end(); ei != ee; ++ei) {
        *file <<**ei<<"\n";
      }
      for (std::vector<ref<Expr> >::const_iterator ei =
             (**chi).call.returnContext.begin(),
             ee = (**chi).call.returnContext.end(); ei != ee; ++ei) {
        *file <<**ei<<"\n";
      }
      *file <<"true)\n";
    }
    *file <<"false)\n";
    delete file;
  }
  std::vector< CallTree* >::iterator ci = children.begin(),
    ce = children.end();
  for (; ci != ce; ++ci) {
    accumulated_prefix.push_back(( *ci )->tip.call);
    accumulated_context.push_back(&(*ci)->tip.call.callContext);
    accumulated_context.push_back(&(*ci)->tip.call.returnContext);
    ( *ci )->dumpCallPrefixes(accumulated_prefix, accumulated_context, fileOpener);
    accumulated_context.pop_back();
    accumulated_context.pop_back();
    accumulated_prefix.pop_back();
  }
}

void CallTree::dumpCallPrefixesSExpr(std::list<CallInfo> accumulated_prefix,
                                     KleeHandler* fileOpener) {
  std::vector<std::vector<CallPathTip*> > tipCalls = groupChildren();
  std::vector<std::vector<CallPathTip*> >::iterator ti = tipCalls.begin(),
    te = tipCalls.end();
  for (; ti != te; ++ti) {
    llvm::raw_ostream* file = fileOpener->openNextCallPathPrefixFile();
    std::list<CallInfo>::iterator ai = accumulated_prefix.begin(),
      ae = accumulated_prefix.end();
    *file <<"((history (\n";
    for (; ai != ae; ++ai) {
      bool dumped = dumpCallInfoSExpr(*ai, *file);
      assert(dumped);
    }
    *file <<"))\n";
    //FIXME: currently there can not be more than one alternative.
    *file <<"(tip_calls (\n";
    for (std::vector<CallPathTip*>::const_iterator chi = ti->begin(),
           che = ti->end(); chi != che; ++chi) {
      *file <<"; id: " <<(**chi).path_id <<"(" <<(**chi).call.callPlace.getLine() <<")\n";
      bool dumped = dumpCallInfoSExpr((**chi).call, *file);
      assert(dumped);
    }
    *file <<")))\n";
    delete file;
  }
  std::vector< CallTree* >::iterator ci = children.begin(),
    ce = children.end();
  for (; ci != ce; ++ci) {
    accumulated_prefix.push_back(( *ci )->tip.call);
    ( *ci )->dumpCallPrefixesSExpr(accumulated_prefix, fileOpener);
    accumulated_prefix.pop_back();
  }
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static std::string strip(std::string &in) {
  unsigned len = in.size();
  unsigned lead = 0, trail = len;
  while (lead<len && isspace(in[lead]))
    ++lead;
  while (trail>lead && isspace(in[trail-1]))
    --trail;
  return in.substr(lead, trail-lead);
}

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  // This version always reads response files
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

static void
preparePOSIX(std::vector<std::unique_ptr<llvm::Module>> &loadedModules,
             llvm::StringRef libCPrefix) {
  // Get the main function from the main module and rename it such that it can
  // be called after the POSIX setup
  Function *mainFn = nullptr;
  for (auto &module : loadedModules) {
    mainFn = module->getFunction(EntryPoint);
    if (mainFn)
      break;
  }

  if (!mainFn)
    klee_error("Entry function '%s' not found in module.", EntryPoint.c_str());
  mainFn->setName("__klee_posix_wrapped_main");

  // Add a definition of the entry function if needed. This is the case if we
  // link against a libc implementation. Preparing for libc linking (i.e.
  // linking with uClibc will expect a main function and rename it to
  // _user_main. We just provide the definition here.
  if (!libCPrefix.empty())
    mainFn->getParent()->getOrInsertFunction(EntryPoint,
                                             mainFn->getFunctionType());

  llvm::Function *wrapper = nullptr;
  for (auto &module : loadedModules) {
    wrapper = module->getFunction("__klee_posix_wrapper");
    if (wrapper)
      break;
  }
  assert(wrapper && "klee_posix_wrapper not found");

  // Rename the POSIX wrapper to prefixed entrypoint, e.g. _user_main as uClibc
  // would expect it or main otherwise
  wrapper->setName(libCPrefix + EntryPoint);
}


// This is a terrible hack until we get some real modeling of the
// system. All we do is check the undefined symbols and warn about
// any "unrecognized" externals and about any obviously unsafe ones.

// Symbols we explicitly support
static const char *modelledExternals[] = {
  "_ZTVN10__cxxabiv117__class_type_infoE",
  "_ZTVN10__cxxabiv120__si_class_type_infoE",
  "_ZTVN10__cxxabiv121__vmi_class_type_infoE",

  "klee_trace_extra_ptr",
  "klee_trace_extra_ptr_field",
  "klee_trace_extra_ptr_nested_field",
  "klee_trace_extra_ptr_nested_nested_field",
  "klee_trace_param_i64",
  "klee_trace_param_ptr_directed",
  "klee_trace_param_ptr_field_directed",
  "klee_trace_param_ptr_nested_field_directed",
  "klee_trace_param_u16",
  "klee_trace_param_u64",

  // special functions
  "_stdio_init",
  "_assert",
  "__assert_fail",
  "__assert_rtn",
  "__errno_location",
  "__error",
  "calloc",
  "_exit",
  "exit",
  "free",
  "abort",
  "klee_abort",
  "klee_assume",
  "klee_check_memory_access",
  "klee_define_fixed_object",
  "klee_get_errno",
  "klee_get_valuef",
  "klee_get_valued",
  "klee_get_valuel",
  "klee_get_valuell",
  "klee_get_value_i32",
  "klee_get_value_i64",
  "klee_get_obj_size",
  "klee_intercept_reads",
  "klee_intercept_writes",
  "klee_is_symbolic",
  "klee_make_symbolic",
  "klee_mark_global",
  "klee_open_merge",
  "klee_close_merge",
  "klee_prefer_cex",
  "klee_posix_prefer_cex",
  "klee_print_expr",
  "klee_print_range",
  "klee_report_error",
  "klee_trace_param_fptr",
  "klee_trace_param_i32",
  "klee_trace_param_u32",
  "klee_trace_param_ptr",
  "klee_trace_param_just_ptr",
  "klee_trace_param_ptr_field",
  "klee_trace_param_ptr_field_just_ptr",
  "klee_trace_param_ptr_nested_field",
  "klee_trace_param_tagged_ptr",
  "klee_trace_ret",
  "klee_induce_invariants",
  "klee_trace_ret_ptr",
  "klee_trace_ret_ptr_field",
  "klee_forbid_access",
  "klee_allow_access",
  "klee_set_forking",
  "klee_silent_exit",
  "klee_warning",
  "klee_warning_once",
  "klee_alias_function",
  "klee_alias_function_regex",
  "klee_alias_undo",
  "klee_stack_trace",
  "llvm.dbg.declare",
  "llvm.dbg.value",
  "llvm.va_start",
  "llvm.va_end",
  "malloc",
  "realloc",
  "_ZdaPv",
  "_ZdlPv",
  "_Znaj",
  "_Znwj",
  "_Znam",
  "_Znwm",
  "__ubsan_handle_add_overflow",
  "__ubsan_handle_sub_overflow",
  "__ubsan_handle_mul_overflow",
  "__ubsan_handle_divrem_overflow",
  "__ubsan_handle_negate_overflow"
};
// Symbols we aren't going to warn about
static const char *dontCareExternals[] = {
#if 0
  // stdio
  "fprintf",
  "fflush",
  "fopen",
  "fclose",
  "fputs_unlocked",
  "putchar_unlocked",
  "vfprintf",
  "fwrite",
  "puts",
  "printf",
  "stdin",
  "stdout",
  "stderr",
  "_stdio_term",
  "__errno_location",
  "fstat",
#endif

  // static information, pretty ok to return
  "getegid",
  "geteuid",
  "getgid",
  "getuid",
  "getpid",
  "gethostname",
  "getpgrp",
  "getppid",
  "getpagesize",
  "getpriority",
  "getgroups",
  "getdtablesize",
  "getrlimit",
  "getrlimit64",
  "getcwd",
  "getwd",
  "gettimeofday",
  "uname",

  // fp stuff we just don't worry about yet
  "frexp",
  "ldexp",
  "__isnan",
  "__signbit",
};
// Extra symbols we aren't going to warn about with klee-libc
static const char *dontCareKlee[] = {
  "__ctype_b_loc",
  "__ctype_get_mb_cur_max",

  // io system calls
  "open",
  "write",
  "read",
  "close",
};
// Extra symbols we aren't going to warn about with uclibc
static const char *dontCareUclibc[] = {
  "__dso_handle",

  // Don't warn about these since we explicitly commented them out of
  // uclibc.
  "printf",
  "vprintf"
};
// Symbols we consider unsafe
static const char *unsafeExternals[] = {
  "fork", // oh lord
  "exec", // heaven help us
  "error", // calls _exit
  "raise", // yeah
  "kill", // mmmhmmm
};
#define NELEMS(array) (sizeof(array)/sizeof(array[0]))
void externalsAndGlobalsCheck(const llvm::Module *m) {
  std::map<std::string, bool> externals;
  std::set<std::string> modelled(modelledExternals,
                                 modelledExternals+NELEMS(modelledExternals));
  std::set<std::string> dontCare(dontCareExternals,
                                 dontCareExternals+NELEMS(dontCareExternals));
  std::set<std::string> unsafe(unsafeExternals,
                               unsafeExternals+NELEMS(unsafeExternals));

  switch (Libc) {
  case LibcType::KleeLibc:
    dontCare.insert(dontCareKlee, dontCareKlee+NELEMS(dontCareKlee));
    break;
  case LibcType::UcLibc:
    dontCare.insert(dontCareUclibc,
                    dontCareUclibc+NELEMS(dontCareUclibc));
    break;
  case LibcType::FreeStandingLibc: /* silence compiler warning */
    break;
  }

  if (WithPOSIXRuntime)
    dontCare.insert("syscall");

  for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end();
       fnIt != fn_ie; ++fnIt) {
    if (fnIt->isDeclaration() && !fnIt->use_empty())
      externals.insert(std::make_pair(fnIt->getName(), false));
    for (Function::const_iterator bbIt = fnIt->begin(), bb_ie = fnIt->end();
         bbIt != bb_ie; ++bbIt) {
      for (BasicBlock::const_iterator it = bbIt->begin(), ie = bbIt->end();
           it != ie; ++it) {
        if (const CallInst *ci = dyn_cast<CallInst>(it)) {
          if (isa<InlineAsm>(ci->getCalledValue())) {
            klee_warning_once(&*fnIt,
                              "function \"%s\" has inline asm",
                              fnIt->getName().data());
          }
        }
      }
    }
  }
  for (Module::const_global_iterator
         it = m->global_begin(), ie = m->global_end();
       it != ie; ++it)
    if (it->isDeclaration() && !it->use_empty())
      externals.insert(std::make_pair(it->getName(), true));
  // and remove aliases (they define the symbol after global
  // initialization)
  for (Module::const_alias_iterator
         it = m->alias_begin(), ie = m->alias_end();
       it != ie; ++it) {
    std::map<std::string, bool>::iterator it2 =
      externals.find(it->getName());
    if (it2!=externals.end())
      externals.erase(it2);
  }

  std::map<std::string, bool> foundUnsafe;
  for (std::map<std::string, bool>::iterator
         it = externals.begin(), ie = externals.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    if (!modelled.count(ext) && (WarnAllExternals ||
                                 !dontCare.count(ext))) {
      if (unsafe.count(ext)) {
        foundUnsafe.insert(*it);
      } else {
        klee_warning("undefined reference to %s: %s",
                     it->second ? "variable" : "function",
                     ext.c_str());
      }
    }
  }

  for (std::map<std::string, bool>::iterator
         it = foundUnsafe.begin(), ie = foundUnsafe.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    klee_warning("undefined reference to %s: %s (UNSAFE)!",
                 it->second ? "variable" : "function",
                 ext.c_str());
  }
}

static Interpreter *theInterpreter = 0;

static bool interrupted = false;

// Pulled out so it can be easily called from a debugger.
extern "C"
void halt_execution() {
  theInterpreter->setHaltExecution(true);
}

extern "C"
void stop_forking() {
  theInterpreter->setInhibitForking(true);
}

static void interrupt_handle() {
  if (!interrupted && theInterpreter) {
    llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
    halt_execution();
    sys::SetInterruptFunction(interrupt_handle);
  } else {
    llvm::errs() << "KLEE: ctrl-c detected, exiting.\n";
    exit(1);
  }
  interrupted = true;
}

static void interrupt_handle_watchdog() {
  // just wait for the child to finish
}

// This is a temporary hack. If the running process has access to
// externals then it can disable interrupts, which screws up the
// normal "nice" watchdog termination process. We try to request the
// interpreter to halt using this mechanism as a last resort to save
// the state data before going ahead and killing it.
static void halt_via_gdb(int pid) {
  char buffer[256];
  sprintf(buffer,
          "gdb --batch --eval-command=\"p halt_execution()\" "
          "--eval-command=detach --pid=%d &> /dev/null",
          pid);
  //  fprintf(stderr, "KLEE: WATCHDOG: running: %s\n", buffer);
  if (system(buffer)==-1)
    perror("system");
}

// returns the end of the string put in buf
static char *format_tdiff(char *buf, long seconds)
{
  assert(seconds >= 0);

  long minutes = seconds / 60;  seconds %= 60;
  long hours   = minutes / 60;  minutes %= 60;
  long days    = hours   / 24;  hours   %= 24;

  buf = strrchr(buf, '\0');
  if (days > 0) buf += sprintf(buf, "%ld days, ", days);
  buf += sprintf(buf, "%02ld:%02ld:%02ld", hours, minutes, seconds);
  return buf;
}

#ifndef SUPPORT_KLEE_UCLIBC
static void
linkWithUclibc(StringRef libDir,
               std::vector<std::unique_ptr<llvm::Module>> &modules) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module,
		const char *old_name, const char *new_name)
{
  Function *new_function, *old_function;
  new_function = module->getFunction(new_name);
  old_function = module->getFunction(old_name);
  if (old_function) {
    if (new_function) {
      old_function->replaceAllUsesWith(new_function);
      old_function->eraseFromParent();
    } else {
      old_function->setName(new_name);
      assert(old_function->getName() == new_name);
    }
  }
}

static void
createLibCWrapper(std::vector<std::unique_ptr<llvm::Module>> &modules,
                  llvm::StringRef intendedFunction,
                  llvm::StringRef libcMainFunction) {
  // XXX we need to rearchitect so this can also be used with
  // programs externally linked with libc implementation.

  // We now need to swap things so that libcMainFunction is the entry
  // point, in such a way that the arguments are passed to
  // libcMainFunction correctly. We do this by renaming the user main
  // and generating a stub function to call intendedFunction. There is
  // also an implicit cooperation in that runFunctionAsMain sets up
  // the environment arguments to what a libc expects (following
  // argv), since it does not explicitly take an envp argument.
  auto &ctx = modules[0]->getContext();
  Function *userMainFn = modules[0]->getFunction(intendedFunction);
  assert(userMainFn && "unable to get user main");
  // Rename entry point using a prefix
  userMainFn->setName("__user_" + intendedFunction);

  // force import of libcMainFunction
  llvm::Function *libcMainFn = nullptr;
  for (auto &module : modules) {
    if ((libcMainFn = module->getFunction(libcMainFunction)))
      break;
  }
  if (!libcMainFn)
    klee_error("Could not add %s wrapper", libcMainFunction.str().c_str());

  auto inModuleRefernce = libcMainFn->getParent()->getOrInsertFunction(
      userMainFn->getName(), userMainFn->getFunctionType());

  const auto ft = libcMainFn->getFunctionType();

  if (ft->getNumParams() != 7)
    klee_error("Imported %s wrapper does not have the correct "
               "number of arguments",
               libcMainFunction.str().c_str());

  std::vector<Type *> fArgs;
  fArgs.push_back(ft->getParamType(1)); // argc
  fArgs.push_back(ft->getParamType(2)); // argv
  Function *stub =
      Function::Create(FunctionType::get(Type::getInt32Ty(ctx), fArgs, false),
                       GlobalVariable::ExternalLinkage, intendedFunction,
                       libcMainFn->getParent());
  BasicBlock *bb = BasicBlock::Create(ctx, "entry", stub);
  llvm::IRBuilder<> Builder(bb);

  std::vector<llvm::Value*> args;
  args.push_back(
      llvm::ConstantExpr::getBitCast(inModuleRefernce, ft->getParamType(0)));
  args.push_back(&*(stub->arg_begin())); // argc
  args.push_back(&*(++stub->arg_begin())); // argv
  args.push_back(Constant::getNullValue(ft->getParamType(3))); // app_init
  args.push_back(Constant::getNullValue(ft->getParamType(4))); // app_fini
  args.push_back(Constant::getNullValue(ft->getParamType(5))); // rtld_fini
  args.push_back(Constant::getNullValue(ft->getParamType(6))); // stack_end
  Builder.CreateCall(libcMainFn, args);
  Builder.CreateUnreachable();
}

static void
linkWithUclibc(StringRef libDir,
               std::vector<std::unique_ptr<llvm::Module>> &modules) {
  LLVMContext &ctx = modules[0]->getContext();

  size_t newModules = modules.size();

  // Ensure that klee-uclibc exists
  SmallString<128> uclibcBCA(libDir);
  std::string errorMsg;
  llvm::sys::path::append(uclibcBCA, KLEE_UCLIBC_BCA_NAME);
  if (!klee::loadFile(uclibcBCA.c_str(), ctx, modules, errorMsg))
    klee_error("Cannot find klee-uclibc '%s': %s", uclibcBCA.c_str(),
               errorMsg.c_str());

  for (auto i = newModules, j = modules.size(); i < j; ++i) {
    replaceOrRenameFunction(modules[i].get(), "__libc_open", "open");
    replaceOrRenameFunction(modules[i].get(), "__libc_fcntl", "fcntl");
  }

  createLibCWrapper(modules, EntryPoint, "__uClibc_main");
  klee_message("NOTE: Using klee-uclibc : %s", uclibcBCA.c_str());
}
#endif

int main(int argc, char **argv, char **envp) {
  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.

  llvm::InitializeNativeTarget();

  parseArguments(argc, argv);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 9)
  sys::PrintStackTraceOnErrorSignal(argv[0]);
#else
  sys::PrintStackTraceOnErrorSignal();
#endif

  if (Watchdog) {
    if (MaxTime==0) {
      klee_error("--watchdog used without --max-time");
    }

    int pid = fork();
    if (pid<0) {
      klee_error("unable to fork watchdog");
    } else if (pid) {
      klee_message("KLEE: WATCHDOG: watching %d\n", pid);
      fflush(stderr);
      sys::SetInterruptFunction(interrupt_handle_watchdog);

      double nextStep = util::getWallTime() + MaxTime*1.1;
      int level = 0;

      // Simple stupid code...
      while (1) {
        sleep(1);

        int status, res = waitpid(pid, &status, WNOHANG);

        if (res < 0) {
          if (errno==ECHILD) { // No child, no need to watch but
                               // return error since we didn't catch
                               // the exit.
            klee_warning("KLEE: watchdog exiting (no child)\n");
            return 1;
          } else if (errno!=EINTR) {
            perror("watchdog waitpid");
            exit(1);
          }
        } else if (res==pid && WIFEXITED(status)) {
          return WEXITSTATUS(status);
        } else {
          double time = util::getWallTime();

          if (time > nextStep) {
            ++level;

            if (level==1) {
              klee_warning(
                  "KLEE: WATCHDOG: time expired, attempting halt via INT\n");
              kill(pid, SIGINT);
            } else if (level==2) {
              klee_warning(
                  "KLEE: WATCHDOG: time expired, attempting halt via gdb\n");
              halt_via_gdb(pid);
            } else {
              klee_warning(
                  "KLEE: WATCHDOG: kill(9)ing child (I tried to be nice)\n");
              kill(pid, SIGKILL);
              return 1; // what more can we do
            }

            // Ideally this triggers a dump, which may take a while,
            // so try and give the process extra time to clean up.
            nextStep = util::getWallTime() + std::max(15., MaxTime*.1);
          }
        }
      }

      return 0;
    }
  }

  sys::SetInterruptFunction(interrupt_handle);

  // Load the bytecode...
  std::string errorMsg;
  LLVMContext ctx;
  std::vector<std::unique_ptr<llvm::Module>> loadedModules;
  if (!klee::loadFile(InputFile, ctx, loadedModules, errorMsg)) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               errorMsg.c_str());
  }
  // Load and link the whole files content. The assumption is that this is the
  // application under test.
  // Nothing gets removed in the first place.
  std::unique_ptr<llvm::Module> M(klee::linkModules(
      loadedModules, "" /* link all modules together */, errorMsg));
  if (!M) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               errorMsg.c_str());
  }

  llvm::Module *mainModule = M.get();
  // Push the module as the first entry
  loadedModules.emplace_back(std::move(M));

  std::string LibraryDir = KleeHandler::getRunTimeLibraryPath(argv[0]);
  Interpreter::ModuleOptions Opts(LibraryDir.c_str(), EntryPoint,
                                  /*Optimize=*/OptimizeModule,
                                  /*CheckDivZero=*/CheckDivZero,
                                  /*CheckOvershift=*/CheckOvershift);

  if (WithPOSIXRuntime) {
    SmallString<128> Path(Opts.LibraryDir);
    llvm::sys::path::append(Path, "libkleeRuntimePOSIX.bca");
    klee_message("NOTE: Using POSIX model: %s", Path.c_str());
    if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
                        errorMsg))
      klee_error("error loading POSIX support '%s': %s", Path.c_str(),
                 errorMsg.c_str());

    std::string libcPrefix = (Libc == LibcType::UcLibc ? "__user_" : "");
    preparePOSIX(loadedModules, libcPrefix);
  }

  switch (Libc) {
  case LibcType::KleeLibc: {
    // FIXME: Find a reasonable solution for this.
    SmallString<128> Path(Opts.LibraryDir);
    llvm::sys::path::append(Path, "libklee-libc.bca");
    if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
                        errorMsg))
      klee_error("error loading klee libc '%s': %s", Path.c_str(),
                 errorMsg.c_str());
  }
  /* Falls through. */
  case LibcType::FreeStandingLibc: {
    SmallString<128> Path(Opts.LibraryDir);
    llvm::sys::path::append(Path, "libkleeRuntimeFreeStanding.bca");
    if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
                        errorMsg))
      klee_error("error loading free standing support '%s': %s", Path.c_str(),
                 errorMsg.c_str());
    break;
  }
  case LibcType::UcLibc:
    linkWithUclibc(LibraryDir, loadedModules);
    break;
  }

  for (const auto &library : LinkLibraries) {
    if (!klee::loadFile(library, mainModule->getContext(), loadedModules,
                        errorMsg))
      klee_error("error loading free standing support '%s': %s",
                 library.c_str(), errorMsg.c_str());
  }

  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.
  Function *mainFn = mainModule->getFunction(EntryPoint);
  if (!mainFn) {
    klee_error("'%s' function not found in module.", EntryPoint.c_str());
  }

  // FIXME: Change me to std types.
  int pArgc;
  char **pArgv;
  char **pEnvp;
  if (Environ != "") {
    std::vector<std::string> items;
    std::ifstream f(Environ.c_str());
    if (!f.good())
      klee_error("unable to open --environ file: %s", Environ.c_str());
    while (!f.eof()) {
      std::string line;
      std::getline(f, line);
      line = strip(line);
      if (!line.empty())
        items.push_back(line);
    }
    f.close();
    pEnvp = new char *[items.size()+1];
    unsigned i=0;
    for (; i != items.size(); ++i)
      pEnvp[i] = strdup(items[i].c_str());
    pEnvp[i] = 0;
  } else {
    pEnvp = envp;
  }

  pArgc = InputArgv.size() + 1;
  pArgv = new char *[pArgc];
  for (unsigned i=0; i<InputArgv.size()+1; i++) {
    std::string &arg = (i==0 ? InputFile : InputArgv[i-1]);
    unsigned size = arg.size() + 1;
    char *pArg = new char[size];

    std::copy(arg.begin(), arg.end(), pArg);
    pArg[size - 1] = 0;

    pArgv[i] = pArg;
  }

  std::vector<bool> replayPath;

  if (ReplayPathFile != "") {
    KleeHandler::loadPathFile(ReplayPathFile, replayPath);
  }

  Interpreter::InterpreterOptions IOpts;
  IOpts.MakeConcreteSymbolic = MakeConcreteSymbolic;
  IOpts.CondoneUndeclaredHavocs = CondoneUndeclaredHavocs;
  KleeHandler *handler = new KleeHandler(pArgc, pArgv);
  Interpreter *interpreter =
    theInterpreter = Interpreter::create(ctx, IOpts, handler);
  assert(interpreter);
  handler->setInterpreter(interpreter);

  for (int i=0; i<argc; i++) {
    handler->getInfoStream() << argv[i] << (i+1<argc ? " ":"\n");
  }
  handler->getInfoStream() << "PID: " << getpid() << "\n";

  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.

  auto finalModule = interpreter->setModule(loadedModules, Opts);
  Function *mainFn = finalModule->getFunction(EntryPoint);
  if (!mainFn) {
    klee_error("Entry function '%s' not found in module.", EntryPoint.c_str());
  }

  externalsAndGlobalsCheck(finalModule);

  if (ReplayPathFile != "") {
    interpreter->setReplayPath(&replayPath);
  }

  char buf[256];
  time_t t[2];
  t[0] = time(NULL);
  strftime(buf, sizeof(buf), "Started: %Y-%m-%d %H:%M:%S\n", localtime(&t[0]));
  handler->getInfoStream() << buf;
  handler->getInfoStream().flush();

  if (!ReplayKTestDir.empty() || !ReplayKTestFile.empty()) {
    assert(SeedOutFile.empty());
    assert(SeedOutDir.empty());

    std::vector<std::string> kTestFiles = ReplayKTestFile;
    for (std::vector<std::string>::iterator
           it = ReplayKTestDir.begin(), ie = ReplayKTestDir.end();
         it != ie; ++it)
      KleeHandler::getKTestFilesInDir(*it, kTestFiles);
    std::vector<KTest*> kTests;
    for (std::vector<std::string>::iterator
           it = kTestFiles.begin(), ie = kTestFiles.end();
         it != ie; ++it) {
      KTest *out = kTest_fromFile(it->c_str());
      if (out) {
        kTests.push_back(out);
      } else {
        klee_warning("unable to open: %s\n", (*it).c_str());
      }
    }

    if (RunInDir != "") {
      int res = chdir(RunInDir.c_str());
      if (res < 0) {
        klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                   sys::StrError(errno).c_str());
      }
    }

    unsigned i=0;
    for (std::vector<KTest*>::iterator
           it = kTests.begin(), ie = kTests.end();
         it != ie; ++it) {
      KTest *out = *it;
      interpreter->setReplayKTest(out);
      llvm::errs() << "KLEE: replaying: " << *it << " (" << kTest_numBytes(out)
                   << " bytes)"
                   << " (" << ++i << "/" << kTestFiles.size() << ")\n";
      // XXX should put envp in .ktest ?
      interpreter->runFunctionAsMain(mainFn, out->numArgs, out->args, pEnvp);
      if (interrupted) break;
    }
    interpreter->setReplayKTest(0);
    while (!kTests.empty()) {
      kTest_free(kTests.back());
      kTests.pop_back();
    }
  } else {
    std::vector<KTest *> seeds;
    for (std::vector<std::string>::iterator
           it = SeedOutFile.begin(), ie = SeedOutFile.end();
         it != ie; ++it) {
      KTest *out = kTest_fromFile(it->c_str());
      if (!out) {
        klee_error("unable to open: %s\n", (*it).c_str());
      }
      seeds.push_back(out);
    }
    for (std::vector<std::string>::iterator
           it = SeedOutDir.begin(), ie = SeedOutDir.end();
         it != ie; ++it) {
      std::vector<std::string> kTestFiles;
      KleeHandler::getKTestFilesInDir(*it, kTestFiles);
      for (std::vector<std::string>::iterator
             it2 = kTestFiles.begin(), ie = kTestFiles.end();
           it2 != ie; ++it2) {
        KTest *out = kTest_fromFile(it2->c_str());
        if (!out) {
          klee_error("unable to open: %s\n", (*it2).c_str());
        }
        seeds.push_back(out);
      }
      if (kTestFiles.empty()) {
        klee_error("seeds directory is empty: %s\n", (*it).c_str());
      }
    }

    if (!seeds.empty()) {
      klee_message("KLEE: using %lu seeds\n", seeds.size());
      interpreter->useSeeds(&seeds);
    }
    if (RunInDir != "") {
      int res = chdir(RunInDir.c_str());
      if (res < 0) {
        klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                   sys::StrError(errno).c_str());
      }
    }
    interpreter->runFunctionAsMain(mainFn, pArgc, pArgv, pEnvp);
    handler->getInfoStream()
      << "KLEE: saving call prefixes \n";

    if (DumpCallTracePrefixes)
      handler->dumpCallPathPrefixes();


    while (!seeds.empty()) {
      kTest_free(seeds.back());
      seeds.pop_back();
    }
  }

  t[1] = time(NULL);
  strftime(buf, sizeof(buf), "Finished: %Y-%m-%d %H:%M:%S\n", localtime(&t[1]));
  handler->getInfoStream() << buf;

  strcpy(buf, "Elapsed: ");
  strcpy(format_tdiff(buf, t[1] - t[0]), "\n");
  handler->getInfoStream() << buf;

  // Free all the args.
  for (unsigned i=0; i<InputArgv.size()+1; i++)
    delete[] pArgv[i];
  delete[] pArgv;

  delete interpreter;

  uint64_t queries =
    *theStatisticManager->getStatisticByName("Queries");
  uint64_t queriesValid =
    *theStatisticManager->getStatisticByName("QueriesValid");
  uint64_t queriesInvalid =
    *theStatisticManager->getStatisticByName("QueriesInvalid");
  uint64_t queryCounterexamples =
    *theStatisticManager->getStatisticByName("QueriesCEX");
  uint64_t queryConstructs =
    *theStatisticManager->getStatisticByName("QueriesConstructs");
  uint64_t instructions =
    *theStatisticManager->getStatisticByName("Instructions");
  uint64_t forks =
    *theStatisticManager->getStatisticByName("Forks");

  handler->getInfoStream()
    << "KLEE: done: explored paths = " << 1 + forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries)
    handler->getInfoStream()
      << "KLEE: done: avg. constructs per query = "
                             << queryConstructs / queries << "\n";
  handler->getInfoStream()
    << "KLEE: done: total queries = " << queries << "\n"
    << "KLEE: done: valid queries = " << queriesValid << "\n"
    << "KLEE: done: invalid queries = " << queriesInvalid << "\n"
    << "KLEE: done: query cex = " << queryCounterexamples << "\n";

  std::stringstream stats;
  stats << "\n";
  stats << "KLEE: done: total instructions = "
        << instructions << "\n";
  stats << "KLEE: done: completed paths = "
        << handler->getNumPathsExplored() << "\n";
  stats << "KLEE: done: generated tests = "
        << handler->getNumTestCases() << "\n";

  bool useColors = llvm::errs().is_displayed();
  if (useColors)
    llvm::errs().changeColor(llvm::raw_ostream::GREEN,
                             /*bold=*/true,
                             /*bg=*/false);

  llvm::errs() << stats.str();

  if (useColors)
    llvm::errs().resetColor();

  handler->getInfoStream() << stats.str();

  delete handler;

  return 0;
}
