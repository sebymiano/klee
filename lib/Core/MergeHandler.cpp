//===-- MergeHandler.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/MergeHandler.h"

#include "CoreStats.h"
#include "Executor.h"
#include "klee/ExecutionState.h"

namespace klee {
llvm::cl::opt<bool>
    UseMerge("use-merge",
        llvm::cl::init(false),
        llvm::cl::desc("Enable support for klee_open_merge() and klee_close_merge() (experimental)"));

llvm::cl::opt<bool>
    DebugLogMerge("debug-log-merge",
        llvm::cl::init(false),
        llvm::cl::desc("Enhanced verbosity for region based merge operations"));

llvm::cl::opt<bool>
    UseIncompleteMerge("use-incomplete-merge",
        llvm::cl::init(false),
        llvm::cl::desc("Heuristic based merging"));

llvm::cl::opt<bool>
    DebugLogIncompleteMerge("debug-log-incomplete-merge",
        llvm::cl::init(false),
        llvm::cl::desc("Debug info about incomplete merging"));

double MergeHandler::getMean() {
  if (closedStateCount == 0)
    return 0;

  return closeMean;
}

unsigned MergeHandler::getInstrDistance(ExecutionState *es){
  return es->steppedInstructions - openInstruction;
}

ExecutionState *MergeHandler::getPrioritizeState(){
  for (ExecutionState *cur_state : openStates) {
    bool stateIsClosed = (executor->inCloseMerge.find(cur_state) !=
                          executor->inCloseMerge.end());

    if (!stateIsClosed && (getInstrDistance(cur_state) < 2 * getMean())) {
      return cur_state;
    }
  }
  return 0;
}


void MergeHandler::addOpenState(ExecutionState *es){
  openStates.push_back(es);
}

void MergeHandler::removeOpenState(ExecutionState *es){
  auto it = std::find(openStates.begin(), openStates.end(), es);
  assert(it != openStates.end());
  std::swap(*it, openStates.back());
  openStates.pop_back();
}

void MergeHandler::removeFromCloseMergeSet(ExecutionState *es){
  executor->inCloseMerge.erase(es);
}

void MergeHandler::addClosedState(ExecutionState *es,
                                         llvm::Instruction *mp) {
  // Update stats
  ++closedStateCount;
  closeMean += (static_cast<double>(getInstrDistance(es)) - closeMean) /
               closedStateCount;

  // Remove from openStates
  removeOpenState(es);

  auto closePoint = reachedMergeClose.find(mp);

  // If no other state has yet encountered this klee_close_merge instruction,
  // add a new element to the map
  if (closePoint == reachedMergeClose.end()) {
    reachedMergeClose[mp].push_back(es);
    executor->pauseState(*es);
  } else {
    // Otherwise try to merge with any state in the map element for this
    // instruction
    auto &cpv = closePoint->second;
    bool mergedSuccessful = false;

    for (auto& mState: cpv) {
      if (mState->merge(*es)) {
        executor->terminateState(*es);
        mergedSuccessful = true;
        break;
      }
    }
    if (!mergedSuccessful) {
      cpv.push_back(es);
      executor->pauseState(*es);
    }
  }
}

void MergeHandler::releaseStates() {
  for (auto& curMergeGroup: reachedMergeClose) {
    for (auto curState: curMergeGroup.second) {
      executor->continueState(*curState);
    }
  }
  reachedMergeClose.clear();
}

bool MergeHandler::hasMergedStates() {
  return (!reachedMergeClose.empty());
}

MergeHandler::MergeHandler(Executor *_executor, ExecutionState *es)
    : executor(_executor), openInstruction(es->steppedInstructions),
      closedStateCount(0), refCount(0) {
  executor->mergeGroups.push_back(this);
  addOpenState(es);
}

MergeHandler::~MergeHandler() {
  auto it = std::find(executor->mergeGroups.begin(),
                      executor->mergeGroups.end(), this);
  std::swap(*it, executor->mergeGroups.back());
  executor->mergeGroups.pop_back();

  releaseStates();
}
}
