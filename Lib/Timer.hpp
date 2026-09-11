/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __Timer__
#define __Timer__

#include <cstdint>
#include <ostream>
#include <string>

namespace Lib {
namespace Timer {
  // (re)initialise the timer - from this point onwards:
  // 1. resource limits are enforced, unless `disableLimitEnforcement();`
  // 2. elapsed time (instructions) data should be live
  //
  // should be called exactly once per process as it internally spawns a std::thread
  void reinitialise(bool tryInitInstructionLimiting=true);

  // disables exit on resource out: call when a proof has been found!
  // permanently disabled per-process
  // blocks if a resource limit was already reached and we are exiting
  void disableLimitEnforcement();

  // heartbeats: the search counts the steps it takes, and elapsed time is
  // that count divided by the beats a millisecond is taken to be worth. Bump
  // the count; a limit reached at a beat is reached at the same beat every run
  bool heartbeats();
  void beat(unsigned beats = 1);
  unsigned long long elapsedBeats();

  // elapsed time
  long elapsedMilliseconds();
  // what the clock says, whatever the beats say
  long realMilliseconds();
  inline long elapsedDeciseconds()
  { return elapsedMilliseconds() / 100; }

  // output times in various formats (?!)
  void printMSString(std::ostream &, int);
  std::string msToSecondsString(int);

  // instruction limiting stuff below - no-op if !VAMPIRE_PERF_EXISTS
  // whether instruction limiting succeeded
  bool instructionLimitingInPlace();
  // elapsed instructions
  long elapsedMegaInstructions();

  // make sure that the instruction data is as up-to-date as possible
  // otherwise may be (slightly) stale
  void updateInstructionCount();
};
}

#endif /* __Timer__ */
