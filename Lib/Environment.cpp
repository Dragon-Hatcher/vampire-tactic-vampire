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
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */


#include "Indexing/TermSharing.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#include "Environment.hpp"

namespace Lib
{

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : options(nullptr), signature(nullptr), sharing(nullptr), statistics(nullptr),
    maxSineLevel(1), predicateSineLevels(nullptr), colorUsed(false),
    _problem(nullptr), _higherOrder(false)
{
  init();
} // Environment::Environment

/**
 * Allocate the components and register the built-in sorts.
 *
 * The order the sorts are created in is VITAL: a number of places rely on the type
 * constructor for $i being 0, that for $o being 1, and so on.
 */
void Environment::init()
{
  options = new Options;
  statistics = new Statistics;
  signature = new Signature;
  sharing = new Indexing::TermSharing;

  //view comment in Signature.cpp
  signature->addEquality();
  AtomicSort::defaultSort();
  AtomicSort::boolSort();
  AtomicSort::intSort();
  AtomicSort::realSort();
  AtomicSort::rationalSort();
} // Environment::init

/**
 * Tear the environment down and build a fresh one, so another problem can be solved
 * in the same process. See Lib::resetGlobalState, which resets this along with the
 * other process-global state that a run leaves behind.
 */
void Environment::reset()
{
  delete sharing;
  delete signature;
  delete statistics;
  delete predicateSineLevels;
  delete options;

  proofExtra.clear();

  options = nullptr;
  signature = nullptr;
  sharing = nullptr;
  statistics = nullptr;
  predicateSineLevels = nullptr;
  maxSineLevel = 1;
  colorUsed = false;
  reconstruction = false;
  _problem = nullptr;
  _higherOrder = false;

  // After the signature is gone and before `init()` puts the built-in symbols back:
  // the interned operator types are keyed by sorts from the term-sharing table that
  // has just been deleted, and `init()` starts refilling them. See
  // `OperatorType::resetCache`.
  Kernel::OperatorType::resetCache();

  init();
} // Environment::reset

Environment::~Environment()
{
  delete sharing;
  delete signature;
  delete statistics;
  delete predicateSineLevels;
  delete options;
}

/**
 * Return remaining time in milliseconds.
 */
int Environment::remainingTime() const
{
  // If time limit is set to 0 then assume we always have an hour left
  if (options->timeLimitInDeciseconds() == 0) {
    return 3600000;
  }
  return options->timeLimitInDeciseconds()*100 - Timer::elapsedMilliseconds();
}

// global environment object, constructed before main() and used everywhere
Environment env;
}
