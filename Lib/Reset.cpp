#include "Lib/Reset.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/Timer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Ordering.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Shell/InferenceRecorder.hpp"

namespace Lib {

void resetGlobalState()
{
  // Order matters: drop the things that point into the signature before the signature
  // itself is replaced.
  Kernel::InferenceStore::instance()->reset();
  Shell::InferenceRecorder::instance()->reset();
  Kernel::Ordering::unsetGlobalOrdering();
  Saturation::SaturationAlgorithm::forgetInstance();

  Kernel::Unit::resetCounters();
  Kernel::Clause::resetAuxState();

  Random::setSeed(1);

  // Saturation ends by taking the exit lock and never releasing it; re-arm it or the
  // next run blocks.
  Timer::resetExitLock();

  // The built-in FOOL constants and sorts are cached; they point into the signature
  // and term-sharing table that env.reset() is about to free, so drop them first.
  Kernel::Term::resetBuiltinCache();

  // Rebuilds options, signature, term sharing and statistics, and re-registers the
  // built-in sorts in the order the rest of the code depends on.
  env.reset();
}

} // namespace Lib
