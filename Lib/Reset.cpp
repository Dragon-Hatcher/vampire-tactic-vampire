#include "Lib/Reset.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/Timer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Ordering.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermOrderingDiagram.hpp"
#include "Kernel/TermPartialOrdering.hpp"
#include "Kernel/Unit.hpp"
#include "Shell/InferenceRecorder.hpp"

namespace Lib {

/// Counts from 1, so that a cache initialised against 0 misses on its first use.
static unsigned g_signatureGeneration = 1;

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

  // Same shape, and the one that actually bit: `TermPartialOrdering` caches relations
  // that keep a `const Ordering&` and `TermList`s from the term-sharing table. Held in
  // function-local statics they are built once per process, so the second problem was
  // handed the first problem's ordering and crashed on the first `_ord.compare` —
  // reached from forward demodulation, which is why only problems large enough to
  // demodulate ever saw it.
  Kernel::TermPartialOrdering::resetCache();
  Kernel::TermOrderingDiagram::resetCache();

  // Rebuilds options, signature, term sharing and statistics, and re-registers the
  // built-in sorts in the order the rest of the code depends on.
  env.reset();

  // Last, so that a cache refilled during `env.reset()` is still counted as belonging
  // to the signature that reset produced.
  g_signatureGeneration++;
}

unsigned signatureGeneration() { return g_signatureGeneration; }

} // namespace Lib
