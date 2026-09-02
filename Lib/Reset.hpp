/*
 * Resetting Vampire's process-global state, so more than one problem can be solved
 * in a single process.
 *
 * Vampire is written as a one-shot executable: it starts, solves one problem, and the
 * OS reclaims everything. Embedding it (for instance behind the Lean tactic's FFI)
 * breaks that assumption, because the process outlives a run and there may be many.
 *
 * This does not make Vampire re-entrant -- the state is still global, so runs must be
 * sequential, not concurrent.
 */

#ifndef __Reset__
#define __Reset__

namespace Lib {

/**
 * Restore the process-global state to the condition it is in immediately after static
 * initialisation.
 *
 * Covers: the environment (options, signature, term sharing, statistics, proof extras,
 * problem), unit numbering, clause aux marking, the global term ordering, the random
 * seed, and the InferenceStore/InferenceRecorder singletons.
 *
 * Does NOT cover, deliberately:
 *   - GLOBAL_SMALL_OBJECT_ALLOCATOR, which keeps its pools; memory is reused rather
 *     than returned, so repeated runs grow the process but stay correct;
 *   - the Timer statics, which belong to the embedding process rather than a run;
 *   - signal handlers and rlimits, which an embedded Vampire never installs.
 */
void resetGlobalState();

} // namespace Lib

#endif // __Reset__
