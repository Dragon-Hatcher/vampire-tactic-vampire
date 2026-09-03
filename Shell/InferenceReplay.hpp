#ifndef __INFERENCE_REPLAY__
#define __INFERENCE_REPLAY__


#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Kernel/Inference.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Unit.hpp"

#include <ostream>
namespace Shell{
class InferenceReplayer
{
    
    public:

    InferenceReplayer(std::ostream& output) : out(&output) {}

    /**
     * Tear the replay engine down.
     *
     * It used to be leaked, which is invisible in a one-shot process and fatal in a
     * long-lived one: a `SaturationAlgorithm` registers itself and its indexes globally
     * and only unregisters in its destructor, so the next problem solved in the same
     * process saturated without finding a refutation it had found before.
     */
    ~InferenceReplayer() { delete alg; alg = nullptr; }

    void replayInference(Kernel::Unit* u);

    void makeInferenceEngine(Kernel::OrderingSP ord) {
        ASS(alg == nullptr);
        _ordering = ord;
        env.options->setSaturationAlgorithm(Shell::Options::SaturationAlgorithm::DISCOUNT);
        env.reconstruction = true;
        // The problem is a member, not a local: the algorithm keeps a reference to it,
        // so it has to outlive the algorithm rather than the call.
        alg = Saturation::SaturationAlgorithm::createFromOptions(_problem, *env.options);
        alg->setOrdering(_ordering);
    }
    
    private:
    Kernel::Problem _problem;
    Kernel::OrderingSP _ordering;
    std::ostream* out = nullptr;
    Indexing::SaturationAlgorithm* alg = nullptr;

    static bool isClauseRule(const InferenceRule &rule);
    void runBackwardsSimp(Inferences::BackwardSimplificationEngine* rule, ClauseStack& context, Clause* goal);
    void runForwardsSimp(Inferences::ForwardSimplificationEngine* rule, ClauseStack& context, Clause* goal);
    Clause* runGenerating(Inferences::GeneratingInferenceEngine* rule, ClauseStack& context, Clause* goal);
    void removeAllActiveClauses();
};
}
#endif /* __INFERENCE_REPLAY__ */