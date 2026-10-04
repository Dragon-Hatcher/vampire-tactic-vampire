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
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <optional>
#include <ostream>
#include <string>
#include <unordered_map>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/Options.hpp"

namespace Kernel {

using namespace Lib;

class InferenceStore
{
public:
  static InferenceStore* instance();

  /** True iff inference provenance is being recorded (proof_extra=full). */
  static bool recording()
  { return env.options->proofExtra() == Shell::Options::ProofExtra::FULL; }

  /**
   * The number of the first unit made by polarity flipping, or zero if it did
   * not run. The flipped predicates mean the opposite of what they meant
   * before this unit.
   */
  void recordPolarityFlipBoundary(unsigned number)
  { if (recording()) _polarityFlipBoundary = number; }
  unsigned polarityFlipBoundary() const { return _polarityFlipBoundary; }

  void recordSplittingNameLiteral(Unit* us, Literal* lit);
  /** The name literal recorded for general splitting component @b us, or nullptr. */
  Literal* splittingNameLiteral(Unit* us) const;
  void recordIntroducedSymbol(Unit* u, const Signature::Symbol* sym);
  /** The symbols introduced by @b u in order of introduction, or nullptr. */
  const Stack<const Signature::Symbol*>* introducedSymbols(Unit* u) const
  { return _introducedSymbols.findPtr(u->number()); }
  /** The split name introduced by @b u, or nullptr. */
  const std::string* introducedSplitName(Unit* u) const
  { return _introducedSplitNames.findPtr(u->number()); }

  /**
   * Record that pure predicate removal replaced @b pred by the truth value
   * @b value. Pure predicates are numbered in the order they are found.
   */
  void recordPurePredicate(unsigned pred, bool value)
  { if (recording()) _purePredicates.insert(pred, {value, _purePredicates.size()}); }
  /** Return true iff @b pred was removed as pure, setting its value and number. */
  bool purePredicate(unsigned pred, bool& value, unsigned& order) const {
    std::pair<bool, unsigned> found;
    if (!_purePredicates.find(pred, found)) return false;
    value = found.first;
    order = found.second;
    return true;
  }
  /** Record how many predicates had been found pure when @b u was made. */
  void recordPureStage(Unit* u);
  bool pureStage(Unit* u, unsigned& stage) const;
  void recordIntroducedSkolemSymbol(Unit* u, const Signature::Symbol* sym, unsigned replacedVar, Term* symTerm);
  void recordIntroducedSplitName(Unit* u, std::string name);

  /**
   * The definition that introduced split name @b name, or nullptr. Needed for
   * names that no inference of the proof leads to, e.g. those of ground
   * literals of a theory conflict.
   */
  Unit* splitDefinition(const std::string& name) const;

  /**
   * A premise literal (after substitution) that the inference rewrote, and
   * what it became. @b turned is true iff the sides of equality @b to are
   * swapped relative to the rewriting.
   */
  struct RewrittenLiteral {
    Literal* from;
    Literal* to;
    bool turned;
  };

  /**
   * How a generated clause used one of its premises: the literal and term the
   * inference acted on and the unifier restricted to the premise's variables.
   */
  struct PremiseUse {
    unsigned premise;
    /**
     * The literal acted on and the clause containing it (the premise unless
     * stated otherwise), or nullptr. The literal is kept rather than its index
     * since literal selection reorders clauses in place.
     */
    Clause* in = nullptr;
    Literal* on = nullptr;
    /**
     * The term acted on within @c on, or empty: for rewriting, the rewritten
     * subterm, resp. the side of the equation used to rewrite.
     */
    TermList term;
    /** Combination of @c rewritesWholePremise, @c virtual* and @c negatedFlag. */
    unsigned flags;
    /** The premise states @c term negated (`j s + u` with negative coefficient). */
    static const unsigned negatedFlag = 16;
    Stack<std::pair<unsigned, TermList>> bindings;
    /**
     * A second term the inference acted on, or empty: what an arithmetic
     * equation `k s + t = 0` rewrote `s` to (`-t/k`); the atom inequality
     * factoring unified @c term with; or the other side of the equation in
     * equality factoring. See @c recordOther.
     */
    TermList other = TermList::empty();
    /**
     * The numeral @c term was scaled by, or empty: the coefficient `k` of the
     * atom rewritten by an arithmetic equation `k s + t = 0`. See @c recordFactor.
     */
    TermList factor = TermList::empty();
    /** The premise literals the inference rewrote. See @c recordRewritten. */
    Stack<RewrittenLiteral> rewritten = Stack<RewrittenLiteral>();
  };

  /** The term was rewritten in the whole premise (simultaneous superposition). */
  static const unsigned rewritesWholePremise = 1;

  /**
   * Virtual terms substituted by VIRAS: plus an infinitesimal, plus and minus
   * infinity. The term, if any, is the use's @c other.
   */
  static const unsigned virtualEpsilon = 2;
  static const unsigned virtualPlusInfinity = 4;
  static const unsigned virtualMinusInfinity = 8;

  /** Record a use that acted on no literal of @b premise. */
  void recordPremiseUse(Unit* generated, Unit* premise, TermList term,
    unsigned flags, const Stack<std::pair<unsigned, TermList>>& bindings);

  /**
   * Record a use that acted on literal @b on (nullptr if none) of @b in, or of
   * @b premise if @b in is nullptr.
   */
  void recordPremiseUse(Unit* generated, Clause* premise, Literal* on,
    TermList term, unsigned flags,
    const Stack<std::pair<unsigned, TermList>>& bindings, Clause* in = nullptr);

  /**
   * Record a use with bindings given by @b subst. Every variable of
   * @b premise is recorded, unbound ones as themselves.
   */
  void recordPremiseUse(Unit* generated, Clause* premise, Literal* on,
    TermList term, unsigned flags, const Substitution& subst);

  /** The substitution unifier @b subs applies to @b premise's variables in @b bank. */
  template<class Premise, class Subs, class S = Substitution>
  static S bankSubstitution(Premise* premise, Subs&& subs, unsigned bank)
  {
    S s;
    DHSet<unsigned, FnvHash, IdentityHash> vars;
    premise->collectVars(vars);
    for (unsigned v : iterTraits(vars.iterator()))
      s.bindUnbound(v, subs.apply(TermList(v, false), bank));
    return s;
  }

  /**
   * Record that literal @b from of @b premise was rewritten into @b to, where
   * @b rewrittenLhs is what the first argument of @b from became (empty if
   * not an equality). Applies to the last use of @b premise for @b generated.
   */
  void recordRewritten(Unit* generated, Unit* premise, Literal* from, Literal* to,
    TermList rewrittenLhs);

  /**
   * Set @c PremiseUse::other of the last use of @b premise for @b generated.
   * @b other is in the premise's variables.
   */
  void recordOther(Unit* generated, Unit* premise, TermList other);

  /** Set @c PremiseUse::negatedFlag on the last use of @b premise for @b generated. */
  void recordNegated(Unit* generated, Unit* premise);

  /** Set @c PremiseUse::factor of the last use of @b premise for @b generated. */
  void recordFactor(Unit* generated, Unit* premise, TermList factor);

  /** The premise uses recorded for @b u, or nullptr. */
  const Stack<PremiseUse>* premiseUses(Unit* u) const;

  /**
   * Record that @b count literals of @b generated starting at index @b first
   * are unification constraints left by unification with abstraction. Must be
   * called right after the clause is built; the literals themselves are kept.
   */
  void recordConstraints(Clause* generated, unsigned first, unsigned count);

  /** The constraint literals of @b u, or nullptr. */
  const Stack<Literal*>* constraints(Unit* u) const;

  /**
   * Literals of a conclusion that the inference built rather than carried
   * over from a premise (e.g. those of a theory axiom), in the order built.
   */
  struct Introduced {
    Stack<Literal*> literals;
    /** Distinguishes differently shaped conclusions of the same rule. */
    unsigned variant;
    /** Empty, or the premise literal each literal was made of. */
    Stack<Literal*> sources;
    /**
     * Terms built by the inference that a checker needs, in the order the rule
     * lists them (e.g. floors in integer Fourier-Motzkin); empty where none.
     */
    Stack<TermList> terms;
  };
  void recordIntroduced(Clause* generated, const Stack<Literal*>& literals,
    unsigned variant = 0, const Stack<Literal*>& sources = Stack<Literal*>(),
    const Stack<TermList>& terms = Stack<TermList>());
  /**
   * Record an abstraction of terms of @b premise into fresh variables
   * (`C[t]` to `x != t | C[x]`). @b abstractions are the disequalities made,
   * recorded as introduced in the order of their variables; @b rewritten pairs
   * each premise literal with what it became. Fresh variables are those
   * numbered from @b firstNewVar.
   */
  void recordAbstraction(Clause* generated, Clause* premise,
    const Stack<Literal*>& abstractions,
    const Stack<std::pair<Literal*, Literal*>>& rewritten, unsigned firstNewVar);

  /** The introduced literals of @b u, or nullptr. */
  const Introduced* introduced(Unit* u) const;

  /** What one premise literal of a literal-wise simplification became. */
  struct LiteralImage {
    Literal* from;
    /** The conclusion literal, or nullptr if @c from was dropped as false. */
    Literal* to;
    /**
     * For ALASCA normalization, the factor relating the difference of the
     * sides to the normal form (see
     * @c InequalityNormalizer::tryNormalizeInterpreted); one otherwise.
     */
    RationalConstantType factor;
  };

  /**
   * The procedure that rewrote a clause literal-wise. The inference rule does
   * not determine it, e.g. evaluation can be done by several evaluators.
   */
  enum class LiteralProcedure : unsigned {
    THEORY_NORMALIZATION = 0,
    INTERPRETED_EVALUATION = 1,
    /** @c InterpretedEvaluation with inequality normalization on. */
    INTERPRETED_EVALUATION_NORMALIZING = 2,
    POLYNOMIAL_EVALUATION = 3,
    PUSH_UNARY_MINUS = 4,
    ALASCA_NORMALIZATION = 5,
    CANCELLATION = 6,
    /** Arithmetic subterm generalization: each literal is equal up to ring identities. */
    GENERALIZATION = 7,
    /** VIRAS: the substituted virtual term is the term of the premise use. */
    VIRAS = 8,
    /**
     * ALASCA's strong normalization of comparisons; a literal may become two,
     * so no images are recorded.
     */
    INEQUALITY_PREDICATE_NORMALIZATION = 9,
  };

  /** How a literal-wise simplification rewrote its premise. */
  struct LiteralRewriting {
    LiteralProcedure procedure;
    Stack<LiteralImage> images;
  };

  void recordLiteralImages(Unit* generated, LiteralProcedure procedure,
                           Stack<LiteralImage> images);

  /** The literal rewriting recorded for @b u, or nullptr. */
  const LiteralRewriting* literalImages(Unit* u) const;

  /**
   * Reconstruct and record the premise uses of subsumption resolution step
   * @b u unless already recorded, by re-solving its SAT problem. Does nothing
   * if @b u does not have the expected shape or the problem is unsatisfiable
   * (e.g. for subsumption demodulation, which uses the same rule).
   */
  void recoverSubsumptionResolutionUses(Unit* u);

  /**
   * A state of one of the generalised clauses of the new clausifier: the
   * clause, the parent state and position that was replaced, and what replaced it.
   */
  struct GenClauseState {
    /** The parent state, or @c stateNone. */
    unsigned parent = stateNone;
    /** The position replaced in the parent, or @c positionNone. */
    unsigned position = positionNone;
    /** The signed subformulas of the clause. */
    Stack<std::pair<Formula*, bool>> literals;
    /** What was put in the replaced position. */
    Stack<std::pair<Formula*, bool>> replacement;
    /** Bindings of the variables the clause quantifies. */
    Stack<std::pair<unsigned, TermList>> bindings;
    /** One of the @c gen* constants below. */
    unsigned how = genIntroduced;
    /**
     * Where each pushed literal went, in push order, with @c genTurned set
     * where `~f` was stored as `f` with the opposite sign. An introduced clause
     * pushes @c replacement; an extended one the parent's literals with
     * @c replacement in place of @c position; a replaced one has one entry.
     */
    Stack<unsigned> placement;
  };

  /** A clause clausification started from: a formula, or a definition. */
  static const unsigned genIntroduced = 0;
  /** A position replaced by the literals of @c replacement. */
  static const unsigned genExtended = 1;
  /** A position rewritten in place: a quantifier's body, a let's contents. */
  static const unsigned genReplaced = 2;
  /** A position replaced by a name for it. */
  static const unsigned genNamed = 3;
  static const unsigned genTurned = 0x80000000u;

  static const unsigned stateNone = UINT_MAX;
  static const unsigned positionNone = UINT_MAX;

  unsigned newGenClauseState(GenClauseState state);
  const GenClauseState* genClauseState(unsigned id) const;

  /** Record the generalised clause state @b clause came from. */
  void recordGenClauseOfClause(Unit* clause, unsigned state);
  unsigned genClauseOfClause(Unit* clause) const;

  /**
   * Record which argument of each conjunction the clausification of
   * @b clause (by the NNF clausifier) followed.
   */
  void recordConjunctChoices(Unit* clause,
    const Stack<std::pair<Formula*, unsigned>>& choices);
  const Stack<std::pair<Formula*, unsigned>>* conjunctChoices(Unit* clause) const;

  /**
   * A predicate introduced by clausification to name subformula @c named,
   * with the variables it is applied to.
   */
  struct Naming {
    const Signature::Symbol* symbol;
    Stack<unsigned> arguments;
    Formula* named;
  };

  void recordIntroducedNaming(Unit* u, const Signature::Symbol* sym,
    const Stack<unsigned>& arguments, Formula* named);

  /** The namings introduced by @b u, or nullptr. */
  const Stack<Naming>* namings(Unit* u) const;

  /**
   * Push to @b out each skolem symbol introduced by @b u with the existential
   * variable it replaced and the skolem term that replaced it.
   */
  void introducedSkolems(Unit* u,
    Stack<std::tuple<const Signature::Symbol*, unsigned, Term*>>& out) const;

  void outputUnsatCore(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, UnitList* units);
  struct ProofPrinter;

private:
  /** The last use of @b premise recorded for @b generated. */
  PremiseUse& lastUse(Unit* generated, Unit* premise);

  unsigned _polarityFlipBoundary = 0;

  Stack<GenClauseState> _genClauseStates;

  struct TPTPProofPrinter;
  struct Smt2ProofCheckPrinter;
  struct ProofCheckPrinter;
  struct ProofPropertyPrinter;
  struct SMTCheckPrinter;

  ProofPrinter* createProofPrinter(std::ostream& out);

  DHMultiset<unsigned, FnvHash, IdentityHash> _nextClIds;

  DHMap<unsigned, Literal*, FnvHash, IdentityHash> _splittingNameLiterals;

  typedef Stack<const Signature::Symbol*> SymbolStack;
  // unit id -> stack of introduced symbols (in order of introduction)
  DHMap<unsigned,SymbolStack, FnvHash, IdentityHash> _introducedSymbols;
  // pure predicate -> (truth value it was replaced by, order found)
  DHMap<unsigned, std::pair<bool, unsigned>, FnvHash, IdentityHash> _purePredicates;
  // symbol id -> existential variable name (number) that was replaced by the symbol
  DHMap<const Signature::Symbol*, unsigned, FnvHash, PtrIdentityHash> _introducedSymbolReplacedVars;
  // symbol id -> the term that is introduced when introducing the skolem symbol
  DHMap<const Signature::Symbol*, Term*, FnvHash, PtrIdentityHash> _introducedSkolemSymTerms;

  DHMap<unsigned,std::string, FnvHash, IdentityHash> _introducedSplitNames;
  // split name -> the definition that introduced it
  std::unordered_map<std::string, Unit*> _splitDefinitions;
};

/**
 * What an inference did to its premises, as recorded by @c InferenceStore.
 * Owned by the unit's @c InferenceExtra.
 */
struct Provenance {
  Stack<InferenceStore::PremiseUse> uses;
  Stack<Literal*> constraints;
  std::optional<InferenceStore::LiteralRewriting> literalImages;
  std::optional<InferenceStore::Introduced> introduced;
  /** Conjunction choices of the NNF clausifier. */
  Stack<std::pair<Formula*, unsigned>> conjunctChoices;
  Stack<InferenceStore::Naming> namings;
  /** Generalised clause state of the new clausifier. */
  unsigned genClause = InferenceStore::stateNone;
  std::optional<unsigned> pureStage;
};

};

#endif /* __InferenceStore__ */
