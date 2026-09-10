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

#include <ostream>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel {

using namespace Lib;

class InferenceStore
{
public:
  static InferenceStore* instance();

  typedef List<int> IntList;

  struct FullInference
  {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { }

    void* operator new(size_t,unsigned premCnt)
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(Unit*);
      size-=sizeof(Unit*);

      return ALLOC_KNOWN(size,"InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(Unit*);
      size-=sizeof(Unit*);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt;
    InferenceRule rule;
    Unit* premises[1];
  };

  void recordSplittingNameLiteral(Unit* us, Literal* lit);
  void recordIntroducedSymbol(Unit* u, Signature::Symbol* sym);
  void recordIntroducedSkolemSymbol(Unit* u, Signature::Symbol* sym, unsigned replacedVar, Term* symTerm);
  void recordIntroducedSplitName(Unit* u, std::string name);

  /**
   * How a generated clause used one of its premises: which of the premise's
   * literals the inference acted on, and what the unifier bound each of the
   * premise's variables to.
   *
   * A generating inference applies a substitution that it computes by
   * unification and then discards, so a proof records the premises but not
   * what was done to them. Anything replaying the step would have to find the
   * substitution again by matching the conclusion against the premises; this
   * records it instead.
   */
  struct PremiseUse {
    unsigned premise;
    /** Index of the literal acted on, or `literalNone` if none was. */
    unsigned literal;
    /**
     * The term the inference acted on within that literal, empty if none.
     *
     * A rewriting inference singles out a term rather than a whole literal:
     * the subterm being rewritten in the premise it rewrites, and the side of
     * the equation doing the rewriting in the premise it comes from.
     */
    TermList term;
    /** `rewritesWholePremise`, or zero. */
    unsigned flags;
    Stack<std::pair<unsigned, TermList>> bindings;
  };

  static const unsigned literalNone = UINT_MAX;

  /**
   * The inference rewrote the term it acted on throughout the premise, rather
   * than only in the literal recorded against it: what superposition does when
   * it is simultaneous.
   */
  static const unsigned rewritesWholePremise = 1;

  void recordPremiseUse(Unit* generated, Unit* premise, unsigned literal,
    TermList term, unsigned flags,
    const Stack<std::pair<unsigned, TermList>>& bindings);

  /**
   * The same, for an inference that already holds the substitution it applied
   * to @b premise as a `Substitution`: @b on is the literal acted on, or null
   * if none was, and every variable of @b premise is recorded, unbound ones
   * as themselves.
   */
  void recordPremiseUse(Unit* generated, Clause* premise, Literal* on,
    TermList term, unsigned flags, const Substitution& subst);

  /** How @b u used each of its premises, empty when nothing was recorded. */
  const Stack<PremiseUse>* premiseUses(Unit* u) const;

  /**
   * Works out how a subsumption resolution step used its premises, and records
   * it, unless something is already recorded.
   *
   * Subsumption resolution drops the one literal of its main premise that the
   * side premise resolves away, so which literal that was is the difference
   * between the main premise and the conclusion. Given the literal, the SAT
   * problem the inference solved is solved again, and its model read as the
   * substitution -- which is cheap here, where only the steps of a proof are
   * looked at, and would not be during the search.
   *
   * Does nothing if the step does not have that shape, or if the problem comes
   * back unsatisfiable: the rule is also what a subsumption demodulation
   * records itself under, and that is not a subsumption resolution.
   */
  void recoverSubsumptionResolutionUses(Unit* u);

  /**
   * The skolem symbols @b u introduced, each paired with the existential
   * variable it replaced and the term it was replaced by.
   *
   * Skolemisation works on a formula in NNF rather than a prenex one, and a
   * skolem's arguments are the universals it actually depends on -- those
   * occurring below it, together with the ones inherited through existentials
   * above it. Anyone reconstructing the step needs that term as built rather
   * than re-derived, which is what this exposes.
   */
  void introducedSkolems(Unit* u,
    Stack<std::tuple<Signature::Symbol*, unsigned, Term*>>& out) const;
  

  void outputUnsatCore(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, UnitList* units);
  struct ProofPrinter;

private:
  struct TPTPProofPrinter;
  struct Smt2ProofCheckPrinter;
  struct ProofCheckPrinter;
  struct ProofPropertyPrinter;
  struct SMTCheckPrinter;

  ProofPrinter* createProofPrinter(std::ostream& out);

  DHMultiset<unsigned, FnvHash, IdentityHash> _nextClIds;

  DHMap<unsigned, Literal*, FnvHash, IdentityHash> _splittingNameLiterals;

  typedef Stack<Signature::Symbol*> SymbolStack;
  // unit id -> stack of introduced symbols (in order of introduction)
  DHMap<unsigned,SymbolStack, FnvHash, IdentityHash> _introducedSymbols;
  // symbol id -> existential variable name (number) that was replaced by the symbol
  DHMap<Signature::Symbol*, unsigned, FnvHash, PtrIdentityHash> _introducedSymbolReplacedVars;
  // symbol id -> the term that is introduced when introducing the skolem symbol
  DHMap<Signature::Symbol*, Term*, FnvHash, PtrIdentityHash> _introducedSkolemSymTerms;

  DHMap<unsigned,std::string, FnvHash, IdentityHash> _introducedSplitNames;

  // generated unit id -> how it used each premise
  DHMap<unsigned,Stack<PremiseUse>, FnvHash, IdentityHash> _premiseUses;
};

};

#endif /* __InferenceStore__ */
