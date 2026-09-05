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
#include "Lib/Stack.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"

#include <set>
namespace Kernel {

using namespace Lib;

class InferenceStore {

public:
  typedef std::pair<SymbolType, unsigned> SymbolId;
  typedef Stack<SymbolId> SymbolStack;

  static InferenceStore *instance();

  typedef List<int> IntList;

  struct FullInference {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) {}

    void *operator new(size_t, unsigned premCnt)
    {
      size_t size = sizeof(FullInference) + premCnt * sizeof(Unit *);
      size -= sizeof(Unit *);

      return ALLOC_KNOWN(size, "InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size = sizeof(FullInference) + premCnt * sizeof(Unit *);
      size -= sizeof(Unit *);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt;
    InferenceRule rule;
    Unit *premises[1];
  };

  /** The ordering the run that produced this proof used. A proof is read back after the
   * saturation algorithm that found it has gone, and the replay needs the ordering it
   * was found under. */
  SmartPtr<Ordering> ordering;

  void recordSplittingNameLiteral(Unit* us, Literal* lit);
  void recordIntroducedSymbol(Unit* u, Signature::Symbol* sym);
  void recordIntroducedSymbol(Unit* u, Signature::Symbol* sym, Formula* formula);
  void recordIntroducedSkolemSymbol(Unit* u, Signature::Symbol* sym, unsigned replacedVar, Term* symTerm);
  void recordIntroducedSplitName(Unit* u, std::string name);

  bool hasIntroducedSymbols(Unit* u);
  Lib::Stack<Signature::Symbol*>& getIntroducedSymbols(Unit* u);
  long variableReplacedByIntroducedSymbol(Signature::Symbol* sym);
  Formula* formulaReplacedByIntroducedSymbol(Signature::Symbol* sym);

  void outputUnsatCore(std::ostream &out, Unit *refutation);
  void outputProof(std::ostream &out, Unit *refutation);
  void outputProof(std::ostream &out, UnitList *units);

  struct AbstractProofPrinter {
  public:
    AbstractProofPrinter(std::ostream &out, InferenceStore *is)
        : _is(is), out(out) {}

    struct CompareUnits {
      bool operator()(Unit *l, Unit *r) const { return l->number() < r->number(); }
    };

    virtual void print()
    {
      for (Unit *u : proof) {
        printStep(u);
      }
    }
    // compute closure of `us`' ancestors for printing and insert into `proof`
    void scheduleForPrinting(Unit *us);
    virtual bool hideProofStep(InferenceRule rule){
      return false;
    }
    virtual void printStep(Unit *u) = 0;
    virtual ~AbstractProofPrinter() = default;

  protected:
    InferenceStore *_is;
    std::ostream &out;
    std::set<Unit *, CompareUnits> proof;
  };

  struct ProofPrinter;

private:
  struct TPTPProofPrinter;
  struct Smt2ProofCheckPrinter;
  struct ProofCheckPrinter;
  struct ProofPropertyPrinter;
  struct SMTCheckPrinter;

  AbstractProofPrinter *createProofPrinter(std::ostream &out);

  DHMultiset<unsigned, FnvHash, IdentityHash> _nextClIds;

  DHMap<unsigned, Literal*, FnvHash, IdentityHash> _splittingNameLiterals;

  typedef Stack<Signature::Symbol*> SymbolStack;
  // unit id -> stack of introduced symbols (in order of introduction)
  DHMap<unsigned,SymbolStack, FnvHash, IdentityHash> _introducedSymbols;
  // symbol id -> existential variable name (number) that was replaced by the symbol
  DHMap<Signature::Symbol*, unsigned, FnvHash, PtrIdentityHash> _introducedSymbolReplacedVars;
  // symbol id -> the term that is introduced when introducing the skolem symbol
  DHMap<Signature::Symbol*, Term*, FnvHash, PtrIdentityHash> _introducedSkolemSymTerms;

  // symbol -> the formula a predicate definition introduced it for
  DHMap<Signature::Symbol*, Formula*, FnvHash, PtrIdentityHash> _introducedSymbolFormulas;

  DHMap<unsigned,std::string, FnvHash, IdentityHash> _introducedSplitNames;
};

}; // namespace Kernel

#endif /* __InferenceStore__ */
