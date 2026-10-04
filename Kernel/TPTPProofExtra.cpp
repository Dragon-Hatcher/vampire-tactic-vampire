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
 * @file TPTPProofExtra.cpp
 * Implements the TPTP proof printer for `--proof_extra full`.
 */

#include <algorithm>
#include <filesystem>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/SharedSet.hpp"
#include "Parse/TPTP.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"

#include "TPTPProofExtra.hpp"

namespace Kernel {

using namespace Lib;
using namespace SAT;
using namespace Saturation;

namespace {

/** Version of the output format, printed on the first line. */
const unsigned FORMAT = 2;
/** Marks a missing index. */
const unsigned NONE = 0xFFFFFFFFu;

using VarSorts = DHMap<unsigned, TermList, FnvHash, IdentityHash>;

/*
 * Reconstruction of congruence-closure conflicts.
 *
 * Such a clause enters the proof as an axiom. Its justification is recomputed
 * here from the clause alone and printed as a list of equality steps.
 */
namespace congruence {

enum Kind {
  /** The equality denied by literal `a`. */
  INPUT,
  /** `f(as) = f(bs)`, from one step per argument pair. */
  CONGRUENCE,
  /** Transitivity of steps `a` and `b`. */
  TRANS,
  /** Symmetry of step `a`. */
  SYMM,
  /** Literal `a` is the equality proved by step `b`. */
  GOAL_EQUALITY,
  /** Literals `a` and `b` are the same atom with opposite signs. */
  GOAL_LITERALS,
};

struct Step {
  Kind kind;
  unsigned a = NONE;
  unsigned b = NONE;
  /** Per argument pair, the step proving it equal, or NONE if identical. */
  std::vector<unsigned> args;
  /** The equality concluded, for steps that conclude one. */
  TermList lhs;
  TermList rhs;
};

/**
 * Congruence closure of a clause's terms under the equalities it denies,
 * keeping a proof of each derived equality.
 *
 * Each class keeps a proof that every member equals its representative, so
 * merging classes composes proofs instead of searching for paths. The
 * algorithm is quadratic, which is fine for the small clauses involved.
 */
class Proof {
public:
  /** Return true iff the clause @b c is shown to be a tautology. */
  bool of(Clause* c)
  {
    for (unsigned i = 0; i < c->size(); i++) {
      Literal* l = (*c)[i];
      for (unsigned j = 0; j < l->arity(); j++)
        collect(*l->nthArgument(j));
    }
    _representative.resize(_terms.size());
    _toRepresentative.assign(_terms.size(), NONE);
    for (unsigned i = 0; i < _terms.size(); i++)
      _representative[i] = i;

    // a != b is false only if a = b, so negative equalities are assumptions
    for (unsigned i = 0; i < c->size(); i++) {
      Literal* l = (*c)[i];
      if (!l->isEquality() || l->isPositive())
        continue;
      TermList lhs = *l->nthArgument(0);
      TermList rhs = *l->nthArgument(1);
      Step step{INPUT};
      step.a = i;
      step.lhs = lhs;
      step.rhs = rhs;
      merge(indexOf(lhs), indexOf(rhs), emit(step));
    }

    close();
    return closeOn(c);
  }

  const std::vector<Step>& steps() const { return _steps; }

private:
  std::vector<TermList> _terms;
  std::vector<unsigned> _representative;
  /** Proof that a term equals its representative; NONE for the representative. */
  std::vector<unsigned> _toRepresentative;
  std::vector<Step> _steps;

  void collect(TermList t)
  {
    if (indexOf(t) == NONE) {
      if (!t.isVar())
        for (unsigned i = 0; i < t.term()->arity(); i++)
          collect(*t.term()->nthArgument(i));
      _terms.push_back(t);
    }
  }

  /** Index of @b t in _terms, or NONE. */
  unsigned indexOf(TermList t) const
  {
    for (unsigned i = 0; i < _terms.size(); i++)
      if (_terms[i] == t)
        return i;
    return NONE;
  }

  unsigned emit(const Step& step)
  {
    _steps.push_back(step);
    return _steps.size() - 1;
  }

  /** Compose two proofs by transitivity; NONE stands for reflexivity. */
  unsigned transitivity(unsigned p, unsigned q)
  {
    if (p == NONE)
      return q;
    if (q == NONE)
      return p;
    Step step{TRANS};
    step.a = p;
    step.b = q;
    step.lhs = _steps[p].lhs;
    step.rhs = _steps[q].rhs;
    return emit(step);
  }

  unsigned symmetry(unsigned p)
  {
    if (p == NONE)
      return NONE;
    Step step{SYMM};
    step.a = p;
    step.lhs = _steps[p].rhs;
    step.rhs = _steps[p].lhs;
    return emit(step);
  }

  /** Proof that terms @b i and @b j of the same class are equal. */
  unsigned equality(unsigned i, unsigned j)
  {
    return transitivity(_toRepresentative[i], symmetry(_toRepresentative[j]));
  }

  void merge(unsigned i, unsigned j, unsigned p)
  {
    unsigned from = _representative[i];
    unsigned to = _representative[j];
    if (from == to)
      return;
    unsigned between = transitivity(symmetry(_toRepresentative[i]),
                                    transitivity(p, _toRepresentative[j]));
    for (unsigned k = 0; k < _terms.size(); k++)
      if (_representative[k] == from) {
        _toRepresentative[k] = transitivity(_toRepresentative[k], between);
        _representative[k] = to;
      }
  }

  /**
   * Push to @b out a proof for each argument pair of @b s and @b t, and
   * return false if some pair is not known to be equal.
   */
  bool argumentsEqual(Term* s, Term* t, std::vector<unsigned>& out)
  {
    for (unsigned k = 0; k < s->arity(); k++) {
      TermList a = *s->nthArgument(k);
      TermList b = *t->nthArgument(k);
      if (a == b) {
        out.push_back(NONE);
        continue;
      }
      unsigned i = indexOf(a);
      unsigned j = indexOf(b);
      if (i == NONE || j == NONE || _representative[i] != _representative[j])
        return false;
      out.push_back(equality(i, j));
    }
    return true;
  }

  /** Merge classes by congruence until a fixpoint is reached. */
  void close()
  {
    bool again = true;
    while (again) {
      again = false;
      for (unsigned i = 0; i < _terms.size(); i++)
        for (unsigned j = i + 1; j < _terms.size(); j++) {
          if (_representative[i] == _representative[j])
            continue;
          if (_terms[i].isVar() || _terms[j].isVar())
            continue;
          Term* s = _terms[i].term();
          Term* t = _terms[j].term();
          if (s->functor() != t->functor() || s->arity() != t->arity())
            continue;
          std::vector<unsigned> args;
          if (!argumentsEqual(s, t, args))
            continue;
          Step step{CONGRUENCE};
          step.args = args;
          step.lhs = _terms[i];
          step.rhs = _terms[j];
          merge(i, j, emit(step));
          again = true;
        }
    }
  }

  /**
   * Find a positive equality of @b c whose sides are in one class, or a
   * complementary pair of non-equality literals with equal arguments, and
   * emit the goal step for it. Return false if there is none.
   */
  bool closeOn(Clause* c)
  {
    for (unsigned i = 0; i < c->size(); i++) {
      Literal* l = (*c)[i];
      if (!l->isEquality() || !l->isPositive())
        continue;
      unsigned lhs = indexOf(*l->nthArgument(0));
      unsigned rhs = indexOf(*l->nthArgument(1));
      if (lhs == NONE || rhs == NONE || _representative[lhs] != _representative[rhs])
        continue;
      Step step{GOAL_EQUALITY};
      step.a = i;
      step.b = equality(lhs, rhs);
      emit(step);
      return true;
    }
    for (unsigned i = 0; i < c->size(); i++) {
      Literal* negative = (*c)[i];
      if (negative->isEquality() || negative->isPositive())
        continue;
      for (unsigned j = 0; j < c->size(); j++) {
        Literal* positive = (*c)[j];
        if (positive->isEquality() || !positive->isPositive())
          continue;
        if (positive->functor() != negative->functor())
          continue;
        std::vector<unsigned> args;
        if (!argumentsEqual(negative, positive, args))
          continue;
        Step step{GOAL_LITERALS};
        step.a = i;
        step.b = j;
        step.args = args;
        emit(step);
        return true;
      }
    }
    return false;
  }
};

}  // namespace congruence

/** Return true iff @b s is a TPTP lower word. */
bool isLowerWord(const std::string& s)
{
  if (s.empty() || s[0] < 'a' || s[0] > 'z')
    return false;
  return std::all_of(s.begin(), s.end(), [](char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
           (c >= '0' && c <= '9') || c == '_';
  });
}

/** Return true iff @b s is a TPTP defined or system word, e.g. `$sum`, `$$name`. */
bool isDollarWord(const std::string& s)
{
  size_t dollars = s.compare(0, 2, "$$") == 0 ? 2 : s.compare(0, 1, "$") == 0 ? 1 : 0;
  return dollars != 0 && isLowerWord(s.substr(dollars));
}

/** @b s as a TPTP single-quoted atom. */
std::string quoted(const std::string& s)
{
  std::string out = "'";
  for (char c : s) {
    if (c == '\\' || c == '\'')
      out.push_back('\\');
    out.push_back(c);
  }
  out.push_back('\'');
  return out;
}

/** @b s as a TPTP atom, quoted unless it is a lower word. */
std::string atom(const std::string& s) { return isLowerWord(s) ? s : quoted(s); }

/** @b s as a symbol in a formula; like atom() but `$` words are not quoted. */
std::string symbol(const std::string& s)
{
  return isLowerWord(s) || isDollarWord(s) ? s : quoted(s);
}

/** The rule's name with spaces replaced by `_`, quoted if necessary. */
std::string tptpRuleName(InferenceRule rule)
{
  std::string name = ruleName(rule);
  std::replace(name.begin(), name.end(), ' ', '_');
  return atom(name);
}

std::string join(const std::vector<std::string>& parts, const char* sep = ",")
{
  std::string out;
  for (size_t i = 0; i < parts.size(); i++) {
    if (i)
      out += sep;
    out += parts[i];
  }
  return out;
}

/** The TPTP name of variable @b v. */
std::string var(unsigned v) { return "X" + std::to_string(v); }

/** @b v as a decimal, or `none` for NONE. */
std::string optionalIndex(unsigned v) { return v == NONE ? "none" : std::to_string(v); }

/** Index of @b lit in @b cl, or NONE (also if @b lit is null). */
unsigned indexIn(Clause* cl, Literal* lit)
{
  for (unsigned i = 0; lit && i < cl->length(); i++)
    if ((*cl)[i] == lit)
      return i;
  return NONE;
}

/** The premises of @b u, in order. */
std::vector<Unit*> premisesOf(Unit* u)
{
  std::vector<Unit*> out;
  const Inference& inference = u->inference();
  Inference::Iterator it = inference.iterator();
  while (inference.hasNext(it))
    out.push_back(inference.next(it));
  return out;
}

/** The first premise of @b u if it is a clause, otherwise nullptr. */
Clause* firstClausePremise(Unit* u)
{
  std::vector<Unit*> premises = premisesOf(u);
  return !premises.empty() && premises[0]->isClause() ? premises[0]->asClause() : nullptr;
}

/** Name of an atomic sort, or the empty string for any other sort. */
std::string sortName(TermList sort)
{
  if (!sort.isTerm() || sort.term()->arity() != 0)
    return "";
  return env.signature->typeConName(sort.term()->functor());
}

/** Name of an atomic sort; throw for any other sort, which is not supported. */
std::string writableSortName(TermList sort)
{
  std::string name = sortName(sort);
  if (name.empty())
    throw UserErrorException("cannot write the sort " + sort.toString() +
                             ": only atomic sorts are supported");
  return name;
}

/** The entries of @b sorts, in the map's iteration order. */
std::vector<std::pair<unsigned, TermList>> sortsInOrder(VarSorts& sorts)
{
  std::vector<std::pair<unsigned, TermList>> out;
  VarSorts::Iterator it(sorts);
  while (it.hasNext()) {
    unsigned v;
    TermList sort;
    it.next(v, sort);
    out.push_back({v, sort});
  }
  return out;
}

/**
 * The recorded image of each literal of @b premise under the literal-wise
 * simplification @b u, in the premise's current literal order, or empty if
 * nothing was recorded.
 *
 * Images are matched by literal, not position, as literal selection reorders
 * clauses. Each image is used once, so duplicate literals match in turn.
 */
std::vector<const InferenceStore::LiteralImage*> literalImagesOf(Unit* u, Clause* premise)
{
  std::vector<const InferenceStore::LiteralImage*> out;
  const InferenceStore::LiteralRewriting* rewriting =
    InferenceStore::instance()->literalImages(u);
  if (!rewriting || !premise)
    return out;
  // this procedure can turn one literal into two, so it records no images
  if (rewriting->procedure ==
      InferenceStore::LiteralProcedure::INEQUALITY_PREDICATE_NORMALIZATION)
    return out;
  const Stack<InferenceStore::LiteralImage>& images = rewriting->images;
  if (images.size() != premise->length())
    throw UserErrorException("unit " + std::to_string(u->number()) + " recorded " +
      std::to_string(images.size()) + " literal images for a premise of " +
      std::to_string(premise->length()) + " literals");
  std::vector<bool> taken(images.size(), false);
  for (unsigned i = 0; i < premise->length(); i++) {
    const InferenceStore::LiteralImage* found = nullptr;
    for (unsigned k = 0; k < images.size() && !found; k++)
      if (!taken[k] && images[k].from == (*premise)[i]) {
        taken[k] = true;
        found = &images[k];
      }
    if (!found)
      throw UserErrorException("unit " + std::to_string(u->number()) +
        " recorded no image of its premise's literal " + std::to_string(i));
    out.push_back(found);
  }
  return out;
}

/**
 * The component of an AVATAR definition `name <=> component`, or nullptr if
 * @b definition is not an equivalence.
 */
Formula* definedComponent(Formula* definition)
{
  if (definition->connective() != IFF)
    return nullptr;
  return definition->left()->connective() == NAME ? definition->right() : definition->left();
}

/**
 * Collect in @b lits the literals of the component defined by the AVATAR
 * definition @b definition (see Formula::fromClause). Return false if it is
 * not such a definition.
 */
bool componentLiterals(Formula* definition, std::vector<Literal*>& lits)
{
  lits.clear();
  Formula* component = definedComponent(definition);
  if (!component)
    return false;
  if (component->connective() == FORALL)
    component = component->qarg();
  std::vector<Formula*> parts;
  if (component->connective() == OR)
    for (const FormulaList* it = component->args(); it; it = it->tail())
      parts.push_back(it->head());
  else
    parts.push_back(component);
  for (Formula* part : parts) {
    if (part->connective() != LITERAL) {
      lits.clear();
      return false;
    }
    lits.push_back(part->literal());
  }
  return true;
}

/** The immediate subformulas of @b f, in order. */
std::vector<Formula*> subformulasOf(Formula* f)
{
  std::vector<Formula*> out;
  switch (f->connective()) {
    case AND:
    case OR:
      for (const FormulaList* it = f->args(); it; it = it->tail())
        out.push_back(it->head());
      break;
    case IMP:
    case IFF:
    case XOR:
      out.push_back(f->left());
      out.push_back(f->right());
      break;
    case NOT:
      out.push_back(f->uarg());
      break;
    case FORALL:
    case EXISTS:
      out.push_back(f->qarg());
      break;
    default:
      break;
  }
  return out;
}

/** Push to @b found the subformula index path of each occurrence of @b target in @b f. */
void positionsOf(Formula* f, Formula* target, std::vector<unsigned>& path,
                 std::vector<std::vector<unsigned>>& found)
{
  if (f == target)
    found.push_back(path);
  std::vector<Formula*> subs = subformulasOf(f);
  for (unsigned i = 0; i < subs.size(); i++) {
    path.push_back(i);
    positionsOf(subs[i], target, path, found);
    path.pop_back();
  }
}

/** The printed name of a literal-wise simplification procedure. */
std::string procedureName(InferenceStore::LiteralProcedure procedure)
{
  using P = InferenceStore::LiteralProcedure;
  switch (procedure) {
    case P::THEORY_NORMALIZATION:
      return "theory_normalization";
    case P::INTERPRETED_EVALUATION:
      return "interpreted_evaluation";
    case P::INTERPRETED_EVALUATION_NORMALIZING:
      return "interpreted_evaluation_normalizing";
    case P::POLYNOMIAL_EVALUATION:
      return "polynomial_evaluation";
    case P::PUSH_UNARY_MINUS:
      return "push_unary_minus";
    case P::ALASCA_NORMALIZATION:
      return "alasca_normalization";
    case P::CANCELLATION:
      return "cancellation";
    case P::GENERALIZATION:
      return "generalization";
    case P::VIRAS:
      return "viras";
    case P::INEQUALITY_PREDICATE_NORMALIZATION:
      return "inequality_predicate_normalization";
  }
  ASSERTION_VIOLATION;
}

/** The printed name of an @c InferenceStore::gen* value. */
std::string genHowName(unsigned how)
{
  switch (how) {
    case InferenceStore::genIntroduced:
      return "introduced";
    case InferenceStore::genExtended:
      return "extended";
    case InferenceStore::genReplaced:
      return "replaced";
    case InferenceStore::genNamed:
      return "named";
  }
  ASSERTION_VIOLATION;
}

/** The TPTP role of @b u, as in vampire's TPTP proofs. */
std::string role(Unit* u)
{
  InferenceRule rule = u->inference().rule();
  if (isTheoryAxiomRule(rule))
    return "axiom";
  switch (rule) {
    case InferenceRule::INPUT:
      switch (u->inputType()) {
        case UnitInputType::CONJECTURE:
          return "conjecture";
        case UnitInputType::NEGATED_CONJECTURE:
          return "negated_conjecture";
        default:
          return "axiom";
      }
    case InferenceRule::NEGATED_CONJECTURE:
      return "negated_conjecture";
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::FUNCTION_DEFINITION:
    case InferenceRule::PREDICATE_DEFINITION:
    case InferenceRule::FOOL_ITE_DEFINITION:
    case InferenceRule::FOOL_LET_DEFINITION:
    case InferenceRule::FOOL_FORMULA_DEFINITION:
    case InferenceRule::FOOL_MATCH_DEFINITION:
    case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::EQUALITY_PROXY_DEFINITION:
      return "definition";
    case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    case InferenceRule::DISTINCTNESS_AXIOM:
      return "axiom";
    default:
      return "plain";
  }
}

/** Where a premise literal went in the conclusion. */
struct Placed {
  /** Index in the conclusion, or NONE if the literal was dropped. */
  unsigned index = NONE;
  /** The equation's sides were swapped. */
  bool turned = false;
  /** The literal was rewritten rather than carried over. */
  bool rewritten = false;

  std::string toString() const
  {
    if (index == NONE)
      return "none";
    std::string out = std::to_string(index);
    if (turned)
      out = "turned(" + out + ")";
    if (rewritten)
      out = "rewritten(" + out + ")";
    return out;
  }
};

std::string placedList(const std::vector<Placed>& entries)
{
  std::vector<std::string> out;
  for (const Placed& entry : entries)
    out.push_back(entry.toString());
  return "placed([" + join(out) + "])";
}

/** Prints a proof in the format described in TPTPProofExtra.hpp. */
class Writer {
public:
  Writer()
    : _boundary(InferenceStore::instance()->polarityFlipBoundary()),
      _splitPrefix(Splitter::splPrefix)
  {
    // A reader tells split names from symbols by their prefix, so make sure
    // no symbol starts with it
    if (!_splitPrefix.empty()) {
      auto startsWith = [&](const std::string& name) { return name.rfind(_splitPrefix, 0) == 0; };
      for (unsigned i = 0; i < env.signature->functions(); i++)
        if (startsWith(env.signature->functionName(i)))
          throw UserErrorException("split names' prefix " + _splitPrefix + " is a symbol's");
      for (unsigned i = 0; i < env.signature->predicates(); i++)
        if (startsWith(env.signature->predicateName(i)))
          throw UserErrorException("split names' prefix " + _splitPrefix + " is a symbol's");
    }
    _linMulPrefix = env.signature->freshPrefix("lin_mul");
    for (unsigned f = 0; f < env.signature->functions(); f++)
      _functors.push_back(describeFunctor(f));
  }

  void write(std::ostream& out, Unit* refutation)
  {
    collect(refutation);
    out << "% VAMPIRE format: " << FORMAT << "\n";
    out << "% VAMPIRE refutation: " << unitName(refutation) << "\n";
    // The steps are printed into a buffer first, as printing them collects
    // the split names to declare. Premises have smaller numbers than their
    // conclusions.
    std::sort(_units.begin(), _units.end(),
              [](Unit* a, Unit* b) { return a->number() < b->number(); });
    std::string body;
    for (Unit* u : _units) {
      if (SATClause* sat = u->inference().satPremise())
        satProof(sat, body);
      // the generalised clauses this clause was produced from
      unsigned state = InferenceStore::instance()->genClauseOfClause(u);
      if (state != InferenceStore::stateNone) {
        std::vector<Unit*> premises = premisesOf(u);
        genChain(state, premises.empty() ? nullptr : premises[0], body);
      }
      unit(u, body);
    }
    declarations(out);
    out << body;
  }

private:
  /** How a function symbol is printed. */
  struct Functor {
    std::string text;
    /** For an ALASCA multiplication by a numeral, the numeral; otherwise empty. */
    std::string multiplier;
  };

  /** The units of the proof. */
  std::vector<Unit*> _units;
  std::set<SATClause*> _satWritten;
  std::set<unsigned> _genWritten;

  std::vector<Functor> _functors;
  std::unordered_map<uint64_t, std::string> _termText;
  /** Cache of printed formulas, keyed also by the value of _unflip. */
  std::map<std::pair<Formula*, bool>, std::string> _formulaText;
  /** Number of the first unit made by polarity flipping, or zero. */
  unsigned _boundary;
  /**
   * True iff the unit being printed comes after polarity flipping, in which
   * case literals of flipped predicates are printed complemented.
   */
  bool _unflip = false;
  std::string _splitPrefix;
  std::string _linMulPrefix;
  /** The split names printed so far, without a leading `~`. */
  std::set<std::string> _splitNames;

  /**
   * Collect in _units the units @b refutation depends on, including through
   * SAT refutations: the first-order clauses they were converted from and
   * the definitions of the split names they mention.
   */
  void collect(Unit* refutation)
  {
    std::vector<Unit*> todo = {refutation};
    std::set<Unit*> unitSeen;
    std::set<SATClause*> satSeen;
    std::vector<SATClause*> satTodo;
    while (!todo.empty() || !satTodo.empty()) {
      if (!satTodo.empty()) {
        SATClause* cl = satTodo.back();
        satTodo.pop_back();
        if (!satSeen.insert(cl).second)
          continue;
        // a name introduced when converting a theory conflict has no
        // definition among the premises, so add the definitions explicitly
        for (SATLiteral l : iterTraits(cl->iter()))
          if (Unit* definition = InferenceStore::instance()->splitDefinition(
                Splitter::getFormulaStringFromLiteral(l.positive() ? l : l.opposite())))
            todo.push_back(definition);
        if (SATInference* inf = cl->inference()) {
          if (inf->getType() == SATInference::InfType::PROP_INF) {
            for (SATClause* p : iterTraits(inf->propInf()->getPremises()->iter()))
              satTodo.push_back(p);
          } else {
            todo.push_back(inf->foConversion()->getOrigin());
          }
        }
        continue;
      }
      Unit* u = todo.back();
      todo.pop_back();
      if (!unitSeen.insert(u).second)
        continue;
      _units.push_back(u);
      for (Unit* premise : premisesOf(u))
        todo.push_back(premise);
      if (SATClause* sat = u->inference().satPremise())
        satTodo.push_back(sat);
    }
  }

  static std::string unitName(Unit* u) { return "f" + std::to_string(u->number()); }
  static std::string satName(SATClause* cl) { return "s" + std::to_string(cl->number); }
  static std::string genName(unsigned state) { return "g" + std::to_string(state); }

  /** How function symbol @b f is printed. */
  Functor describeFunctor(unsigned f) const
  {
    const Signature::Symbol* sym = env.signature->getFunction(f);
    auto integer = [](IntegerConstantType const& n) {
      std::ostringstream o;
      o << n;
      return o.str();
    };
    auto rational = [](auto const& n) {
      std::ostringstream o;
      o << n.numerator() << "/" << n.denominator();
      return o.str();
    };
    // ALASCA multiplication by a numeral: fresh prefix, sort and numeral
    auto linMul = [&](const std::string& sort, auto const& numerator,
                      auto const& denominator, const std::string& multiplier) {
      std::ostringstream o;
      o << numerator;
      std::string num = o.str();
      if (!num.empty() && num[0] == '-')
        num = "m" + num.substr(1);
      std::ostringstream d;
      d << denominator;
      std::string name = _linMulPrefix + sort + "_" + num;
      if (d.str() != "1")
        name += "_" + d.str();
      return Functor{name, multiplier};
    };
    if (sym->integerConstant())
      return {integer(sym->integerValue()), ""};
    if (sym->rationalConstant())
      return {rational(sym->rationalValue()), ""};
    if (sym->realConstant())
      return {"$to_real(" + rational(sym->realValue()) + ")", ""};
    if (auto n = env.signature->tryLinMul<IntegerConstantType>(f))
      return linMul("int", *n, 1, integer(*n));
    if (auto n = env.signature->tryLinMul<RationalConstantType>(f))
      return linMul("rat", n->numerator(), n->denominator(), rational(*n));
    if (auto n = env.signature->tryLinMul<RealConstantType>(f))
      return linMul("real", n->numerator(), n->denominator(),
                    "$to_real(" + rational(*n) + ")");
    return {symbol(sym->name()), ""};
  }

  static std::string sortText(TermList sort) { return symbol(writableSortName(sort)); }

  /** @b sorts as `X0:s,X1:t`, for use in a general list. */
  static std::string typedVars(const std::vector<std::pair<unsigned, TermList>>& sorts)
  {
    std::vector<std::string> out;
    for (const auto& [v, sort] : sorts)
      out.push_back(var(v) + ":" + atom(writableSortName(sort)));
    return join(out);
  }

  /** `! [X0: s, ...] : @b body`, or just @b body if @b sorts is empty. */
  static std::string universalClosure(const std::vector<std::pair<unsigned, TermList>>& sorts,
                                      const std::string& body)
  {
    if (sorts.empty())
      return body;
    std::vector<std::string> vars;
    for (const auto& [v, sort] : sorts)
      vars.push_back(var(v) + ": " + sortText(sort));
    return "! [" + join(vars, ", ") + "] : " + body;
  }

  /** The parenthesised arguments of @b t, or the empty string if it has none. */
  std::string arguments(Term* t)
  {
    if (t->arity() == 0)
      return "";
    std::string out = "(";
    for (unsigned i = 0; i < t->arity(); i++) {
      if (i)
        out += ",";
      out += term(*t->nthArgument(i));
    }
    return out + ")";
  }

  const std::string& term(TermList t)
  {
    auto found = _termText.find(t.content());
    if (found != _termText.end())
      return found->second;
    std::string out;
    if (t.isVar()) {
      out = var(t.var());
    } else {
      out = _functors[t.term()->functor()].text + arguments(t.term());
    }
    return _termText[t.content()] = std::move(out);
  }

  std::string fot(TermList t) { return "$fot(" + term(t) + ")"; }

  std::string optionalTerm(TermList t) { return t.isEmpty() ? "none" : fot(t); }

  /** Return true iff @b l is printed with its polarity flipped back. */
  bool turnedBack(Literal* l) const
  {
    return _unflip && !l->isEquality() && env.signature->getPredicate(l->functor())->wasFlipped();
  }

  std::string literal(Literal* l)
  {
    bool positive = l->isPositive() != turnedBack(l);
    if (l->isEquality())
      return term(*l->nthArgument(0)) + (positive ? " = " : " != ") + term(*l->nthArgument(1));
    std::string out = symbol(env.signature->getPredicate(l->functor())->name()) + arguments(l);
    return positive ? out : "~" + out;
  }

  /**
   * The split name @b name as a literal, recording it for declaration.
   * @b name has a leading `~` for a negatively named component.
   */
  std::string splitLiteral(const std::string& name)
  {
    bool negative = !name.empty() && name[0] == '~';
    std::string positive = negative ? name.substr(1) : name;
    if (_splitPrefix.empty() || positive.rfind(_splitPrefix, 0) != 0 || !isLowerWord(positive))
      throw UserErrorException("the split name " + name + " is not one this format can write");
    _splitNames.insert(positive);
    return negative ? "~" + positive : positive;
  }

  /** The complement of splitLiteral(name). */
  std::string negatedSplitLiteral(const std::string& name)
  {
    bool negative = !name.empty() && name[0] == '~';
    return splitLiteral(negative ? name.substr(1) : "~" + name);
  }

  const std::string& formula(Formula* f)
  {
    auto found = _formulaText.find({f, _unflip});
    if (found != _formulaText.end())
      return found->second;
    std::vector<Formula*> subs = subformulasOf(f);
    std::string out;
    switch (f->connective()) {
      case LITERAL:
        out = literal(f->literal());
        break;
      case AND:
      case OR:
        if (subs.size() < 2)
          throw UserErrorException("cannot write a junction of " +
                                   std::to_string(subs.size()) + " formulas");
        out = "(";
        for (unsigned i = 0; i < subs.size(); i++) {
          if (i)
            out += f->connective() == AND ? " & " : " | ";
          out += formula(subs[i]);
        }
        out += ")";
        break;
      case IMP:
      case IFF:
      case XOR:
        out = "(" + formula(subs[0]) +
              (f->connective() == IMP ? " => " : f->connective() == IFF ? " <=> " : " <~> ") +
              formula(subs[1]) + ")";
        break;
      case NOT:
        out = "~ (" + formula(subs[0]) + ")";
        break;
      case FORALL:
      case EXISTS: {
        std::vector<std::string> vars;
        for (const VSList* it = f->vars(); it; it = it->tail())
          vars.push_back(var(it->head().first) + ": " + sortText(it->head().second));
        out = std::string(f->connective() == FORALL ? "! [" : "? [") + join(vars, ", ") +
              "] : (" + formula(subs[0]) + ")";
        break;
      }
      case TRUE:
        out = "$true";
        break;
      case FALSE:
        out = "$false";
        break;
      case NAME:
        out = splitLiteral(static_cast<const NamedFormula*>(f)->name());
        break;
      case BOOL_TERM:
        throw UserErrorException("cannot write a formula that is a boolean term: "
                                 "FOOL is not supported");
      default:
        throw UserErrorException("cannot write a formula of connective " +
                                 std::to_string(f->connective()));
    }
    return _formulaText[{f, _unflip}] = std::move(out);
  }

  /** @b f as `$tff(f)`, wrapped in `scoped` if it has free variables. */
  std::string recordFormula(Formula* f)
  {
    VarSorts sorts;
    SortHelper::collectVariableSorts(f, sorts);
    std::string body = "$tff(" + formula(f) + ")";
    return sorts.size() == 0 ? body
      : "scoped([" + typedVars(sortsInOrder(sorts)) + "]," + body + ")";
  }

  static std::string typeText(OperatorType* type, unsigned arity, const std::string& result)
  {
    if (arity == 0)
      return result;
    std::string args;
    for (unsigned i = 0; i < arity; i++) {
      std::string name = sortName(type->arg(i));
      if (name.empty())
        return "";
      args += (i ? " * " : "") + symbol(name);
    }
    return (arity == 1 ? args : "(" + args + ")") + " > " + result;
  }

  /**
   * Print type declarations of the uninterpreted sorts and symbols. Symbols
   * whose type is not first-order over atomic sorts are skipped.
   */
  void declarations(std::ostream& out)
  {
    for (unsigned i = 0; i < env.signature->typeCons(); i++) {
      std::string name = env.signature->typeConName(i);
      if (name.empty() || name[0] == '$' || env.signature->getTypeCon(i)->arity() != 0)
        continue;
      out << "tff(type_def_" << i << ", type, " << symbol(name) << ": $tType).\n";
    }
    for (unsigned f = 0; f < env.signature->functions(); f++) {
      const Signature::Symbol* sym = env.signature->getFunction(f);
      const Functor& written = _functors[f];
      bool linMul = !written.multiplier.empty();
      if (!linMul && (sym->interpreted() || sym->name().empty() || sym->name()[0] == '$'))
        continue;
      OperatorType* type = sym->type();
      if (type->numTypeArguments() != 0)
        continue;
      std::string result = sortName(type->result());
      if (result.empty())
        continue;
      std::string text = typeText(type, sym->arity(), symbol(result));
      if (text.empty())
        continue;
      out << "tff(func_def_" << f << ", type, " << written.text << ": " << text
          << ", unknown, [created(" << sym->created() << ")"
          << (linMul ? ", lin_mul($fot(" + written.multiplier + "))" : "") << "]).\n";
    }
    for (unsigned p = 1; p < env.signature->predicates(); p++) {
      const Signature::Symbol* sym = env.signature->getPredicate(p);
      if (sym->interpreted() || sym->name().empty() || sym->name()[0] == '$')
        continue;
      OperatorType* type = sym->type();
      if (type->numTypeArguments() != 0)
        continue;
      std::string text = typeText(type, sym->arity(), "$o");
      if (text.empty())
        continue;
      out << "tff(pred_def_" << p << ", type, " << symbol(sym->name()) << ": " << text
          << ", unknown, [created(" << sym->created() << ")";
      bool pureValue = false;
      unsigned pureOrder = 0;
      if (InferenceStore::instance()->purePredicate(p, pureValue, pureOrder))
        out << ", pure(" << (pureValue ? "true" : "false") << "," << pureOrder << ")";
      out << "]).\n";
    }
    // split names are not in the signature
    unsigned k = 0;
    for (const std::string& name : _splitNames)
      out << "tff(split_def_" << k++ << ", type, " << name << ": $o, unknown, [split_name]).\n";
  }

  /** The items printed for the premise use @b use of @b u. */
  std::vector<std::string> useItems(Unit* u, const InferenceStore::PremiseUse& use)
  {
    std::vector<std::string> items;
    // the store keeps literals since literal selection reorders clauses
    if (use.on) {
      unsigned at = indexIn(use.in, use.on);
      if (at == NONE)
        throw UserErrorException("unit " + std::to_string(u->number()) +
          " recorded a use of a literal its premise does not have");
      items.push_back("literal(" + std::to_string(at) + ")");
    }
    if (!use.term.isEmpty())
      items.push_back("term(" + fot(use.term) + ")");
    for (const auto& [v, t] : use.bindings)
      items.push_back("bind(" + var(v) + "," + fot(t) + ")");
    const unsigned knownFlags = InferenceStore::rewritesWholePremise |
      InferenceStore::virtualEpsilon | InferenceStore::virtualPlusInfinity |
      InferenceStore::virtualMinusInfinity | InferenceStore::PremiseUse::negatedFlag;
    if (use.flags & ~knownFlags)
      throw UserErrorException("a premise use has unknown flags " + std::to_string(use.flags));
    if (use.flags & InferenceStore::rewritesWholePremise)
      items.push_back("rewrites_whole_premise");
    if (use.flags & InferenceStore::virtualEpsilon)
      items.push_back("virtual(epsilon)");
    if (use.flags & InferenceStore::virtualPlusInfinity)
      items.push_back("virtual(plus_infinity)");
    if (use.flags & InferenceStore::virtualMinusInfinity)
      items.push_back("virtual(minus_infinity)");
    if (use.flags & InferenceStore::PremiseUse::negatedFlag)
      items.push_back("negated");
    if (!use.other.isEmpty())
      items.push_back("other(" + fot(use.other) + ")");
    if (!use.factor.isEmpty())
      items.push_back("factor(" + fot(use.factor) + ")");
    return items;
  }

  /**
   * Where each literal of @b from went in @b into, given the unifier
   * @b bindings and the @b rewritten literals of the use (both may be null).
   * @b position is the premise's position among the parents of @b u.
   */
  std::vector<Placed> place(Unit* u, unsigned position, const std::vector<Literal*>& from,
                            Clause* into, const Stack<std::pair<unsigned, TermList>>* bindings,
                            const Stack<InferenceStore::RewrittenLiteral>* rewritten)
  {
    struct Bound {
      DHMap<unsigned, TermList, FnvHash, IdentityHash> map;
      TermList apply(unsigned v) {
        TermList t;
        return map.find(v, t) ? t : TermList(v, false);
      }
    } bound;
    if (bindings)
      for (const auto& [v, t] : *bindings)
        bound.map.set(v, t);
    std::vector<Placed> out;
    // a literal-wise simplification records the image of each literal
    std::vector<const InferenceStore::LiteralImage*> images;
    if (position == 0 && u->isClause())
      images = literalImagesOf(u, firstClausePremise(u));
    if (!images.empty()) {
      for (const auto* image : images) {
        // a null image means the literal was dropped
        Placed entry{indexIn(into, image->to)};
        if (image->to && entry.index == NONE)
          throw UserErrorException("unit " + std::to_string(u->number()) +
            " recorded a literal image its conclusion does not have");
        out.push_back(entry);
      }
      return out;
    }
    for (Literal* lit : from) {
      const InferenceStore::RewrittenLiteral* became = nullptr;
      for (unsigned k = 0; rewritten && k < rewritten->size() && !became; k++)
        if ((*rewritten)[k].from == lit)
          became = &(*rewritten)[k];
      if (became) {
        Placed entry{indexIn(into, became->to), became->turned, true};
        if (entry.index == NONE)
          throw UserErrorException("unit " + std::to_string(u->number()) +
            " recorded a rewritten literal its conclusion does not have");
        out.push_back(entry);
        continue;
      }
      Literal* image = SubstHelper::apply(lit, bound);
      // see Shuffling::polarityFlip
      if (u->inference().rule() == InferenceRule::POLARITY_FLIPPING && !lit->isEquality()
          && env.signature->getPredicate(lit->functor())->wasFlipped())
        image = Literal::complementaryLiteral(image);
      Placed entry{indexIn(into, image)};
      // equations are shared modulo orientation, so compare the sides
      if (entry.index != NONE && lit->isEquality())
        entry.turned = SubstHelper::apply(*lit->nthArgument(0), bound) !=
                       *(*into)[entry.index]->nthArgument(0);
      out.push_back(entry);
    }
    return out;
  }

  /**
   * The placements of the premise literals of @b u, keyed by the premise's
   * position among the parents and the index of the use among its uses.
   */
  std::map<std::pair<unsigned, unsigned>, std::vector<Placed>> placements(Unit* u)
  {
    std::map<std::pair<unsigned, unsigned>, std::vector<Placed>> out;
    const Inference& inference = u->inference();
    // for a split clause (a formula), place the components' literals into
    // the clause being split
    bool splitClause = inference.rule() == InferenceRule::AVATAR_SPLIT_CLAUSE;
    if (!u->isClause() && !splitClause)
      return out;
    const Stack<InferenceStore::PremiseUse>* recorded =
      InferenceStore::instance()->premiseUses(u);
    auto usesOf = [&](unsigned number) {
      std::vector<const InferenceStore::PremiseUse*> uses;
      if (recorded)
        for (const auto& use : *recorded)
          if (use.premise == number)
            uses.push_back(&use);
      return uses;
    };
    std::vector<Unit*> premises = premisesOf(u);
    std::map<unsigned, unsigned> occurrences;
    for (unsigned pos = 0; pos < premises.size(); pos++) {
      Unit* premise = premises[pos];
      unsigned occurrence = occurrences[premise->number()]++;
      auto premiseUses = usesOf(premise->number());
      if (premise->isClause() && !splitClause) {
        Clause* cl = premise->asClause();
        std::vector<Literal*> lits(cl->literals(), cl->literals() + cl->length());
        const auto* use = occurrence < premiseUses.size() ? premiseUses[occurrence] : nullptr;
        out[{pos, occurrence}] = place(u, pos, lits, u->asClause(),
          use ? &use->bindings : nullptr, use ? &use->rewritten : nullptr);
      } else if (splitClause && !premise->isClause() && pos > 0 && premises[0]->isClause()) {
        // a component definition, placed once per recorded renaming
        std::vector<Literal*> lits;
        if (!componentLiterals(premise->getFormula(), lits))
          continue;
        // a negative ground singleton is defined by its complement, see
        // Splitter::buildAndInsertComponentClause
        Clause* split = premises[0]->asClause();
        if (lits.size() == 1 && lits[0]->ground()) {
          Literal* complement = Literal::complementaryLiteral(lits[0]);
          if (complement->isNegative() && indexIn(split, complement) != NONE)
            lits[0] = complement;
        }
        for (unsigned k = 0; k < premiseUses.size(); k++)
          out[{pos, k}] = place(u, pos, lits, split, &premiseUses[k]->bindings, nullptr);
      } else if (inference.rule() == InferenceRule::CLAUSIFY && pos == 0 && !premise->isClause()
                 && InferenceStore::instance()->genClauseOfClause(u) != InferenceStore::stateNone) {
        // place the literals of the last generalised clause, see
        // NewCNF::toClause
        const auto* state = InferenceStore::instance()->genClauseState(
          InferenceStore::instance()->genClauseOfClause(u));
        Substitution subst;
        for (const auto& [v, t] : state->bindings)
          subst.bindUnbound(v, t);
        Clause* into = u->asClause();
        std::vector<Placed> entries;
        for (const auto& [f, positive] : state->literals) {
          Placed entry;
          if (f->connective() == LITERAL) {
            Literal* made = f->literal()->apply(subst);
            if (!positive)
              made = Literal::complementaryLiteral(made);
            entry.index = indexIn(into, made);
            entry.turned = entry.index != NONE && made->isEquality()
              && SubstHelper::apply(*f->literal()->nthArgument(0), subst)
                   != *(*into)[entry.index]->nthArgument(0);
          }
          entries.push_back(entry);
        }
        out[{pos, 0}] = entries;
      } else if (inference.rule() == InferenceRule::AVATAR_COMPONENT && pos == 0
                 && !premise->isClause()) {
        // a component clause, from its definition
        std::vector<Literal*> lits;
        if (!componentLiterals(premise->getFormula(), lits))
          continue;
        // a negative ground singleton is defined by its complement, see
        // Splitter::buildAndInsertComponentClause
        Clause* cl = u->asClause();
        if (lits.size() == 1 && cl->length() == 1 && (*cl)[0]->ground()
            && (*cl)[0]->isNegative() && lits[0] == Literal::complementaryLiteral((*cl)[0]))
          lits[0] = (*cl)[0];
        out[{pos, 0}] = place(u, pos, lits, cl, nullptr, nullptr);
      }
    }
    return out;
  }

  /**
   * The parent list of @b u with the recorded uses and placements.
   *
   * The Jth occurrence of a premise gets its Jth use, and the last occurrence
   * also gets the remaining ones. Throw if some use or placement cannot be
   * attached to a parent.
   */
  std::string parentList(Unit* u)
  {
    std::vector<Unit*> premises = premisesOf(u);
    std::map<unsigned, std::vector<const InferenceStore::PremiseUse*>> usesOf;
    size_t numUses = 0;
    if (const auto* recorded = InferenceStore::instance()->premiseUses(u))
      for (const auto& use : *recorded) {
        usesOf[use.premise].push_back(&use);
        numUses++;
      }
    auto placementAt = placements(u);
    std::map<unsigned, unsigned> occurrences, last;
    for (unsigned pos = 0; pos < premises.size(); pos++)
      last[premises[pos]->number()] = pos;
    size_t usesWritten = 0;
    size_t placementsWritten = 0;
    std::vector<std::string> out;
    for (unsigned pos = 0; pos < premises.size(); pos++) {
      unsigned number = premises[pos]->number();
      unsigned j = occurrences[number]++;
      const auto& uses = usesOf[number];
      unsigned end = last[number] == pos ? std::max<unsigned>(j + 1, uses.size()) : j + 1;
      std::vector<std::string> details;
      for (unsigned k = j; k < end; k++) {
        auto at = placementAt.find({pos, k});
        if (k < uses.size()) {
          std::vector<std::string> items = useItems(u, *uses[k]);
          if (at != placementAt.end()) {
            items.push_back(placedList(at->second));
            placementsWritten++;
          }
          details.push_back(items.empty() ? "use" : "use(" + join(items) + ")");
          usesWritten++;
        } else if (at != placementAt.end()) {
          if (k != j)
            throw UserErrorException("step " + std::to_string(u->number()) +
              " places a premise's literals under a use it did not record");
          details.push_back(placedList(at->second));
          placementsWritten++;
        }
      }
      out.push_back(unitName(premises[pos]) +
                    (details.empty() ? "" : ":[" + join(details) + "]"));
    }
    if (usesWritten != numUses || placementsWritten != placementAt.size())
      throw UserErrorException("step " + std::to_string(u->number()) +
        " recorded uses or placements of premises it does not have");
    return "[" + join(out) + "]";
  }

  /**
   * The sorts of variables that occur in the premise uses of @b u but not in
   * @b u itself, whose variable sorts are @b own.
   */
  static std::vector<std::pair<unsigned, TermList>> boundSorts(Unit* u, VarSorts& own)
  {
    std::vector<std::pair<unsigned, TermList>> out;
    const auto* recorded = InferenceStore::instance()->premiseUses(u);
    if (!recorded)
      return out;
    VarSorts bound;
    std::map<unsigned, Unit*> premiseByNumber;
    for (Unit* premise : premisesOf(u))
      premiseByNumber[premise->number()] = premise;
    for (const InferenceStore::PremiseUse& use : *recorded) {
      // computed lazily
      VarSorts premiseSorts;
      bool readPremiseSorts = false;
      auto premiseSortOf = [&](unsigned v) {
        if (!readPremiseSorts) {
          auto premise = premiseByNumber.find(use.premise);
          if (premise != premiseByNumber.end())
            SortHelper::collectVariableSorts(premise->second, premiseSorts);
          readPremiseSorts = true;
        }
        TermList sort;
        return premiseSorts.find(v, sort) ? sort : TermList::empty();
      };
      for (const auto& [v, t] : use.bindings) {
        if (t.isTerm()) {
          SortHelper::collectVariableSorts(const_cast<Term*>(t.term()), bound);
        } else if (t.isVar()) {
          // a variable image takes the sort of the premise variable
          TermList sort = premiseSortOf(v);
          if (sort.isNonEmpty())
            bound.set(t.var(), sort);
        }
      }
      for (TermList t : {use.term, use.other, use.factor})
        if (t.isTerm())
          SortHelper::collectVariableSorts(const_cast<Term*>(t.term()), bound);
    }
    for (const auto& [v, sort] : sortsInOrder(bound))
      if (!own.findPtr(v))
        out.push_back({v, sort});
    return out;
  }

  /** The `choice(...)` items for the conjuncts @b chosen by CNF::clausify for @b u. */
  std::string choices(Unit* u, const Stack<std::pair<Formula*, unsigned>>& chosen)
  {
    std::vector<Unit*> premises = premisesOf(u);
    if (premises.empty() || premises[0]->isClause())
      throw UserErrorException("clausification step " + std::to_string(u->number()) +
                               " records conjunct choices but has no premise formula");
    Formula* premise = premises[0]->getFormula();
    std::vector<std::string> out;
    for (const auto& [conjunction, argument] : chosen) {
      std::vector<std::vector<unsigned>> found;
      std::vector<unsigned> path;
      positionsOf(premise, conjunction, path, found);
      if (found.empty())
        throw UserErrorException("clausification step " + std::to_string(u->number()) +
                                 " chose a conjunct of a conjunction its premise does not have");
      // a shared subformula gets one choice per occurrence
      for (const auto& at : found) {
        std::vector<std::string> positions;
        for (unsigned k : at)
          positions.push_back(std::to_string(k));
        out.push_back("choice([" + join(positions) + "]," + std::to_string(argument) + ")");
      }
    }
    return join(out);
  }

  /** The printed congruence-closure @b steps for @b cl. */
  std::string congruences(Clause* cl, const std::vector<congruence::Step>& steps)
  {
    std::vector<std::string> out;
    for (unsigned i = 0; i < steps.size(); i++) {
      const congruence::Step& step = steps[i];
      std::vector<std::string> args;
      for (unsigned arg : step.args)
        args.push_back(optionalIndex(arg));
      std::string argList = "[" + join(args) + "]";
      switch (step.kind) {
        case congruence::INPUT:
          out.push_back("input(" + std::to_string(step.a) + ")");
          break;
        case congruence::CONGRUENCE:
          out.push_back("congruence(" + fot(step.lhs) + "," + fot(step.rhs) + "," + argList + ")");
          break;
        case congruence::TRANS:
          out.push_back("trans(" + std::to_string(step.a) + "," + std::to_string(step.b) + ")");
          break;
        case congruence::SYMM:
          out.push_back("symm(" + std::to_string(step.a) + ")");
          break;
        case congruence::GOAL_EQUALITY:
          out.push_back("goal_equality(" + std::to_string(step.a) + "," +
                        optionalIndex(step.b) + ")");
          break;
        case congruence::GOAL_LITERALS: {
          // If the literals are printed flipped back, they swap roles and the
          // argument equalities are needed reversed. As the goal is the last
          // step, the symmetry steps can be inserted before it.
          if (!turnedBack((*cl)[step.a])) {
            out.push_back("goal_literals(" + std::to_string(step.a) + "," +
                          std::to_string(step.b) + "," + argList + ")");
            break;
          }
          if (i + 1 != steps.size())
            throw UserErrorException("congruence closure of a step does not end at its goal");
          unsigned next = i;
          std::vector<std::string> swapped;
          for (unsigned arg : step.args) {
            if (arg == NONE) {
              swapped.push_back("none");
              continue;
            }
            out.push_back("symm(" + std::to_string(arg) + ")");
            swapped.push_back(std::to_string(next++));
          }
          out.push_back("goal_literals(" + std::to_string(step.b) + "," +
                        std::to_string(step.a) + ",[" + join(swapped) + "])");
          break;
        }
      }
    }
    return join(out);
  }

  /** The information items recorded for @b u. */
  std::vector<std::string> information(Unit* u)
  {
    InferenceStore* store = InferenceStore::instance();
    const Inference& inference = u->inference();
    InferenceRule rule = inference.rule();
    std::vector<std::string> info;

    if (const auto* symbols = store->introducedSymbols(u); symbols && !symbols->isEmpty()) {
      std::vector<std::string> names;
      for (const Signature::Symbol* sym : iterTraits(symbols->iter()))
        names.push_back(symbol(sym->name()));
      info.push_back(std::string("new_symbols(") +
                     (rule == InferenceRule::SKOLEMIZE ? "skolem" : "definition") + ",[" +
                     join(names) + "])");
    }
    if (const std::string* name = store->introducedSplitName(u))
      info.push_back("new_symbols(definition,[" + splitLiteral(*name) + "])");
    Stack<std::tuple<const Signature::Symbol*, unsigned, Term*>> skolems;
    store->introducedSkolems(u, skolems);
    for (auto [sym, replaced, symTerm] : skolems)
      info.push_back("skolemize(" + var(replaced) + "," + term(TermList(symTerm)) + ")");
    if (SATClause* sat = inference.satPremise())
      info.push_back("sat_premise(" + satName(sat) + ")");
    if (const auto* named = store->namings(u); named && !named->isEmpty()) {
      std::vector<std::string> namings;
      for (const auto& naming : *named) {
        std::vector<std::string> args;
        for (unsigned v : naming.arguments)
          args.push_back(var(v));
        namings.push_back("naming(" + atom(naming.symbol->name()) + ",[" + join(args) + "]," +
                          recordFormula(naming.named) + ")");
      }
      info.push_back("namings([" + join(namings) + "])");
    }
    unsigned genClause = store->genClauseOfClause(u);
    if (genClause != InferenceStore::stateNone)
      info.push_back("gen_clause(" + genName(genClause) + ")");
    if (const auto* chosen = store->conjunctChoices(u); chosen && !chosen->isEmpty())
      info.push_back("choices([" + choices(u, *chosen) + "])");
    if (u->isClause() && rule == InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT) {
      congruence::Proof derivation;
      if (derivation.of(u->asClause()))
        info.push_back("congruences([" + congruences(u->asClause(), derivation.steps()) + "])");
    }
    if (const Stack<Literal*>* constraints = store->constraints(u);
        constraints && !constraints->isEmpty()) {
      std::vector<std::string> at;
      for (Literal* constraint : iterTraits(constraints->iter())) {
        unsigned i = indexIn(u->asClause(), constraint);
        if (i == NONE)
          throw UserErrorException("a unification constraint of unit " +
            std::to_string(u->number()) + " is not among its literals");
        at.push_back(std::to_string(i));
      }
      info.push_back("constraints([" + join(at) + "])");
    }
    if (u->isClause() && (rule == InferenceRule::GENERAL_SPLITTING_COMPONENT ||
                          rule == InferenceRule::GENERAL_SPLITTING)) {
      unsigned at = indexIn(u->asClause(), store->splittingNameLiteral(u));
      if (at == NONE)
        throw UserErrorException("general splitting step " +
          std::to_string(u->number()) + " has no recorded name literal");
      info.push_back("splitting_name(" + std::to_string(at) + ")");
    }
    std::vector<const InferenceStore::LiteralImage*> images;
    if (u->isClause())
      images = literalImagesOf(u, firstClausePremise(u));
    bool scaled = false;
    for (const auto* image : images)
      scaled = scaled || image->factor != RationalConstantType(1);
    if (scaled) {
      std::vector<std::string> factors;
      for (const auto* image : images) {
        std::ostringstream text;
        text << image->factor.numerator() << "/" << image->factor.denominator();
        factors.push_back(text.str());
      }
      info.push_back("literal_factors([" + join(factors) + "])");
    }
    // INEQUALITY_PREDICATE_NORMALIZATION records no images, see literalImagesOf
    if (const auto* rewriting = store->literalImages(u);
        rewriting && (!images.empty() || rewriting->procedure ==
          InferenceStore::LiteralProcedure::INEQUALITY_PREDICATE_NORMALIZATION))
      info.push_back("procedure(" + procedureName(rewriting->procedure) + ")");
    // for pure predicate removal, the number of predicates found pure so far
    unsigned variant = 0;
    store->pureStage(u, variant);
    if (const auto* introduced = store->introduced(u); introduced && u->isClause()) {
      Clause* cl = u->asClause();
      variant = introduced->variant;
      Clause* first = firstClausePremise(u);
      std::vector<std::string> lits;
      for (unsigned i = 0; i < introduced->literals.size(); i++) {
        unsigned entry = indexIn(cl, introduced->literals[i]);
        if (entry == NONE)
          throw UserErrorException("unit " + std::to_string(u->number()) +
            " recorded an introduced literal its conclusion does not have");
        unsigned source = NONE;
        if (!introduced->sources.isEmpty() && first) {
          source = indexIn(first, introduced->sources[i]);
          if (source == NONE)
            throw UserErrorException("unit " + std::to_string(u->number()) +
              " recorded an introduced literal of a literal its premise does not have");
        }
        lits.push_back("lit(" + std::to_string(entry) + "," + optionalIndex(source) + ")");
      }
      if (!lits.empty())
        info.push_back("introduced([" + join(lits) + "])");
      if (variant != 0)
        info.push_back("variant(" + std::to_string(variant) + ")");
      if (!introduced->terms.isEmpty()) {
        std::vector<std::string> terms;
        for (TermList t : iterTraits(introduced->terms.iterFifo()))
          terms.push_back(optionalTerm(t));
        info.push_back("introduced_terms([" + join(terms) + "])");
      }
    } else if (variant != 0) {
      info.push_back("variant(" + std::to_string(variant) + ")");
    }
    return info;
  }

  void unit(Unit* u, std::string& out)
  {
    _unflip = _boundary != 0 && u->number() >= _boundary;
    const Inference& inference = u->inference();
    InferenceRule rule = inference.rule();
    std::vector<Unit*> premises = premisesOf(u);

    // subsumption resolution does not record its substitution
    if (rule == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION ||
        rule == InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)
      InferenceStore::instance()->recoverSubsumptionResolutionUses(u);

    VarSorts own;
    SortHelper::collectVariableSorts(u, own);
    auto ownSorts = sortsInOrder(own);
    std::vector<std::string> info;
    std::string statement;
    if (u->isClause()) {
      Clause* cl = u->asClause();
      std::vector<std::string> lits;
      for (unsigned i = 0; i < cl->length(); i++)
        lits.push_back(literal((*cl)[i]));
      if (cl->splits())
        for (SplitLevel name : iterTraits(cl->splits()->iter()))
          lits.push_back(negatedSplitLiteral(Splitter::getFormulaStringFromName(name)));
      statement = universalClosure(ownSorts,
        lits.empty() ? "$false" : "(" + join(lits, " | ") + ")");
    } else {
      statement = formula(u->getFormula());
      if (!ownSorts.empty())
        info.push_back("variable_sorts([" + typedVars(ownSorts) + "])");
    }
    auto bound = boundSorts(u, own);
    if (!bound.empty())
      info.push_back("bound_sorts([" + typedVars(bound) + "])");
    for (std::string& item : information(u))
      info.push_back(std::move(item));

    std::string axiomName;
    std::filesystem::path axiomPath;
    bool named = Parse::TPTP::findAxiomName(u, axiomName, axiomPath);
    std::string source;
    if (rule == InferenceRule::INPUT && premises.empty()) {
      source = "file(" + quoted(named ? axiomPath.string() : std::string("unknown")) +
               (named ? "," + atom(axiomName) : std::string()) + ")";
      // file() has no info list, so use the annotation's useful info
      if (!info.empty())
        source += ", [" + join(info) + "]";
    } else {
      std::string status = rule == InferenceRule::SKOLEMIZE ? "status(esa)"
        : rule == InferenceRule::NEGATED_CONJECTURE ? "status(cth)" : "";
      if (named)
        info.push_back("input_name(" + atom(axiomName) + ")");
      std::vector<std::string> items;
      if (!status.empty())
        items.push_back(status);
      items.insert(items.end(), info.begin(), info.end());
      if (premises.empty()) {
        bool definition = InferenceStore::instance()->introducedSymbols(u) ||
                          InferenceStore::instance()->introducedSplitName(u);
        items.insert(items.begin(), tptpRuleName(rule));
        source = std::string("introduced(") + (definition ? "definition" : "theory") + ",[" +
                 join(items) + "],[])";
      } else {
        source = "inference(" + tptpRuleName(rule) + ",[" + join(items) + "]," +
                 parentList(u) + ")";
      }
    }

    out += std::string(u->isClause() ? "tcf(" : "tff(") + unitName(u) + ", " + role(u) + ", " +
           statement + ", " + source + ").\n";
  }

  /** Print the SAT clauses @b root depends on, premises first, each only once. */
  void satProof(SATClause* root, std::string& out)
  {
    std::set<SATClause*> closure;
    std::vector<SATClause*> todo = {root};
    while (!todo.empty()) {
      SATClause* next = todo.back();
      todo.pop_back();
      if (!closure.insert(next).second)
        continue;
      SATInference* inf = next->inference();
      if (inf && inf->getType() == SATInference::InfType::PROP_INF)
        for (SATClause* p : iterTraits(inf->propInf()->getPremises()->iter()))
          todo.push_back(p);
    }
    std::vector<SATClause*> ordered(closure.begin(), closure.end());
    std::sort(ordered.begin(), ordered.end(),
              [](SATClause* a, SATClause* b) { return a->number < b->number; });
    for (SATClause* cl : ordered)
      if (_satWritten.insert(cl).second)
        satClause(cl, out);
  }

  void satClause(SATClause* cl, std::string& out)
  {
    // only split names, which are never flipped
    _unflip = false;
    std::vector<SATLiteral> lits;
    std::vector<std::string> written;
    for (SATLiteral l : iterTraits(cl->iter())) {
      lits.push_back(l);
      written.push_back(splitLiteral(Splitter::getFormulaStringFromLiteral(l)));
    }
    std::string statement = written.empty() ? "$false" : "(" + join(written, " | ") + ")";
    std::string source = "unknown";
    SATInference* inf = cl->inference();
    if (inf && inf->getType() == SATInference::InfType::PROP_INF) {
      std::vector<SATClause*> premises;
      for (SATClause* p : iterTraits(inf->propInf()->getPremises()->iter()))
        premises.push_back(p);
      // the premise list is in reverse order of use
      std::reverse(premises.begin(), premises.end());
      std::vector<std::string> names;
      for (SATClause* p : premises)
        names.push_back(satName(p));
      source = "inference(rat,[],[" + join(names) + "])";
    } else if (inf) {
      Unit* origin = inf->foConversion()->getOrigin();
      std::string order;
      // SAT2FO::toSAT sorts the literals, so print for each first-order
      // literal the index of the propositional literal naming it
      if (origin->isClause()) {
        Clause* ocl = origin->asClause();
        std::vector<std::string> entries;
        for (unsigned i = 0; i < ocl->length(); i++) {
          Literal* lit = (*ocl)[i];
          unsigned found = NONE;
          for (unsigned j = 0; j < lits.size() && found == NONE; j++) {
            SATLiteral named = lits[j].positive() ? lits[j] : lits[j].opposite();
            Unit* definition = InferenceStore::instance()->splitDefinition(
              Splitter::getFormulaStringFromLiteral(named));
            if (!definition || definition->isClause())
              continue;
            Formula* component = definedComponent(definition->getFormula());
            if (!component || component->connective() != LITERAL)
              continue;
            Literal* meant = component->literal();
            if (lits[j].positive() ? meant == lit : meant == Literal::complementaryLiteral(lit))
              found = j;
          }
          if (found == NONE)
            throw UserErrorException("a propositional clause of unit " +
              std::to_string(origin->number()) + " has no literal for its literal " +
              std::to_string(i));
          entries.push_back(std::to_string(found));
        }
        order = "order([" + join(entries) + "])";
      }
      source = "inference(sat_conversion,[" + order + "],[" + unitName(origin) + "])";
    }
    out += "cnf(" + satName(cl) + ", plain, " + statement + ", " + source + ").\n";
  }

  /** Print generalised clause @b state and its unprinted ancestors, ancestors first. */
  void genChain(unsigned state, Unit* premise, std::string& out)
  {
    std::vector<unsigned> chain;
    for (unsigned at = state; at != InferenceStore::stateNone && !_genWritten.count(at);
         at = InferenceStore::instance()->genClauseState(at)->parent)
      chain.push_back(at);
    for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
      _genWritten.insert(*it);
      genStep(*it, premise, out);
    }
  }

  /**
   * Print the generalised clause @b id of the new clausifier as a step.
   * @b premise is the formula unit being clausified, if any.
   */
  void genStep(unsigned id, Unit* premise, std::string& out)
  {
    // clausification precedes polarity flipping
    _unflip = false;
    const InferenceStore::GenClauseState* state = InferenceStore::instance()->genClauseState(id);
    VarSorts sorts;
    for (const auto& [f, positive] : state->literals)
      SortHelper::collectVariableSorts(f, sorts, /*ignoreBound=*/true);
    std::vector<std::string> disjuncts, bound;
    for (const auto& [v, image] : state->bindings) {
      if (image.isTerm()) {
        SortHelper::collectVariableSorts(const_cast<Term*>(image.term()), sorts);
        if (!sorts.find(v))
          sorts.insert(v, SortHelper::getResultSort(image.term()));
      }
      bound.push_back(var(v));
      disjuncts.push_back(var(v) + " != " + term(image));
    }
    for (const auto& [f, positive] : state->literals) {
      if (positive && f->connective() == NOT)
        throw UserErrorException("a generalised clause holds a negation positively");
      disjuncts.push_back(positive ? formula(f) : "~ (" + formula(f) + ")");
    }
    auto prefix = sortsInOrder(sorts);
    std::sort(prefix.begin(), prefix.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });
    std::string statement = universalClosure(prefix,
      disjuncts.empty() ? "$false" : "(" + join(disjuncts, " | ") + ")");

    std::vector<std::string> items = {genHowName(state->how)};
    if (state->position != InferenceStore::positionNone)
      items.push_back("position(" + std::to_string(state->position) + ")");
    if (!bound.empty())
      items.push_back("bound([" + join(bound) + "])");
    std::vector<std::string> replacement;
    for (const auto& [f, positive] : state->replacement)
      replacement.push_back(std::string(positive ? "pos(" : "neg(") + recordFormula(f) + ")");
    items.push_back("replacement([" + join(replacement) + "])");
    std::vector<std::string> placed;
    for (unsigned at : iterTraits(state->placement.iterFifo())) {
      std::string k = std::to_string(at & ~InferenceStore::genTurned);
      placed.push_back(at & InferenceStore::genTurned ? "turned(" + k + ")" : k);
    }
    items.push_back("placed([" + join(placed) + "])");

    // an initial clause comes from the premise or is a definition
    std::string source;
    if (state->parent != InferenceStore::stateNone) {
      source = "inference(clausification_step,[" + join(items) + "],[" +
               genName(state->parent) + "])";
    } else {
      bool fromPremise = premise && !premise->isClause() && state->replacement.size() == 1 &&
        state->replacement[0].second && state->replacement[0].first == premise->getFormula();
      source = fromPremise
        ? "inference(clausification_step,[" + join(items) + "],[" + unitName(premise) + "])"
        : "introduced(definition,[clausification_step," + join(items) + "],[])";
    }
    out += "tff(" + genName(id) + ", plain, " + statement + ", " + source + ").\n";
  }
};

}  // namespace

void outputTPTPProofExtra(std::ostream& out, Unit* refutation)
{
  Writer().write(out, refutation);
}

}  // namespace Kernel
