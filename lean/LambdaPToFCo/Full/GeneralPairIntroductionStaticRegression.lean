import LambdaPFC.GeneralPairRegression
import LambdaPToFCo.Full.PairIntroductionCompiler

/-!
# Demand-local general-pair introduction regression

This leaf compiles the direct type-member pair that forms the body of
`LambdaPFC.GeneralPairRegression.term`. The witness is the singleton of the
bound `Top` variable. Its exact variable path package is already available in
the singleton-bound scope, so `WfPlan.Proper.singletonFromPathPackage` builds
the one witness plan demanded by `PairIntroductionCompiler` without requiring
an implementation of the global `WfPlan.Resolver`.

The result is the exact `tpair` package and its target typing. It deliberately
does not claim to compile the following pair subsumption or close the enclosing
source `let`; those remain separate higher-compiler obligations.
-/

namespace LambdaPToFCo.Full.GeneralPairIntroductionStaticRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

def rootScope : ScopeModel LambdaPFC.Ctx.nil SystemFCoExt.Ctx.empty :=
  ScopeModel.empty SystemFCoExt.Ctx.empty

def topResult := WfPlan.Proper.top rootScope

/-- The concrete target scope corresponding to the `Top`-typed bound variable
in the source body. -/
noncomputable def bodyScope :
    ScopeModel (LambdaPFC.Ctx.nil.snoc .Top)
      (topResult.plan.context SystemFCoExt.Ctx.empty) :=
  rootScope.bindBidirectional topResult.model

def witness : LambdaPFC.Ty 1 := .Single (.var 0)

def witnessWf : LambdaPFC.Tau.Wf (LambdaPFC.Ctx.nil.snoc .Top)
    (.ty witness) :=
  .path .var

def exactBody : LambdaPFC.Tm 1 :=
  .pair 0 LambdaPFC.GeneralPairRegression.label (.type witness)

def exactType : LambdaPFC.Ty 1 :=
  .Pair (.Single (.var 0)) LambdaPFC.GeneralPairRegression.label
    ((Tau.intv witness witness).weaken)

def exactBodySourceTyping :
    Tm.Ty (LambdaPFC.Ctx.nil.snoc .Top) exactBody exactType :=
  .tpair witnessWf

/-- The compiled source introduction is definitionally the body of the
existing closed regression term. -/
theorem sourceTerm_eq :
    LambdaPFC.GeneralPairRegression.term =
      .let (.abs .Top (.path (.var 0))) exactBody := by
  rfl

noncomputable def witnessBoundScope :=
  PairIntroductionCompiler.bindVariableSingleton bodyScope (0 : Fin 1)

/-- Weakening the witness path below the freshly bound singleton first
component selects the older `Top` slot. -/
def weakenedPrecise :
    Path.Ty
      ((LambdaPFC.Ctx.nil.snoc .Top).snoc (.Single (.var 0)))
      (.var (1 : Fin 2)) (.ty .Top) := by
  exact .var

noncomputable def witnessPath :=
  witnessBoundScope.variablePath (1 : Fin 2)

/-- The exact demand-local witness plan, derived only from the variable path
package already certified by `witnessBoundScope`. -/
noncomputable def witnessPlan :
    PairIntroductionCompiler.WitnessPlan bodyScope (0 : Fin 1) witness := by
  simpa [witness, LambdaPFC.Ty.weaken, LambdaPFC.Ty.rename,
    LambdaPFC.Path.weaken, LambdaPFC.Path.rename] using
    (WfPlan.Proper.singletonFromPathPackage witnessBoundScope weakenedPrecise
      witnessPath)

/-- Public Full compilation of the exact type-member introduction. -/
noncomputable def compiled :=
  PairIntroductionCompiler.typePairFromWitnessPlan bodyScope (0 : Fin 1)
    LambdaPFC.GeneralPairRegression.label witnessWf witnessPlan

def sourceOrigin : ProducerOrigin (LambdaPFC.Ctx.nil.snoc .Top) exactType :=
  .value exactBodySourceTyping .pair

theorem compiled_origin_eq : compiled.origin = sourceOrigin := by
  rfl

/-- Concrete target typing for the exact compiled `tpair` package. -/
noncomputable def targetTerm_hasType :
    Exp.HasType (topResult.plan.context SystemFCoExt.Ctx.empty)
      compiled.package.expression compiled.plan.inputTy :=
  compiled.package.typing

end LambdaPToFCo.Full.GeneralPairIntroductionStaticRegression
