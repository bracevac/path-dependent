import LambdaPToFCo.Full.PairIntroductionCompiler
import LambdaPToFCo.Full.NormalizedTermCompilation

/-!
# Certified direct pair introductions

This high leaf connects both direct pair-introduction kernels to the
syntax-directed term-compilation boundary.  The value-member constructor
reuses the two exact variable interfaces already sealed by its `ScopeModel`.
The type-member constructor consumes one demand-local
`PairIntroductionCompiler.WitnessPlan` in the singleton-bound scope.  In both
cases `PairIntroductionCompiler` computes the target model, package, and every
representation adapter internally.

The result stops at `NormalizedTermCompilation`: the direct source typing has
the reflexive normalized suffix, but this leaf neither executes that suffix
nor claims to compile an enclosing subsumption.  No package, adapter, path
resolver, or callback is accepted by this API.
-/

namespace LambdaPToFCo.Full.PairIntroductionTermCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Value-member introduction -/

/-- The exact direct value-member typing compiled by `compileValuePair`. -/
def valueSourceTyping
    (first member : Fin n) (label : LambdaPFC.Name) :
    Tm.Ty sourceContext (.pair first label (.val member))
      (.Pair (.Single (.var first)) label
        (.ty (.Single ((Path.var member).weaken)))) :=
  .pair

/-- Compile and certify a direct value-member pair.  The indexed producer is
literally `PairIntroductionCompiler.valuePair`; this wrapper cannot replace
its package or origin. -/
noncomputable def compileValuePair
    (scope : ScopeModel sourceContext targetContext)
    (first member : Fin n) (label : LambdaPFC.Name) :
    NormalizedTermCompilation (valueSourceTyping first member label) scope
      (.ordinary
        (PairIntroductionCompiler.valuePair scope first member label)) where
  root_origin_eq := rfl

/-! ## Type-member introduction -/

/-- The exact direct type-member typing compiled by
`compileTypePairFromWitnessPlan`. -/
def typeSourceTyping
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    Tm.Ty sourceContext (.pair first label (.type witness))
      (.Pair (.Single (.var first)) label
        ((Tau.intv witness witness).weaken)) :=
  .tpair witnessWf

/-- Compile and certify a direct type-member pair from the one exact witness
plan already constructed in the singleton-bound scope.  This demand-local
input deliberately replaces any need for a total `WfPlan.Resolver`. -/
noncomputable def compileTypePairFromWitnessPlan
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness) :
    NormalizedTermCompilation
      (typeSourceTyping first label witnessWf) scope
      (.ordinary
        (PairIntroductionCompiler.typePairFromWitnessPlan scope first label
          witnessWf witnessPlan)) where
  root_origin_eq := rfl

end LambdaPToFCo.Full.PairIntroductionTermCompiler
