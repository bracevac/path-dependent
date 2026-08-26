import LambdaPToFCo.Direct.ContextRelation

/-!
# Relations for paths under divergent compiler contexts

This bounded leaf relates the exact runtime identities reached by one source
path under the two raw environments of a `ContextRelation.Scope`.  It starts
with variables, where the sealed pointwise relation supplies precisely the
coherence that source syntax does not.

An arbitrary proof-side `fst` or `sel_r` cannot be projected at the opposite
endpoint: the aligned receiver may validly relate a Pair to Top.  Structural
projection also cannot recover a child relation from a compact pair-to-pair
`Relation`, which intentionally erases its structural premises.  Such cases
must be fused inside the pair principal-cut continuation that still has both
actual receiver interfaces and the child relation.  No opposite path typing,
target-shape equality, or intermediate path plan is fabricated here.
-/

namespace LambdaPToFCo.Direct.Internal.PathRelation

open SystemFCo
open Representation
open ContextRelation

/-- Ignore an argument and return the package retained by one exact
interface.

This is the value-specific reverse leg needed to repackage a distinguished
path identity.  It is not an inverse to the aligned source relation and does
not assert source-level equivalence. -/
private noncomputable def distinguishedReverse
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig) :
    Conversion base source shape.inputTy :=
  let typed := Rename.Typed.weaken base (.var source)
  Conversion.ofFunction
    (Adapter.ofBody source
      (interface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken, Shape.inputTy_rename] using
        interface.package_hasType.rename typed))

/-- Applying the value-specific reverse to a value takes one ordinary
System FCo beta step to the retained package. -/
private theorem distinguishedReverse_beta
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig)
    (argument : Exp sig) (argumentValue : Exp.IsValue argument) :
    Exp.Step
      (Adapter.apply
        (distinguishedReverse interface source).function argument)
      interface.package := by
  change Exp.Step
    (.app (.abs source
      (interface.package.rename (Rename.weaken .var))) argument)
    interface.package
  have step := Exp.Step.beta (parameter := source)
    (body := interface.package.rename (Rename.weaken .var)) argumentValue
  have cancel := interface.package.weaken_subst_cancel
    (Subst.openVar argument) (Subst.weakenAsSubst_comp_openVar argument)
  change
    (interface.package.rename (Rename.weaken .var)).subst
      (Subst.openVar argument) = interface.package at cancel
  rw [cancel] at step
  exact step

/-- The exact two aligned variable interfaces determine the bridge used to
retarget their singleton packages.  The proof-side relation supplies its
oriented leg; the opposite leg is only the value-specific constant above. -/
private noncomputable def singletonBridge
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) :
    Conversion.Bridge base (scope.source.lookup index).shape.inputTy
      (scope.target.lookup index).shape.inputTy := by
  cases side with
  | source =>
      exact {
        leftToRight := (scope.aligned index).conversion
        rightToLeft := distinguishedReverse
          (scope.source.lookup index).interface
          (scope.target.lookup index).shape.inputTy
      }
  | target =>
      exact {
        leftToRight := distinguishedReverse
          (scope.target.lookup index).interface
          (scope.source.lookup index).shape.inputTy
        rightToLeft := (scope.aligned index).conversion
      }

/-- Contextual reflexivity for the singleton of an aligned variable.

The result is always oriented from the source endpoint to the target
endpoint.  `ProofSide` only determines which direction of the pointwise
relation is available when constructing the singleton bridge. -/
noncomputable def singletonVariable
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) :
    Relation base (.Single (.var index)) (.Single (.var index))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy))
      (.stable (Single.plan
        (scope.target.lookup index).shape.inputTy)) :=
  Relation.ofConversion
    (.singleton base (.var index)
      (scope.source.lookup index).shape.inputTy)
    (.singleton base (.var index)
      (scope.target.lookup index).shape.inputTy)
    (Conversion.Singleton.retarget base
      (scope.source.lookup index).shape.inputTy
      (scope.target.lookup index).shape.inputTy
      (singletonBridge scope index))

end LambdaPToFCo.Direct.Internal.PathRelation
