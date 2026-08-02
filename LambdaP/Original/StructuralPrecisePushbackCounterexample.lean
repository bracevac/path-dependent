import LambdaP.Original.StructuralPreciseCanonical

/-!
Exact structural stores do not validate singleton head pushback.

The counterexample needs only two cells.  The older cell is an abstraction
`f`; the newer cell is a type-member pair whose exact member is `Top..Top`.
Ordinary widening and `Top` give `{f} <: Top`, while selection lowering gives
`Top <: {q.A}`.  Path promotion therefore rechecks `f` at `{q.A}`; allowing
that non-precise check as the premise of singleton symmetry then produces

`Top <: {q.A} <: {f} <: type(f)`.

Thus the singleton of the pair cell is below a function type via `Top`, even
though the cell contains a pair.  Every context entry is nevertheless an
exact `Tm.StructPrecise` introduction type.  No interval subsumption is
needed.  The problematic operation is the interaction between proper-type
promotion and structural singleton symmetry: source `Tau.Sub.symm` accepts
only a precise `Path.Ty` premise, not a path reclassified by subtyping.
-/

namespace LambdaP.Original
namespace StructuralPrecisePushbackCounterexample

abbrev label : Name := 0

/-! ## Cell 0: a closure -/

abbrev fType0 : Ty 0 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

abbrev fValue : Tm 0 :=
  Tm.abs Ty.Top (Tm.path (Path.var 0))

theorem f_value : fValue.IsValue := by
  exact .abs

theorem f_precise :
    Tm.StructPrecise Ctx.nil
      (Path.RuntimeEq (Store.empty : Store 0)) fValue fType0 := by
  exact Tm.StructPrecise.abs
    (Tm.StructCheck.path (Path.StructCheck.var Ctx.Binds.here))
    Tau.StructWf.top

abbrev GammaF : Ctx 1 := Ctx.nil.snoc fType0

abbrev sigmaF : Store 1 :=
  Store.val (Store.empty : Store 0) fValue f_value

theorem storeF : Store.StructPreciseTy GammaF sigmaF := by
  exact Store.StructPreciseTy.val .empty f_precise f_value

/-! ## Cell 1: an exact `Top..Top` type member -/

abbrev f1 : Fin 1 := 0

abbrev qValue : Tm 1 :=
  Tm.pair f1 label (Def.type Ty.Top)

abbrev qType : Ty 1 :=
  Ty.Pair (Ty.Single (Path.var f1)) label
    (Tau.intv Ty.Top Ty.Top).weaken

theorem q_value : qValue.IsValue := by
  exact .pair

theorem q_precise :
    Tm.StructPrecise GammaF (Path.RuntimeEq sigmaF) qValue qType := by
  exact Tm.StructPrecise.tpair Ctx.Binds.here Tau.StructWf.top

abbrev Gamma : Ctx 2 := GammaF.snoc qType

abbrev sigma : Store 2 := Store.val sigmaF qValue q_value

theorem store_precise : Store.StructPreciseTy Gamma sigma := by
  exact Store.StructPreciseTy.val storeF q_precise q_value

abbrev qRoot : Fin 2 := 0
abbrev f : Fin 2 := 1

abbrev qSel : Path 2 := (Path.var qRoot).sel label

/-- The weakened closure entry retains the same dependent identity-function
shape; its codomain's variable `0` is the function binder. -/
abbrev fType : Ty 2 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

theorem f_context : Ctx.Binds Gamma f fType := by
  simpa only [Gamma, GammaF, fType, fType0, Ty.weaken, Ty.rename,
    Path.rename] using
    (Ctx.Binds.there (S := qType)
      (Ctx.Binds.here (Γ := Ctx.nil) (T := fType0)))

theorem q_context : Ctx.Binds Gamma qRoot qType.weaken := by
  exact Ctx.Binds.here

theorem q_store : Store.Binds sigma qRoot qValue.weaken := by
  exact Store.Binds.here

/-! ## The structural collapse -/

/-- Exact selection of the stored `Top..Top` member. -/
theorem q_selection_exact :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) qSel
      (Tau.intv Ty.Top Ty.Top) := by
  have hroot : Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var qRoot) (Tau.ty qType.weaken) :=
    Path.StructCheck.var q_context
  have hsel := Path.StructCheck.sel_r hroot
  simpa only [qSel, qType, Ty.weaken, Ty.rename, Tau.weaken,
    Tau.rename, Tau.weaken_open] using hsel

/-- Widening gives `{f}` its exact function type; that type is below `Top`,
and the exact `Top..Top` lower bound puts `Top` below `{q.A}`. -/
theorem f_singleton_sub_q_singleton :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var f)))
      (Tau.ty (Ty.Single qSel)) := by
  exact Tau.StructSub.trans
    (Tau.StructSub.widen (Path.StructCheck.var f_context))
    (Tau.StructSub.trans Tau.StructSub.top
      (Tau.StructSub.sel_lo q_selection_exact Tau.StructSub.refl))

/-- Promotion rechecks the ordinary variable `f` at the singleton `{q.A}`. -/
theorem f_checks_q_singleton :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) (Path.var f)
      (Tau.ty (Ty.Single qSel)) := by
  exact Path.StructCheck.promote
    (Path.StructCheck.var f_context) f_singleton_sub_q_singleton

/-- Singleton symmetry now supplies the reverse alias. -/
theorem q_singleton_sub_f_singleton :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single qSel))
      (Tau.ty (Ty.Single (Path.var f))) := by
  exact Tau.StructSub.symm f_checks_q_singleton

/-- The exact `Top..Top` lower bound puts `Top` below the selection
singleton. -/
theorem top_sub_q_singleton :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty Ty.Top) (Tau.ty (Ty.Single qSel)) := by
  exact Tau.StructSub.sel_lo q_selection_exact Tau.StructSub.refl

/-- Hence `Top` is below the exact function type of `f`. -/
theorem top_sub_function :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty Ty.Top) (Tau.ty fType) := by
  exact Tau.StructSub.trans top_sub_q_singleton
    (Tau.StructSub.trans q_singleton_sub_f_singleton
      (Tau.StructSub.widen (Path.StructCheck.var f_context)))

/-- The singleton of the type-member pair is consequently below a function
type, despite naming a concrete pair. -/
theorem pair_singleton_sub_function :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var qRoot))) (Tau.ty fType) := by
  exact Tau.StructSub.trans Tau.StructSub.top top_sub_function

/-! ## Checked failure of exact-store head inversion -/

theorem q_not_abstraction_binding :
    forall {A : Ty 2} {body : Tm 3},
      ¬ Store.Binds sigma qRoot (Tm.abs A body) := by
  intro A body habs
  have heq := habs.unique q_store
  cases heq

/-- The function component of exact singleton head pushback is false. -/
theorem not_singleton_head_pushback :
    ¬ Store.StructPreciseSingletonHeadPushback Gamma sigma := by
  intro hpush
  obtain ⟨A, body, hbind⟩ :=
    hpush.function store_precise pair_singleton_sub_function
  exact q_not_abstraction_binding hbind

/-- Equivalently, exact structural store typing does not imply the function
head reflection consumed by progress. -/
theorem not_function_check_reflection :
    ¬ Store.FunctionCheckReflection Gamma sigma := by
  intro hreflect
  have hqAtFunction : Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var qRoot) (Tau.ty fType) :=
    Path.StructCheck.promote (Path.StructCheck.var q_context)
      pair_singleton_sub_function
  obtain ⟨A, body, hbind⟩ := hreflect hqAtFunction
  exact q_not_abstraction_binding hbind

end StructuralPrecisePushbackCounterexample
end LambdaP.Original
