import LambdaPHistory.RuntimeTyping
import LambdaPHistory.Machine

/-!
A probe for the variable-opening case of the runtime typing invariant.

The local opening principle one would like for the machine's `rename` step is

```
  Gamma, b : S |- t : T
  Gamma; sigma |- x : S        (runtime typing)
  ------------------------------------------------
  Gamma; sigma |- t[x/b] : T   (runtime typing).
```

`Tm.RuntimeTy` cannot validate this principle.  Its runtime subtyping is
available only after an ordinary source typing derivation has already been
constructed.  The counterexample below keeps the store and context related by
`Store.RefinedTy`, and uses only an abstract type member with equal bounds.
-/

namespace LambdaPHistory.RuntimeOpeningProbe

/-! ## A refined-store obstruction

The construction uses one abstract type member with equal pair bounds
`R..R`.  A concrete pair can therefore be exposed publicly as the singleton
of that type selection (`R <: a.A`), while the same selection can be used at
its upper bound (`a.A <: R`).  The bounds are manifestly nonempty.  Term
subsumption therefore types the atomic variable at `R`, but precise path
typing still classifies it only at `{a.A}` and cannot derive a type for its
first projection.
-/

namespace Refined

abbrev fieldLabel : Name := 0
abbrev typeLabel : Name := 1

/-! ### An initial value used by all concrete pairs -/

abbrev yType : Ty 0 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

abbrev yValue : Tm 0 :=
  Tm.abs Ty.Top (Tm.path (Path.var 0))

theorem y_value : yValue.IsValue := by
  exact .abs

theorem y_precise : Tm.PreciseTy Ctx.nil yValue yType := by
  exact Tm.PreciseTy.abs
    (Tm.Ty.path (Path.Ty.var Ctx.Binds.here))
    Tau.Wf.top

abbrev GammaY : Ctx 1 := Ctx.nil.snoc yType

abbrev sigmaY : Store 1 :=
  Store.val (Store.empty : Store 0) yValue y_value

theorem sigmaY_refined : Store.RefinedTy GammaY sigmaY := by
  exact .val .empty y_precise y_precise.toTy .refl y_value

abbrev y1 : Fin 1 := 0

/-! ### A type member with equal pair bounds -/

/-- The pair type later used as the frame's binder type, stated before the
type-member cell is allocated. -/
abbrev pairBase : Ty 1 :=
  Ty.Pair (Ty.Single (Path.var y1)) fieldLabel
    (Tau.ty (Ty.Single (Path.var y1).weaken))

theorem pairBase_wf : Tau.Wf GammaY (Tau.ty pairBase) := by
  exact Tau.Wf.pair
    (Tau.Wf.path (Path.Ty.var Ctx.Binds.here))
    (Tau.Wf.path (Path.Ty.var
      (Ctx.Binds.there Ctx.Binds.here)))

abbrev memberValue : Tm 1 :=
  Tm.pair y1 typeLabel (Def.type pairBase)

theorem member_value : memberValue.IsValue := by
  exact .pair

abbrev memberType : Ty 1 :=
  Ty.Pair (Ty.Single (Path.var y1)) typeLabel
    (Tau.intv pairBase pairBase).weaken

theorem member_precise :
    Tm.PreciseTy GammaY memberValue memberType := by
  exact Tm.PreciseTy.tpair Ctx.Binds.here pairBase_wf

abbrev GammaMember : Ctx 2 := GammaY.snoc memberType

abbrev sigmaMember : Store 2 :=
  Store.val sigmaY memberValue member_value

theorem sigmaMember_refined :
    Store.RefinedTy GammaMember sigmaMember := by
  exact .val sigmaY_refined member_precise member_precise.toTy
    .refl member_value

abbrev member2 : Fin 2 := 0
abbrev y2 : Fin 2 := 1

/-- The equal bounds selected from the type-member cell. -/
abbrev pairType : Ty 2 := pairBase.weaken

theorem member_path_typing :
    Path.Ty GammaMember (Path.var member2)
      (Tau.ty memberType.weaken) := by
  exact Path.Ty.var Ctx.Binds.here

theorem abstract_selection_typing :
    Path.Ty GammaMember ((Path.var member2).sel typeLabel)
      (Tau.intv pairType pairType) := by
  simpa [memberType, pairType] using
    Path.Ty.sel_r member_path_typing

/-! ### A concrete pair hidden behind the abstract singleton -/

abbrev targetValue : Tm 2 :=
  Tm.pair y2 fieldLabel (Def.val y2)

theorem target_value : targetValue.IsValue := by
  exact .pair

theorem y2_binding : Ctx.Binds GammaMember y2 yType.weaken.weaken := by
  exact Ctx.Binds.there Ctx.Binds.here

theorem target_precise :
    Tm.PreciseTy GammaMember targetValue pairType := by
  simpa [pairType, pairBase] using
    (Tm.PreciseTy.pair y2_binding y2_binding)

abbrev targetPublicType : Ty 2 :=
  Ty.Single ((Path.var member2).sel typeLabel)

theorem target_precise_sub_public :
    Tau.Sub GammaMember (Tau.ty pairType) (Tau.ty targetPublicType) := by
  exact Tau.Sub.sel_lo abstract_selection_typing .refl

theorem target_public_wf :
    Tau.Wf GammaMember (Tau.ty targetPublicType) := by
  exact Tau.Wf.sel member_path_typing

theorem target_public_typing :
    Tm.Ty GammaMember targetValue targetPublicType := by
  exact Tm.Ty.sub target_precise.toTy target_precise_sub_public
    target_public_wf

abbrev GammaTarget : Ctx 3 :=
  GammaMember.snoc targetPublicType

abbrev sigmaTarget : Store 3 :=
  Store.val sigmaMember targetValue target_value

theorem sigmaTarget_refined :
    Store.RefinedTy GammaTarget sigmaTarget := by
  exact .val sigmaMember_refined target_precise target_public_typing
    target_precise_sub_public target_value

abbrev target3 : Fin 3 := 0
abbrev member3 : Fin 3 := 1

abbrev pairType3 : Ty 3 := pairType.weaken

theorem target3_binding :
    Ctx.Binds GammaTarget target3 targetPublicType.weaken := by
  exact Ctx.Binds.here

theorem abstract_selection_typing3 :
    Path.Ty GammaTarget ((Path.var member3).sel typeLabel)
      (Tau.intv pairType3 pairType3) := by
  simpa [member3, pairType3] using
    (abstract_selection_typing.weaken (S := targetPublicType))

/-- The public singleton of the target variable is below the pair type, but
the target variable still does not *precisely* synthesize a pair. -/
theorem target_singleton_sub_pair :
    Tau.Sub GammaTarget
      (Tau.ty (Ty.Single (Path.var target3)))
      (Tau.ty pairType3) := by
  apply Tau.Sub.trans (Tau.Sub.widen (Path.Ty.var target3_binding))
  simpa [targetPublicType, member3] using
    (Tau.Sub.sel_hi abstract_selection_typing3 Tau.Sub.refl)

theorem pairType3_wf : Tau.Wf GammaTarget (Tau.ty pairType3) := by
  simpa [pairType3, pairType] using
    (pairBase_wf.weaken (S := memberType)).weaken
      (S := targetPublicType)

/-- The counterexample is stronger than merely requiring runtime typing: the
replacement atom has the binder type even in ordinary term typing, by using
the upper bound of its public abstract singleton.  What it lacks is *precise
path typing* at a pair type. -/
theorem target3_source_typed :
    Tm.Ty GammaTarget (Tm.path (Path.var target3)) pairType3 := by
  exact Tm.Ty.sub
    (Tm.Ty.path (Path.Ty.var target3_binding))
    target_singleton_sub_pair pairType3_wf

theorem target3_runtime_typed :
    Tm.RuntimeTy GammaTarget sigmaTarget
      (Tm.path (Path.var target3)) pairType3 :=
  Tm.RuntimeTy.of_source target3_source_typed

/-! ### A source-typed frame body whose opening has no source witness -/

abbrev bound4 : Fin 4 := 0

abbrev body4 : Tm 4 :=
  Tm.path (Path.var bound4).fst

theorem body4_source_typed :
    Tm.Ty (GammaTarget.snoc pairType3) body4 Ty.Top.weaken := by
  exact Tm.Ty.sub
    (Tm.Ty.path (Path.Ty.fst (Path.Ty.var Ctx.Binds.here)))
    Tau.Sub.top Tau.Wf.top

theorem body4_open_target :
    body4.open target3 = Tm.path (Path.var target3).fst := by
  rfl

theorem target3_fst_not_path_typed (U : Ty 3) :
    ¬ Path.Ty GammaTarget (Path.var target3).fst (Tau.ty U) := by
  intro hp
  cases hp with
  | fst htarget =>
      cases htarget with
      | var hb =>
          have heq := hb.unique target3_binding
          cases heq

theorem opened_body4_not_source_typed (U : Ty 3) :
    ¬ Tm.Ty GammaTarget (body4.open target3) U := by
  intro ht
  rw [body4_open_target] at ht
  obtain ⟨V, hp, _, _⟩ := ht.path_inversion rfl
  exact target3_fst_not_path_typed V hp

theorem opened_body4_not_runtime_typed :
    ¬ Tm.RuntimeTy GammaTarget sigmaTarget
      (body4.open target3) Ty.Top := by
  intro hrt
  obtain ⟨U, ht, _⟩ := hrt
  exact opened_body4_not_source_typed U ht

/-- Even a refined, well-typed store does not make top-level runtime closure
stable under opening through source term constructors. -/
theorem refined_runtime_opening_counterexample :
    Store.RefinedTy GammaTarget sigmaTarget ∧
    Tm.Ty (GammaTarget.snoc pairType3) body4 Ty.Top.weaken ∧
    Tm.Ty GammaTarget (Tm.path (Path.var target3)) pairType3 ∧
    Tm.RuntimeTy GammaTarget sigmaTarget
      (Tm.path (Path.var target3)) pairType3 ∧
    ¬ Tm.RuntimeTy GammaTarget sigmaTarget
      (body4.open target3) Ty.Top := by
  exact ⟨sigmaTarget_refined, body4_source_typed,
    target3_source_typed, target3_runtime_typed,
    opened_body4_not_runtime_typed⟩

/-! ### The literal machine `rename` transition -/

abbrev beforeRename : State 3 :=
  ⟨sigmaTarget, [Tm.Frame.let body4],
    Tm.path (Path.var target3)⟩

abbrev afterRename : State 3 :=
  ⟨sigmaTarget, [], body4.open target3⟩

theorem before_rename_source_typed :
    State.Ty GammaTarget beforeRename Ty.Top := by
  exact State.Ty.ok sigmaTarget_refined.toTy
    (Tm.Cont.Ty.cons (Tm.Cont.Ty.hole .refl)
      (Tm.Frame.Ty.let body4_source_typed))
    target3_source_typed

theorem takes_rename_step : State.Step beforeRename afterRename := by
  exact State.Step.rename

/-- The successor cannot satisfy even the term component of the proposed
runtime-aware state invariant. -/
theorem after_rename_term_not_runtime_typed :
    ¬ Tm.RuntimeTy GammaTarget sigmaTarget
      afterRename.term Ty.Top := by
  exact opened_body4_not_runtime_typed

theorem after_rename_not_source_typed :
    ¬ State.Ty GammaTarget afterRename Ty.Top := by
  intro hs
  cases hs with
  | ok _ _ ht =>
      exact opened_body4_not_source_typed _ ht

theorem literal_rename_case_counterexample :
    Store.RefinedTy GammaTarget sigmaTarget ∧
    State.Ty GammaTarget beforeRename Ty.Top ∧
    State.Step beforeRename afterRename ∧
    ¬ State.Ty GammaTarget afterRename Ty.Top ∧
    ¬ Tm.RuntimeTy GammaTarget sigmaTarget
      afterRename.term Ty.Top := by
  exact ⟨sigmaTarget_refined, before_rename_source_typed,
    takes_rename_step, after_rename_not_source_typed,
    after_rename_term_not_runtime_typed⟩

end Refined

end LambdaPHistory.RuntimeOpeningProbe
