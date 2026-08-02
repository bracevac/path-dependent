import LambdaP.Original.RuntimeOpeningProbe

/-!
A structural runtime-checking prototype.

`Tm.RuntimeTy` retains an ordinary source typing derivation and applies
runtime subtyping only at its outer result.  Consequently it cannot type a
path elimination whose root has the required pair type only after source or
runtime conversion.  `Path.RuntimeCheck` puts that conversion before the
elimination rules.

This is intentionally not yet a full runtime type system.  The term judgment
below covers only path terms and trailing runtime subsumption.  In particular,
this file provides no binder extension, store extension, general renaming or
substitution theorem, and no runtime counterparts of generalized-type
well-formedness or all term constructors.
-/

namespace LambdaP.Original

/-! ## Structural checking for paths -/

/-- Store-indexed path checking.  Unlike source `Path.Ty`, a path may be
converted with `Tau.RuntimeSub` before it is used as the scrutinee of `fst` or
selection. -/
inductive Path.RuntimeCheck (Gamma : Ctx n) (sigma : Store n) :
    Path n -> Tau n k -> Prop where
| source :
    Path.Ty Gamma p d ->
    Path.RuntimeCheck Gamma sigma p d
| sub :
    Path.RuntimeCheck Gamma sigma p d1 ->
    Tau.RuntimeSub Gamma sigma d1 d2 ->
    Path.RuntimeCheck Gamma sigma p d2
| fst :
    Path.RuntimeCheck Gamma sigma p
      (Tau.ty (Ty.Pair S a d)) ->
    Path.RuntimeCheck Gamma sigma p.fst (Tau.ty S)
| sel_r :
    Path.RuntimeCheck Gamma sigma p
      (Tau.ty (Ty.Pair S a d)) ->
    Path.RuntimeCheck Gamma sigma (p.sel a) (d.open p.fst)
| sel_l :
    Path.RuntimeCheck Gamma sigma p
      (Tau.ty (Ty.Pair S b d')) ->
    Path.RuntimeCheck Gamma sigma (p.fst.sel a) d ->
    a ≠ b ->
    Path.RuntimeCheck Gamma sigma (p.sel a) d

/-- Every source precise-path derivation embeds directly. -/
theorem Path.RuntimeCheck.of_source
    (h : Path.Ty Gamma p d) : Path.RuntimeCheck Gamma sigma p d :=
  .source h

/-- A source subtyping derivation may be used as a checking conversion. -/
theorem Path.RuntimeCheck.source_sub
    (h : Path.RuntimeCheck Gamma sigma p d1)
    (hs : Tau.Sub Gamma d1 d2) :
    Path.RuntimeCheck Gamma sigma p d2 :=
  .sub h (.source hs)

/-! ## The path-term fragment -/

/-- Runtime checking for the fragment needed by path machine states: path
introduction followed by any number of mixed runtime-subtyping steps. -/
inductive Tm.RuntimeCheck (Gamma : Ctx n) (sigma : Store n) :
    Tm n -> LambdaP.Original.Ty n -> Prop where
| path :
    Path.RuntimeCheck Gamma sigma p (Tau.ty U) ->
    Tm.RuntimeCheck Gamma sigma (Tm.path p) (Ty.Single p)
| sub :
    Tm.RuntimeCheck Gamma sigma t S ->
    Tau.RuntimeSub Gamma sigma (Tau.ty S) (Tau.ty T) ->
    Tm.RuntimeCheck Gamma sigma t T

/-- A source-typed path term embeds, including all of its trailing source
subsumption steps. -/
theorem Tm.RuntimeCheck.of_source_path
    (h : Tm.Ty Gamma (Tm.path p) T) :
    Tm.RuntimeCheck Gamma sigma (Tm.path p) T := by
  obtain ⟨U, hp, hsub, _⟩ := h.path_inversion rfl
  exact .sub (.path (.source hp)) (.source hsub)

/-! ## The failed `rename` successor now checks -/

namespace RuntimeCheckingProbe

open RuntimeOpeningProbe.Refined

/-- The public singleton type of `target3` is below the pair type selected
from the equal abstract bounds. -/
theorem target_public_sub_pair :
    Tau.RuntimeSub GammaTarget sigmaTarget
      (Tau.ty targetPublicType.weaken) (Tau.ty pairType3) := by
  apply Tau.RuntimeSub.source
  simpa [targetPublicType, member3] using
    (Tau.Sub.sel_hi abstract_selection_typing3 Tau.Sub.refl)

/-- Conversion is deliberately performed before projection. -/
theorem target3_checks_as_pair :
    Path.RuntimeCheck GammaTarget sigmaTarget
      (Path.var target3) (Tau.ty pairType3) := by
  exact .sub (.source (Path.Ty.var target3_binding))
    target_public_sub_pair

theorem target3_fst_checks_top :
    Path.RuntimeCheck GammaTarget sigmaTarget
      (Path.var target3).fst (Tau.ty Ty.Top) := by
  have hfst := Path.RuntimeCheck.fst target3_checks_as_pair
  exact .sub hfst (.source Tau.Sub.top)

theorem target3_fst_term_checks_top :
    Tm.RuntimeCheck GammaTarget sigmaTarget
      (Tm.path (Path.var target3).fst) Ty.Top := by
  exact .sub (.path target3_fst_checks_top) (.source Tau.Sub.top)

/-- This is the term produced by the concrete `State.Step.rename` transition
in `RuntimeOpeningProbe`. -/
theorem rename_successor_checks :
    Tm.RuntimeCheck GammaTarget sigmaTarget afterRename.term Ty.Top := by
  simpa [afterRename, body4_open_target] using
    target3_fst_term_checks_top

/-- The structural prototype checks exactly the successor for which the
top-level `Tm.RuntimeTy` invariant has no source witness. -/
theorem structural_check_is_strictly_deeper_here :
    Tm.RuntimeCheck GammaTarget sigmaTarget afterRename.term Ty.Top ∧
    ¬ Tm.RuntimeTy GammaTarget sigmaTarget afterRename.term Ty.Top := by
  exact ⟨rename_successor_checks,
    after_rename_term_not_runtime_typed⟩

end RuntimeCheckingProbe

end LambdaP.Original
