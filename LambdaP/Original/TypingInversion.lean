import LambdaP.Original.StoreRefinement

/-! Syntax-directed inversion facts for ordinary term typing. -/

namespace LambdaP.Original

/-- A typing derivation for a path term consists of its precise path
classification followed by (possibly several) subsumption steps. -/
theorem Tm.Ty.path_inversion
    {n : Nat} {Γ : Ctx n} {t : Tm n}
    {T : LambdaP.Original.Ty n} (h : Tm.Ty Γ t T) :
    ∀ {p : Path n}, t = Tm.path p ->
      ∃ U,
        Path.Ty Γ p (Tau.ty U) ∧
        Tau.Sub Γ (Tau.ty (Ty.Single p)) (Tau.ty T) ∧
        Tau.Wf Γ (Tau.ty T) := by
  induction h with
  | path hp =>
      intro p heq
      cases heq
      exact ⟨_, hp, .refl, .path hp⟩
  | abs _ _ _ =>
      intro p heq
      cases heq
  | app _ _ _ _ =>
      intro p heq
      cases heq
  | pair _ _ =>
      intro p heq
      cases heq
  | tpair _ _ =>
      intro p heq
      cases heq
  | «let» _ _ _ _ _ =>
      intro p heq
      cases heq
  | typed _ _ _ =>
      intro p heq
      cases heq
  | sub _ hsub hwf ih =>
      intro p heq
      obtain ⟨U, hp, hbase, _⟩ := ih heq
      exact ⟨U, hp, .trans hbase hsub, hwf⟩

/-- Any ordinary typing of a path term factors through subtyping from the
path's principal singleton. -/
theorem Tm.Ty.path_subtyping
    {n : Nat} {Γ : Ctx n} {p : Path n}
    {T : LambdaP.Original.Ty n}
    (h : Tm.Ty Γ (Tm.path p) T) :
    Tau.Sub Γ (Tau.ty (Ty.Single p)) (Tau.ty T) := by
  obtain ⟨U, hp, hsub, hwf⟩ := h.path_inversion rfl
  exact hsub

/-- Trailing subsumption does not obscure the two premises of an application
typing derivation. -/
theorem Tm.Ty.app_inversion_of_eq
    {n : Nat} {Γ : Ctx n} {u : Tm n}
    {R : LambdaP.Original.Ty n}
    (h : Tm.Ty Γ u R) :
    ∀ {p q : Path n}, u = Tm.app p q ->
      ∃ S T,
        Tm.Ty Γ (Tm.path p) (Ty.Fun S T) ∧
        Tm.Ty Γ (Tm.path q) S := by
  induction h with
  | path _ =>
      intro p q heq
      cases heq
  | abs _ _ _ =>
      intro p q heq
      cases heq
  | app hp hq _ _ =>
      intro p q heq
      cases heq
      exact ⟨_, _, hp, hq⟩
  | pair _ _ =>
      intro p q heq
      cases heq
  | tpair _ _ =>
      intro p q heq
      cases heq
  | «let» _ _ _ _ _ =>
      intro p q heq
      cases heq
  | typed _ _ _ =>
      intro p q heq
      cases heq
  | sub _ _ _ ih =>
      intro p q heq
      exact ih heq

/-- Public application inversion. -/
theorem Tm.Ty.app_inversion
    (h : Tm.Ty Γ (Tm.app p q) R) :
    ∃ S T,
      Tm.Ty Γ (Tm.path p) (Ty.Fun S T) ∧
      Tm.Ty Γ (Tm.path q) S :=
  h.app_inversion_of_eq rfl

end LambdaP.Original
