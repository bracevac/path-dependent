import LambdaPHistory.Typing

/-!
Functionality and inversion for the original precise path-typing judgment.

The result kind is an index of `Tau`, so ordinary homogeneous equality is
not a sufficiently general conclusion.  `Tau.DEq` below is the specialized
dependent equality for generalized types.  It has one constructor and can be
eliminated with `cases`, simultaneously identifying the kinds and signatures.
-/

namespace LambdaPHistory

/-- The type stored at a context index, weakened through every newer binder. -/
def Ctx.typeAt : (Γ : Ctx n) -> Fin n -> Ty n
| .nil, x => Fin.elim0 x
| .snoc Γ T, x =>
    Fin.cases T.weaken (fun i => (Ctx.typeAt Γ i).weaken) x

/-- A derivation of context lookup computes the deterministic type at that
index. -/
theorem Ctx.Binds.eq_typeAt (h : Ctx.Binds Γ x T) : T = Γ.typeAt x := by
  induction h with
  | here => rfl
  | there h ih =>
      change _ = (Ctx.typeAt _ _).weaken
      exact congrArg Ty.weaken ih

/-- Context lookup is functional.  This deliberately uses a different name
from `Ctx.Binds.unique` in `PreciseStore`. -/
theorem Ctx.Binds.functional
    (h1 : Ctx.Binds Γ x T1) (h2 : Ctx.Binds Γ x T2) : T1 = T2 :=
  h1.eq_typeAt.trans h2.eq_typeAt.symm

/-- Dependent equality of generalized types, including equality of their
kind indices. -/
inductive Tau.DEq {n k} (τ : Tau n k) : {k' : Kind} -> Tau n k' -> Prop where
| refl : Tau.DEq τ τ

namespace Tau.DEq

/-- Dependent equality identifies the kind indices. -/
theorem kind_eq {τ1 : Tau n k1} {τ2 : Tau n k2} (h : Tau.DEq τ1 τ2) :
    k1 = k2 := by
  cases h
  rfl

/-- Dependent equality implies heterogeneous equality of the signatures. -/
theorem heq {τ1 : Tau n k1} {τ2 : Tau n k2} (h : Tau.DEq τ1 τ2) :
    HEq τ1 τ2 := by
  cases h
  rfl

end Tau.DEq

/-- Precise path typing is functional.  Eliminating the result identifies
both its hidden kind and its generalized-type signature. -/
theorem Path.Ty.functional
    {Γ : Ctx n} {p : Path n}
    {k1 k2 : Kind} {τ1 : Tau n k1} {τ2 : Tau n k2}
    (h1 : Path.Ty Γ p τ1) (h2 : Path.Ty Γ p τ2) : Tau.DEq τ1 τ2 := by
  induction h1 generalizing k2 with
  | var hb1 =>
      cases h2 with
      | var hb2 =>
          cases Ctx.Binds.functional hb1 hb2
          exact .refl
  | fst hp1 ih =>
      cases h2 with
      | fst hp2 =>
          cases ih hp2
          exact .refl
  | sel_r hp1 ih =>
      cases h2 with
      | sel_r hp2 =>
          cases ih hp2
          exact .refl
      | sel_l hp2 htail2 hne2 =>
          cases ih hp2
          exact (hne2 rfl).elim
  | sel_l hp1 htail1 hne1 ihp ihtail =>
      cases h2 with
      | sel_r hp2 =>
          cases ihp hp2
          exact (hne1 rfl).elim
      | sel_l hp2 htail2 hne2 =>
          exact ihtail htail2

/-- The kind assigned to a path is unique. -/
theorem Path.Ty.kind_unique
    {Γ : Ctx n} {p : Path n}
    {k1 k2 : Kind} {τ1 : Tau n k1} {τ2 : Tau n k2}
    (h1 : Path.Ty Γ p τ1) (h2 : Path.Ty Γ p τ2) : k1 = k2 :=
  (h1.functional h2).kind_eq

/-- The complete signatures assigned to a path are heterogeneously equal. -/
theorem Path.Ty.signature_unique
    {Γ : Ctx n} {p : Path n}
    {k1 k2 : Kind} {τ1 : Tau n k1} {τ2 : Tau n k2}
    (h1 : Path.Ty Γ p τ1) (h2 : Path.Ty Γ p τ2) : HEq τ1 τ2 :=
  (h1.functional h2).heq

/-! Constructor-specific inversion principles. -/

theorem Path.Ty.invert_var
    {Γ : Ctx n} {x : Fin n} {k : Kind} {τ : Tau n k}
    (h : Path.Ty Γ (Path.var x) τ) :
    ∃ T, Ctx.Binds Γ x T ∧ Tau.DEq τ (Tau.ty T) := by
  cases h with
  | var hb => exact ⟨_, hb, .refl⟩

theorem Path.Ty.invert_fst
    {Γ : Ctx n} {p : Path n} {k : Kind} {τ : Tau n k}
    (h : Path.Ty Γ p.fst τ) :
    ∃ (S : LambdaPHistory.Ty n) (a : Name) (k' : Kind)
      (d : Tau (n + 1) k'),
      Path.Ty Γ p (Tau.ty (Ty.Pair S a d)) ∧ Tau.DEq τ (Tau.ty S) := by
  cases h with
  | fst hp => exact ⟨_, _, _, _, hp, .refl⟩

/-- A selection is typed either by hitting the current member label or by
following the first component and continuing lookup there. -/
theorem Path.Ty.invert_sel
    {Γ : Ctx n} {p : Path n} {a : Name} {k : Kind} {τ : Tau n k}
    (h : Path.Ty Γ (p.sel a) τ) :
    (∃ (S : LambdaPHistory.Ty n) (k' : Kind) (d : Tau (n + 1) k'),
      Path.Ty Γ p (Tau.ty (Ty.Pair S a d)) ∧
        Tau.DEq τ (d.open p.fst)) ∨
    (∃ (S : LambdaPHistory.Ty n) (b : Name) (k' : Kind)
      (d : Tau (n + 1) k'),
      Path.Ty Γ p (Tau.ty (Ty.Pair S b d)) ∧
        Path.Ty Γ (p.fst.sel a) τ ∧ a ≠ b) := by
  cases h with
  | sel_r hp => exact .inl ⟨_, _, _, hp, .refl⟩
  | sel_l hp htail hne => exact .inr ⟨_, _, _, _, hp, htail, hne⟩

end LambdaPHistory
