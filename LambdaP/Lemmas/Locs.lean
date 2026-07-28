import LambdaP.Lemmas.StoWeaken

/-!
Location bounds from the judgments: well-typed syntax mentions only
locations recorded in the store typing. Needed to preserve heap
acyclicity across allocation.
-/

namespace LambdaP

/-! ### LocsBelow is invariant under renaming, monotone under substitution -/

theorem Var.locsBelow_rename {s1 s2 : Sig} {f : Rename s1 s2} {x : Var s1} {k : Nat} :
    (x.rename f).LocsBelow k ↔ x.LocsBelow k := by
  cases x <;> simp [Var.rename, Var.LocsBelow]

theorem Path.locsBelow_rename {s1 s2 : Sig} {f : Rename s1 s2} {p : Path s1} {k : Nat} :
    (p.rename f).LocsBelow k ↔ p.LocsBelow k := by
  induction p with
  | var x => exact Var.locsBelow_rename
  | fst p ih => exact ih
  | sel p a ih => exact ih

theorem Ty.locsBelow_rename {s1 s2 : Sig} {f : Rename s1 s2} {T : Ty s1} {k : Nat} :
    (T.rename f).LocsBelow k ↔ T.LocsBelow k := by
  induction T generalizing s2 with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | arrow S T ih1 ih2 => exact and_congr ih1 ih2
  | pairTm S a T ih1 ih2 => exact and_congr ih1 ih2
  | pairTy S A T1 T2 ih1 ih2 ih3 => exact and_congr ih1 (and_congr ih2 ih3)
  | single p => exact Path.locsBelow_rename
  | tsel p A => exact Path.locsBelow_rename

/-- All images of a substitution are below `k`. -/
def Subst.LocsBelow (k : Nat) (σ : Subst s1 s2) : Prop :=
  ∀ x, (σ.var x).LocsBelow k

theorem Subst.LocsBelow.lift {σ : Subst s1 s2} {k : Nat}
    (hσ : σ.LocsBelow k) : (σ.lift).LocsBelow k := by
  intro x
  cases x with
  | here => trivial
  | there x => exact Path.locsBelow_rename.mpr (hσ x)

theorem Path.LocsBelow.subst {p : Path s1} {σ : Subst s1 s2} {k : Nat}
    (hσ : σ.LocsBelow k) (hp : p.LocsBelow k) : (p.subst σ).LocsBelow k := by
  induction p with
  | var x =>
    cases x with
    | bound b => exact hσ b
    | free ℓ => exact hp
  | fst p ih => exact ih hp
  | sel p a ih => exact ih hp

theorem Ty.LocsBelow.subst {T : Ty s1} {σ : Subst s1 s2} {k : Nat}
    (hσ : σ.LocsBelow k) (hT : T.LocsBelow k) : (T.subst σ).LocsBelow k := by
  induction T generalizing s2 with
  | top => trivial
  | bot => trivial
  | arrow S T ih1 ih2 => exact ⟨ih1 hσ hT.1, ih2 hσ.lift hT.2⟩
  | pairTm S a T ih1 ih2 => exact ⟨ih1 hσ hT.1, ih2 hσ.lift hT.2⟩
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    exact ⟨ih1 hσ hT.1, ih2 hσ.lift hT.2.1, ih3 hσ.lift hT.2.2⟩
  | single p => exact Path.LocsBelow.subst hσ hT
  | tsel p A => exact Path.LocsBelow.subst hσ hT

theorem Subst.LocsBelow.openPath {q : Path s} {k : Nat}
    (hq : q.LocsBelow k) : (Subst.openPath q).LocsBelow k := by
  intro x
  cases x with
  | here => exact hq
  | there x => trivial

/-- Opening with a bounded path keeps a bounded type bounded. -/
theorem Ty.LocsBelow.open {T : Ty (s+1)} {q : Path s} {k : Nat}
    (hT : T.LocsBelow k) (hq : q.LocsBelow k) : (T.open q).LocsBelow k :=
  Ty.LocsBelow.subst (Subst.LocsBelow.openPath hq) hT

/-! ### Bounds from the judgments -/

def Tau.LocsBelow (k : Nat) : Tau s -> Prop
| .ty T => T.LocsBelow k
| .intv T1 T2 => T1.LocsBelow k ∧ T2.LocsBelow k

/-- Wellformed paths mention only recorded locations. -/
theorem Path.Wf.locsBelow {Θ : Sto} {Γ : Ctx s} {p : Path s}
    (hw : Path.Wf Θ Γ p) : p.LocsBelow Θ.length :=
  match hw with
  | .var_bound _ => trivial
  | .var_free hl => (List.getElem?_eq_some_iff.mp hl).1
  | .fst_tm h1 _ => h1.locsBelow
  | .fst_ty h1 _ => h1.locsBelow
  | .sel h1 _ => h1.locsBelow
  | .sel_skip_tm h1 _ _ => h1.locsBelow
  | .sel_skip_ty h1 _ => h1.locsBelow

/-- Wellformed types mention only recorded locations. -/
theorem Wf.locsBelow {Θ : Sto} {Γ : Ctx s} {τ : Tau s}
    (hw : Wf Θ Γ τ) : τ.LocsBelow Θ.length := by
  induction hw with
  | bot => trivial
  | top => trivial
  | single hp => exact hp.locsBelow
  | tsel hp _ => exact hp.locsBelow
  | arrow _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | pair_tm _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | pair_ty _ _ ih1 ih2 => exact ⟨ih1, ih2.1, ih2.2⟩
  | intv _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

/-- Well-typed terms mention only recorded locations. -/
theorem HasType.locsBelow_tm {Θ : Sto} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (ht : HasType Θ Γ t T) : t.LocsBelow Θ.length := by
  induction ht with
  | path hp => exact hp.locsBelow
  | sub _ _ _ ih => exact ih
  | abs hwf _ ih => exact ⟨hwf.locsBelow, ih⟩
  | app _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | pair_tm hy hz => exact ⟨hy.locsBelow, hz.locsBelow⟩
  | pair_ty hy hwf => exact ⟨hy.locsBelow, hwf.locsBelow⟩
  | letin _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | typed _ hwf ih => exact ⟨ih, hwf.locsBelow⟩

/-- The type of a well-typed term mentions only recorded locations. -/
theorem HasType.locsBelow_ty {Θ : Sto} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (ht : HasType Θ Γ t T) : T.LocsBelow Θ.length := by
  induction ht with
  | path hp => exact hp.locsBelow
  | sub _ _ hwf _ => exact hwf.locsBelow
  | abs hwf _ ih => exact ⟨hwf.locsBelow, ih⟩
  | app _ h2 ih1 _ =>
    exact Ty.LocsBelow.open ih1.2 h2.locsBelow_tm
  | pair_tm hy hz =>
    exact ⟨hy.locsBelow, Ty.locsBelow_rename.mpr hz.locsBelow⟩
  | pair_ty hy hwf =>
    exact ⟨hy.locsBelow, Ty.locsBelow_rename.mpr hwf.locsBelow,
      Ty.locsBelow_rename.mpr hwf.locsBelow⟩
  | letin _ hwf _ _ _ => exact hwf.locsBelow
  | typed _ hwf _ => exact hwf.locsBelow

end LambdaP
