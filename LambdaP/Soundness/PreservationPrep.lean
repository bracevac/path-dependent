import LambdaP.Soundness.RealizedSubst

/-!
Preservation prerequisites (ported from the superseded conditional
file): store/heap extension under allocation, typing inversions up to
subsumption, and precise value typing. The three opening call-sites
(β, let-path, let-val bodies) await the realized substitution lemma.
-/

namespace LambdaP

theorem List.getElem?_concat_lt {α : Type} {l : List α} {a : α} {i : Nat}
    (h : i < l.length) : (l ++ [a])[i]? = l[i]? := by
  rw [List.getElem?_append_left h]

theorem List.getElem?_concat_self {α : Type} {l : List α} {a : α} :
    (l ++ [a])[l.length]? = some a := by
  simp

theorem List.getElem?_concat_inv {α : Type} {l : List α} {a b : α} {i : Nat}
    (h : (l ++ [a])[i]? = some b) :
    l[i]? = some b ∨ (i = l.length ∧ b = a) := by
  have hlt : i < l.length + 1 := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa using this
  rcases Nat.lt_or_ge i l.length with hi | hi
  · left
    rw [List.getElem?_concat_lt hi] at h
    exact h
  · right
    have hie : i = l.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hi
    subst hie
    rw [List.getElem?_concat_self] at h
    exact ⟨rfl, (Option.some_inj.mp h).symm⟩

theorem Sto.extends_concat {Θ : Sto} {Tp : Ty 0} : (Θ ++ [Tp]).Extends Θ := by
  intro ℓ T hl
  show (Θ ++ [Tp])[ℓ]? = some T
  rw [List.getElem?_concat_lt (List.getElem?_eq_some_iff.mp hl).1]
  exact hl

theorem Sto.lookup_concat {Θ : Sto} {Tp : Ty 0} :
    Sto.Lookup (Θ ++ [Tp]) Θ.length Tp :=
  List.getElem?_concat_self

/-! ### Precise types are bounded -/

theorem Val.PreciseTy.locsBelow {Θ : Sto} {v : Tm 0} {T : Ty 0}
    (h : Val.PreciseTy Θ v T) : T.LocsBelow Θ.length := by
  cases h with
  | abs hwf hty => exact ⟨hwf.locsBelow, hty.locsBelow_ty⟩
  | pair_tm hy hz =>
    exact ⟨hy.locsBelow, Ty.locsBelow_rename.mpr hz.locsBelow⟩
  | pair_ty hy hwf =>
    exact ⟨hy.locsBelow, Ty.locsBelow_rename.mpr hwf.locsBelow,
      Ty.locsBelow_rename.mpr hwf.locsBelow⟩

/-! ### Typing inversions (up to subsumption) -/

theorem HasType.app_inv' {Θ : Sto} {Γ : Ctx s} {p q : Path s} {T : Ty s}
    (ht : HasType Θ Γ (.app p q) T) :
    ∃ S T1, HasType Θ Γ (.path p) (.arrow S T1) ∧ HasType Θ Γ (.path q) S ∧
      Sub Θ Γ (.ty (T1.open q)) (.ty T) := by
  generalize he : Tm.app p q = t0 at ht
  induction ht with
  | path _ => cases he
  | sub _ hsub _ ih =>
    obtain ⟨S, T1, ha, hb, hc⟩ := ih he
    exact ⟨S, T1, ha, hb, .trans hc hsub⟩
  | abs _ _ _ => cases he
  | app h1 h2 =>
    cases he
    exact ⟨_, _, h1, h2, .refl⟩
  | pair_tm _ _ => cases he
  | pair_ty _ _ => cases he
  | letin _ _ _ _ _ => cases he
  | typed _ _ _ => cases he

theorem HasType.letin_inv {Θ : Sto} {Γ : Ctx s} {t1 : Tm s} {t2 : Tm (s+1)} {T : Ty s}
    (ht : HasType Θ Γ (.letin t1 t2) T) :
    ∃ S T0, HasType Θ Γ t1 S ∧ Wf Θ Γ (.ty T0) ∧
      HasType Θ (Γ.push S) t2 T0.weaken ∧ Sub Θ Γ (.ty T0) (.ty T) := by
  generalize he : Tm.letin t1 t2 = t0 at ht
  induction ht with
  | path _ => cases he
  | sub _ hsub _ ih =>
    obtain ⟨S, T0, ha, hb, hc, hd⟩ := ih he
    exact ⟨S, T0, ha, hb, hc, .trans hd hsub⟩
  | abs _ _ _ => cases he
  | app _ _ => cases he
  | pair_tm _ _ => cases he
  | pair_ty _ _ => cases he
  | letin h1 hwf h2 _ _ =>
    cases he
    exact ⟨_, _, h1, hwf, h2, .refl⟩
  | typed _ _ _ => cases he

theorem HasType.typed_inv {Θ : Sto} {Γ : Ctx s} {t : Tm s} {T0 T : Ty s}
    (ht : HasType Θ Γ (.typed t T0) T) :
    HasType Θ Γ t T0 ∧ Sub Θ Γ (.ty T0) (.ty T) := by
  generalize he : Tm.typed t T0 = tx at ht
  induction ht with
  | path _ => cases he
  | sub _ hsub _ ih =>
    obtain ⟨ha, hb⟩ := ih he
    exact ⟨ha, .trans hb hsub⟩
  | abs _ _ _ => cases he
  | app _ _ => cases he
  | pair_tm _ _ => cases he
  | pair_ty _ _ => cases he
  | letin _ _ _ _ _ => cases he
  | typed h1 hwf _ =>
    cases he
    exact ⟨h1, .refl⟩

/-! ### Value inversion -/

/-- A closed typed value has a precise type below its assigned type. -/
theorem HasType.value_inv {Θ : Sto} {v : Tm 0} {S : Ty 0}
    (ht : HasType Θ .empty v S) (hv : v.IsValue) :
    ∃ Tp, Val.PreciseTy Θ v Tp ∧ Sub Θ .empty (.ty Tp) (.ty S) := by
  suffices go : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s},
      HasType Θ Γ t T -> t.IsValue -> ∀ (hs : s = 0),
      ∃ Tp, Val.PreciseTy Θ (hs ▸ t) Tp ∧ Sub Θ .empty (.ty Tp) (.ty (hs ▸ T)) by
    exact go ht hv rfl
  clear ht hv
  intro s Γ t T ht
  induction ht with
  | path _ => intro hv _; cases hv
  | sub _ hsub _ ih =>
    intro hv hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨Tp, hpre, hs1⟩ := ih hv rfl
    exact ⟨Tp, hpre, .trans hs1 hsub⟩
  | abs hwf hbody _ =>
    intro _ hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    exact ⟨_, .abs hwf hbody, .refl⟩
  | app _ _ => intro hv _; cases hv
  | pair_tm hy hz =>
    intro _ hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    cases hy with
    | var_bound hx => exact absurd hx (fun hx => nomatch hx)
    | var_free hl1 =>
      cases hz with
      | var_bound hx => exact absurd hx (fun hx => nomatch hx)
      | var_free hl2 =>
        exact ⟨_, .pair_tm (.var_free hl1) (.var_free hl2), .refl⟩
  | pair_ty hy hwf =>
    intro _ hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    cases hy with
    | var_bound hx => exact absurd hx (fun hx => nomatch hx)
    | var_free hl1 => exact ⟨_, .pair_ty (.var_free hl1) hwf, .refl⟩
  | letin _ _ _ _ _ => intro hv _; cases hv
  | typed _ _ _ => intro hv _; cases hv


end LambdaP
