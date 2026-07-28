import LambdaP.Soundness.Transfer
import LambdaP.Soundness.Progress
import LambdaP.Soundness.Functionality
import LambdaP.Lemmas.Locs

/-!
Preservation: a step of a closed well-typed term is typed at a subtype in
an extended store typing. The subtype conclusion (rather than the exact
type) is what makes the beta case independent of syntactic functionality:
`repl` bridges the argument-path/argument-location gap, and narrowing
re-types let-contexts around stepped subterms.
-/

namespace LambdaP

/-! ### Concatenation lookups -/

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

theorem Sto.lookup_lt {Θ : Sto} {m : Nat} (hm : m < Θ.length) :
    ∃ T, Sto.Lookup Θ m T :=
  ⟨Θ[m], List.getElem?_eq_getElem hm⟩

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
    have hE := Ctx.eq_empty ‹Ctx 0›
    subst hE
    obtain ⟨Tp, hpre, hs1⟩ := ih hv rfl
    exact ⟨Tp, hpre, .trans hs1 hsub⟩
  | abs hwf hbody _ =>
    intro _ hs
    subst hs
    have hE := Ctx.eq_empty ‹Ctx 0›
    subst hE
    exact ⟨_, .abs hwf hbody, .refl⟩
  | app _ _ => intro hv _; cases hv
  | pair_tm hy hz =>
    intro _ hs
    subst hs
    have hE := Ctx.eq_empty ‹Ctx 0›
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
    have hE := Ctx.eq_empty ‹Ctx 0›
    subst hE
    cases hy with
    | var_bound hx => exact absurd hx (fun hx => nomatch hx)
    | var_free hl1 => exact ⟨_, .pair_ty (.var_free hl1) hwf, .refl⟩
  | letin _ _ _ _ _ => intro hv _; cases hv
  | typed _ _ _ => intro hv _; cases hv

/-! ### Preservation -/

/-- Preservation: a step of a closed well-typed term is typed at a subtype
in an extended store typing, and the extended store typing types the new
heap. -/
theorem preservation {Θ : Sto} {Ξ : SemSto} {h h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (hstep : Step h t h' t') :
    HeapTyped Θ h -> SemStoOk Θ Ξ h -> HasType Θ .empty t T ->
    ∃ Θ', Θ'.Extends Θ ∧ HeapTyped Θ' h' ∧
      ∃ T', HasType Θ' .empty t' T' ∧ Sub Θ' .empty (.ty T') (.ty T) := by
  induction hstep generalizing T with
  | apply hevf heva hlk =>
    intro hh hok ht
    obtain ⟨S, T1, h1, h2, hsub⟩ := ht.app_inv'
    obtain ⟨ℓf', T0', tb', T1', hevf', hlkf, hwf0, hbody, hdom, hcod⟩ :=
      canonical_arrow hh hok h1
    cases PathEval.deterministic hevf' hevf
    have heqv := Option.some_inj.mp ((Eq.symm hlkf).trans hlk)
    injection heqv with hs0 hT0 htb
    subst hT0
    subst htb
    obtain ⟨hwq, hsubq⟩ := h2.path_inv rfl
    have hma := hwq.eval_target_lt hh heva
    obtain ⟨Ta, hlka⟩ := Sto.lookup_lt hma
    have hwla : Path.Wf Θ .empty (.var (.free _)) := .var_free hlka
    have hsla := Sub.symm hwq (heva.to_sub hh)
    have hda := Sub.trans (Sub.trans hsla hsubq) hdom
    have hopened := hbody.open hwla hda
    have hc1 := hcod.subst (SubstTyping.openPath hwla (.trans hsla hsubq))
    simp only [Tau.subst] at hc1
    have hc2 := Sub.repl (T := T1) hwla hwq hsla (heva.to_sub hh)
    exact ⟨Θ, Sto.Extends.refl, hh,
      _, hopened, .trans hc1 (.trans hc2 hsub)⟩
  | path hev hne =>
    intro hh hok ht
    obtain ⟨hw, hsub⟩ := ht.path_inv rfl
    have hm := hw.eval_target_lt hh hev
    obtain ⟨Tm0, hlkm⟩ := Sto.lookup_lt hm
    exact ⟨Θ, Sto.Extends.refl, hh,
      _, .path (.var_free hlkm),
      .trans (.symm hw (hev.to_sub hh)) hsub⟩
  | let_path hev =>
    intro hh hok ht
    obtain ⟨S, T0, h1, hwf0, h2, hsub⟩ := ht.letin_inv
    obtain ⟨hwp, hsubp⟩ := h1.path_inv rfl
    have hm := hwp.eval_target_lt hh hev
    obtain ⟨Tm0, hlkm⟩ := Sto.lookup_lt hm
    have hwl : Path.Wf Θ .empty (.var (.free _)) := .var_free hlkm
    have hsl := Sub.trans (Sub.symm hwp (hev.to_sub hh)) hsubp
    exact ⟨Θ, Sto.Extends.refl, hh, T0, h2.open_weaken hwl hsl, hsub⟩
  | let_val hv =>
    intro hh hok ht
    obtain ⟨S, T0, h1, hwf0, h2, hsub⟩ := ht.letin_inv
    obtain ⟨Tp, hpre, hsubp⟩ := h1.value_inv hv
    have hext : (Θ ++ [Tp]).Extends Θ := Sto.extends_concat
    have hhlen := hh.1
    have hlknew := Sto.lookup_concat (Θ := Θ) (Tp := Tp)
    rw [hhlen] at hlknew
    have hwl := Path.Wf.var_free (Γ := (Ctx.empty : Ctx 0)) hlknew
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hlknew
    rw [Ty.fromClosed_zero] at hvf
    have hsl := Sub.trans hvf (hsubp.sto_weaken hext)
    refine ⟨Θ ++ [Tp], hext, ?_, T0,
      (h2.sto_weaken hext).open_weaken hwl hsl, hsub.sto_weaken hext⟩
    constructor
    · simp [hhlen]
    · intro ℓ Tl hl
      rcases List.getElem?_concat_inv hl with hold | ⟨hle, hTe⟩
      · obtain ⟨hTb, w, hwlk, hwb, hwpre⟩ := hh.2 hold
        exact ⟨hTb, w,
          (List.getElem?_concat_lt (List.getElem?_eq_some_iff.mp hwlk).1).trans hwlk,
          hwb, hwpre.sto_weaken hext⟩
      · subst hle
        subst hTe
        refine ⟨hpre.locsBelow, _, ?_, h1.locsBelow_tm, hpre.sto_weaken hext⟩
        show (_ ++ [_])[Θ.length]? = some _
        rw [hhlen]
        exact List.getElem?_concat_self
  | let_ctx hstep1 ih =>
    intro hh hok ht
    obtain ⟨S, T0, h1, hwf0, h2, hsub⟩ := ht.letin_inv
    obtain ⟨Θ', hext, hh', S', h1', hsubS⟩ := ih hh hok h1
    exact ⟨Θ', hext, hh', T0,
      .letin h1' (hwf0.sto_weaken hext)
        ((h2.sto_weaken hext).narrow hsubS),
      hsub.sto_weaken hext⟩
  | ascribe =>
    intro hh hok ht
    obtain ⟨h1, hsub⟩ := ht.typed_inv
    exact ⟨Θ, Sto.Extends.refl, hh, _, h1, hsub⟩

end LambdaP
