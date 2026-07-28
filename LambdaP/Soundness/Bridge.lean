import LambdaP.Soundness.PT

/-!
The bridge between the two runtime interpretations, conditional on the
one conserved obligation. `InvSubClosure` — runtime possible types are
closed under general subtyping at the empty context — is the sharpest
form of the open problem (it subsumes the roles of `SemStoExists`).
Under it: the inductive interpretation embeds into the functional one
(`PT.of_inv`), and every location inhabits its recorded type
(`PT.precise`).
-/

namespace LambdaP

/-- The conserved obligation: runtime possible types are closed under
general subtyping. -/
def InvSubClosure : Prop :=
  ∀ (Θ : Sto) (h : Heap), HeapTyped Θ h ->
    ∀ {U1 U2 : Ty 0} {ℓ : Nat},
      Sub Θ .empty (.ty U1) (.ty U2) -> Inv Θ ℓ U1 -> Inv Θ ℓ U2

/-- Component locations of a precise entry are themselves recorded. -/
theorem HeapTyped.entry_lt {Θ : Sto} {h : Heap} {ℓ ℓc : Nat} {T : Ty 0}
    (_hh : HeapTyped Θ h) (hl : Sto.Lookup Θ ℓ T) (hc : ℓc < ℓ) :
    ∃ Tc, Sto.Lookup Θ ℓc Tc :=
  Sto.lookup_lt (Nat.lt_trans hc (List.getElem?_eq_some_iff.mp hl).1)

/-- Bridge (mpr): under closure, inductive possible types embed into
the functional interpretation. -/
theorem PT.of_inv {Θ : Sto} {h : Heap}
    (hcl : InvSubClosure) (hh : HeapTyped Θ h) :
    ∀ (sz : Nat) (W : Ty 0), W.structSize ≤ sz ->
    ∀ {y : Nat}, Inv Θ y W -> PT Θ W y := by
  intro sz
  induction sz with
  | zero =>
    intro W hsz y hi
    match W with
    | .top => simp [PT]
    | .bot => exact absurd hi (fun hi => Inv.bot_elim hh hi)
    | .single q => simpa [PT] using Inv.single_inv hh hi
    | .tsel q A =>
      obtain ⟨m, ℓ1, W', hc, hl, hiW⟩ := Inv.tsel_inv hh hi
      simp only [PT]
      exact ⟨m, ℓ1, W', hc, hl, hiW⟩
    | .arrow S T => simp [Ty.structSize] at hsz
    | .pairTm S a T => simp [Ty.structSize] at hsz
    | .pairTy S A T1 T2 => simp [Ty.structSize] at hsz
  | succ sz ih =>
    intro W hsz y hi
    match W with
    | .top => simp [PT]
    | .bot => exact absurd hi (fun hi => Inv.bot_elim hh hi)
    | .single q => simpa [PT] using Inv.single_inv hh hi
    | .tsel q A =>
      obtain ⟨m, ℓ1, W', hc, hl, hiW⟩ := Inv.tsel_inv hh hi
      simp only [PT]
      exact ⟨m, ℓ1, W', hc, hl, hiW⟩
    | .arrow S T =>
      obtain ⟨T0, T1, hl, hdom, hcod⟩ := Inv.arrow_inv hh hi
      simp only [PT]
      exact ⟨T0, T1, hl, hdom.to_sub, hcod⟩
    | .pairTm S a T =>
      simp only [Ty.structSize] at hsz
      obtain ⟨ℓ1, ℓ2, hl, hs1, hmem⟩ := Inv.pairTm_inv hh hi
      have hb := (hh.2 hl).1
      obtain ⟨T1c, hl1⟩ := hh.entry_lt hl hb.1
      obtain ⟨T2c, hl2⟩ := hh.entry_lt hl (Ty.locsBelow_rename.mp hb.2)
      simp only [PT]
      refine ⟨ℓ1, ℓ2, hl, hs1.to_sub, ?_, ?_⟩
      · exact ih S (by omega)
          (hcl Θ h hh hs1.to_sub (.sngl (.loc hl1)))
      · intro q' hq'
        have hres := hmem.subst (SubstTyping.openPath hq'.wf hq'.to_sub)
        simp only [Tau.subst] at hres
        have we : (Ty.single (.var (.free ℓ2))).weaken.subst (Subst.openPath q')
            = Ty.single (.var (.free ℓ2)) := Ty.weaken_open
        rw [we] at hres
        have hi2 : Inv Θ ℓ2 (Ty.open T q') :=
          hcl Θ h hh hres (.sngl (.loc hl2))
        exact ih _ (by simp; omega) hi2
    | .pairTy S A T1 T2 =>
      simp only [Ty.structSize] at hsz
      obtain ⟨ℓ1, W', hl, hs1, hlo, hhi⟩ := Inv.pairTy_inv hh hi
      have hb := (hh.2 hl).1
      obtain ⟨T1c, hl1⟩ := hh.entry_lt hl hb.1
      simp only [PT]
      refine ⟨ℓ1, W', hl, hs1.to_sub, ?_, ?_⟩
      · exact ih S (by omega)
          (hcl Θ h hh hs1.to_sub (.sngl (.loc hl1)))
      · intro q' hq'
        have wlo := hlo.subst (SubstTyping.openPath hq'.wf hq'.to_sub)
        have whi := hhi.subst (SubstTyping.openPath hq'.wf hq'.to_sub)
        simp only [Tau.subst] at wlo whi
        have we : W'.weaken.subst (Subst.openPath q') = W' := Ty.weaken_open
        rw [we] at wlo whi
        constructor
        · intro z hz
          exact hcl Θ h hh wlo hz
        · intro z hz
          exact ih _ (by simp; omega) (hcl Θ h hh whi hz)

/-- Every location inhabits its recorded type (conditional precise
inhabitation; the alias fields make the lower direction the identity
and defer the upper to the bridge). -/
theorem PT.precise {Θ : Sto} {h : Heap}
    (hcl : InvSubClosure) (hh : HeapTyped Θ h)
    {ℓ : Nat} {T : Ty 0} (hl : Sto.Lookup Θ ℓ T) : PT Θ T ℓ := by
  rcases hh.lookup_shape hl with ⟨S, B, rfl⟩ | ⟨ℓ1, a, ℓ2, rfl⟩ | ⟨ℓ1, A, W, rfl⟩
  · simp only [PT]
    exact ⟨S, B, hl, .refl, .refl⟩
  · have hb := (hh.2 hl).1
    obtain ⟨T1c, hl1⟩ := hh.entry_lt hl hb.1
    obtain ⟨T2c, hl2⟩ := hh.entry_lt hl (Ty.locsBelow_rename.mp hb.2)
    simp only [PT]
    refine ⟨ℓ1, ℓ2, hl, .refl, .loc hl1, ?_⟩
    intro q' hq'
    show PT Θ (Ty.open (Ty.single (.var (.free ℓ2))).weaken q') ℓ2
    rw [Ty.weaken_open]
    unfold PT
    exact .loc hl2
  · have hb := (hh.2 hl).1
    obtain ⟨T1c, hl1⟩ := hh.entry_lt hl hb.1
    simp only [PT]
    refine ⟨ℓ1, W, hl, .refl, .loc hl1, ?_⟩
    intro q' hq'
    constructor
    · intro z hz
      show Inv Θ z W
      rw [Ty.weaken_open] at hz
      exact hz
    · intro z hz
      show PT Θ (Ty.open W.weaken q') z
      rw [Ty.weaken_open]
      exact PT.of_inv hcl hh W.structSize W (Nat.le_refl _) hz

end LambdaP
