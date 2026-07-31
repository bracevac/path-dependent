import LambdaP.Soundness.PreservationPrep
import LambdaP.Soundness.Progress
import LambdaP.Soundness.Functionality
import LambdaP.Lemmas.Locs

/-!
Preservation: a step of a closed well-typed term is typed at a subtype in
an extended store typing. The subtype conclusion (rather than the exact
type) is what makes the beta case independent of syntactic functionality:
`repl` bridges the argument-path/argument-location gap, and narrowing
re-types let-contexts around stepped subterms.

V14: unconditional. The semantic store typing (`Ξ`/`SemStoOk`) that the
old statement threaded existed only to feed canonical forms; the live
`Sub.canonical_arrow` is store-anchored and needs no semantic tower, so
the parameter is gone. The three opening call-sites (β body, let-path
body, let-val body) are the ones the deviation-11 reversal (V14 step 1)
unblocked: their images are BARE LOCATIONS, which `SubstTyping.rooted`
made unsatisfiable.
-/

namespace LambdaP

/-! ### Preservation -/

/-- Preservation: a step of a closed well-typed term is typed at a subtype
in an extended store typing, and the extended store typing types the new
heap. -/
theorem preservation {Θ : Sto} {h h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (hcol : Sto.ResidueCollapse Θ) (hstep : Step h t h' t') :
    HeapTyped Θ h -> HasType Θ .empty t T ->
    ∃ Θ', Θ'.Extends Θ ∧ HeapTyped Θ' h' ∧
      ∃ T', HasType Θ' .empty t' T' ∧ Sub Θ' .empty (.ty T') (.ty T) := by
  induction hstep generalizing T with
  | apply hevf heva hlk =>
    intro hh ht
    obtain ⟨S, T1, h1, h2, hsub⟩ := ht.app_inv'
    obtain ⟨hwfp, hsubp⟩ := h1.path_inv rfl
    obtain ⟨ℓf', S0, T0', tb', hcf, hlkf, hwf0, hbody, hdom, hcod⟩ :=
      Sub.canonical_arrow hh hcol hsubp
    have hchf : Chains Θ _ _ :=
      hevf.to_chains hh (Sto.lookup_lt (hwfp.eval_target_lt hh hevf))
    cases Chains.deterministic hcf hchf
    have heqv := Option.some_inj.mp ((Eq.symm hlkf).trans hlk)
    injection heqv with _hs0 hT0 htb
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
    intro hh ht
    obtain ⟨hw, hsub⟩ := ht.path_inv rfl
    have hm := hw.eval_target_lt hh hev
    obtain ⟨Tm0, hlkm⟩ := Sto.lookup_lt hm
    exact ⟨Θ, Sto.Extends.refl, hh,
      _, .path (.var_free hlkm),
      .trans (.symm hw (hev.to_sub hh)) hsub⟩
  | let_path hev =>
    intro hh ht
    obtain ⟨S, T0, h1, hwf0, h2, hsub⟩ := ht.letin_inv
    obtain ⟨hwp, hsubp⟩ := h1.path_inv rfl
    have hm := hwp.eval_target_lt hh hev
    obtain ⟨Tm0, hlkm⟩ := Sto.lookup_lt hm
    have hwl : Path.Wf Θ .empty (.var (.free _)) := .var_free hlkm
    have hsl := Sub.trans (Sub.symm hwp (hev.to_sub hh)) hsubp
    exact ⟨Θ, Sto.Extends.refl, hh, T0, h2.open_weaken hwl hsl, hsub⟩
  | let_val hv =>
    intro hh ht
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
    intro hh ht
    obtain ⟨S, T0, h1, hwf0, h2, hsub⟩ := ht.letin_inv
    obtain ⟨Θ', hext, hh', S', h1', hsubS⟩ := ih hh h1
    exact ⟨Θ', hext, hh', T0,
      .letin h1' (hwf0.sto_weaken hext)
        ((h2.sto_weaken hext).narrow hsubS),
      hsub.sto_weaken hext⟩
  | ascribe =>
    intro hh ht
    obtain ⟨h1, hsub⟩ := ht.typed_inv
    exact ⟨Θ, Sto.Extends.refl, hh, _, h1, hsub⟩

end LambdaP
