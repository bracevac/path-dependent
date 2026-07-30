import LambdaP.Soundness.DOut
import LambdaP.Soundness.Pushback

namespace LambdaP

/-- Generic-target version of `CoChains` (the committed one is `Subst s 0`). -/
def CoChainsG (Θ : Sto) (σ1 σ2 : Subst s1 s2) : Prop :=
  ∀ (x : BVar s1) (m : Nat), Chains Θ (σ1.var x) m ↔ Chains Θ (σ2.var x) m

/-- Generic-target version of `Chains.subst_congr` (proof copied verbatim;
nothing in it depends on the target signature being 0). -/
theorem Chains.subst_congr' {Θ : Sto} {σ1 σ2 : Subst s1 s2}
    (hco : CoChainsG Θ σ1 σ2) :
    ∀ {p : Path s1} {m : Nat},
      Chains Θ (p.subst σ1) m -> Chains Θ (p.subst σ2) m := by
  intro p m he
  generalize hE : p.subst σ1 = r at he
  induction he generalizing p with
  | loc hl =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .loc hl)
    | .var (.free n), hE =>
      cases hE
      exact .loc hl
  | fst_tm he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_tm he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_tm (ih (p := p') rfl) hl
  | fst_ty he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_ty he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_ty (ih (p := p') rfl) hl
  | sel he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel he' hl)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel (ih (p := p') rfl) hl
  | sel_skip_tm hp hl hne hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_tm hp hl hne hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_tm (ihp (p := p') rfl) hl hne
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))
  | sel_skip_ty hp hl hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_ty hp hl hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_ty (ihp (p := p') rfl) hl
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))

theorem CoChainsG.of_iff {Θ : Sto} {q q' : Path s}
    (h : ∀ m, Chains Θ q m ↔ Chains Θ q' m) :
    CoChainsG Θ (Subst.openPath q) (Subst.openPath q') := by
  intro x m
  cases x with
  | here => exact h m
  | there b => exact Iff.rfl

/-- Mirror of `PEq.chains_iff` for `CoChain`. -/
theorem CoChain.chains_iff {s : Sig} {Θ : Sto} {Δ : Ctx s} {p q : Path s}
    (h : CoChain Θ Δ p q) : ∀ m, Chains Θ p m ↔ Chains Θ q m := by
  induction h with
  | refl => exact fun m => Iff.rfl
  | symm _ ih => exact fun m => (ih m).symm
  | trans _ _ ih1 ih2 => exact fun m => (ih1 m).trans (ih2 m)
  | cochain hp hq =>
    intro m
    constructor
    · intro hm; cases hm.deterministic hp; exact hq
    · intro hm; cases hm.deterministic hq; exact hp
  | skip_tm hp hl hne =>
    intro m
    constructor
    · intro hm
      cases hm with
      | sel hp' hl' =>
        cases hp'.deterministic hp
        have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
        injection heq with _ _ hab _
        exact absurd hab hne
      | sel_skip_tm _ _ _ hin => exact hin
      | sel_skip_ty hp' hl' _ =>
        cases hp'.deterministic hp
        cases Option.some_inj.mp ((Eq.symm hl').trans hl)
    · intro hm
      exact .sel_skip_tm hp hl hne hm
  | skip_ty hp hl =>
    intro m
    constructor
    · intro hm
      cases hm with
      | sel hp' hl' =>
        cases hp'.deterministic hp
        cases Option.some_inj.mp ((Eq.symm hl').trans hl)
      | sel_skip_tm hp' hl' _ _ =>
        cases hp'.deterministic hp
        cases Option.some_inj.mp ((Eq.symm hl').trans hl)
      | sel_skip_ty _ _ hin => exact hin
    · intro hm
      exact .sel_skip_ty hp hl hm
  | congr _ _ _ ih =>
    intro m
    constructor
    · exact Chains.subst_congr' (CoChainsG.of_iff ih)
    · exact Chains.subst_congr' (CoChainsG.of_iff (fun m => (ih m).symm))

/-- **Transfer 3**: at a store-resolved subject a `CoChain` collapses into
an `RtEq`.  Both endpoints then co-target (`CoChain.chains_iff`), so the
whole chain — skip hops included — is a single co-targeting hop, and the
`RtEq` transfer lemmas (`RtEq.to_sub`, `RtEq.wf_iff`) become available for
a `CoChain`-carried cell.  This is the only route from `CoChain` to
`RtEq`: `CoChain` on its own transfers neither wellformedness nor mutual
subtyping (see the `RtEq` doc comment in `DOut.lean`). -/
theorem CoChain.toRtEq {s : Sig} {Θ : Sto} {Δ : Ctx s} {p q : Path s} {m : Nat}
    (h : CoChain Θ Δ p q) (hc : Chains Θ p m) : RtEq Θ Δ p q :=
  .cochain hc ((h.chains_iff m).mp hc)

/-! ### Height-indexed copy of `DOut`.

Composition shrinks the left cell in some cases, the right cell in
others, and SWAPS the cells in the contravariant arrow-domain case
(`compose dom2 dom1` with `dom1 ⊂ d1`, `dom2 ⊂ d2`), so no nested
structural induction on the Prop cells terminates. Every `DOut`
constructor has at most one recursive field, so a height index
threads through with no max-merging, and compose runs by strong
induction on the height sum. -/
inductive DOutH (Θ : Sto) : {s : Sig} → Ctx s → Nat → Ty s → Ty s → Nat → Prop where
| refl {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} {k : Nat} :
    DOutH Θ Δ n T T k
| captured {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s} {T2 : Ty s} {k : Nat} :
    CapturedTok Θ Δ p →
    DOutH Θ Δ n (.single p) T2 k
/-- Mirror of `DOut.bound_tok`. -/
| bound_tok {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s} {T2 : Ty s} {k : Nat} :
    p.root.IsBound →
    DOutH Θ Δ n (.single p) T2 k
| bot_tok {s : Sig} {Δ : Ctx s} {n : Nat} {T1 T2 : Ty s} {k : Nat} :
    Sub Θ Δ (.ty T1) (.ty .bot) →
    DOutH Θ Δ n T1 T2 k
| botL {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} {k : Nat} :
    DOutH Θ Δ n .bot T k
| topR {s : Sig} {Δ : Ctx s} {n : Nat} {T : Ty s} {k : Nat} :
    DOutH Θ Δ n T .top k
| single {s : Sig} {Δ : Ctx s} {n : Nat} {p q : Path s} {k : Nat} :
    CoChain Θ Δ p q →
    DOutH Θ Δ n (.single p) (.single q) k
| co_subject {s : Sig} {Δ : Ctx s} {n : Nat} {p q : Path s} {Y : Ty s} {k : Nat} :
    CoChain Θ Δ p q →
    DOutH Θ Δ n (.single q) Y k →
    Sub Θ Δ (.ty (.single q)) (.ty Y) →
    DOutH Θ Δ n (.single p) Y (k+1)
| sngl_unfold {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s}
    {ℓ0 : Nat} {E : Ty 0} {X : Ty s} {k : Nat} :
    Chains Θ p ℓ0 →
    Sto.Lookup Θ ℓ0 E →
    ℓ0 < n →
    DOutH Θ Δ n (Ty.fromClosed E) X k →
    Sub Θ Δ (.ty (Ty.fromClosed E)) (.ty X) →
    DOutH Θ Δ n (.single p) X (k+1)
| fst_of_tm {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s} {S : Ty s}
    {a : Name} {T : Ty (s+1)} {Y : Ty s} {k1 k2 : Nat} :
    DOutH Θ Δ n (.single p) (.pairTm S a T) k1 →
    Sub Θ Δ (.ty (.single p)) (.ty (.pairTm S a T)) →
    DOutH Θ Δ n S Y k2 →
    Sub Θ Δ (.ty S) (.ty Y) →
    DOutH Θ Δ n (.single p.fst) Y (k1+k2+1)
| fst_of_ty {s : Sig} {Δ : Ctx s} {n : Nat} {p : Path s} {S : Ty s}
    {A : Name} {T1 T2 : Ty (s+1)} {Y : Ty s} {k1 k2 : Nat} :
    DOutH Θ Δ n (.single p) (.pairTy S A T1 T2) k1 →
    Sub Θ Δ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) →
    DOutH Θ Δ n S Y k2 →
    Sub Θ Δ (.ty S) (.ty Y) →
    DOutH Θ Δ n (.single p.fst) Y (k1+k2+1)
| tsel_r {s : Sig} {Δ : Ctx s} {n : Nat} {X : Ty s} {q : Path s}
    {mq ℓ1 : Nat} {A : Name} {W : Ty 0} {k : Nat} :
    Chains Θ q mq →
    Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
      (Ty.weaken W) (Ty.weaken W)) →
    mq < n →
    DOutH Θ Δ n X (Ty.fromClosed W) k →
    Sub Θ Δ (.ty X) (.ty (Ty.fromClosed W)) →
    DOutH Θ Δ n X (.tsel q A) (k+1)
| tsel_l {s : Sig} {Δ : Ctx s} {n : Nat} {Y : Ty s} {q : Path s}
    {mq ℓ1 : Nat} {A : Name} {W : Ty 0} {k : Nat} :
    Chains Θ q mq →
    Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
      (Ty.weaken W) (Ty.weaken W)) →
    mq < n →
    DOutH Θ Δ n (Ty.fromClosed W) Y k →
    Sub Θ Δ (.ty (Ty.fromClosed W)) (.ty Y) →
    DOutH Θ Δ n (.tsel q A) Y (k+1)
| tsel_co {s : Sig} {Δ : Ctx s} {n : Nat} {p q : Path s} {A : Name} {k : Nat} :
    CoChain Θ Δ p q →
    Path.Wf Θ Δ p →
    Path.Wf Θ Δ q →
    Sub Θ Δ (.ty (.single p)) (.ty (.single q)) →
    Sub Θ Δ (.ty (.single q)) (.ty (.single p)) →
    DOutH Θ Δ n (.tsel p A) (.tsel q A) k
| reapp_l {s : Sig} {Δ : Ctx s} {n : Nat} {q r : Path s}
    {S : Ty s} {A : Name} {T1 T2 : Ty (s+1)} {Y : Ty s} {k : Nat} :
    r.root.IsBound →
    q.root.IsBound →
    Path.Wf Θ Δ r →
    Path.Wf Θ Δ q →
    Sub Θ Δ (.ty (.single q)) (.ty (.single r)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.single q)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) →
    Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) →
    DOutH Θ Δ n (T2.open r.fst) Y k →
    Sub Θ Δ (.ty (T2.open r.fst)) (.ty Y) →
    DOutH Θ Δ n (.tsel q A) Y (k+1)
| reapp_r {s : Sig} {Δ : Ctx s} {n : Nat} {q r : Path s}
    {S : Ty s} {A : Name} {T1 T2 : Ty (s+1)} {X : Ty s} {k : Nat} :
    r.root.IsBound →
    q.root.IsBound →
    Path.Wf Θ Δ r →
    Path.Wf Θ Δ q →
    Sub Θ Δ (.ty (.single q)) (.ty (.single r)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.single q)) →
    Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) →
    Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) →
    DOutH Θ Δ n X (T1.open r.fst) k →
    Sub Θ Δ (.ty X) (.ty (T1.open r.fst)) →
    DOutH Θ Δ n X (.tsel q A) (k+1)
| sel_bridge {s : Sig} {Δ : Ctx s} {n : Nat} {X Y M1 M2 : Ty s}
    {q : Path s} {A : Name} {k1 k2 : Nat} :
    SelLoAnchor Θ Δ n q A M1 →
    SelHiAnchor Θ Δ n q A M2 →
    DOutH Θ Δ n X M1 k1 →
    Sub Θ Δ (.ty X) (.ty M1) →
    DOutH Θ Δ n M2 Y k2 →
    Sub Θ Δ (.ty M2) (.ty Y) →
    DOutH Θ Δ n X Y (k1+k2+1)
| repl_bridge {s : Sig} {Δ : Ctx s} {n : Nat} {X Y : Ty s} {T : Ty (s+1)}
    {p q : Path s} {k1 k2 : Nat} :
    RtEq Θ Δ p q →
    DOutH Θ Δ n X (T.open p) k1 →
    Sub Θ Δ (.ty X) (.ty (T.open p)) →
    DOutH Θ Δ n (T.open q) Y k2 →
    Sub Θ Δ (.ty (T.open q)) (.ty Y) →
    DOutH Θ Δ n X Y (k1+k2+1)
| arrow {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {T T' : Ty (s+1)} {k : Nat} :
    DOutH Θ Δ n S' S k →
    Sub Θ Δ (.ty S') (.ty S) →
    Sub Θ (Δ.push S') (.ty T) (.ty T') →
    DOutH Θ Δ n (.arrow S T) (.arrow S' T') (k+1)
| pair_tm {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {a : Name}
    {T T' : Ty (s+1)} {k : Nat} :
    DOutH Θ Δ n S S' k →
    Sub Θ Δ (.ty S) (.ty S') →
    Sub Θ (Δ.push S) (.ty T) (.ty T') →
    DOutH Θ Δ n (.pairTm S a T) (.pairTm S' a T') (k+1)
| pair_ty {s : Sig} {Δ : Ctx s} {n : Nat} {S S' : Ty s} {A : Name}
    {T1 T2 T1' T2' : Ty (s+1)} {k : Nat} :
    DOutH Θ Δ n S S' k →
    Sub Θ Δ (.ty S) (.ty S') →
    Sub Θ (Δ.push S) (.ty T1') (.ty T1) →
    Sub Θ (Δ.push S) (.ty T2) (.ty T2') →
    DOutH Θ Δ n (.pairTy S A T1 T2) (.pairTy S' A T1' T2') (k+1)

/-- Height erasure. -/
theorem DOutH.toDOut {s : Sig} {Θ : Sto} {Δ : Ctx s} {n : Nat} {T1 T2 : Ty s}
    {k : Nat} (h : DOutH Θ Δ n T1 T2 k) : DOut Θ Δ n T1 T2 := by
  induction h with
  | refl => exact .refl
  | captured hc => exact .captured hc
  | bound_tok hb => exact .bound_tok hb
  | bot_tok hb => exact .bot_tok hb
  | botL => exact .botL
  | topR => exact .topR
  | single hco => exact .single hco
  | co_subject hco _ l1 ih => exact .co_subject hco ih l1
  | sngl_unfold hc hE hm _ l1 ih => exact .sngl_unfold hc hE hm ih l1
  | fst_of_tm _ l1 _ l2 ih1 ih2 => exact .fst_of_tm ih1 l1 ih2 l2
  | fst_of_ty _ l1 _ l2 ih1 ih2 => exact .fst_of_ty ih1 l1 ih2 l2
  | tsel_r hc hE hm _ l1 ih => exact .tsel_r hc hE hm ih l1
  | tsel_l hc hE hm _ l1 ih => exact .tsel_l hc hE hm ih l1
  | tsel_co hco hwp hwq l1 l2 => exact .tsel_co hco hwp hwq l1 l2
  | reapp_l hrb hqb hwr hwq hlk hlk2 hev hgd _ l1 ih => exact .reapp_l hrb hqb hwr hwq hlk hlk2 hev hgd ih l1
  | reapp_r hrb hqb hwr hwq hlk hlk2 hev hgd _ l1 ih => exact .reapp_r hrb hqb hwr hwq hlk hlk2 hev hgd ih l1
  | sel_bridge lo hi _ l1 _ l2 ih1 ih2 => exact .sel_bridge lo hi ih1 l1 ih2 l2
  | repl_bridge hco _ l1 _ l2 ih1 ih2 => exact .repl_bridge hco ih1 l1 ih2 l2
  | arrow _ l1 l2 ih => exact .arrow ih l1 l2
  | pair_tm _ l1 l2 ih => exact .pair_tm ih l1 l2
  | pair_ty _ l1 l2 l3 ih => exact .pair_ty ih l1 l2 l3

/-- Height assignment. -/
theorem DOut.toH {s : Sig} {Θ : Sto} {Δ : Ctx s} {n : Nat} {T1 T2 : Ty s}
    (h : DOut Θ Δ n T1 T2) : ∃ k, DOutH Θ Δ n T1 T2 k := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | captured hc => exact ⟨0, .captured hc⟩
  | bound_tok hb => exact ⟨0, .bound_tok hb⟩
  | bot_tok hb => exact ⟨0, .bot_tok hb⟩
  | botL => exact ⟨0, .botL⟩
  | topR => exact ⟨0, .topR⟩
  | single hco => exact ⟨0, .single hco⟩
  | co_subject hco _ l1 ih => exact ⟨_, .co_subject hco ih.choose_spec l1⟩
  | sngl_unfold hc hE hm _ l1 ih => exact ⟨_, .sngl_unfold hc hE hm ih.choose_spec l1⟩
  | fst_of_tm _ l1 _ l2 ih1 ih2 =>
    exact ⟨_, .fst_of_tm ih1.choose_spec l1 ih2.choose_spec l2⟩
  | fst_of_ty _ l1 _ l2 ih1 ih2 =>
    exact ⟨_, .fst_of_ty ih1.choose_spec l1 ih2.choose_spec l2⟩
  | tsel_r hc hE hm _ l1 ih => exact ⟨_, .tsel_r hc hE hm ih.choose_spec l1⟩
  | tsel_l hc hE hm _ l1 ih => exact ⟨_, .tsel_l hc hE hm ih.choose_spec l1⟩
  | tsel_co hco hwp hwq l1 l2 => exact ⟨0, .tsel_co hco hwp hwq l1 l2⟩
  | reapp_l hrb hqb hwr hwq hlk hlk2 hev hgd _ l1 ih =>
    exact ⟨_, .reapp_l hrb hqb hwr hwq hlk hlk2 hev hgd ih.choose_spec l1⟩
  | reapp_r hrb hqb hwr hwq hlk hlk2 hev hgd _ l1 ih =>
    exact ⟨_, .reapp_r hrb hqb hwr hwq hlk hlk2 hev hgd ih.choose_spec l1⟩
  | sel_bridge lo hi _ l1 _ l2 ih1 ih2 =>
    exact ⟨_, .sel_bridge lo hi ih1.choose_spec l1 ih2.choose_spec l2⟩
  | repl_bridge hco _ l1 _ l2 ih1 ih2 =>
    exact ⟨_, .repl_bridge hco ih1.choose_spec l1 ih2.choose_spec l2⟩
  | arrow _ l1 l2 ih => exact ⟨_, .arrow ih.choose_spec l1 l2⟩
  | pair_tm _ l1 l2 ih => exact ⟨_, .pair_tm ih.choose_spec l1 l2⟩
  | pair_ty _ l1 l2 l3 ih => exact ⟨_, .pair_ty ih.choose_spec l1 l2 l3⟩

/-! The former `DOut.compose_tsel_gap` obstruction is resolved by the
strengthened table: corner (b) (`reapp ∘ tsel_co` either way) closes by
rebuilding the reapp cell at the co-chained subject — its `Path.Wf` is
now a `tsel_co` field, and the reverse mediator link composes with the
mutual legs; corner (a) (mixed or twin anchors at a `tsel q An` middle)
is hosted by the new `sel_bridge` cell, which carries both residue
cells verbatim. `sel_bridge` composes on either side by recursing into
the residue cell facing the other operand, so the strong induction
below stays well-founded (its height dominates both residues). -/

/-- The composition workhorse, by strong induction on the height sum. -/
theorem DOutH.compose {s : Sig} {Θ : Sto} {Δ : Ctx s} (hwf : Sto.Shaped Θ) {n : Nat} :
    ∀ (k : Nat) {A B C : Ty s} {h1 h2 : Nat}, h1 + h2 ≤ k →
    DOutH Θ Δ n A B h1 → DOutH Θ Δ n B C h2 →
    Sub Θ Δ (.ty A) (.ty B) → Sub Θ Δ (.ty B) (.ty C) → DOut Θ Δ n A C := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro A B C h1 h2 hk d1 d2 sAB sBC
  cases d1 with
  | refl => exact d2.toDOut
  | captured hc => exact .captured hc
  | bound_tok hb => exact .bound_tok hb
  | bot_tok hb => exact .bot_tok hb
  | botL => exact .botL
  | sel_bridge lo hi cellL lzL cellR lzR =>
    -- recurse the right residue against d2; the left side is verbatim
    exact .sel_bridge lo hi cellL.toDOut lzL
      (IH _ (by omega) (Nat.le_refl _) cellR d2 lzR sBC) (lzR.trans sBC)
  | repl_bridge hrt cellL lzL cellR lzR =>
    -- same shape as `sel_bridge`: the facing residue absorbs `d2`
    exact .repl_bridge hrt cellL.toDOut lzL
      (IH _ (by omega) (Nat.le_refl _) cellR d2 lzR sBC) (lzR.trans sBC)
  | topR =>
    -- B = ⊤; the only right cells with ⊤ subject: refl, bot_tok, topR,
    -- tsel_r, reapp_r
    cases d2 with
    | refl => exact .topR
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_r hcq hEq hmq res2 lazy2 =>
      exact .tsel_r hcq hEq hmq
        (IH _ (by omega) (Nat.le_refl _) (.topR (k := 0)) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.topR (k := 0)) res2 sAB lazy2)
        (sAB.trans lazy2)
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.topR (k := 0)) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.topR (k := 0)) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | single hco =>
    -- B = single q: the whole right cell moves under the co-chain hop.
    -- (Was a nine-way case split that re-anchored each right row across
    -- `CoChain.chains_iff`/`root_iff`; `co_subject` does it uniformly and
    -- is the one row a new right-hand cell shape can never break.)
    exact .co_subject hco d2.toDOut sBC
  | co_subject hco res1 lazy1 =>
    exact .co_subject hco
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | sngl_unfold hc hE hm res1 lazy1 =>
    exact .sngl_unfold hc hE hm
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | fst_of_tm ev lev res1 lazy1 =>
    exact .fst_of_tm ev.toDOut lev
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | fst_of_ty ev lev res1 lazy1 =>
    exact .fst_of_ty ev.toDOut lev
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | tsel_l hcq hEq hmq res1 lazy1 =>
    exact .tsel_l hcq hEq hmq
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | reapp_l hrb hqb hwr hwq hqr hrq hrp hgd res1 lazy1 =>
    exact .reapp_l hrb hqb hwr hwq hqr hrq hrp hgd
      (IH _ (by omega) (Nat.le_refl _) res1 d2 lazy1 sBC) (lazy1.trans sBC)
  | tsel_r hcq hEq hmq res1 lazy1 =>
    -- B = tsel q An, store-anchored on the left
    cases d2 with
    | refl => exact .tsel_r hcq hEq hmq res1.toDOut lazy1
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_l hcq2 hEq2 hm2 res2 lazy2 =>
      -- det-unify the two store anchors, recurse residue-vs-residue
      cases Chains.deterministic hcq2 hcq
      cases alias_unify hEq2 hEq
      exact IH _ (by omega) (Nat.le_refl _) res1 res2 lazy1 lazy2
    | tsel_co hco2 hwp2 hwq2 s1 s2 =>
      -- re-anchor the chains along the co-chain
      exact .tsel_r ((hco2.chains_iff _).mp hcq) hEq hmq res1.toDOut lazy1
    | tsel_r hcq3 hEq3 hm3 res2 lazy2 =>
      exact .tsel_r hcq3 hEq3 hm3
        (IH _ (by omega) (Nat.le_refl _) (.tsel_r hcq hEq hmq res1 lazy1)
          res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.tsel_r hcq hEq hmq res1 lazy1)
          res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_l hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      -- UNREACHABLE: the store anchor resolves `q`, the mediator anchor
      -- declares it bound-rooted (anchor dichotomy, see `SelLoAnchor`)
      exact absurd hqb hcq.root_not_bound
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.tsel_r hcq hEq hmq res1 lazy1)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.tsel_r hcq hEq hmq res1 lazy1)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1 lazy1 =>
    -- B = tsel q An, mediator-anchored on the left
    cases d2 with
    | refl => exact .reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1.toDOut lazy1
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_l hcq2 hEq2 hm2 res2 lazy2 =>
      -- UNREACHABLE (anchor dichotomy, mirror of the corner above)
      exact absurd hqb1 hcq2.root_not_bound
    | tsel_co hco2 hwp2 hwq2 s1' s2' =>
      -- rebuild the reapp cell at the co-chained subject: its Wf is
      -- carried by tsel_co; the mediator links compose with the
      -- mutual legs, and the anchor's root-boundness moves along the
      -- co-chain (`CoChain.root_iff`)
      exact .reapp_r hrb1 (hco2.root_iff.mp hqb1) hwr1 hwq2
        (s2'.trans hqr1) (hrq1.trans s1') hrp1 hgd1 res1.toDOut lazy1
    | tsel_r hcq3 hEq3 hm3 res2 lazy2 =>
      exact .tsel_r hcq3 hEq3 hm3
        (IH _ (by omega) (Nat.le_refl _)
          (.reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1 lazy1) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _)
          (.reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1 lazy1) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_l hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      -- two distinct mediators: bridge at the tsel middle
      exact .sel_bridge (.mediator hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1)
        (.mediator hrb hqb hwr hwq hqr hrq hrp hgd)
        res1.toDOut lazy1 res2.toDOut lazy2
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _)
          (.reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1 lazy1)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _)
          (.reapp_r hrb1 hqb1 hwr1 hwq1 hqr1 hrq1 hrp1 hgd1 res1 lazy1)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | tsel_co hco hwp hwq s1 s2 =>
    -- A = tsel p An, B = tsel q An, co-chained subjects
    cases d2 with
    | refl => exact .tsel_co hco hwp hwq s1 s2
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_l hcq2 hEq2 hm2 res2 lazy2 =>
      -- re-anchor the chains along the co-chain
      exact .tsel_l ((hco.chains_iff _).mpr hcq2) hEq2 hm2 res2.toDOut lazy2
    | tsel_co hco2 hwp2 hwq2 s1' s2' =>
      exact .tsel_co (hco.trans hco2) hwp hwq2 (s1.trans s1') (s2'.trans s2)
    | tsel_r hcq3 hEq3 hm3 res2 lazy2 =>
      exact .tsel_r hcq3 hEq3 hm3
        (IH _ (by omega) (Nat.le_refl _) (.tsel_co (k := 0) hco hwp hwq s1 s2)
          res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq2 hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq2 hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.tsel_co (k := 0) hco hwp hwq s1 s2)
          res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_l hrb hqb hwr hwq2 hqr hrq hrp hgd res2 lazy2 =>
      -- rebuild the reapp cell at the co-chained subject: its Wf is
      -- carried by tsel_co; the mediator links compose with the
      -- mutual legs
      exact .reapp_l hrb (hco.root_iff.mpr hqb) hwr hwp (s1.trans hqr)
        (hrq.trans s2) hrp hgd res2.toDOut lazy2
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.tsel_co (k := 0) hco hwp hwq s1 s2)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.tsel_co (k := 0) hco hwp hwq s1 s2)
          cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | arrow dom1 l1 l2 =>
    -- B = arrow S' T'
    cases d2 with
    | refl => exact .arrow dom1.toDOut l1 l2
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_r hcq hEq hmq res2 lazy2 =>
      exact .tsel_r hcq hEq hmq
        (IH _ (by omega) (Nat.le_refl _) (.arrow dom1 l1 l2) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.arrow dom1 l1 l2) res2 sAB lazy2)
        (sAB.trans lazy2)
    | arrow dom2 l1' l2' =>
      -- contravariant domain: compose dom2 (⊂ d2) with dom1 (⊂ d1)
      exact .arrow (IH _ (by omega) (Nat.le_refl _) dom2 dom1 l1' l1)
        (l1'.trans l1) ((l2.narrow l1').trans l2')
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.arrow dom1 l1 l2) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.arrow dom1 l1 l2) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | pair_tm dom1 l1 l2 =>
    -- B = pairTm S' a T'
    cases d2 with
    | refl => exact .pair_tm dom1.toDOut l1 l2
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_r hcq hEq hmq res2 lazy2 =>
      exact .tsel_r hcq hEq hmq
        (IH _ (by omega) (Nat.le_refl _) (.pair_tm dom1 l1 l2) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.pair_tm dom1 l1 l2) res2 sAB lazy2)
        (sAB.trans lazy2)
    | pair_tm dom2 l1' l2' =>
      exact .pair_tm (IH _ (by omega) (Nat.le_refl _) dom1 dom2 l1 l1')
        (l1.trans l1') (l2.trans (l2'.narrow l1))
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.pair_tm dom1 l1 l2) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.pair_tm dom1 l1 l2) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
  | pair_ty dom1 l1 lo1 hi1 =>
    -- B = pairTy S' A T1' T2'
    cases d2 with
    | refl => exact .pair_ty dom1.toDOut l1 lo1 hi1
    | bot_tok hb => exact .bot_tok (sAB.trans hb)
    | topR => exact .topR
    | tsel_r hcq hEq hmq res2 lazy2 =>
      exact .tsel_r hcq hEq hmq
        (IH _ (by omega) (Nat.le_refl _) (.pair_ty dom1 l1 lo1 hi1) res2 sAB lazy2)
        (sAB.trans lazy2)
    | reapp_r hrb hqb hwr hwq hqr hrq hrp hgd res2 lazy2 =>
      exact .reapp_r hrb hqb hwr hwq hqr hrq hrp hgd
        (IH _ (by omega) (Nat.le_refl _) (.pair_ty dom1 l1 lo1 hi1) res2 sAB lazy2)
        (sAB.trans lazy2)
    | pair_ty dom2 l1' lo2 hi2 =>
      exact .pair_ty (IH _ (by omega) (Nat.le_refl _) dom1 dom2 l1 l1')
        (l1.trans l1') ((lo2.narrow l1).trans lo1) (hi1.trans (hi2.narrow l1))
    | sel_bridge lo hi cellL lzL cellR lzR =>
      exact .sel_bridge lo hi
        (IH _ (by omega) (Nat.le_refl _) (.pair_ty dom1 l1 lo1 hi1) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR
    | repl_bridge hrt cellL lzL cellR lzR =>
      exact .repl_bridge hrt
        (IH _ (by omega) (Nat.le_refl _) (.pair_ty dom1 l1 lo1 hi1) cellL sAB lzL)
        (sAB.trans lzL) cellR.toDOut lzR

theorem DOut.compose {s : Sig} {Θ : Sto} {Δ : Ctx s} (hwf : Sto.Shaped Θ) {n : Nat} :
    ∀ {A B C : Ty s}, DOut Θ Δ n A B → DOut Θ Δ n B C →
    Sub Θ Δ (.ty A) (.ty B) → Sub Θ Δ (.ty B) (.ty C) → DOut Θ Δ n A C := by
  intro A B C d1 d2 sAB sBC
  obtain ⟨h1, dh1⟩ := d1.toH
  obtain ⟨h2, dh2⟩ := d2.toH
  exact DOutH.compose hwf (h1 + h2) (Nat.le_refl _) dh1 dh2 sAB sBC

end LambdaP
