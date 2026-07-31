import LambdaP.Soundness.Embedding

/-! THE EMBEDDING GAP (V11 probe p1 + the V12 refutation,
machine-checked, sorry-free).

The last section of this file (§V12) refutes the V12 repair — the sized
instantiation leg on `SSub`'s congruence rows — by showing its production
obligation IS the `EmbPower` oracle stated here. See NOTES.md, "V12
EXECUTION REPORT".

What `Sub.to_ssub` would owe if the five evidence rules
(`sel_tm`/`sel_hi`/`sel_lo`/`skip_tm`/`skip_ty`) lost their
`p.root.IsBound` premises — the deletion that makes the realized
substitution lemma a standard structural induction (V9/V10 refuted every
other repair). Today those premises make the five cases VACUOUS at scope
0 (`Path.root_not_isBound_zero`); without them the cases must be proved,
and this file states them as five standalone obligations. It compiles
against the UNMODIFIED tree: the two powers are hypotheses.

* `SubstPower` is what the deletion BUYS: `Sub.subst` at the
  `SubstTyping.openPath` instance with a LOCATION-rooted image (today
  `SubstTyping.openPath` demands `q.root.IsBound`; after the deletion the
  `rooted` field of `SubstTyping` goes away and this is a one-liner).
* `EmbPower` is `Sub.to_ssub` ITSELF — an oracle. Any case needing it is
  CIRCULAR.

VERDICT: `case_skip_tm`/`case_skip_ty` close with NEITHER power.
`case_sel_tm`/`case_sel_hi`/`case_sel_lo` need BOTH, and
`sel_hi_forces_residue` shows the oracle's output is not one route among
many but the only one: the missing fact is the instantiation of the
`pairTm`/`pairTy` row's SECOND component, which `SSub` (and `SOut`) carry
as a RAW `Sub` leg at a pushed context. Instantiating it (`SubstPower`)
lands in `Sub`; re-entering `SSub` is `to_ssub` at a store-extracted
derivation that is neither a subderivation, nor `SSub`-fuel-bounded, nor
anchor-location-bounded. See NOTES.md, "V11 EXECUTION REPORT". -/

namespace LambdaP
namespace EmbedGap

/-- What deleting the premises buys: realized opening of a pushed-context
leg by a resolving path. -/
def SubstPower (Θ : Sto) : Prop :=
  ∀ {S0 : Ty 0} {A B : Ty 1} {q : Path 0},
    Path.Wf Θ .empty q -> Sub Θ .empty (.ty (.single q)) (.ty S0) ->
    Sub Θ (Ctx.empty.push S0) (.ty A) (.ty B) ->
    Sub Θ .empty (.ty (A.open q)) (.ty (B.open q))

/-- The ORACLE: `Sub.to_ssub` itself. -/
def EmbPower (Θ : Sto) : Prop :=
  ∀ {X Y : Ty 0}, Sub Θ .empty (.ty X) (.ty Y) -> ∃ n, SSub Θ X Y n

/-! ### SSub-level anchors (`Sub.single_pair*_anchor` with the `Sub`
premise replaced by its `SSub` image: no `to_ssub`, hence no
circularity — `SSub.invert` is propext-only). -/

theorem ssub_pairTm_anchor {Θ : Sto} {p : Path 0} {S : Ty 0} {a : Name}
    {T : Ty 1} {n : Nat} (hwf : Sto.Shaped Θ)
    (h : SSub Θ (.single p) (.pairTm S a T) n) :
    ∃ ℓ0 ℓ1 ℓ2, Chains Θ p ℓ0 ∧
      Sto.Lookup Θ ℓ0 (.pairTm (.single (.var (.free ℓ1))) a
        (Ty.single (.var (.free ℓ2))).weaken) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty (Ty.single (.var (.free ℓ2))).weaken) (.ty T) := by
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hres⟩ := SSub.invert hwf n h
  have oE := SSub.invert hwf m hres
  rcases (hwf hE0).1 with hs | hs | hs
  · exact (oE : False).elim
  · obtain ⟨hba, -, res⟩ := oE
    subst hba
    exact ⟨ℓ0, _, _, hcp, hE0, res⟩
  · exact (oE : False).elim

theorem ssub_pairTy_anchor {Θ : Sto} {p : Path 0} {S : Ty 0} {A : Name}
    {T1 T2 : Ty 1} {n : Nat} (hwf : Sto.Shaped Θ)
    (h : SSub Θ (.single p) (.pairTy S A T1 T2) n) :
    ∃ ℓ0 ℓ1 W, Chains Θ p ℓ0 ∧
      Sto.Lookup Θ ℓ0 (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty T1) (.ty (Ty.weaken W)) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty (Ty.weaken W)) (.ty T2) := by
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hres⟩ := SSub.invert hwf n h
  have oE := SSub.invert hwf m hres
  rcases (hwf hE0).1 with hs | hs | hs
  · exact (oE : False).elim
  · exact (oE : False).elim
  · obtain ⟨hBA, -, lo, hi⟩ := oE
    subst hBA
    exact ⟨ℓ0, _, _, hcp, hE0, lo, hi⟩

/-! ### (p1.4) skip_tm — CLOSES, no oracle. -/

theorem case_skip_tm {Θ : Sto} {p : Path 0} {S : Ty 0} {a b : Name}
    {T : Ty 1} (hwf : Sto.Shaped Θ) (_hwp : Path.Wf Θ .empty p) (hne : a ≠ b)
    (ih : ∃ n, SSub Θ (.single p) (.pairTm S b T) n) :
    ∃ n, SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) n := by
  obtain ⟨n, hs⟩ := ih
  obtain ⟨ℓ0, ℓ1, ℓ2, hcp, hE0, -⟩ := ssub_pairTm_anchor hwf hs
  exact ⟨1, .skip_tm_loc hcp hE0 hne⟩

/-! ### (p1.5) skip_ty — CLOSES, no oracle. -/

theorem case_skip_ty {Θ : Sto} {p : Path 0} {S : Ty 0} {a B : Name}
    {T1 T2 : Ty 1} (hwf : Sto.Shaped Θ) (_hwp : Path.Wf Θ .empty p)
    (ih : ∃ n, SSub Θ (.single p) (.pairTy S B T1 T2) n) :
    ∃ n, SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) n := by
  obtain ⟨n, hs⟩ := ih
  obtain ⟨ℓ0, ℓ1, W, hcp, hE0, -, -⟩ := ssub_pairTy_anchor hwf hs
  exact ⟨1, .skip_ty_loc hcp hE0⟩

/-! ### (p1.1) sel_tm — needs BOTH powers, one of which is the oracle. -/

theorem case_sel_tm {Θ : Sto} {p : Path 0} {S : Ty 0} {a : Name} {T : Ty 1}
    (hwf : Sto.Shaped Θ) (hsp : SubstPower Θ) (hemb : EmbPower Θ)
    (_hwp : Path.Wf Θ .empty p)
    (ih : ∃ n, SSub Θ (.single p) (.pairTm S a T) n) :
    ∃ n, SSub Θ (.single (p.sel a)) (T.open p.fst) n := by
  obtain ⟨n, hs⟩ := ih
  obtain ⟨ℓ0, ℓ1, ℓ2, hcp, hE0, hres⟩ := ssub_pairTm_anchor hwf hs
  have hcf : Chains Θ p.fst ℓ1 := .fst_tm hcp hE0
  have hwq : Path.Wf Θ .empty p.fst := hcf.wf
  have hq : Sub Θ .empty (.ty (.single p.fst))
      (.ty (.single (.var (.free ℓ1)))) := hcf.to_sub
  have hop := hsp hwq hq hres
  rw [Ty.weaken_open] at hop
  obtain ⟨k, hk⟩ := hemb hop
  exact ⟨k + 2, .trans (n := k+1) (.sel_tm_loc hcp hE0) (hk.mono (Nat.le_succ k))⟩

/-! ### (p1.2) sel_hi — same. -/

theorem case_sel_hi {Θ : Sto} {p : Path 0} {S : Ty 0} {A : Name} {T1 T2 : Ty 1}
    (hwf : Sto.Shaped Θ) (hsp : SubstPower Θ) (hemb : EmbPower Θ)
    (_hwp : Path.Wf Θ .empty p)
    (ih : ∃ n, SSub Θ (.single p) (.pairTy S A T1 T2) n)
    (_hgd : Sub Θ .empty (.ty (T1.open p.fst)) (.ty (T2.open p.fst))) :
    ∃ n, SSub Θ (.tsel p A) (T2.open p.fst) n := by
  obtain ⟨n, hs⟩ := ih
  obtain ⟨ℓ0, ℓ1, W, hcp, hE0, -, hhi⟩ := ssub_pairTy_anchor hwf hs
  have hcf : Chains Θ p.fst ℓ1 := .fst_ty hcp hE0
  have hwq : Path.Wf Θ .empty p.fst := hcf.wf
  have hq : Sub Θ .empty (.ty (.single p.fst))
      (.ty (.single (.var (.free ℓ1)))) := hcf.to_sub
  have hop := hsp hwq hq hhi
  rw [Ty.weaken_open] at hop
  obtain ⟨k, hk⟩ := hemb hop
  rw [← Ty.fromClosed_zero (T := W)] at hk
  exact ⟨k + 1, .sel_hi_loc hcp hE0 hk⟩

/-! ### (p1.3) sel_lo — same. -/

theorem case_sel_lo {Θ : Sto} {p : Path 0} {S : Ty 0} {A : Name} {T1 T2 : Ty 1}
    (hwf : Sto.Shaped Θ) (hsp : SubstPower Θ) (hemb : EmbPower Θ)
    (_hwp : Path.Wf Θ .empty p)
    (ih : ∃ n, SSub Θ (.single p) (.pairTy S A T1 T2) n)
    (_hgd : Sub Θ .empty (.ty (T1.open p.fst)) (.ty (T2.open p.fst))) :
    ∃ n, SSub Θ (T1.open p.fst) (.tsel p A) n := by
  obtain ⟨n, hs⟩ := ih
  obtain ⟨ℓ0, ℓ1, W, hcp, hE0, hlo, -⟩ := ssub_pairTy_anchor hwf hs
  have hcf : Chains Θ p.fst ℓ1 := .fst_ty hcp hE0
  have hwq : Path.Wf Θ .empty p.fst := hcf.wf
  have hq : Sub Θ .empty (.ty (.single p.fst))
      (.ty (.single (.var (.free ℓ1)))) := hcf.to_sub
  have hop := hsp hwq hq hlo
  rw [Ty.weaken_open] at hop
  obtain ⟨k, hk⟩ := hemb hop
  rw [← Ty.fromClosed_zero (T := W)] at hk
  exact ⟨k + 1, .sel_lo_loc hcp hE0 hk⟩

/-! ### The oracle is NECESSARY, not merely convenient.

For `sel_hi` the instantiated residue is not one route among many: at any
target that is neither `⊤` nor a type selection, EVERY `SSub` proof of
the conclusion `p.A <: U` hands back exactly the fact the oracle was used
to produce, namely `SSub Θ W U m` for the STORED alias `W` of `p.A`. So
the case cannot be closed without converting the (instantiated) store
residue `W <: T2.open p.fst` into `SSub` — and its only source is the raw
`Sub` leg of the `pairTy` row. -/

theorem sel_hi_forces_residue {Θ : Sto} (hwf : Sto.Shaped Θ) {p : Path 0}
    {A : Name} {U : Ty 0} {n : Nat} (h : SSub Θ (.tsel p A) U n)
    (hU1 : ∀ (q : Path 0) (B : Name), U ≠ .tsel q B) (hU2 : U ≠ .top) :
    ∃ mq ℓ1 W, Chains Θ p mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ W U m := by
  have o := SSub.invert hwf n h
  cases U with
  | top => exact absurd rfl hU2
  | tsel q B => exact absurd rfl (hU1 q B)
  | bot | single _ | arrow _ _ | pairTm _ _ _ | pairTy _ _ _ _ =>
    simp only [SOut] at o
    rcases o with ⟨p2, hX, -⟩ | hgood | ⟨p2, A2, mq, ℓ1, W, hX, -⟩
    · exact absurd hX (by intro hh; cases hh)
    · exact hgood
    · exact absurd hX (by intro hh; cases hh)

/-! ### (V12) THE SIZED INSTANTIATION LEG IS THE ORACLE IN DISGUISE.

V12 (§4 of the V11 report) proposes to break the circle by giving the
three congruence rows of `SSub` a SECOND, SIZED leg: the pushed-context
component, pre-instantiated at every conforming opener.

    | pair_tm : SSub Θ S S' n -> Sub Θ (∅ ▸ S) (.ty T) (.ty T') ->
        OpenLeg Θ S T T' n -> SSub Θ (.pairTm S a T) (.pairTm S' a T') (n+1)

Two KERNEL facts fix the leg's shape (probed; the messages are quoted in
NOTES.md, "V12 EXECUTION REPORT"):
* the conformance hypothesis may NOT be `∃ m, SSub Θ (.single q) S m` —
  that is a non-positive occurrence of the datatype being declared. It
  must be a judgment that exists BEFORE `SSub`, i.e. `Sub`.
* the leg's conclusion may NOT be `∃ m, SSub Θ … m` (nested `Exists`
  whose parameters contain local variables), so the leg's fuel is
  UNIFORM in `q`.

The rest of this section shows that the proposal does not break the
circle, it MOVES it: producing the legs — even pointwise, even with the
fuel existentially quantified per opener, which is WEAKER than what the
rows demand — is exactly `EmbPower`. -/

/-- The V12 leg, standalone (V12 puts it inside the three rows). -/
def OpenLeg (Θ : Sto) (S : Ty 0) (T T' : Ty 1) (n : Nat) : Prop :=
  ∀ q : Path 0, (∃ ℓ, Chains Θ q ℓ) ->
    Sub Θ .empty (.ty (.single q)) (.ty S) ->
    SSub Θ (T.open q) (T'.open q) n

/-- The obligation `Sub.to_ssub` acquires at `pair_tm`/`arrow`/`pair_ty`
once the rows carry a leg, WEAKENED to a per-opener fuel (the rows
really demand the uniform-fuel `∃ n, OpenLeg Θ S T T' n`). The second
premise of those rules is an arbitrary derivation at the pushed
context, so this quantifies over all of them. -/
def LegPower (Θ : Sto) : Prop :=
  ∀ {S : Ty 0} {T T' : Ty 1},
    Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
    ∀ q : Path 0, (∃ ℓ, Chains Θ q ℓ) ->
      Sub Θ .empty (.ty (.single q)) (.ty S) ->
      ∃ n, SSub Θ (T.open q) (T'.open q) n

/-- (V12.1) THE LEAF WITNESS: instantiate the obligation at the
`var_bound` LEAF — `Sub Θ (∅ ▸ S) ⌊0⌋ S.weaken`, whose opening at `q` is
`⌊q⌋ <: S`. The leg for that row IS the oracle for resolving singleton
subjects, and there is no induction hypothesis at a leaf: the leg's own
conformance hypothesis is the only input. This is the `Sub`-vs-`SSub`
conversion that `Realized` needs at `var_bound`. -/
theorem legpower_forces_singleton_oracle {Θ : Sto} (hleg : LegPower Θ)
    {q : Path 0} {S : Ty 0} (hq : ∃ ℓ, Chains Θ q ℓ)
    (hc : Sub Θ .empty (.ty (.single q)) (.ty S)) :
    ∃ n, SSub Θ (.single q) S n := by
  have hleaf : Sub Θ (Ctx.empty.push S)
      (.ty (.single (.var (.bound .here)))) (.ty S.weaken) := .var_bound .here
  have h := hleg hleaf q hq hc
  rw [Ty.weaken_open] at h
  exact h

/-- (V12.2) At any non-empty store the obligation is the FULL oracle:
weaken a closed derivation under the binder of a `⊤`-domain row and read
the leg back at any stored location. -/
theorem legpower_forces_oracle {Θ : Sto} {ℓ0 : Nat} {E : Ty 0}
    (hl : Sto.Lookup Θ ℓ0 E) (hleg : LegPower Θ) : EmbPower Θ := by
  intro X Y h
  have hleaf : Sub Θ (Ctx.empty.push .top) (.ty X.weaken) (.ty Y.weaken) :=
    h.weaken (S := .top)
  obtain ⟨n, hn⟩ := hleg hleaf (.var (.free ℓ0)) ⟨ℓ0, .loc hl⟩ .top
  rw [Ty.weaken_open, Ty.weaken_open] at hn
  exact ⟨n, hn⟩

/-- (V12.3) The converse, so the equivalence is exact: with the two V11
powers the pointwise leg is provable. `LegPower ↔ EmbPower` (modulo
`SubstPower`, which the premise deletion buys) — V12 relocates the
oracle from the five evidence cases to the `var_bound` leaf, and buys
nothing. -/
theorem oracle_gives_legpower {Θ : Sto} (hsp : SubstPower Θ)
    (hemb : EmbPower Θ) : LegPower Θ := by
  intro S T T' h q hq hc
  obtain ⟨ℓ, hch⟩ := hq
  exact hemb (hsp hch.wf hc h)

end EmbedGap
end LambdaP

section
open LambdaP.EmbedGap
#print axioms LambdaP.EmbedGap.case_skip_tm
#print axioms LambdaP.EmbedGap.case_skip_ty
#print axioms LambdaP.EmbedGap.case_sel_tm
#print axioms LambdaP.EmbedGap.case_sel_hi
#print axioms LambdaP.EmbedGap.case_sel_lo
#print axioms LambdaP.EmbedGap.sel_hi_forces_residue
#print axioms LambdaP.EmbedGap.legpower_forces_singleton_oracle
#print axioms LambdaP.EmbedGap.legpower_forces_oracle
#print axioms LambdaP.EmbedGap.oracle_gives_legpower
end
