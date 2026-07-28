import LambdaP.Soundness.Store

/-!
The trans-free runtime subtyping pipeline (deviation 9 endgame):

1. `SSub`: `Sub` at the empty context with a derivation-size index
   (minidot's `stp`). Structural premises are sized (the pushback
   recursion walks them); congruence premises and wellformedness stay
   at the general judgment (lazy). At scope 0 the evidence-shaped
   selection rules of `Sub` are vacuous — `Var 0` has no bound
   variables — so runtime derivations are forced through the
   store-anchored rules, which is what makes this complete for
   `Sub Θ ∅` and invertible after pushback.
-/

namespace LambdaP


/-! ### Store-shape prerequisites (review finding F1)

Pushback and the trans-free inversion lemmas are false over an
unconstrained store typing (countermodel: a `⊥` entry lets `unfold`
conclude anything). The syntactic shape invariant below is exactly the
image of `Val.PreciseTy`, so it is discharged from `HeapTyped` at every
use site and end-to-end safety stays unconditional. -/

/-- The shapes a precise store entry can take. -/
inductive Sto.EntryShape : Ty 0 -> Prop where
| arrow : Sto.EntryShape (.arrow S T)
| pair_tm :
    Sto.EntryShape (.pairTm (.single (.var (.free ℓ1))) a
      (Ty.single (.var (.free ℓ2))).weaken)
| pair_ty :
    Sto.EntryShape (.pairTy (.single (.var (.free ℓ1))) A
      (Ty.weaken W) (Ty.weaken W))

/-- Syntactic store wellformedness: every entry is precise-value-shaped
and mentions only older locations. -/
def Sto.Shaped (Θ : Sto) : Prop :=
  ∀ {ℓ : Nat} {T : Ty 0}, Sto.Lookup Θ ℓ T ->
    Sto.EntryShape T ∧ T.LocsBelow ℓ

/-- Typed heaps have shaped store typings. -/
theorem HeapTyped.shaped {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h) :
    Sto.Shaped Θ := by
  intro ℓ T hl
  obtain ⟨hb, v, -, -, hpre⟩ := hh.2 hl
  refine ⟨?_, hb⟩
  cases hpre with
  | abs _ _ => exact .arrow
  | pair_tm _ _ => exact .pair_tm
  | pair_ty _ _ => exact .pair_ty

/-! ### Chains as subtyping evidence (ports of the tight-layer lemmas;
the selection cases are now single anchored-rule applications). -/

/-- A chaining path is a subtype of its target's singleton. -/
theorem Chains.to_sub {Θ : Sto} {p : Path 0} {ℓ : Nat}
    (hc : Chains Θ p ℓ) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single (.var (.free ℓ)))) := by
  induction hc with
  | loc _ => exact .refl
  | fst_tm _ hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_tm (.trans ih hvf)
  | fst_ty _ hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_ty (.trans ih hvf)
  | sel hc hl ih => exact Sub.sel_tm_loc hc hl
  | sel_skip_tm hc hl hne _ ihp ihin =>
    exact .trans (Sub.skip_tm_loc hc hl hne) ihin
  | sel_skip_ty hc hl _ ihp ihin =>
    exact .trans (Sub.skip_ty_loc hc hl) ihin

/-- A chaining path sits below its target's entry. -/
theorem Chains.to_sub_entry {Θ : Sto} {p : Path 0} {m : Nat} {T : Ty 0}
    (hc : Chains Θ p m) (hl : Sto.Lookup Θ m T) :
    Sub Θ .empty (.ty (.single p)) (.ty T) := by
  have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
  rw [Ty.fromClosed_zero] at hvf
  exact .trans hc.to_sub hvf

/-- Store-side resolution yields wellformedness. -/
theorem Chains.wf {Θ : Sto} {p : Path 0} {ℓ : Nat}
    (hc : Chains Θ p ℓ) : Path.Wf Θ .empty p := by
  induction hc with
  | loc hl => exact .var_free hl
  | fst_tm hc hl ih => exact .fst_tm ih (hc.to_sub_entry hl)
  | fst_ty hc hl ih => exact .fst_ty ih (hc.to_sub_entry hl)
  | sel hc hl ih => exact .sel ih (hc.to_sub_entry hl)
  | sel_skip_tm hc hl hne _ ihp ihin =>
    exact .sel_skip_tm ihin (hc.to_sub_entry hl) hne
  | sel_skip_ty hc hl _ ihp ihin =>
    exact .sel_skip_ty ihin (hc.to_sub_entry hl)

/-- Co-chaining paths are mutual subtypes. -/
theorem Chains.mutual_sub {Θ : Sto} {p q : Path 0} {ℓ0 : Nat}
    (hp : Chains Θ p ℓ0) (hq : Chains Θ q ℓ0) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single q)) :=
  .trans hp.to_sub (.symm hq.wf hq.to_sub)

/-- Contiguity: any index below the store length is recorded (hoisted
from the quarantined preservation file). -/
theorem Sto.lookup_lt {Θ : Sto} {m : Nat} (hm : m < Θ.length) :
    ∃ T, Sto.Lookup Θ m T :=
  ⟨Θ[m], List.getElem?_eq_some_iff.mpr ⟨hm, rfl⟩⟩

/-- Chain targets are recorded (locations mentioned by entries are older
and the store is contiguous). -/
theorem Chains.in_dom {Θ : Sto} {p : Path 0} {m : Nat}
    (hwf : Sto.Shaped Θ) (hc : Chains Θ p m) :
    ∃ E, Sto.Lookup Θ m E := by
  induction hc with
  | loc hl => exact ⟨_, hl⟩
  | fst_tm hc hl ih =>
    obtain ⟨hs, hb⟩ := hwf hl
    have hlt : Θ.length > _ := (List.getElem?_eq_some_iff.mp hl).1
    exact Sto.lookup_lt (by
      simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow] at hb
      omega)
  | fst_ty hc hl ih =>
    obtain ⟨hs, hb⟩ := hwf hl
    have hlt : Θ.length > _ := (List.getElem?_eq_some_iff.mp hl).1
    exact Sto.lookup_lt (by
      simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow] at hb
      omega)
  | sel hc hl ih =>
    obtain ⟨hs, hb⟩ := hwf hl
    have hlt : Θ.length > _ := (List.getElem?_eq_some_iff.mp hl).1
    exact Sto.lookup_lt (by
      simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow, Ty.weaken,
        Ty.rename, Path.rename, Var.rename] at hb
      omega)
  | sel_skip_tm _ _ _ _ _ ihin => exact ihin
  | sel_skip_ty _ _ _ _ ihin => exact ihin

/-- Weakening is injective on types. -/
theorem Ty.weaken_inj {T1 T2 : Ty s}
    (h : (Ty.weaken T1 : Ty (s+1)) = Ty.weaken T2) : T1 = T2 := by
  have h2 := congrArg (fun X => Ty.open X (.var (.free 0))) h
  simpa [Ty.weaken_open] using h2

/-- Sized runtime subtyping over proper types at the empty context. -/
inductive SSub (Θ : Sto) : Ty 0 -> Ty 0 -> Nat -> Prop where
| refl :
  SSub Θ T T (n+1)
| trans :
  SSub Θ T1 T2 n -> SSub Θ T2 T3 n ->
  SSub Θ T1 T3 (n+1)
| bot :
  SSub Θ .bot T (n+1)
| top :
  SSub Θ T .top (n+1)
| var_free :
  Sto.Lookup Θ ℓ T ->
  SSub Θ (.single (.var (.free ℓ))) T.fromClosed (n+1)
| symm :
  Path.Wf Θ .empty p ->
  SSub Θ (.single p) (.single q) n ->
  SSub Θ (.single q) (.single p) (n+1)
| fst_tm :
  SSub Θ (.single p) (.pairTm S a T) n ->
  SSub Θ (.single p.fst) S (n+1)
| fst_ty :
  SSub Θ (.single p) (.pairTy S A T1 T2) n ->
  SSub Θ (.single p.fst) S (n+1)
| sel_tm_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTm S a (Ty.single (.var (.free ℓ2))).weaken) ->
  SSub Θ (.single (p.sel a)) (.single (.var (.free ℓ2))) (n+1)
| sel_hi_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  SSub Θ (Ty.fromClosed W) U n ->
  SSub Θ (.tsel p A) U (n+1)
| sel_lo_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  SSub Θ U (Ty.fromClosed W) n ->
  SSub Θ U (.tsel p A) (n+1)
| arrow :
  SSub Θ S' S n ->
  Sub Θ (Ctx.empty.push S') (.ty T) (.ty T') ->
  SSub Θ (.arrow S T) (.arrow S' T') (n+1)
| pair_tm :
  SSub Θ S S' n ->
  Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
  SSub Θ (.pairTm S a T) (.pairTm S' a T') (n+1)
| pair_ty :
  SSub Θ S S' n ->
  Sub Θ (Ctx.empty.push S) (.ty T1') (.ty T1) ->
  Sub Θ (Ctx.empty.push S) (.ty T2) (.ty T2') ->
  SSub Θ (.pairTy S A T1 T2) (.pairTy S' A T1' T2') (n+1)
| repl :
  Path.Wf Θ .empty p -> Path.Wf Θ .empty q ->
  SSub Θ (.single p) (.single q) n ->
  SSub Θ (.single q) (.single p) n ->
  SSub Θ (Ty.open T p) (Ty.open T q) (n+1)
| skip_tm_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm S b Tc) ->
  a ≠ b ->
  SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) (n+1)
| skip_ty_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTy S B T1 T2) ->
  SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) (n+1)

/-- Growing a derivation by one (right-premise growth keeps the size
arithmetic definitional). -/
theorem SSub.succ {Θ} {T1 T2 : Ty 0} {n : Nat}
    (h : SSub Θ T1 T2 n) : SSub Θ T1 T2 (n+1) := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_free hl => exact .var_free hl
  | symm hw _ ih => exact .symm hw ih
  | fst_tm _ ih => exact .fst_tm ih
  | fst_ty _ ih => exact .fst_ty ih
  | sel_tm_loc hc hl => exact .sel_tm_loc hc hl
  | sel_hi_loc hc hl _ ih => exact .sel_hi_loc hc hl ih
  | sel_lo_loc hc hl _ ih => exact .sel_lo_loc hc hl ih
  | arrow _ h2 ih => exact .arrow ih h2
  | pair_tm _ h2 ih => exact .pair_tm ih h2
  | pair_ty _ h1 h2 ih => exact .pair_ty ih h1 h2
  | repl hwp hwq _ _ ih1 ih2 => exact .repl hwp hwq ih1 ih2
  | skip_tm_loc hc hl hne => exact .skip_tm_loc hc hl hne
  | skip_ty_loc hc hl => exact .skip_ty_loc hc hl

/-- Sizes are monotone (minidot's upgrade idiom). -/
theorem SSub.mono {Θ} {T1 T2 : Ty 0} {n n' : Nat}
    (h : SSub Θ T1 T2 n) (hle : n ≤ n') : SSub Θ T1 T2 n' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => exact h
  | succ k ih => exact ih.succ

/-! ### The trans-free layer

`PEq` is runtime path equivalence — the directed, invertible core of
singleton subtyping (Chains co-targeting, label skips, and congruence
under opening; symmetry and transitivity are primitive since PEq is a
leaf: the pushback never recurses into it). `SPP` is trans-free
runtime subtyping: reflexivity is primitive (stuck selections have no
chains to rebuild it from), selections anchor to the store with
recursive upper tails and lazy general lower tails, and congruence
first components are recursive (the pushback walks them) while
push-context premises stay lazy at the general judgment. Inversion
lemmas carry `Sto.Shaped`; the judgments themselves are hypothesis-free. -/

/-- Runtime path equivalence. -/
inductive PEq (Θ : Sto) : Path 0 -> Path 0 -> Prop where
| refl :
  PEq Θ p p
| symm :
  PEq Θ p q -> PEq Θ q p
| trans :
  PEq Θ p q -> PEq Θ q r -> PEq Θ p r
| cochain :
  Chains Θ p ℓ -> Chains Θ q ℓ -> PEq Θ p q
| skip_tm :
  Chains Θ p ℓ -> Sto.Lookup Θ ℓ (.pairTm S b Tc) -> a ≠ b ->
  PEq Θ (p.sel a) ((Path.fst p).sel a)
| skip_ty :
  Chains Θ p ℓ -> Sto.Lookup Θ ℓ (.pairTy S B T1 T2) ->
  PEq Θ (p.sel a) ((Path.fst p).sel a)
| congr :
  Path.Wf Θ .empty p -> Path.Wf Θ .empty q -> PEq Θ p q ->
  PEq Θ (Path.subst r (Subst.openPath p)) (Path.subst r (Subst.openPath q))

/-- Trans-free runtime subtyping. -/
inductive SPP (Θ : Sto) : Ty 0 -> Ty 0 -> Prop where
| refl :
  SPP Θ T T
| bot :
  SPP Θ .bot T
| top :
  SPP Θ T .top
| sngl :
  PEq Θ p q -> SPP Θ (.single p) (.single q)
| unfold :
  Chains Θ p ℓ -> Sto.Lookup Θ ℓ E -> SPP Θ E U ->
  SPP Θ (.single p) U
| tsel_hi :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  SPP Θ W U ->
  SPP Θ (.tsel p A) U
| tsel_lo :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  Sub Θ .empty (.ty U) (.ty W) ->
  SPP Θ U (.tsel p A)
| repl :
  Path.Wf Θ .empty p -> Path.Wf Θ .empty q -> PEq Θ p q ->
  SPP Θ (Ty.open T p) (Ty.open T q)
| arrow :
  SPP Θ S' S ->
  Sub Θ (Ctx.empty.push S') (.ty T) (.ty T') ->
  SPP Θ (.arrow S T) (.arrow S' T')
| pair_tm :
  SPP Θ S S' ->
  Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
  SPP Θ (.pairTm S a T) (.pairTm S' a T')
| pair_ty :
  SPP Θ S S' ->
  Sub Θ (Ctx.empty.push S) (.ty T1') (.ty T1) ->
  Sub Θ (Ctx.empty.push S) (.ty T2) (.ty T2') ->
  SPP Θ (.pairTy S A T1 T2) (.pairTy S' A T1' T2')

/-- The sized judgment is sound for the general one (used to grow the
lazy general tails during pushback compositions). -/
theorem SSub.to_sub {Θ : Sto} {T1 T2 : Ty 0} {n : Nat}
    (h : SSub Θ T1 T2 n) : Sub Θ .empty (.ty T1) (.ty T2) := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_free hl => exact .var_free hl
  | symm hw _ ih => exact .symm hw ih
  | fst_tm _ ih => exact .fst_tm ih
  | fst_ty _ ih => exact .fst_ty ih
  | sel_tm_loc hc hl => exact .sel_tm_loc hc hl
  | sel_hi_loc hc hl _ ih => exact .trans (.sel_hi_loc hc hl) ih
  | sel_lo_loc hc hl _ ih => exact .trans ih (.sel_lo_loc hc hl)
  | arrow _ h2 ih => exact .arrow ih h2
  | pair_tm _ h2 ih => exact .pair_tm ih h2
  | pair_ty _ h1 h2 ih => exact .pair_ty ih h1 h2
  | repl hwp hwq _ _ ih1 ih2 => exact .repl hwp hwq ih1 ih2
  | skip_tm_loc hc hl hne => exact .skip_tm_loc hc hl hne
  | skip_ty_loc hc hl => exact .skip_ty_loc hc hl

end LambdaP
