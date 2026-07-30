import LambdaP.Soundness.Store
import LambdaP.Lemmas.Locs

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
theorem Chains.to_sub {s : Sig} {Θ : Sto} {Γ : Ctx s} {p : Path s} {ℓ : Nat}
    (hc : Chains Θ p ℓ) :
    Sub Θ Γ (.ty (.single p)) (.ty (.single (.var (.free ℓ)))) := by
  induction hc with
  | loc _ => exact .refl
  | fst_tm _ hl ih =>
    have hvf := Sub.var_free (Γ := Γ) hl
    exact .fst_tm (.trans ih hvf)
  | fst_ty _ hl ih =>
    have hvf := Sub.var_free (Γ := Γ) hl
    exact .fst_ty (.trans ih hvf)
  | sel hc hl ih => exact Sub.sel_tm_loc hc hl
  | sel_skip_tm hc hl hne _ ihp ihin =>
    exact .trans (Sub.skip_tm_loc hc hl hne) ihin
  | sel_skip_ty hc hl _ ihp ihin =>
    exact .trans (Sub.skip_ty_loc hc hl) ihin

/-- A chaining path sits below its target's entry. -/
theorem Chains.to_sub_entry {s : Sig} {Θ : Sto} {Γ : Ctx s} {p : Path s}
    {m : Nat} {T : Ty 0}
    (hc : Chains Θ p m) (hl : Sto.Lookup Θ m T) :
    Sub Θ Γ (.ty (.single p)) (.ty (Ty.fromClosed T)) := by
  have hvf := Sub.var_free (Γ := Γ) hl
  exact .trans hc.to_sub hvf

/-- Store-side resolution yields wellformedness. -/
theorem Chains.wf {s : Sig} {Θ : Sto} {Γ : Ctx s} {p : Path s} {ℓ : Nat}
    (hc : Chains Θ p ℓ) : Path.Wf Θ Γ p := by
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
theorem Chains.mutual_sub {s : Sig} {Θ : Sto} {Γ : Ctx s} {p q : Path s}
    {ℓ0 : Nat} (hp : Chains Θ p ℓ0) (hq : Chains Θ q ℓ0) :
    Sub Θ Γ (.ty (.single p)) (.ty (.single q)) :=
  .trans hp.to_sub (.symm hq.wf hq.to_sub)

/-- Contiguity: any index below the store length is recorded (hoisted
from the quarantined preservation file). -/
theorem Sto.lookup_lt {Θ : Sto} {m : Nat} (hm : m < Θ.length) :
    ∃ T, Sto.Lookup Θ m T :=
  ⟨Θ[m], List.getElem?_eq_some_iff.mpr ⟨hm, rfl⟩⟩


/-! ### Replacement corollaries (P4.3): mutual singleton aliases are
congruences for projections, selections, and arbitrary openings. -/

/-- Mutual aliases transport through first projection. -/
theorem Sub.repl_fst {s : Sig} {Θ : Sto} {Γ : Ctx s} {p q : Path s}
    (hwp : Path.Wf Θ Γ p) (hwq : Path.Wf Θ Γ q)
    (h1 : Sub Θ Γ (.ty (.single p)) (.ty (.single q)))
    (h2 : Sub Θ Γ (.ty (.single q)) (.ty (.single p))) :
    Sub Θ Γ (.ty (.single p.fst)) (.ty (.single q.fst)) :=
  Sub.repl (T := .single ((Path.var (Var.bound .here)).fst)) hwp hwq h1 h2

/-- Mutual aliases transport through selection. -/
theorem Sub.repl_sel {s : Sig} {Θ : Sto} {Γ : Ctx s} {p q : Path s} {a : Name}
    (hwp : Path.Wf Θ Γ p) (hwq : Path.Wf Θ Γ q)
    (h1 : Sub Θ Γ (.ty (.single p)) (.ty (.single q)))
    (h2 : Sub Θ Γ (.ty (.single q)) (.ty (.single p))) :
    Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single (q.sel a))) :=
  Sub.repl (T := .single ((Path.var (Var.bound .here)).sel a)) hwp hwq h1 h2

/-- Mutual aliases transport through type selection. -/
theorem Sub.repl_tsel {s : Sig} {Θ : Sto} {Γ : Ctx s} {p q : Path s} {A : Name}
    (hwp : Path.Wf Θ Γ p) (hwq : Path.Wf Θ Γ q)
    (h1 : Sub Θ Γ (.ty (.single p)) (.ty (.single q)))
    (h2 : Sub Θ Γ (.ty (.single q)) (.ty (.single p))) :
    Sub Θ Γ (.ty (.tsel p A)) (.ty (.tsel q A)) :=
  Sub.repl (T := .tsel (Path.var (Var.bound .here)) A) hwp hwq h1 h2

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

/-- Alias entries at the same location and label carry the same alias. -/
theorem alias_unify {Θ : Sto} {m ℓa ℓb : Nat} {A : Name} {Wa Wb : Ty 0}
    (h : Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓa))) A (Ty.weaken Wa) (Ty.weaken Wa)))
    (h' : Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓb))) A (Ty.weaken Wb) (Ty.weaken Wb))) :
    Wa = Wb := by
  have heq := Option.some_inj.mp ((Eq.symm h).trans h')
  injection heq with _ _ _ hT1 _
  exact Ty.weaken_inj hT1

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

/-! ### Chains congruence (ported from the superseded invertible layer)
and the invariance theorem for path equivalence. -/

def CoChains (Θ : Sto) (σ1 σ2 : Subst s 0) : Prop :=
  ∀ (x : BVar s) (m : Nat), Chains Θ (σ1.var x) m ↔ Chains Θ (σ2.var x) m

/-- Resolution of a substituted path only depends on the targets of the
substituted-in paths (store-side mirror of `PathEval.subst_congr`). -/
theorem Chains.subst_congr {Θ : Sto} {σ1 σ2 : Subst s 0}
    (hco : CoChains Θ σ1 σ2) :
    ∀ {p : Path s} {m : Nat},
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

/-- Co-resolution of the two opening substitutions of co-resolving
opener paths. -/
theorem CoChains.openPath {Θ : Sto} {q q' : Path 0} {ℓq : Nat}
    (hq : Chains Θ q ℓq) (hq' : Chains Θ q' ℓq) :
    CoChains Θ (Subst.openPath q) (Subst.openPath q') := by
  intro x m
  cases x with
  | here =>
    constructor
    · intro he
      cases Chains.deterministic he hq
      exact hq'
    · intro he
      cases Chains.deterministic he hq'
      exact hq
  | there b => exact nomatch b

/-- Resolution of an opened path only depends on the target of the
opening path (the store-side mirror of `PathEval.open_congr`). -/
theorem Chains.open_congr {Θ : Sto} {q q' : Path 0} {ℓq : Nat}
    (hq : Chains Θ q ℓq) (hq' : Chains Θ q' ℓq) :
    ∀ {p : Path 1} {m : Nat},
      Chains Θ (p.subst (Subst.openPath q)) m ->
      Chains Θ (p.subst (Subst.openPath q')) m :=
  fun he => Chains.subst_congr (CoChains.openPath hq hq') he

/-- Chains-iff on roots induces co-chaining of the opening
substitutions (no common target required — either both resolve or
neither does). -/
theorem CoChains.of_iff {Θ : Sto} {q q' : Path 0}
    (h : ∀ m, Chains Θ q m ↔ Chains Θ q' m) :
    CoChains Θ (Subst.openPath q) (Subst.openPath q') := by
  intro x m
  cases x with
  | here => exact h m
  | there b => exact nomatch b

/-- Equivalent paths resolve identically: the invariance theorem that
makes `PEq` a leaf the pushback can consult without recursion. -/
theorem PEq.chains_iff {Θ : Sto} {p q : Path 0} (h : PEq Θ p q) :
    ∀ m, Chains Θ p m ↔ Chains Θ q m := by
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
    · exact Chains.subst_congr (CoChains.of_iff ih)
    · exact Chains.subst_congr (CoChains.of_iff (fun m => (ih m).symm))



/-! ### Opening decompositions (ported): heads survive opening, so
replacement conclusions decompose by the template's head. -/

theorem Ty.open_eq_arrow {T : Ty 1} {q : Path 0} {S : Ty 0} {B : Ty 1}
    (he : T.open q = .arrow S B) :
    ∃ S0 B0, T = .arrow S0 B0 ∧ S = S0.open q ∧
      B = B0.subst (Subst.openPath q).lift := by
  cases T with
  | arrow S0 B0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2
    exact ⟨S0, B0, rfl, h1.symm, h2.symm⟩
  | top => cases he
  | bot => cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_pairTm {T : Ty 1} {q : Path 0} {S : Ty 0} {a : Name} {B : Ty 1}
    (he : T.open q = .pairTm S a B) :
    ∃ S0 B0, T = .pairTm S0 a B0 ∧ S = S0.open q ∧
      B = B0.subst (Subst.openPath q).lift := by
  cases T with
  | pairTm S0 a0 B0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2 h3
    subst h2
    exact ⟨S0, B0, rfl, h1.symm, h3.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_pairTy {T : Ty 1} {q : Path 0} {S : Ty 0} {A : Name} {B1 B2 : Ty 1}
    (he : T.open q = .pairTy S A B1 B2) :
    ∃ S0 C1 C2, T = .pairTy S0 A C1 C2 ∧ S = S0.open q ∧
      B1 = C1.subst (Subst.openPath q).lift ∧
      B2 = C2.subst (Subst.openPath q).lift := by
  cases T with
  | pairTy S0 A0 C1 C2 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2 h3 h4
    subst h2
    exact ⟨S0, C1, C2, rfl, h1.symm, h3.symm, h4.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_single {T : Ty 1} {q : Path 0} {r : Path 0}
    (he : T.open q = .single r) :
    ∃ P0, T = .single P0 ∧ r = P0.subst (Subst.openPath q) := by
  cases T with
  | single P0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1
    exact ⟨P0, rfl, h1.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel _ _ => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_tsel {T : Ty 1} {q : Path 0} {r : Path 0} {A : Name}
    (he : T.open q = .tsel r A) :
    ∃ P0, T = .tsel P0 A ∧ r = P0.subst (Subst.openPath q) := by
  cases T with
  | tsel P0 A0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2
    subst h2
    exact ⟨P0, rfl, h1.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single _ => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_bot {T : Ty 1} {q : Path 0}
    (he : T.open q = .bot) : T = .bot := by
  cases T with
  | bot => rfl
  | top => cases he
  | single _ => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he



/-! ### Inversion pack under shaped stores. -/

/-- Entry-shaped types are never below a singleton in the trans-free
judgment (the shape lemma the symm and singles cases consult). -/
theorem SPP.entry_no_single {Θ : Sto} {E U : Ty 0}
    (hs : Sto.EntryShape E) (h : SPP Θ E U) :
    ∀ {q : Path 0}, U = .single q -> False := by
  cases h with
  | refl =>
    intro q hU
    subst hU
    nomatch hs
  | bot => nomatch hs
  | top => intro q hU; cases hU
  | sngl _ => nomatch hs
  | unfold _ _ _ => nomatch hs
  | tsel_hi _ _ _ => nomatch hs
  | tsel_lo _ _ _ => intro q hU; cases hU
  | repl hwp hwq hpe =>
    intro q hU
    obtain ⟨P0, hT, -⟩ := Ty.open_eq_single hU
    subst hT
    simp only [Ty.open, Ty.subst] at hs
    nomatch hs
  | arrow _ _ => intro q hU; cases hU
  | pair_tm _ _ => intro q hU; cases hU
  | pair_ty _ _ _ => intro q hU; cases hU

/-- Trans-free singleton-singleton facts are path equivalences. -/
theorem SPP.single_single_inv {Θ : Sto} {T1 T2 : Ty 0}
    (hwf : Sto.Shaped Θ) (h : SPP Θ T1 T2) :
    ∀ {p q : Path 0}, T1 = .single p -> T2 = .single q -> PEq Θ p q := by
  cases h with
  | refl =>
    intro p q h1 h2
    subst h1
    injection h2 with hs0 hpq
    subst hpq
    exact .refl
  | bot => intro p q h1 _; cases h1
  | top => intro p q _ h2; cases h2
  | sngl hpe =>
    intro p q h1 h2
    injection h1 with hs1 e1
    injection h2 with hs2 e2
    subst e1; subst e2
    exact hpe
  | unfold hc hl hE =>
    intro p q h1 h2
    exact absurd h2 (fun h2 => SPP.entry_no_single (hwf hl).1 hE h2)
  | tsel_hi _ _ _ => intro p q h1 _; cases h1
  | tsel_lo _ _ _ => intro p q _ h2; cases h2
  | repl hwp hwq hpe =>
    intro p q h1 h2
    obtain ⟨P1, hT1, hp⟩ := Ty.open_eq_single h1
    obtain ⟨P2, hT2, hq⟩ := Ty.open_eq_single h2
    subst hT1
    injection hT2 with hs0 hP
    subst hP
    subst hp; subst hq
    exact .congr hwp hwq hpe
  | arrow _ _ => intro p q h1 _; cases h1
  | pair_tm _ _ => intro p q h1 _; cases h1
  | pair_ty _ _ _ => intro p q h1 _; cases h1



/-- Resolution targets of location-bounded paths are strictly below
the bound over shaped stores: entries mention only older locations,
so chains descend. This is the well-founded measure for the
alias-hop descent (lexicographic with fuel). -/
theorem Chains.target_lt {Θ : Sto} {q : Path 0} {mq k : Nat}
    (hwf : Sto.Shaped Θ) (hc : Chains Θ q mq)
    (hb : Path.LocsBelow k q) : mq < k := by
  induction hc with
  | loc _ => exact hb
  | fst_tm hc hl ih =>
    have h1 := (hwf hl).2
    have := ih hb
    simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow] at h1
    omega
  | fst_ty hc hl ih =>
    have h1 := (hwf hl).2
    have := ih hb
    simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow] at h1
    omega
  | sel hc hl ih =>
    have h1 := (hwf hl).2
    have := ih hb
    simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow, Ty.weaken,
      Ty.rename, Path.rename, Var.rename] at h1
    omega
  | sel_skip_tm hc hl hne hin ihp ihin =>
    have hp := ihp hb
    exact ihin (by
      simp only [Path.LocsBelow] at hb ⊢
      exact hb)
  | sel_skip_ty hc hl hin ihp ihin =>
    have hp := ihp hb
    exact ihin (by
      simp only [Path.LocsBelow] at hb ⊢
      exact hb)



/-! ### The sized inversion package: statement

`SOut` is the shape-directed reading of a sized runtime subtyping fact
over a shaped store. Fuel discipline (NOTES, "LOCKED"): tsel-anchored
tails are strict (`m < n`) except the shaped-subject ones (`m ≤ n`,
built by raw-premise composition, never re-inverted); dominance
components are `m ≤ n`. The `PEq` wrapper keeps the single-subject
tsel tail strict under transport. -/
def SOut (Θ : Sto) (n : Nat) : Ty 0 -> Ty 0 -> Prop
| .single p, .single q => PEq Θ p q
| .single p, .pairTm S a T =>
    ∃ ℓ0 E, Chains Θ p ℓ0 ∧ Sto.Lookup Θ ℓ0 E ∧
      ∃ m, m ≤ n ∧ SSub Θ E (.pairTm S a T) m
| .single p, .pairTy S A T1 T2 =>
    ∃ ℓ0 E, Chains Θ p ℓ0 ∧ Sto.Lookup Θ ℓ0 E ∧
      ∃ m, m ≤ n ∧ SSub Θ E (.pairTy S A T1 T2) m
| .single p, .arrow S T =>
    ∃ ℓ0 E, Chains Θ p ℓ0 ∧ Sto.Lookup Θ ℓ0 E ∧
      ∃ m, m ≤ n ∧ SSub Θ E (.arrow S T) m
| .single p, .tsel q A =>
    (∃ ℓ0 E, Chains Θ p ℓ0 ∧ Sto.Lookup Θ ℓ0 E ∧
      ∃ m, m ≤ n ∧ SSub Θ E (.tsel q A) m) ∨
    (∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ p', PEq Θ p p' ∧ ∃ m, m ≤ n ∧ SSub Θ (.single p') W m)
| .single p, .bot =>
    ∃ ℓ0 E, Chains Θ p ℓ0 ∧ Sto.Lookup Θ ℓ0 E ∧
      ∃ m, m ≤ n ∧ SSub Θ E .bot m
| .single _, .top => True
| .pairTm S a T, .pairTm S' a' T' =>
    a = a' ∧ (∃ m, m ≤ n ∧ SSub Θ S S' m) ∧
    Sub Θ (Ctx.empty.push S) (.ty T) (.ty T')
| .pairTy S A T1 T2, .pairTy S' A' T1' T2' =>
    A = A' ∧ (∃ m, m ≤ n ∧ SSub Θ S S' m) ∧
    Sub Θ (Ctx.empty.push S) (.ty T1') (.ty T1) ∧
    Sub Θ (Ctx.empty.push S) (.ty T2) (.ty T2')
| .arrow S T, .arrow S' T' =>
    (∃ m, m ≤ n ∧ SSub Θ S' S m) ∧
    Sub Θ (Ctx.empty.push S') (.ty T) (.ty T')
| .pairTm S a T, .tsel q A =>
    ∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ (.pairTm S a T) W m
| .pairTy S A T1 T2, .tsel q A' =>
    ∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A'
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ (.pairTy S A T1 T2) W m
| .arrow S T, .tsel q A =>
    ∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ (.arrow S T) W m
| .pairTm _ _ _, .top => True
| .pairTy _ _ _ _, .top => True
| .arrow _ _, .top => True
| .pairTm _ _ _, .pairTy _ _ _ _ => False
| .pairTm _ _ _, .arrow _ _ => False
| .pairTm _ _ _, .single _ => False
| .pairTm _ _ _, .bot => False
| .pairTy _ _ _ _, .pairTm _ _ _ => False
| .pairTy _ _ _ _, .arrow _ _ => False
| .pairTy _ _ _ _, .single _ => False
| .pairTy _ _ _ _, .bot => False
| .arrow _ _, .pairTm _ _ _ => False
| .arrow _ _, .pairTy _ _ _ _ => False
| .arrow _ _, .single _ => False
| .arrow _ _, .bot => False
| .tsel _ _, .top => True
| .tsel q A, X =>
    (∃ p2, X = .tsel p2 A ∧ PEq Θ q p2) ∨
    (∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ W X m) ∨
    (∃ p2 A2 mq ℓ1 W, X = .tsel p2 A2 ∧ Chains Θ p2 mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A2
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ (.tsel q A) W m)
| .top, .top => True
| .top, .tsel q A =>
    ∃ mq ℓ1 W, Chains Θ q mq ∧
      Sto.Lookup Θ mq (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      ∃ m, m ≤ n ∧ SSub Θ .top W m
| .top, _ => False
| .bot, _ => True

/-- `SOut` is monotone in fuel. -/
theorem SOut.mono {Θ : Sto} {n n' : Nat} {T1 T2 : Ty 0}
    (h : SOut Θ n T1 T2) (hle : n ≤ n') : SOut Θ n' T1 T2 := by
  cases T1 <;> cases T2 <;>
    simp only [SOut] at h ⊢ <;>
    first
    | exact h
    | (obtain ⟨a1, a2, h1, h2, m, hm, hs⟩ := h
       exact ⟨a1, a2, h1, h2, m, by omega, hs⟩)
    | (obtain ⟨a1, a2, a3, h1, h2, m, hm, hs⟩ := h
       exact ⟨a1, a2, a3, h1, h2, m, by omega, hs⟩)
    | (obtain ⟨he, m, hm, hs⟩ := h
       exact ⟨he, m, by omega, hs⟩)
    | (obtain ⟨he, ⟨m, hm, hs⟩, r⟩ := h
       exact ⟨he, ⟨m, by omega, hs⟩, r⟩)
    | (obtain ⟨he, ⟨m, hm, hs⟩, r1, r2⟩ := h
       exact ⟨he, ⟨m, by omega, hs⟩, r1, r2⟩)
    | (obtain ⟨m, hm, hs⟩ := h
       exact ⟨m, by omega, hs⟩)
    | (obtain ⟨⟨m, hm, hs⟩, res⟩ := h
       exact ⟨⟨m, by omega, hs⟩, res⟩)
    | (rcases h with ⟨a1, a2, h1, h2, m, hm, hs⟩ |
         ⟨a1, a2, a3, h1, h2, p', hpe, m, hm, hs⟩
       · exact Or.inl ⟨a1, a2, h1, h2, m, by omega, hs⟩
       · exact Or.inr ⟨a1, a2, a3, h1, h2, p', hpe, m, by omega, hs⟩)
    | (rcases h with ⟨p2, hX, hpe⟩ | ⟨a1, a2, a3, h1, h2, m, hm, hs⟩
         | ⟨p2, A2, a1, a2, a3, hX, h1, h2, m, hm, hs⟩
       · exact Or.inl ⟨p2, hX, hpe⟩
       · exact Or.inr (Or.inl ⟨a1, a2, a3, h1, h2, m, by omega, hs⟩)
       · exact Or.inr (Or.inr ⟨p2, A2, a1, a2, a3, hX, h1, h2, m, by omega, hs⟩))

/-- Chains from a bare location resolve to it. -/
theorem Chains.var_free_eq {Θ : Sto} {ℓ m : Nat}
    (h : Chains Θ (.var (.free ℓ) : Path 0) m) : m = ℓ := by
  cases h with
  | loc _ => rfl


/-- Subject transport: `SOut` facts about a singleton subject move
along path equivalence. -/
theorem SOut.peq_subject {Θ : Sto} {p p0 : Path 0} {S : Ty 0} {m n : Nat}
    (hpe : PEq Θ p p0)
    (o : SOut Θ m (.single p0) S) (hmn : m ≤ n) :
    SOut Θ n (.single p) S := by
  cases S with
  | single s => exact hpe.trans o
  | top => trivial
  | tsel q A =>
    rcases o with ⟨ℓ0, E, hc, hE, m', hm', hs⟩ |
      ⟨mq, ℓ1, W, hcq, hEq, p', hpe', m', hm', hs⟩
    · exact Or.inl ⟨ℓ0, E, (hpe.chains_iff ℓ0).mpr hc, hE, m', by omega, hs⟩
    · exact Or.inr ⟨mq, ℓ1, W, hcq, hEq, p', hpe.trans hpe', m', by omega, hs⟩
  | pairTm S a T =>
    obtain ⟨ℓ0, E, hc, hE, m', hm', hs⟩ := o
    exact ⟨ℓ0, E, (hpe.chains_iff ℓ0).mpr hc, hE, m', by omega, hs⟩
  | pairTy S A T1 T2 =>
    obtain ⟨ℓ0, E, hc, hE, m', hm', hs⟩ := o
    exact ⟨ℓ0, E, (hpe.chains_iff ℓ0).mpr hc, hE, m', by omega, hs⟩
  | arrow S T =>
    obtain ⟨ℓ0, E, hc, hE, m', hm', hs⟩ := o
    exact ⟨ℓ0, E, (hpe.chains_iff ℓ0).mpr hc, hE, m', by omega, hs⟩
  | bot =>
    obtain ⟨ℓ0, E, hc, hE, m', hm', hs⟩ := o
    exact ⟨ℓ0, E, (hpe.chains_iff ℓ0).mpr hc, hE, m', by omega, hs⟩


set_option maxHeartbeats 1600000 in
/-- The tsel-middle workhorse for the trans case of inversion:
compose two sized tails meeting at a stored alias interval, recursing
along alias hops — well-founded because alias contents mention only
older locations (`Chains.target_lt`). Takes the outer induction
hypothesis as an argument. -/
theorem SSub.descend {Θ : Sto} (hwf : Sto.Shaped Θ) {k : Nat}
    (IH : ∀ j, j ≤ k → ∀ {A B : Ty 0}, SSub Θ A B j → SOut Θ j A B) :
    ∀ manchor : Nat, ∀ {ℓ1 : Nat} {An : Name} {W X Y : Ty 0} {m1 m2 : Nat},
      Sto.Lookup Θ manchor (.pairTy (.single (.var (.free ℓ1))) An
        (Ty.weaken W) (Ty.weaken W)) ->
      SSub Θ X W m1 -> SSub Θ W Y m2 -> m1 ≤ k -> m2 ≤ k ->
      SOut Θ (k+1) X Y := by
  intro manchor
  induction manchor using Nat.strongRecOn with
  | ind manchor IHa =>
    intro ℓ1 An W X Y m1 m2 hE hXW hWY hm1 hm2
    have o1 := IH m1 hm1 hXW
    have o2 := IH m2 hm2 hWY
    cases W with
    | top =>
      cases X with
      | bot => trivial
      | top => exact o2.mono (by omega)
      | single p =>
        cases Y with
        | top => trivial
        | tsel y B =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m3, hm3, hW2⟩ := o2
          exact Or.inr ⟨my, ℓy, Wy, hcy, hEy, p, .refl, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m3))
                   (hW2.mono (Nat.le_max_right m1 m3))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | arrow S T =>
        cases Y with
        | top => trivial
        | tsel y B =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m3, hm3, hW2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m3))
                   (hW2.mono (Nat.le_max_right m1 m3))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | pairTm S a T =>
        cases Y with
        | top => trivial
        | tsel y B =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m3, hm3, hW2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m3))
                   (hW2.mono (Nat.le_max_right m1 m3))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | pairTy S A T1 T2 =>
        cases Y with
        | top => trivial
        | tsel y B =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m3, hm3, hW2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m3))
                   (hW2.mono (Nat.le_max_right m1 m3))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | tsel q A =>
        cases Y with
        | top => trivial
        | tsel y B =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m3, hm3, hW2⟩ := o2
          exact Or.inr (Or.inr ⟨y, B, my, ℓy, Wy, rfl, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m3))
                   (hW2.mono (Nat.le_max_right m1 m3))⟩)
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
    | bot =>
      cases X with
      | bot => trivial
      | top => exact o1.elim
      | single p =>
        obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, hEbot⟩ := o1
        have oE := IH m3 (by omega) hEbot
        rcases (hwf hE0).1 with hs | hs | hs
        all_goals first
          | exact (oE : False).elim
      | arrow _ _ => exact o1.elim
      | pairTm _ _ _ => exact o1.elim
      | pairTy _ _ _ _ => exact o1.elim
      | tsel q A =>
        rcases o1 with ⟨p2, hX, hpe⟩ | ⟨mq, ℓq, Wq, hcq, hEq, m3, hm3, htail⟩
          | ⟨p2, A2, mq, ℓq, Wq, hX, hcq, hEq, m3, hm3, htail⟩
        · exact absurd hX (by intro h; cases h)
        · have tl : SSub Θ Wq Y (max m3 m2 + 1) :=
            .trans (htail.mono (Nat.le_max_left m3 m2))
                   (hWY.mono (Nat.le_max_right m3 m2))
          cases Y with
          | top => trivial
          | single _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | bot => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
        · exact absurd hX (by intro h; cases h)
    | single w =>
      cases X with
      | bot => trivial
      | top => exact o1.elim
      | arrow _ _ => exact o1.elim
      | pairTm _ _ _ => exact o1.elim
      | pairTy _ _ _ _ => exact o1.elim
      | single p => exact o2.peq_subject o1 (by omega)
      | tsel q A =>
        rcases o1 with ⟨p2, hX, hpe⟩ | ⟨mq, ℓq, Wq, hcq, hEq, m3, hm3, htail⟩
          | ⟨p2, A2, mq, ℓq, Wq, hX, hcq, hEq, m3, hm3, htail⟩
        · exact absurd hX (by intro h; cases h)
        · have tl : SSub Θ Wq Y (max m3 m2 + 1) :=
            .trans (htail.mono (Nat.le_max_left m3 m2))
                   (hWY.mono (Nat.le_max_right m3 m2))
          cases Y with
          | top => trivial
          | single _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | bot => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
        · exact absurd hX (by intro h; cases h)
    | arrow S0 T0 =>
      cases X with
      | bot => trivial
      | top => exact o1.elim
      | pairTm _ _ _ => exact o1.elim
      | pairTy _ _ _ _ => exact o1.elim
      | single p =>
        obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
        have tl : SSub Θ E Y (max m3 m2 + 1) :=
          .trans (tailE.mono (Nat.le_max_left m3 m2))
                 (hWY.mono (Nat.le_max_right m3 m2))
        cases Y with
        | top => trivial
        | single s => exact o2.elim
        | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
      | arrow S T =>
        obtain ⟨⟨m3, hm3, dom1⟩, res1⟩ := o1
        cases Y with
        | top => trivial
        | arrow S' T' =>
          obtain ⟨⟨m4, hm4, dom2⟩, res2⟩ := o2
          exact ⟨⟨_, by omega, .trans (dom2.mono (Nat.le_max_left m4 m3))
            (dom1.mono (Nat.le_max_right m4 m3))⟩,
            .trans (res1.narrow dom2.to_sub) res2⟩
        | tsel y C =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m4))
                   (tail2.mono (Nat.le_max_right m1 m4))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | tsel q A =>
        rcases o1 with ⟨p2, hX, hpe⟩ | ⟨mq, ℓq, Wq, hcq, hEq, m3, hm3, htail⟩
          | ⟨p2, A2, mq, ℓq, Wq, hX, hcq, hEq, m3, hm3, htail⟩
        · exact absurd hX (by intro h; cases h)
        · have tl : SSub Θ Wq Y (max m3 m2 + 1) :=
            .trans (htail.mono (Nat.le_max_left m3 m2))
                   (hWY.mono (Nat.le_max_right m3 m2))
          cases Y with
          | top => trivial
          | single _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | bot => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
        · exact absurd hX (by intro h; cases h)
    | pairTm S0 a0 T0 =>
      cases X with
      | bot => trivial
      | top => exact o1.elim
      | arrow _ _ => exact o1.elim
      | pairTy _ _ _ _ => exact o1.elim
      | single p =>
        obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
        have tl : SSub Θ E Y (max m3 m2 + 1) :=
          .trans (tailE.mono (Nat.le_max_left m3 m2))
                 (hWY.mono (Nat.le_max_right m3 m2))
        cases Y with
        | top => trivial
        | single s => exact o2.elim
        | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
      | pairTm S a T =>
        obtain ⟨ha0, ⟨m3, hm3, dom1⟩, res1⟩ := o1
        cases Y with
        | top => trivial
        | pairTm S' a' T' =>
          obtain ⟨ha1, ⟨m4, hm4, dom2⟩, res2⟩ := o2
          exact ⟨ha0.trans ha1, ⟨_, by omega,
            .trans (dom1.mono (Nat.le_max_left m3 m4))
                   (dom2.mono (Nat.le_max_right m3 m4))⟩,
            .trans res1 (res2.narrow dom1.to_sub)⟩
        | tsel y C =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m4))
                   (tail2.mono (Nat.le_max_right m1 m4))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTy _ _ _ _ => exact o2.elim
      | tsel q A =>
        rcases o1 with ⟨p2, hX, hpe⟩ | ⟨mq, ℓq, Wq, hcq, hEq, m3, hm3, htail⟩
          | ⟨p2, A2, mq, ℓq, Wq, hX, hcq, hEq, m3, hm3, htail⟩
        · exact absurd hX (by intro h; cases h)
        · have tl : SSub Θ Wq Y (max m3 m2 + 1) :=
            .trans (htail.mono (Nat.le_max_left m3 m2))
                   (hWY.mono (Nat.le_max_right m3 m2))
          cases Y with
          | top => trivial
          | single _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | bot => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
        · exact absurd hX (by intro h; cases h)
    | pairTy S0 A0 T01 T02 =>
      cases X with
      | bot => trivial
      | top => exact o1.elim
      | arrow _ _ => exact o1.elim
      | pairTm _ _ _ => exact o1.elim
      | single p =>
        obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
        have tl : SSub Θ E Y (max m3 m2 + 1) :=
          .trans (tailE.mono (Nat.le_max_left m3 m2))
                 (hWY.mono (Nat.le_max_right m3 m2))
        cases Y with
        | top => trivial
        | single s => exact o2.elim
        | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
      | pairTy S A T1c T2c =>
        obtain ⟨hA0, ⟨m3, hm3, dom1⟩, lo1, hi1⟩ := o1
        cases Y with
        | top => trivial
        | pairTy S' A' T1' T2' =>
          obtain ⟨hA1, ⟨m4, hm4, dom2⟩, lo2, hi2⟩ := o2
          exact ⟨hA0.trans hA1, ⟨_, by omega,
            .trans (dom1.mono (Nat.le_max_left m3 m4))
                   (dom2.mono (Nat.le_max_right m3 m4))⟩,
            .trans (lo2.narrow dom1.to_sub) lo1,
            .trans hi1 (hi2.narrow dom1.to_sub)⟩
        | tsel y C =>
          obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
          exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
            .trans (hXW.mono (Nat.le_max_left m1 m4))
                   (tail2.mono (Nat.le_max_right m1 m4))⟩
        | single _ => exact o2.elim
        | bot => exact o2.elim
        | arrow _ _ => exact o2.elim
        | pairTm _ _ _ => exact o2.elim
      | tsel q A =>
        rcases o1 with ⟨p2, hX, hpe⟩ | ⟨mq, ℓq, Wq, hcq, hEq, m3, hm3, htail⟩
          | ⟨p2, A2, mq, ℓq, Wq, hX, hcq, hEq, m3, hm3, htail⟩
        · exact absurd hX (by intro h; cases h)
        · have tl : SSub Θ Wq Y (max m3 m2 + 1) :=
            .trans (htail.mono (Nat.le_max_left m3 m2))
                   (hWY.mono (Nat.le_max_right m3 m2))
          cases Y with
          | top => trivial
          | single _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | bot => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
          | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓq, Wq, hcq, hEq, _, by omega, tl⟩)
        · exact absurd hX (by intro h; cases h)
    | tsel r B =>
      have hrb : Path.LocsBelow manchor r := by
        have hb := (hwf hE).2
        exact (Ty.locsBelow_rename.mp hb.2.1 : Ty.LocsBelow manchor (.tsel r B))
      have o1 := IH m1 hm1 hXW
      have o2 := IH m2 hm2 hWY
      cases X with
      | bot => trivial
      | top =>
        obtain ⟨mq, ℓw, W', hcr, hE', m3, hm3, tail1⟩ := o1
        have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
        cases Y with
        | top => trivial
        | tsel y C =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
            exact ⟨mq, ℓw, W', (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tail1⟩
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
            exact ⟨mq2, ℓ2', W2, hc2, hE2, _, by omega,
              .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩
        | single s =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | bot =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | arrow S' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTm S' a' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTy S' A' T1' T2' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
      | single p =>
        rcases o1 with ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ |
          ⟨mq, ℓw, W', hcr, hE', p', hpe', m3, hm3, tail1⟩
        · -- o1 = unfold: raw-compose the entry tail with the raw right arg
          cases Y with
          | top => trivial
          | tsel y C =>
            exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega,
              .trans (tailE.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩
          | single s =>
            -- invert the entry tail (fuel ≤ k), det-unify, recurse: (shaped, single) = False
            have oE := IH m3 (by omega) tailE
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases (hwf hE0).1 with
              | arrow =>
                obtain ⟨mqE, ℓwE, WE, hcrE, hEE, m4, hm4, tailE2⟩ := oE
                cases hcrE.deterministic hcr'
                cases alias_unify hEE hE''
                exact ((IHa mq' (Chains.target_lt hwf hcrE hrb) hEE tailE2 tail2
                  (by omega) (by omega) : SOut _ _ _ _) : False).elim
              | pair_tm =>
                obtain ⟨mqE, ℓwE, WE, hcrE, hEE, m4, hm4, tailE2⟩ := oE
                cases hcrE.deterministic hcr'
                cases alias_unify hEE hE''
                exact ((IHa mq' (Chains.target_lt hwf hcrE hrb) hEE tailE2 tail2
                  (by omega) (by omega) : SOut _ _ _ _) : False).elim
              | pair_ty =>
                obtain ⟨mqE, ℓwE, WE, hcrE, hEE, m4, hm4, tailE2⟩ := oE
                cases hcrE.deterministic hcr'
                cases alias_unify hEE hE''
                exact ((IHa mq' (Chains.target_lt hwf hcrE hrb) hEE tailE2 tail2
                  (by omega) (by omega) : SOut _ _ _ _) : False).elim
            · cases hYeq
          | bot =>
            exact ⟨ℓ0, E, hcp, hE0, _, by omega,
              .trans (tailE.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩
          | arrow S' T' =>
            exact ⟨ℓ0, E, hcp, hE0, _, by omega,
              .trans (tailE.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩
          | pairTm S' a' T' =>
            exact ⟨ℓ0, E, hcp, hE0, _, by omega,
              .trans (tailE.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩
          | pairTy S' A' T1' T2' =>
            exact ⟨ℓ0, E, hcp, hE0, _, by omega,
              .trans (tailE.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩
        · -- o1 = RHS-anchored at r (subject transported by PEq p p')
          have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
          cases Y with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
              exact Or.inr ⟨mq, ℓw, W', (hpe2.chains_iff mq).mp hcr, hE',
                p', hpe', m3, by omega, tail1⟩
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
              exact Or.inr ⟨mq2, ℓ2', W2, hc2, hE2, p, .refl, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩
          | single s =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
          | bot =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
          | arrow S' T' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
          | pairTm S' a' T' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
          | pairTy S' A' T1' T2' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · cases hYeq
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact SOut.peq_subject hpe'
                (IHa mq hlt hE' tail1 tail2 (by omega) (by omega)) (Nat.le_refl _)
            · cases hYeq
      | tsel q0 A0 =>
        rcases o1 with ⟨r', hReq, hpe0⟩ |
          ⟨mq0, ℓw0, W0, hcq0, hE0', m3, hm3, tailA⟩ |
          ⟨p2, A2, mq, ℓw, W', hReq, hcr, hE', m3, hm3, tailB⟩
        · -- o1 congruent: PEq q0 r (and B = A0)
          cases hReq
          cases Y with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | single s =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | bot =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | arrow S' T' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | pairTm S' a' T' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | pairTy S' A' T1' T2' =>
            rcases o2 with ⟨p2, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inl ⟨p2, hYeq, hpe0.trans hpe2⟩
            · exact Or.inr (Or.inl ⟨mq', ℓw', W'',
                (hpe0.chains_iff mq').mpr hcr', hE'', m5, by omega, tail2⟩)
            · exact Or.inr (Or.inr ⟨p2, A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
        · -- o1 LHS-anchored at q0: uniform raw composition, o2 untouched
          cases Y with
          | top => trivial
          | tsel y C =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
          | single s =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
          | bot =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
          | arrow S' T' =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
          | pairTm S' a' T' =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
          | pairTy S' A' T1' T2' =>
            exact Or.inr (Or.inl ⟨mq0, ℓw0, W0, hcq0, hE0', _, by omega,
              .trans (tailA.mono (Nat.le_max_left _ _)) (hWY.mono (Nat.le_max_right _ _))⟩)
        · -- o1 RHS-anchored at r
          cases hReq
          have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
          cases Y with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | single s =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | bot =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | arrow S' T' =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | pairTm S' a' T' =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
          | pairTy S' A' T1' T2' =>
            rcases o2 with ⟨p2', hYeq, hpe2⟩ |
              ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
              ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
            · exact Or.inr (Or.inr ⟨p2', _, mq, ℓw, W', hYeq,
                (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tailB⟩)
            · cases hcr.deterministic hcr'
              cases alias_unify hE' hE''
              exact IHa mq hlt hE' tailB tail2 (by omega) (by omega)
            · exact Or.inr (Or.inr ⟨p2', A2', mq2, ℓ2', W2, hYeq, hc2, hE2, _, by omega,
                .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩)
      | arrow S1 T1 =>
        obtain ⟨mq, ℓw, W', hcr, hE', m3, hm3, tail1⟩ := o1
        have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
        cases Y with
        | top => trivial
        | tsel y C =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
            exact ⟨mq, ℓw, W', (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tail1⟩
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
            exact ⟨mq2, ℓ2', W2, hc2, hE2, _, by omega,
              .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩
        | single s =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | bot =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | arrow S' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTm S' a' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTy S' A' T1' T2' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
      | pairTm S1 a1 T1 =>
        obtain ⟨mq, ℓw, W', hcr, hE', m3, hm3, tail1⟩ := o1
        have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
        cases Y with
        | top => trivial
        | tsel y C =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
            exact ⟨mq, ℓw, W', (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tail1⟩
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
            exact ⟨mq2, ℓ2', W2, hc2, hE2, _, by omega,
              .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩
        | single s =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | bot =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | arrow S' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTm S' a' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTy S' A' T1' T2' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
      | pairTy S1 A1 T11 T12 =>
        obtain ⟨mq, ℓw, W', hcr, hE', m3, hm3, tail1⟩ := o1
        have hlt : mq < manchor := Chains.target_lt hwf hcr hrb
        cases Y with
        | top => trivial
        | tsel y C =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
            exact ⟨mq, ℓw, W', (hpe2.chains_iff mq).mp hcr, hE', m3, by omega, tail1⟩
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
            exact ⟨mq2, ℓ2', W2, hc2, hE2, _, by omega,
              .trans (hXW.mono (Nat.le_max_left _ _)) (tail2.mono (Nat.le_max_right _ _))⟩
        | single s =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | bot =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | arrow S' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTm S' a' T' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq
        | pairTy S' A' T1' T2' =>
          rcases o2 with ⟨p2, hYeq, hpe2⟩ |
            ⟨mq', ℓw', W'', hcr', hE'', m5, hm5, tail2⟩ |
            ⟨p2, A2, mq2, ℓ2', W2, hYeq, hc2, hE2, m5, hm5, tail2⟩
          · cases hYeq
          · cases hcr.deterministic hcr'
            cases alias_unify hE' hE''
            exact IHa mq hlt hE' tail1 tail2 (by omega) (by omega)
          · cases hYeq

/-- The sized inversion theorem: every sized runtime subtyping fact
reads off as its shape-directed store content. -/
theorem SSub.invert {Θ : Sto} (hwf : Sto.Shaped Θ) :
    ∀ (n : Nat) {T1 T2 : Ty 0}, SSub Θ T1 T2 n -> SOut Θ n T1 T2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro T1 T2 hs
    cases hs with
    | refl =>
      rename_i k
      cases T1 with
      | single p => exact .refl
      | pairTm S a T => exact ⟨rfl, ⟨1, by omega, .refl⟩, .refl⟩
      | pairTy S A T1 T2 => exact ⟨rfl, ⟨1, by omega, .refl⟩, .refl, .refl⟩
      | arrow S T => exact ⟨⟨1, by omega, .refl⟩, .refl⟩
      | tsel q A => exact Or.inl ⟨q, rfl, .refl⟩
      | top => trivial
      | bot => trivial
    | bot => trivial
    | top =>
      rename_i k
      cases T1 <;> simp only [SOut] <;> trivial
    | var_free hl =>
      rename_i ℓ T k
      rw [Ty.fromClosed_zero]
      cases (hwf hl).1 with
      | arrow =>
        exact ⟨ℓ, _, .loc hl, hl, 1, by omega, .refl⟩
      | pair_tm =>
        exact ⟨ℓ, _, .loc hl, hl, 1, by omega, .refl⟩
      | pair_ty =>
        exact ⟨ℓ, _, .loc hl, hl, 1, by omega, .refl⟩
    | symm hw h =>
      rename_i p q k
      exact (IH k (by omega) h).symm
    | sel_tm_loc hc hl =>
      rename_i p m0 S a ℓ2 k
      have hlt : m0 < Θ.length := (List.getElem?_eq_some_iff.mp hl).1
      have hb := (hwf hl).2
      simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow, Ty.weaken,
        Ty.rename, Path.rename, Var.rename] at hb
      obtain ⟨E2, hE2⟩ := Sto.lookup_lt (show ℓ2 < Θ.length by omega)
      exact .cochain (.sel hc hl) (.loc hE2)
    | sel_hi_loc hc hl h =>
      rename_i p m0 ℓ1 A W k
      rw [Ty.fromClosed_zero] at h
      cases T2 <;> simp only [SOut]
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
      · exact Or.inr (Or.inl ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩)
    | sel_lo_loc hc hl h =>
      rename_i p m0 ℓ1 A W k
      rw [Ty.fromClosed_zero] at h
      cases T1 with
      | single u =>
        exact Or.inr ⟨m0, ℓ1, W, hc, hl, u, .refl, k, by omega, h⟩
      | pairTm S a T => exact ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩
      | pairTy S A T1 T2 => exact ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩
      | arrow S T => exact ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩
      | tsel u B =>
        exact Or.inr (Or.inr ⟨p, _, m0, ℓ1, W, rfl, hc, hl, k, by omega, h⟩)
      | top => exact ⟨m0, ℓ1, W, hc, hl, k, by omega, h⟩
      | bot => trivial
    | skip_tm_loc hc hl hne =>
      exact .skip_tm hc hl hne
    | skip_ty_loc hc hl =>
      exact .skip_ty hc hl
    | arrow h1 h2 =>
      rename_i S' S k T T'
      exact ⟨⟨k, by omega, h1⟩, h2⟩
    | pair_tm h1 h2 =>
      rename_i S S' k T T' a
      exact ⟨rfl, ⟨k, by omega, h1⟩, h2⟩
    | pair_ty h1 h2 h3 =>
      rename_i S S' k T1' T1 T2 T2' A
      exact ⟨rfl, ⟨k, by omega, h1⟩, h2, h3⟩
    | repl hwp hwq h1 h2 =>
      rename_i p q k T0
      have hpe : PEq Θ p q := IH k (by omega) h1
      cases T0 with
      | top => simp only [Ty.open, Ty.subst, SOut]
      | bot => simp only [Ty.open, Ty.subst, SOut]
      | single r =>
        simp only [Ty.open, Ty.subst, SOut]
        exact .congr hwp hwq hpe
      | tsel r B =>
        simp only [Ty.open, Ty.subst, SOut]
        exact Or.inl ⟨_, rfl, .congr hwp hwq hpe⟩
      | arrow S0 T0' =>
        simp only [Ty.open, Ty.subst, SOut]
        refine ⟨⟨k + 1, by omega, .repl hwq hwp h2 h1⟩, ?_⟩
        have hreplT : Sub Θ (Ctx.empty.push (Ty.open S0 q))
            (.ty ((T0'.rename Rename.swap).open (p.rename Rename.succ)))
            (.ty ((T0'.rename Rename.swap).open (q.rename Rename.succ))) :=
          Sub.repl hwp.weaken hwq.weaken
            (SSub.to_sub h1).weaken (SSub.to_sub h2).weaken
        rw [Ty.swap_open_weaken, Ty.swap_open_weaken] at hreplT
        exact hreplT
      | pairTm S0 b T0' =>
        simp only [Ty.open, Ty.subst, SOut]
        refine ⟨by trivial, ⟨k + 1, by omega, .repl hwp hwq h1 h2⟩, ?_⟩
        have hreplT : Sub Θ (Ctx.empty.push (Ty.open S0 p))
            (.ty ((T0'.rename Rename.swap).open (p.rename Rename.succ)))
            (.ty ((T0'.rename Rename.swap).open (q.rename Rename.succ))) :=
          Sub.repl hwp.weaken hwq.weaken
            (SSub.to_sub h1).weaken (SSub.to_sub h2).weaken
        rw [Ty.swap_open_weaken, Ty.swap_open_weaken] at hreplT
        exact hreplT
      | pairTy S0 B T01 T02 =>
        simp only [Ty.open, Ty.subst, SOut]
        refine ⟨by trivial, ⟨k + 1, by omega, .repl hwp hwq h1 h2⟩, ?_, ?_⟩
        · have hreplT : Sub Θ (Ctx.empty.push (Ty.open S0 p))
              (.ty ((T01.rename Rename.swap).open (q.rename Rename.succ)))
              (.ty ((T01.rename Rename.swap).open (p.rename Rename.succ))) :=
            Sub.repl hwq.weaken hwp.weaken
              (SSub.to_sub h2).weaken (SSub.to_sub h1).weaken
          rw [Ty.swap_open_weaken, Ty.swap_open_weaken] at hreplT
          exact hreplT
        · have hreplT : Sub Θ (Ctx.empty.push (Ty.open S0 p))
              (.ty ((T02.rename Rename.swap).open (p.rename Rename.succ)))
              (.ty ((T02.rename Rename.swap).open (q.rename Rename.succ))) :=
            Sub.repl hwp.weaken hwq.weaken
              (SSub.to_sub h1).weaken (SSub.to_sub h2).weaken
          rw [Ty.swap_open_weaken, Ty.swap_open_weaken] at hreplT
          exact hreplT
    | fst_tm h =>
      rename_i p a T k
      obtain ⟨ℓ0, E0, hcp, hE0, m1, hm1, hres⟩ := IH k (by omega) h
      cases (hwf hE0).1 with
      | arrow => exact ((IH m1 (by omega) hres : SOut _ _ _ _) : False).elim
      | pair_ty => exact ((IH m1 (by omega) hres : SOut _ _ _ _) : False).elim
      | pair_tm =>
        rename_i ℓ1 b ℓ2
        obtain ⟨hba, ⟨m2, hm2, hdom⟩, -⟩ := IH m1 (by omega) hres
        have hcf : Chains Θ p.fst ℓ1 := .fst_tm hcp hE0
        obtain ⟨E1, hE1⟩ := hcf.in_dom hwf
        have oS := IH m2 (by omega) hdom
        exact oS.peq_subject (.cochain hcf (.loc hE1)) (by omega)
    | fst_ty h =>
      rename_i p A T1c T2c k
      obtain ⟨ℓ0, E0, hcp, hE0, m1, hm1, hres⟩ := IH k (by omega) h
      cases (hwf hE0).1 with
      | arrow => exact ((IH m1 (by omega) hres : SOut _ _ _ _) : False).elim
      | pair_tm => exact ((IH m1 (by omega) hres : SOut _ _ _ _) : False).elim
      | pair_ty =>
        rename_i ℓ1 B W0
        obtain ⟨hBA, ⟨m2, hm2, hdom⟩, -, -⟩ := IH m1 (by omega) hres
        have hcf : Chains Θ p.fst ℓ1 := .fst_ty hcp hE0
        obtain ⟨E1, hE1⟩ := hcf.in_dom hwf
        have oS := IH m2 (by omega) hdom
        exact oS.peq_subject (.cochain hcf (.loc hE1)) (by omega)
    | trans h1 h2 =>
      rename_i M k
      have o1 := IH k (by omega) h1
      have o2 := IH k (by omega) h2
      have IHd : ∀ j, j ≤ k → ∀ {A B : Ty 0}, SSub Θ A B j → SOut Θ j A B :=
        fun j hj {A B} h => IH j (by omega) h
      cases T1 with
      | bot => trivial
      | top =>
        cases M with
        | top => exact o2.mono (by omega)
        | bot => exact o1.elim
        | single _ => exact o1.elim
        | arrow _ _ => exact o1.elim
        | pairTm _ _ _ => exact o1.elim
        | pairTy _ _ _ _ => exact o1.elim
        | tsel q A =>
          obtain ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailT⟩ := o1
          cases T2 with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq, ℓw, W, (hpe.chains_iff mq).mp hcq, hEw, m3, by omega, tailT⟩
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq2, ℓ22, W2, hc2, hE2, _, by omega,
                .trans (h1.mono (Nat.le_max_left k m4))
                       (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ | ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | bot =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ | ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | arrow _ _ =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ | ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTm _ _ _ =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ | ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTy _ _ _ _ =>
            rcases o2 with ⟨p2, hYeq, hpe⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ | ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailT tail2 (by omega) (by omega)
            · exact nomatch hYeq
      | single p =>
        cases M with
        | single p0 => exact o2.peq_subject o1 (by omega)
        | top =>
          cases T2 with
          | top => trivial
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, hW⟩ := o2
            exact Or.inr ⟨my, ℓy, Wy, hcy, hEy, p, .refl, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (hW.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | bot =>
          obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, hEbot⟩ := o1
          have oE := IHd m3 (by omega) hEbot
          rcases (hwf hE0).1 with hs | hs | hs
          all_goals exact (oE : False).elim
        | arrow S0 T0 =>
          obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
          have tl : SSub Θ E T2 (max m3 k + 1) :=
            .trans (tailE.mono (Nat.le_max_left m3 k))
                   (h2.mono (Nat.le_max_right m3 k))
          cases T2 with
          | top => trivial
          | single s => exact o2.elim
          | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTm S0 a0 T0 =>
          obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
          have tl : SSub Θ E T2 (max m3 k + 1) :=
            .trans (tailE.mono (Nat.le_max_left m3 k))
                   (h2.mono (Nat.le_max_right m3 k))
          cases T2 with
          | top => trivial
          | single s => exact o2.elim
          | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | pairTy S0 A0 T01 T02 =>
          obtain ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ := o1
          have tl : SSub Θ E T2 (max m3 k + 1) :=
            .trans (tailE.mono (Nat.le_max_left m3 k))
                   (h2.mono (Nat.le_max_right m3 k))
          cases T2 with
          | top => trivial
          | single s => exact o2.elim
          | bot => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | arrow _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTm _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | pairTy _ _ _ _ => exact ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
          | tsel _ _ => exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega, tl⟩
        | tsel q A =>
          rcases o1 with ⟨ℓ0, E, hcp, hE0, m3, hm3, tailE⟩ |
            ⟨mq, ℓw, W, hcq, hEw, p', hpe', m3, hm3, tailW⟩
          · cases T2 with
            | top => trivial
            | tsel y C =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inl ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
            | single s =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · have oE := IHd m3 (by omega) tailE
                rcases (hwf hE0).1 with hs | hs | hs <;>
                  (obtain ⟨mq'', ℓw'', W'', hcq'', hEw'', m5, hm5, tail3⟩ := oE
                   cases hcq''.deterministic hcq'
                   cases alias_unify hEw'' hEw'
                   exact ((SSub.descend hwf IHd mq' hEw' tail3 tail2
                     (by omega) (by omega) : SOut _ _ _ _) : False).elim)
              · exact nomatch hYeq
            | bot =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · exact nomatch hYeq
            | arrow _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · exact nomatch hYeq
            | pairTm _ _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · exact nomatch hYeq
            | pairTy _ _ _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact ⟨ℓ0, E, hcp, hE0, _, by omega,
                  .trans (tailE.mono (Nat.le_max_left m3 k))
                         (h2.mono (Nat.le_max_right m3 k))⟩
              · exact nomatch hYeq
          · cases T2 with
            | top => trivial
            | tsel y C =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inr ⟨mq, ℓw, W, (hpe2.chains_iff mq).mp hcq, hEw,
                  p', hpe', m3, by omega, tailW⟩
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inr ⟨mq2, ℓ22, W2, hc2, hE2, p, .refl, _, by omega,
                  .trans (h1.mono (Nat.le_max_left k m4))
                         (tail2.mono (Nat.le_max_right k m4))⟩
            | single s =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · exact nomatch hYeq
            | bot =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · exact nomatch hYeq
            | arrow _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · exact nomatch hYeq
            | pairTm _ _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · exact nomatch hYeq
            | pairTy _ _ _ _ =>
              rcases o2 with ⟨p2, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p2, A2, mq2, ℓ22, W2, hYeq, hc2, hE2, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hcq'.deterministic hcq
                cases alias_unify hEw' hEw
                exact (SSub.descend hwf IHd mq hEw tailW tail2
                  (by omega) (by omega)).peq_subject hpe' (Nat.le_refl _)
              · exact nomatch hYeq
      | tsel q A =>
        cases M with
        | top =>
          cases T2 with
          | top => trivial
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, hW⟩ := o2
            exact Or.inr (Or.inr ⟨y, C, my, ℓy, Wy, rfl, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (hW.mono (Nat.le_max_right k m4))⟩)
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | single w =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · exact nomatch hMeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · exact nomatch hMeq
        | bot =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · exact nomatch hMeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · exact nomatch hMeq
        | arrow _ _ =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · exact nomatch hMeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · exact nomatch hMeq
        | pairTm _ _ _ =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · exact nomatch hMeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · exact nomatch hMeq
        | pairTy _ _ _ _ =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · exact nomatch hMeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · exact nomatch hMeq
        | tsel qM AM =>
          rcases o1 with ⟨p2, hMeq, hpe⟩ |
            ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ |
            ⟨p2, A2, mq2, ℓ22, W2, hMeq, hc2, hE2, m3, hm3, tailM⟩
          · cases hMeq
            cases T2 with
            | top => trivial
            | tsel y C =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inl ⟨_, rfl, hpe.trans hpe2⟩
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inr (Or.inr ⟨_, _, mq3, ℓ33, W3, rfl, hc3, hE3,
                  _, by omega, .trans (h1.mono (Nat.le_max_left k m4))
                                      (tail2.mono (Nat.le_max_right k m4))⟩)
            | single _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · exact nomatch hYeq
            | bot =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · exact nomatch hYeq
            | arrow _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · exact nomatch hYeq
            | pairTm _ _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · exact nomatch hYeq
            | pairTy _ _ _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · exact Or.inr (Or.inl ⟨mq', ℓw', W',
                  (hpe.chains_iff mq').mpr hcq', hEw', m4, by omega, tail2⟩)
              · exact nomatch hYeq
          · cases T2 with
            | top => trivial
            | single _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | bot => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | arrow _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTm _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | pairTy _ _ _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
            | tsel _ _ => exact Or.inr (Or.inl ⟨mq, ℓw, W, hcq, hEw, _, by omega,
                .trans (tailW.mono (Nat.le_max_left m3 k))
                       (h2.mono (Nat.le_max_right m3 k))⟩)
          · cases hMeq
            cases T2 with
            | top => trivial
            | tsel y C =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inr (Or.inr ⟨_, _, mq2, ℓ22, W2, rfl,
                  (hpe2.chains_iff mq2).mp hc2, hE2, m3, by omega, tailM⟩)
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · injection hYeq with hs0 hy hC
                subst hy; subst hC
                exact Or.inr (Or.inr ⟨_, _, mq3, ℓ33, W3, rfl, hc3, hE3,
                  _, by omega, .trans (h1.mono (Nat.le_max_left k m4))
                                      (tail2.mono (Nat.le_max_right k m4))⟩)
            | single _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · exact nomatch hYeq
            | bot =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · exact nomatch hYeq
            | arrow _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · exact nomatch hYeq
            | pairTm _ _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · exact nomatch hYeq
            | pairTy _ _ _ _ =>
              rcases o2 with ⟨p3, hYeq, hpe2⟩ |
                ⟨mq2', ℓ22', W2', hc2', hE2', m4, hm4, tail2⟩ |
                ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
              · exact nomatch hYeq
              · cases hc2'.deterministic hc2
                cases alias_unify hE2' hE2
                exact SSub.descend hwf IHd mq2 hE2 tailM tail2 (by omega) (by omega)
              · exact nomatch hYeq
      | arrow S T =>
        cases M with
        | bot => exact o1.elim
        | single _ => exact o1.elim
        | pairTm _ _ _ => exact o1.elim
        | pairTy _ _ _ _ => exact o1.elim
        | top =>
          cases T2 with
          | top => trivial
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, hW⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (hW.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | arrow S0 T0 =>
          obtain ⟨⟨m3, hm3, dom1⟩, res1⟩ := o1
          cases T2 with
          | top => trivial
          | arrow S' T' =>
            obtain ⟨⟨m4, hm4, dom2⟩, res2⟩ := o2
            exact ⟨⟨_, by omega, .trans (dom2.mono (Nat.le_max_left m4 m3))
              (dom1.mono (Nat.le_max_right m4 m3))⟩,
              .trans (res1.narrow dom2.to_sub) res2⟩
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | tsel q' A' =>
          obtain ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ := o1
          cases T2 with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq, ℓw, W, (hpe2.chains_iff mq).mp hcq, hEw, m3, by omega, tailW⟩
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq3, ℓ33, W3, hc3, hE3, _, by omega,
                .trans (h1.mono (Nat.le_max_left k m4))
                       (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | bot =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | arrow _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTm _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTy _ _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
      | pairTm S a T =>
        cases M with
        | bot => exact o1.elim
        | single _ => exact o1.elim
        | arrow _ _ => exact o1.elim
        | pairTy _ _ _ _ => exact o1.elim
        | top =>
          cases T2 with
          | top => trivial
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, hW⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (hW.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | pairTm S0 a0 T0 =>
          obtain ⟨ha0, ⟨m3, hm3, dom1⟩, res1⟩ := o1
          cases T2 with
          | top => trivial
          | pairTm S' a' T' =>
            obtain ⟨ha1, ⟨m4, hm4, dom2⟩, res2⟩ := o2
            exact ⟨ha0.trans ha1, ⟨_, by omega,
              .trans (dom1.mono (Nat.le_max_left m3 m4))
                     (dom2.mono (Nat.le_max_right m3 m4))⟩,
              .trans res1 (res2.narrow dom1.to_sub)⟩
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | tsel q' A' =>
          obtain ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ := o1
          cases T2 with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq, ℓw, W, (hpe2.chains_iff mq).mp hcq, hEw, m3, by omega, tailW⟩
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq3, ℓ33, W3, hc3, hE3, _, by omega,
                .trans (h1.mono (Nat.le_max_left k m4))
                       (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | bot =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | arrow _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTm _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTy _ _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
      | pairTy S A T1c T2c =>
        cases M with
        | bot => exact o1.elim
        | single _ => exact o1.elim
        | arrow _ _ => exact o1.elim
        | pairTm _ _ _ => exact o1.elim
        | top =>
          cases T2 with
          | top => trivial
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, hW⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (hW.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
          | pairTy _ _ _ _ => exact o2.elim
        | pairTy S0 A0 T01 T02 =>
          obtain ⟨hA0, ⟨m3, hm3, dom1⟩, lo1, hi1⟩ := o1
          cases T2 with
          | top => trivial
          | pairTy S' A' T1' T2' =>
            obtain ⟨hA1, ⟨m4, hm4, dom2⟩, lo2, hi2⟩ := o2
            exact ⟨hA0.trans hA1, ⟨_, by omega,
              .trans (dom1.mono (Nat.le_max_left m3 m4))
                     (dom2.mono (Nat.le_max_right m3 m4))⟩,
              .trans (lo2.narrow dom1.to_sub) lo1,
              .trans hi1 (hi2.narrow dom1.to_sub)⟩
          | tsel y C =>
            obtain ⟨my, ℓy, Wy, hcy, hEy, m4, hm4, tail2⟩ := o2
            exact ⟨my, ℓy, Wy, hcy, hEy, _, by omega,
              .trans (h1.mono (Nat.le_max_left k m4))
                     (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ => exact o2.elim
          | bot => exact o2.elim
          | arrow _ _ => exact o2.elim
          | pairTm _ _ _ => exact o2.elim
        | tsel q' A' =>
          obtain ⟨mq, ℓw, W, hcq, hEw, m3, hm3, tailW⟩ := o1
          cases T2 with
          | top => trivial
          | tsel y C =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq, ℓw, W, (hpe2.chains_iff mq).mp hcq, hEw, m3, by omega, tailW⟩
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · injection hYeq with hs0 hy hC
              subst hy; subst hC
              exact ⟨mq3, ℓ33, W3, hc3, hE3, _, by omega,
                .trans (h1.mono (Nat.le_max_left k m4))
                       (tail2.mono (Nat.le_max_right k m4))⟩
          | single _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | bot =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | arrow _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTm _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq
          | pairTy _ _ _ _ =>
            rcases o2 with ⟨p3, hYeq, hpe2⟩ |
              ⟨mq', ℓw', W', hcq', hEw', m4, hm4, tail2⟩ |
              ⟨p3, A3, mq3, ℓ33, W3, hYeq, hc3, hE3, m4, hm4, tail2⟩
            · exact nomatch hYeq
            · cases hcq'.deterministic hcq
              cases alias_unify hEw' hEw
              exact SSub.descend hwf IHd mq hEw tailW tail2 (by omega) (by omega)
            · exact nomatch hYeq


#print axioms LambdaP.SSub.invert

end LambdaP
