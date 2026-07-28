import LambdaP.Typing

/-!
Operational semantics of λ_p: a heap of closed values addressed by
locations (`Var.free`), big-step path evaluation, and a small-step
reduction with a single `let`-congruence rule.

This realizes the paper's store-context semantics without a CK machine:
MNF means `let` is the only evaluation context, and the paper's
`e p | x e | e.a | e.1` contexts are subsumed by big-step path evaluation
(stored pairs hold only locations, so path lookup is structural — see
DESIGN.md, Decision 2). Allocation appends to the heap and never renames
anything.

Rule correspondence with the paper (`pdt-eval.tex`):
- (apply)          → `Step.apply` (paths resolved big-step)
- (fst), (snd)     → `PathEval.fst_tm/fst_ty/sel`
- (rename)         → `Step.let_path` (fused with path resolution)
- (lift)           → `Step.let_val` (allocation)
- (ascribe)        → `Step.ascribe`
- store/eval ctxs  → `Step.let_ctx` + big-step `PathEval`
-/

namespace LambdaP

/-- A heap: the `ℓ`-th entry is the closed value stored at location `ℓ`. -/
abbrev Heap : Type := List (Tm 0)

/-- Heap lookup. -/
def Heap.Lookup (h : Heap) (ℓ : Nat) (v : Tm 0) : Prop := h[ℓ]? = some v

/-- Big-step path evaluation: `PathEval h p ℓ` resolves the path `p` to the
heap location `ℓ`. Structural in `p` because stored pair components are
always locations. -/
inductive PathEval (h : Heap) : Path 0 -> Nat -> Prop where
/-- A location evaluates to itself. -/
| var :
  PathEval h (.var (.free ℓ)) ℓ
/-- First projection of a stored term-member pair. -/
| fst_tm :
  PathEval h p ℓ ->
  Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) ->
  PathEval h p.fst ℓ1
/-- First projection of a stored type-member pair. -/
| fst_ty :
  PathEval h p ℓ ->
  Heap.Lookup h ℓ (.pairTy (.free ℓ1) A T) ->
  PathEval h p.fst ℓ1
/-- Selection of a term member (the paper's (snd) rule). -/
| sel :
  PathEval h p ℓ ->
  Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) ->
  PathEval h (p.sel a) ℓ2
/-- Selection skips a term member with a different label: records are
nested pairs, so the member is found in the first component. -/
| sel_skip_tm :
  PathEval h p ℓ ->
  Heap.Lookup h ℓ (.pairTm (.free ℓ1) b (.free ℓ2)) ->
  a ≠ b ->
  PathEval h ((Path.fst p).sel a) m ->
  PathEval h (p.sel a) m
/-- Selection skips a type member. -/
| sel_skip_ty :
  PathEval h p ℓ ->
  Heap.Lookup h ℓ (.pairTy (.free ℓ1) B T) ->
  PathEval h ((Path.fst p).sel a) m ->
  PathEval h (p.sel a) m

/-- Small-step reduction on heap/term configurations. -/
inductive Step : Heap -> Tm 0 -> Heap -> Tm 0 -> Prop where
/-- β-reduction; function and argument positions resolve big-step. -/
| apply :
  PathEval h p ℓf ->
  PathEval h q ℓa ->
  Heap.Lookup h ℓf (.abs T t) ->
  Step h (.app p q) h (t.open (.free ℓa))
/-- A path in tail position resolves to its location. -/
| path :
  PathEval h p ℓ ->
  p ≠ .var (.free ℓ) ->
  Step h (.path p) h (.path (.var (.free ℓ)))
/-- The paper's (rename), fused with path resolution. -/
| let_path :
  PathEval h p ℓ ->
  Step h (.letin (.path p) t) h (t.open (.free ℓ))
/-- The paper's (lift): allocate the value, continue with the fresh location. -/
| let_val :
  Tm.IsValue v ->
  Step h (.letin v t) (h ++ [v]) (t.open (.free h.length))
/-- Congruence under the let context. -/
| let_ctx :
  Step h t1 h' t1' ->
  Step h (.letin t1 t2) h' (.letin t1' t2)
/-- Ascriptions evaluate their body. -/
| ascribe :
  Step h (.typed t T) h t

/-- Reflexive-transitive closure of `Step`. -/
inductive Reduce : Heap -> Tm 0 -> Heap -> Tm 0 -> Prop where
| refl : Reduce h t h t
| step :
  Step h1 t1 h2 t2 ->
  Reduce h2 t2 h3 t3 ->
  Reduce h1 t1 h3 t3

/-- Final configurations: values and locations (the paper's results `r`). -/
inductive Final : Tm 0 -> Prop where
| val : Tm.IsValue v -> Final v
| loc : Final (.path (.var (.free ℓ)))

/-! ### Heap acyclicity

Pair values store variables and allocation proceeds in order, so every
stored value mentions only strictly earlier locations. This gives λ_p
heaps a well-founded structure (unlike DOT's cyclic object stores) on
which the semantic denotation recurses. -/

/-- All free locations mentioned are strictly below `k`. -/
def Var.LocsBelow (k : Nat) : Var s -> Prop
| .bound _ => True
| .free ℓ => ℓ < k

def Path.LocsBelow (k : Nat) : Path s -> Prop
| .var x => x.LocsBelow k
| .fst p => p.LocsBelow k
| .sel p _ => p.LocsBelow k

def Ty.LocsBelow (k : Nat) : Ty s -> Prop
| .top => True
| .bot => True
| .arrow S T => S.LocsBelow k ∧ T.LocsBelow k
| .pairTm S _ T => S.LocsBelow k ∧ T.LocsBelow k
| .pairTy S _ T1 T2 => S.LocsBelow k ∧ T1.LocsBelow k ∧ T2.LocsBelow k
| .single p => p.LocsBelow k
| .tsel p _ => p.LocsBelow k

def Tm.LocsBelow (k : Nat) : Tm s -> Prop
| .path p => p.LocsBelow k
| .abs T t => T.LocsBelow k ∧ t.LocsBelow k
| .pairTm y _ z => y.LocsBelow k ∧ z.LocsBelow k
| .pairTy y _ T => y.LocsBelow k ∧ T.LocsBelow k
| .app p q => p.LocsBelow k ∧ q.LocsBelow k
| .letin t1 t2 => t1.LocsBelow k ∧ t2.LocsBelow k
| .typed t T => t.LocsBelow k ∧ T.LocsBelow k

/-- A heap is bounded if each stored value mentions only earlier locations. -/
def Heap.Bounded (h : Heap) : Prop :=
  ∀ {ℓ : Nat} {v : Tm 0}, Heap.Lookup h ℓ v -> v.LocsBelow ℓ

/-- In a bounded heap, path evaluation descends: the target of a path is
strictly below any bound on the path's own locations. -/
theorem PathEval.target_lt {h : Heap} (hb : Heap.Bounded h) {p : Path 0} {m k : Nat}
    (he : PathEval h p m) (hp : p.LocsBelow k) : m < k := by
  induction he with
  | var => exact hp
  | fst_tm _ hl ih => exact Nat.lt_trans (hb hl).1 (ih hp)
  | fst_ty _ hl ih => exact Nat.lt_trans (hb hl).1 (ih hp)
  | sel _ hl ih => exact Nat.lt_trans (hb hl).2 (ih hp)
  | sel_skip_tm _ _ _ _ _ ihs => exact ihs hp
  | sel_skip_ty _ _ _ _ ihs => exact ihs hp

/-! ### Heap typing -/

/-- Precise typing of stored values: λ-abstractions get their declared
function type, pairs get their singleton pair types (as introduced by the
pair typing rules — no subsumption at the top). This precision is what
makes path lookup type-preserving. -/
inductive Val.PreciseTy (Θ : Sto) : Tm 0 -> Ty 0 -> Prop where
| abs :
  Wf Θ .empty (.ty S) ->
  HasType Θ (Ctx.empty.push S) t T ->
  Val.PreciseTy Θ (.abs S t) (.arrow S T)
| pair_tm :
  Path.Wf Θ .empty (.var (.free ℓ1)) ->
  Path.Wf Θ .empty (.var (.free ℓ2)) ->
  Val.PreciseTy Θ (.pairTm (.free ℓ1) a (.free ℓ2))
    (.pairTm (.single (.var (.free ℓ1))) a (Ty.single (.var (.free ℓ2))).weaken)
| pair_ty :
  Path.Wf Θ .empty (.var (.free ℓ1)) ->
  Wf Θ .empty (.ty T) ->
  Val.PreciseTy Θ (.pairTy (.free ℓ1) A T)
    (.pairTy (.single (.var (.free ℓ1))) A T.weaken T.weaken)

/-- A store typing describes a heap: same domain, every location holds a
value of its recorded precise type, and both the value and the type
mention only earlier locations (acyclicity). -/
def HeapTyped (Θ : Sto) (h : Heap) : Prop :=
  Θ.length = h.length ∧
  ∀ {ℓ : Nat} {T : Ty 0}, Sto.Lookup Θ ℓ T ->
    T.LocsBelow ℓ ∧
    ∃ v, Heap.Lookup h ℓ v ∧ v.LocsBelow ℓ ∧ Val.PreciseTy Θ v T

end LambdaP
