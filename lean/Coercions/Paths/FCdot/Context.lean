import Coercions.Paths.FCdot.RenameLemmas

namespace Paths

/-!
# FCdot contexts

A binder is opaque (abstract block) or transparent (block defined by a node
of the block forest).  Transparent binders arise inside object literals and
in store typing.

A transparent binder carries one `Block (s,x)`, whose self is the binder
itself, so its witnesses are written over `(s,x)` exactly as the base's
`Witnesses (s,x)` were, and each child's witnesses are written at the
child's own path.  `Ctx.lookupDef` and `Ctx.lookupFields` read the object
node of that block and answer `none` at a forwarding node, which is the
reading that an alias binder lists no fields of its own.

`Ctx.lookupBlock` follows forwardings, so two names that denote one object
share one block.  The walk is fuel driven in the tree's own idiom: the
budget is the number of forwarding nodes of the context plus one, and a
chain that runs out of budget is cyclic, which makes the name opaque.
-/

namespace FCdot

/-- A binding for a term binder.  The block of a transparent binder lives in
the scope that includes the binder itself. -/
inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s
  | transparent : Ty s → Block (s,x) → Binding s

def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ => T

/-- Forwarding nodes of a binding. -/
def Binding.fwdCount : Binding s → Nat
  | .opaque _ => 0
  | .transparent _ B => B.fwdCount

/-- The binder of a let over a path: typed at the singleton of `q`, and
forwarding to `q` in the forest.  Both readings of the alias are in scope in
the body, the type and the table. -/
def Binding.fwdAt (q : Path s) : Binding s := .transparent (Ty.snglOf q) (.fwd q.weaken)

/-! ### The forwarding targets

The walk spends one unit of fuel exactly when it follows a forwarding node,
and every forwarding node names the path it forwards to.  These lists collect
those paths, one per node, and their length is the count the budget is built
from.  They are what the argument of `Ctx.blockFuel_budget` counts. -/

mutual
/-- The targets of the forwarding nodes of a block. -/
def Block.targets : Block s → List (Path s)
  | .obj _ _ _ ch => ch.targets
  | .fwd q => [q]

/-- The targets of the forwarding nodes of a child list. -/
def Children.targets : Children s → List (Path s)
  | .nil => []
  | .cons ch _ b => ch.targets ++ b.targets
end

mutual
theorem Block.length_targets : ∀ B : Block s, B.targets.length = B.fwdCount
  | .obj _ _ _ ch => Children.length_targets ch
  | .fwd _ => rfl

theorem Children.length_targets : ∀ ch : Children s, ch.targets.length = ch.fwdCount
  | .nil => rfl
  | .cons ch _ b => by
      simp only [Children.targets, Children.fwdCount, List.length_append,
        Children.length_targets ch, Block.length_targets b]
end

mutual
theorem Block.targets_rename {s1 s2 : Sig} :
    ∀ (B : Block s1) (ρ : Rename s1 s2),
      (B.rename ρ).targets = B.targets.map (Path.rename · ρ)
  | .obj _ _ _ ch, ρ => Children.targets_rename ch ρ
  | .fwd _, _ => rfl

theorem Children.targets_rename {s1 s2 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2),
      (ch.rename ρ).targets = ch.targets.map (Path.rename · ρ)
  | .nil, _ => rfl
  | .cons ch _ b, ρ => by
      simp only [Children.rename, Children.targets, List.map_append,
        Children.targets_rename ch ρ, Block.targets_rename b ρ]
end

/-- A child's targets are targets of the list it is read from. -/
theorem Children.at?_targets {s : Sig} :
    ∀ (ch : Children s) (a : Label) (B : Block s),
      ch.at? a = some B → ∀ q ∈ B.targets, q ∈ ch.targets
  | .nil, _, _, h, _, _ => by simp [Children.at?] at h
  | .cons ch ℓ b, a, B, h, q, hq => by
      by_cases hl : a = ℓ
      · obtain rfl : b = B := by simpa [Children.at?, hl] using h
        exact List.mem_append_right _ hq
      · rw [show (Children.cons ch ℓ b).at? a = ch.at? a by simp [Children.at?, hl]] at h
        exact List.mem_append_left _ (Children.at?_targets ch a B h q hq)

/-- The targets of a binding, in the scope that includes the binder itself. -/
def Binding.targets : Binding s → List (Path (s,x))
  | .opaque _ => []
  | .transparent _ B => B.targets

theorem Binding.length_targets (b : Binding s) :
    b.targets.length = b.fwdCount := by
  cases b with
  | «opaque» _ => rfl
  | transparent _ B => exact Block.length_targets B

/-! ### Counting a list against a sharper predicate

Two facts about `List.countP` that core Lean does not state: a predicate that
follows another counts no more, and counts strictly less when one element of
the list separates them. -/

theorem countP_mono {α : Type} {p p' : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = true → p' a = true) → l.countP p ≤ l.countP p'
  | [], _ => by simp
  | a :: l, h => by
      have hih := countP_mono l (fun b hb => h b (List.mem_cons_of_mem a hb))
      have ha := h a (List.mem_cons_self ..)
      simp only [List.countP_cons]
      cases hp : p a with
      | false => simp only [Bool.false_eq_true, if_false]; omega
      | true => rw [ha hp]; simp only [if_true]; omega

theorem countP_lt {α : Type} {p p' : α → Bool} {a : α} :
    ∀ (l : List α), (∀ b ∈ l, p b = true → p' b = true) → a ∈ l →
      p a = false → p' a = true → l.countP p < l.countP p'
  | [], _, ha, _, _ => by simp at ha
  | b :: l, h, ha, hpa, hp'a => by
      have hsub : ∀ c ∈ l, p c = true → p' c = true :=
        fun c hc => h c (List.mem_cons_of_mem b hc)
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hih := countP_mono l hsub
        simp only [List.countP_cons, hpa, hp'a, Bool.false_eq_true, if_false, if_true]
        omega
      · have hih := countP_lt l hsub ha' hpa hp'a
        have hb := h b (List.mem_cons_self ..)
        simp only [List.countP_cons]
        cases hp : p b with
        | false => simp only [Bool.false_eq_true, if_false]; omega
        | true => rw [hb hp]; simp only [if_true]; omega

theorem countP_all {α : Type} {p : α → Bool} :
    ∀ (l : List α) (a : α), a ∈ l → l.countP p = l.length → p a = true
  | [], _, ha, _ => by simp at ha
  | b :: l, a, ha, hc => by
      have hle : l.countP p ≤ l.length := List.countP_le_length
      simp only [List.countP_cons, List.length_cons] at hc
      have hb : p b = true := by
        cases hp : p b with
        | false => simp only [hp, Bool.false_eq_true, if_false] at hc; omega
        | true => rfl
      rw [hb] at hc
      simp only [if_true] at hc
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hb
      · exact countP_all l a ha' (by omega)

inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Binding s → Ctx (s,x)

namespace Ctx

/-- Type of a variable, in the current scope. -/
def lookupTy : Ctx s → BVar s .var → Ty s
  | .cons _ b, .here => b.ty↑
  | .cons Γ _, .there y => (lookupTy Γ y)↑

/-- The block of a binder, weakened through the context spine, `none` at an
opaque binder. -/
def blockAt : Ctx s → BVar s .var → Option (Block s)
  | .cons _ (.transparent _ B), .here => some B
  | .cons _ (.opaque _), .here => none
  | .cons Γ _, .there y => (blockAt Γ y).map Block.weaken

/-- Definition of a block name, if its binder is transparent and its block is
an object node. -/
def lookupDef : Ctx s → BVar s .var → Label → Option (Ty s)
  | .cons _ (.transparent _ (.obj W _ _ _)), .here, ℓ => some (W.get ℓ)
  | .cons _ (.transparent _ (.fwd _)), .here, _ => none
  | .cons _ (.opaque _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Ty.weaken

/-- Field labels of a transparent binder, read off the object node. -/
def lookupFields : Ctx s → BVar s .var → Option (List Label)
  | .cons _ (.transparent _ (.obj _ Fs _ _)), .here => some Fs
  | .cons _ (.transparent _ (.fwd _)), .here => none
  | .cons _ (.opaque _), .here => none
  | .cons Γ _, .there y => lookupFields Γ y

/-- A binder is transparent when it records fields (possibly none). -/
def IsTransparent (Γ : Ctx s) (x : BVar s .var) : Prop := (Γ.lookupFields x).isSome

/-- Every binder is transparent. -/
inductive Transparent : Ctx s → Prop where
  | nil : Transparent .nil
  | cons : Transparent Γ → Transparent (Ctx.cons Γ (.transparent T (.obj W Fs Vs ch)))

/-! ## The walk through the forest -/

/-- Forwarding nodes of the whole context. -/
def fwdCount : Ctx s → Nat
  | .nil => 0
  | .cons Γ b => Γ.fwdCount + b.fwdCount

/-- The budget a following chain can need before it repeats a node. -/
def aliasBudget (Γ : Ctx s) : Nat := Γ.fwdCount + 1

/-- One pass along a path at a fixed budget: `k` is the walk at the next
lower budget, which is what following a forwarding spends. -/
def blockPass (Γ : Ctx s) (k : Path s → Option (Block s)) : Path s → Option (Block s)
  | .var x =>
      match Γ.blockAt x with
      | some (.fwd q) => k q
      | b => b
  | .sel p a =>
      match Γ.blockPass k p with
      | some (.obj _ _ _ ch) =>
          match ch.at? a with
          | some (.fwd q) => k q
          | b => b
      | _ => none

/-- The block of a path, with fuel.  The measure is lexicographic, the fuel
before the depth of the path: a step through a field keeps the budget and
shortens the path, and following a forwarding spends one unit of budget.
The recursion is written as a structural recursion on the fuel whose body is
a structural recursion on the path, which is that order, and it keeps the
walk executable so that `decide` closes examples. -/
def blockFuel (Γ : Ctx s) : Nat → Path s → Option (Block s)
  | 0, _ => none
  | n+1, p => Γ.blockPass (Γ.blockFuel n) p

/-- The block of a path: the walk with the context's own budget.  The result
is never a forwarding node unless the budget ran out, in which case the
following chain is cyclic and the name is opaque. -/
def lookupBlock (Γ : Ctx s) (p : Path s) : Option (Block s) := Γ.blockFuel Γ.aliasBudget p

/-- Definition of the block name `p ∙ ℓ`.  `Ctx.lookupDef` generalized from a
binder to a path. -/
def lookupDefP (Γ : Ctx s) (p : Path s) (ℓ : Label) : Option (Ty s) :=
  match Γ.lookupBlock p with
  | some (.obj W _ _ _) => some (W.get ℓ)
  | _ => none

/-- Field labels of the block of a path. -/
def lookupFieldsP (Γ : Ctx s) (p : Path s) : Option (List Label) :=
  match Γ.lookupBlock p with
  | some (.obj _ Fs _ _) => some Fs
  | _ => none

/-- Stable field labels of the block of a path. -/
def lookupValFieldsP (Γ : Ctx s) (p : Path s) : Option (List Label) :=
  match Γ.lookupBlock p with
  | some (.obj _ _ Vs _) => some Vs
  | _ => none

/-- The block written at `p`: the walk that follows no forwarding.  Its answer
is never a forwarding node.  A path whose walk meets a forwarding, at its
binder or at a child, has no node (decision 24). -/
def nodeBlock (Γ : Ctx s) (p : Path s) : Option (Block s) := Γ.blockPass (fun _ => none) p

/-- The type a root's chain starts at: the binder's declared type at a
variable, the precise type of the node below. -/
def nodeTy (Γ : Ctx s) : Path s → Ty s
  | .var x => Γ.lookupTy x
  | p@(.sel _ _) =>
      match Γ.nodeBlock p with
      | some (.obj W ls vls _) => .obj (Telescope.ofLiteral (W.rename Rename.succ) ls vls)
      | _ => .top

@[simp] theorem nodeTy_var (Γ : Ctx s) (x : BVar s .var) :
    Γ.nodeTy (.var x) = Γ.lookupTy x := rfl

/-! ### The walk, unfolded

The two clauses of the walk that P1.3 writes with a lexicographic measure.
They hold by `rfl` on the structural definition above. -/

@[simp] theorem blockFuel_zero (Γ : Ctx s) (p : Path s) : Γ.blockFuel 0 p = none := rfl

theorem blockFuel_var (Γ : Ctx s) (n : Nat) (x : BVar s .var) :
    Γ.blockFuel (n+1) (.var x) =
      (match Γ.blockAt x with
       | some (.fwd q) => Γ.blockFuel n q
       | b => b) := rfl

theorem blockFuel_sel (Γ : Ctx s) (n : Nat) (p : Path s) (a : Label) :
    Γ.blockFuel (n+1) (.sel p a) =
      (match Γ.blockFuel (n+1) p with
       | some (.obj _ _ _ ch) =>
           (match ch.at? a with
            | some (.fwd q) => Γ.blockFuel n q
            | b => b)
       | _ => none) := rfl

/-! ### Agreement of the two lookups

`Ctx.lookupDef` and `Ctx.lookupFields` read the object node of the binder's
block, so both are the corresponding field of `Ctx.blockAt`.  `lookupDefP` at
a variable path is then `lookupDef` by one unfolding of the walk, whenever
the binder's block is not a forwarding node.  That is every binder of a typed
store, since a value's block is always an object node. -/

theorem lookupDef_eq_blockAt {s : Sig} :
    ∀ (Γ : Ctx s) (x : BVar s .var) (ℓ : Label),
      Γ.lookupDef x ℓ = (Γ.blockAt x).bind (fun B => B.def? ℓ)
  | .cons _ (.transparent _ (.obj _ _ _ _)), .here, _ => rfl
  | .cons _ (.transparent _ (.fwd _)), .here, _ => rfl
  | .cons _ (.opaque _), .here, _ => rfl
  | .cons Γ b, .there y, ℓ => by
      have hd : (Ctx.cons Γ b).lookupDef (.there y) ℓ = (Γ.lookupDef y ℓ).map Ty.weaken := by
        cases b with
        | «opaque» T => rfl
        | transparent T B => cases B <;> rfl
      have hb : (Ctx.cons Γ b).blockAt (.there y) = (Γ.blockAt y).map Block.weaken := by
        cases b with
        | «opaque» T => rfl
        | transparent T B => rfl
      rw [hd, hb, lookupDef_eq_blockAt Γ y ℓ]
      cases Γ.blockAt y with
      | none => rfl
      | some B =>
          cases B <;>
            simp [Block.def?, Block.weaken, Block.rename, Witnesses.get_rename, Ty.weaken]

theorem lookupFields_eq_blockAt {s : Sig} :
    ∀ (Γ : Ctx s) (x : BVar s .var), Γ.lookupFields x = (Γ.blockAt x).bind Block.fields?
  | .cons _ (.transparent _ (.obj _ _ _ _)), .here => rfl
  | .cons _ (.transparent _ (.fwd _)), .here => rfl
  | .cons _ (.opaque _), .here => rfl
  | .cons Γ b, .there y => by
      have hf : (Ctx.cons Γ b).lookupFields (.there y) = Γ.lookupFields y := by
        cases b with
        | «opaque» T => rfl
        | transparent T B => cases B <;> rfl
      have hb : (Ctx.cons Γ b).blockAt (.there y) = (Γ.blockAt y).map Block.weaken := by
        cases b with
        | «opaque» T => rfl
        | transparent T B => rfl
      rw [hf, hb, lookupFields_eq_blockAt Γ y]
      cases Γ.blockAt y with
      | none => rfl
      | some B => cases B <;> rfl

theorem lookupDefP_eq_bind (Γ : Ctx s) (p : Path s) (ℓ : Label) :
    Γ.lookupDefP p ℓ = (Γ.lookupBlock p).bind (fun B => B.def? ℓ) := by
  unfold lookupDefP
  cases Γ.lookupBlock p with
  | none => rfl
  | some B => cases B <;> rfl

theorem lookupBlock_var (Γ : Ctx s) (x : BVar s .var) {B : Block s}
    (h : Γ.blockAt x = some B) (hB : ∀ q, B ≠ .fwd q) : Γ.lookupBlock (.var x) = some B := by
  show Γ.blockFuel (Γ.fwdCount + 1) (.var x) = _
  rw [blockFuel_var, h]
  cases B with
  | obj => rfl
  | fwd q => exact absurd rfl (hB q)

theorem lookupBlock_var_none (Γ : Ctx s) (x : BVar s .var) (h : Γ.blockAt x = none) :
    Γ.lookupBlock (.var x) = none := by
  show Γ.blockFuel (Γ.fwdCount + 1) (.var x) = _
  rw [blockFuel_var, h]

/-- The one-unfolding lemma of P1.9.  At a binder whose block is not a
forwarding node, the path lookup is the base's binder lookup. -/
theorem lookupDefP_var (Γ : Ctx s) (x : BVar s .var) (ℓ : Label)
    (h : ∀ q, Γ.blockAt x ≠ some (.fwd q)) :
    Γ.lookupDefP (.var x) ℓ = Γ.lookupDef x ℓ := by
  rw [lookupDefP_eq_bind, lookupDef_eq_blockAt]
  cases hx : Γ.blockAt x with
  | none => rw [lookupBlock_var_none Γ x hx]
  | some B =>
      cases B with
      | fwd q => exact absurd hx (h q)
      | obj W Fs Vs ch =>
          rw [lookupBlock_var Γ x hx (by intro q hq; cases hq)]

/-- The same for field labels. -/
theorem lookupFieldsP_var (Γ : Ctx s) (x : BVar s .var)
    (h : ∀ q, Γ.blockAt x ≠ some (.fwd q)) :
    Γ.lookupFieldsP (.var x) = Γ.lookupFields x := by
  rw [lookupFields_eq_blockAt]
  unfold lookupFieldsP
  cases hx : Γ.blockAt x with
  | none => rw [lookupBlock_var_none Γ x hx]; rfl
  | some B =>
      cases B with
      | fwd q => exact absurd hx (h q)
      | obj W Fs Vs ch => rw [lookupBlock_var Γ x hx (by intro q hq; cases hq)]; rfl

/-! ### The binder table, unfolded -/

@[simp] theorem blockAt_here_transparent (Γ : Ctx s) (T : Ty s) (B : Block (s,x)) :
    (Γ.cons (.transparent T B)).blockAt .here = some B := rfl

@[simp] theorem blockAt_here_opaque (Γ : Ctx s) (T : Ty s) :
    (Γ.cons (.opaque T)).blockAt .here = none := rfl

@[simp] theorem blockAt_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).blockAt (.there y) = (Γ.blockAt y).map Block.weaken := by
  cases b <;> rfl

/-! ### The walk against more fuel and against a context renaming

Two facts the evidence layer needs.  More fuel never loses an answer, and a
renaming that carries the whole table carries the whole walk, step for step.
Together they say that a block found in one context is found in any context
the table embeds into with at least as much budget. -/

theorem blockPass_mono (Γ : Ctx s) {k k' : Path s → Option (Block s)}
    (hk : ∀ q B, k q = some B → k' q = some B) :
    ∀ (p : Path s) (B : Block s), Γ.blockPass k p = some B → Γ.blockPass k' p = some B
  | .var x, B, h => by
      simp only [blockPass] at h ⊢
      cases hx : Γ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hx] at h ⊢; exact hk q B h
          | obj W ls vls ch => simp only [hx] at h ⊢; exact h
  | .sel p a, B, h => by
      simp only [blockPass] at h ⊢
      cases hp : Γ.blockPass k p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              simp only [blockPass_mono Γ hk p _ hp]
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd q => simp only [hc] at h ⊢; exact hk q B h
                  | obj W' ls' vls' ch' => simp only [hc] at h ⊢; exact h

theorem blockFuel_mono_succ (Γ : Ctx s) :
    ∀ (n : Nat) (p : Path s) (B : Block s), Γ.blockFuel n p = some B → Γ.blockFuel (n+1) p = some B
  | 0, p, B, h => by rw [blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h => by
      simp only [blockFuel] at h ⊢
      exact Γ.blockPass_mono (fun q B' h' => Γ.blockFuel_mono_succ n q B' h') p B h

theorem blockFuel_mono (Γ : Ctx s) {m n : Nat} (hmn : m ≤ n) {p : Path s} {B : Block s}
    (h : Γ.blockFuel m p = some B) : Γ.blockFuel n p = some B := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      exact h
  | succ n ih =>
      rcases Nat.lt_or_ge m (n+1) with hlt | hge
      · exact Γ.blockFuel_mono_succ n p B (ih (by omega))
      · have hmn' : m = n+1 := by omega
        exact hmn' ▸ h

/-! ### The budget suffices

The pigeonhole P1.3 promises.  The walk spends one unit of fuel exactly when
it follows a forwarding node, and the target of that node is one of the paths
the context names.  If the walk answers at fuel `n+1` and not at fuel `n`,
then one of those targets answers at `n` and not at `n-1`: the walk of a
shorter fuel is the same walk with one less unit to spend, so the difference
must show at a place where a unit is spent.  Following that down, each step
lands on a target whose least fuel is one smaller, so the targets are
pairwise distinct and `n` of them have been named.  There are `Γ.fwdCount`
targets in the whole context, so a walk that answers at all answers at fuel
`Γ.fwdCount + 1`, which is the budget.  Above the budget the walk is
therefore `Ctx.lookupBlock` itself. -/

/-- The targets of the whole context, one per forwarding node. -/
def targets : Ctx s → List (Path s)
  | .nil => []
  | .cons Γ b => Γ.targets.map Path.weaken ++ b.targets

theorem length_targets : ∀ Γ : Ctx s, Γ.targets.length = Γ.fwdCount
  | .nil => rfl
  | .cons Γ b => by
      simp only [targets, fwdCount, List.length_append, List.length_map,
        length_targets Γ, Binding.length_targets b]

/-- Every target of a binder's block is a target of the context. -/
theorem blockAt_targets {s : Sig} :
    ∀ (Γ : Ctx s) (x : BVar s .var) (B : Block s),
      Γ.blockAt x = some B → ∀ q ∈ B.targets, q ∈ Γ.targets
  | .cons _ (.transparent _ B₀), .here, B, h, q, hq => by
      obtain rfl : B₀ = B := by simpa using h
      exact List.mem_append_right _ hq
  | .cons _ (.opaque _), .here, _, h, _, _ => by simp at h
  | .cons Γ b, .there y, B, h, q, hq => by
      rw [blockAt_there] at h
      obtain ⟨B₀, hB₀, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Block.weaken, Block.targets_rename] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
      exact List.mem_append_left _
        (List.mem_map_of_mem (blockAt_targets Γ y B₀ hB₀ q₀ hq₀))

/-- Every target of a block the walk answers with is a target of the
context: the walk only ever reaches nodes the context holds. -/
theorem blockPass_targets (Γ : Ctx s) {k : Path s → Option (Block s)}
    (hk : ∀ q B, k q = some B → ∀ r ∈ B.targets, r ∈ Γ.targets) :
    ∀ (p : Path s) (B : Block s),
      Γ.blockPass k p = some B → ∀ r ∈ B.targets, r ∈ Γ.targets
  | .var x, B, h, r, hr => by
      simp only [blockPass] at h
      cases hx : Γ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hx] at h; exact hk q B h r hr
          | obj W ls vls ch =>
              simp only [hx] at h
              obtain rfl : Block.obj W ls vls ch = B := by simpa using h
              exact Γ.blockAt_targets x _ hx r hr
  | .sel p a, B, h, r, hr => by
      simp only [blockPass] at h
      cases hp : Γ.blockPass k p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              have hch := Γ.blockPass_targets hk p _ hp
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd q => simp only [hc] at h; exact hk q B h r hr
                  | obj W' ls' vls' ch' =>
                      simp only [hc] at h
                      obtain rfl : Block.obj W' ls' vls' ch' = B := by simpa using h
                      exact hch r (Children.at?_targets ch a _ hc r hr)

theorem blockFuel_targets (Γ : Ctx s) :
    ∀ (n : Nat) (p : Path s) (B : Block s),
      Γ.blockFuel n p = some B → ∀ r ∈ B.targets, r ∈ Γ.targets
  | 0, _, _, h, _, _ => by rw [blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h, r, hr => by
      simp only [blockFuel] at h
      exact Γ.blockPass_targets (fun q B' h' => Γ.blockFuel_targets n q B' h') p B h r hr

/-- Where one pass answers and the pass with one unit less does not, a
target of the context separates the two continuations. -/
theorem blockPass_gap (Γ : Ctx s) {k k' : Path s → Option (Block s)}
    (hmono : ∀ q B, k' q = some B → k q = some B)
    (hk : ∀ q B, k q = some B → ∀ r ∈ B.targets, r ∈ Γ.targets) :
    ∀ (p : Path s) (B : Block s),
      Γ.blockPass k p = some B → Γ.blockPass k' p = none →
        ∃ q, q ∈ Γ.targets ∧ (k q).isSome ∧ k' q = none
  | .var x, B, h, h0 => by
      simp only [blockPass] at h h0
      cases hx : Γ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q =>
              simp only [hx] at h h0
              refine ⟨q, ?_, by rw [h]; rfl, h0⟩
              exact Γ.blockAt_targets x _ hx q (by simp [Block.targets])
          | obj W ls vls ch =>
              simp only [hx] at h h0
              exact absurd h0 (by simp)
  | .sel p a, B, h, h0 => by
      simp only [blockPass] at h h0
      cases hp : Γ.blockPass k p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              have hch := Γ.blockPass_targets hk p _ hp
              cases hp' : Γ.blockPass k' p with
              | none => exact Γ.blockPass_gap hmono hk p _ hp hp'
              | some B₁ =>
                  obtain rfl : Block.obj W ls vls ch = B₁ := by
                    have := Γ.blockPass_mono hmono p B₁ hp'
                    rw [hp] at this
                    exact Option.some.inj this
                  simp only [hp'] at h0
                  cases hc : ch.at? a with
                  | none => simp only [hc] at h; exact absurd h (by simp)
                  | some B₂ =>
                      cases B₂ with
                      | fwd q =>
                          simp only [hc] at h h0
                          refine ⟨q, ?_, by rw [h]; rfl, h0⟩
                          exact hch q (Children.at?_targets ch a _ hc q
                            (by simp [Block.targets]))
                      | obj W' ls' vls' ch' =>
                          simp only [hc] at h0
                          exact absurd h0 (by simp)

theorem blockFuel_gap (Γ : Ctx s) (n : Nat) (p : Path s) (B : Block s)
    (h : Γ.blockFuel (n+2) p = some B) (h0 : Γ.blockFuel (n+1) p = none) :
    ∃ q, q ∈ Γ.targets ∧ (Γ.blockFuel (n+1) q).isSome ∧ Γ.blockFuel n q = none := by
  simp only [blockFuel] at h h0
  exact Γ.blockPass_gap (fun q B' h' => Γ.blockFuel_mono_succ n q B' h')
    (fun q B' h' => Γ.blockFuel_targets (n+1) q B' h') p B h h0

/-- The number of targets the walk answers at, at a given fuel. -/
def satCount (Γ : Ctx s) (n : Nat) : Nat :=
  Γ.targets.countP (fun q => (Γ.blockFuel n q).isSome)

theorem satCount_le (Γ : Ctx s) (n : Nat) : Γ.satCount n ≤ Γ.fwdCount := by
  rw [← Γ.length_targets]
  exact List.countP_le_length

theorem satCount_lt (Γ : Ctx s) {n : Nat} {q : Path s} (hq : q ∈ Γ.targets)
    (h1 : (Γ.blockFuel (n+1) q).isSome) (h0 : Γ.blockFuel n q = none) :
    Γ.satCount n < Γ.satCount (n+1) := by
  refine countP_lt Γ.targets ?_ hq ?_ ?_
  · intro r _ hr
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hr
    rw [Γ.blockFuel_mono_succ n r B hB]
    rfl
  · rw [h0]; rfl
  · exact h1

/-- A walk that answers at fuel `n+1` and not at `n` has named `n` distinct
targets, so `n` is at most the number of targets the walk answers at. -/
theorem gap_le (Γ : Ctx s) : ∀ (n : Nat) (p : Path s) (B : Block s),
    Γ.blockFuel (n+1) p = some B → Γ.blockFuel n p = none → n ≤ Γ.satCount n
  | 0, _, _, _, _ => Nat.zero_le _
  | n+1, p, B, h, h0 => by
      obtain ⟨q, hq, h1, h2⟩ := Γ.blockFuel_gap n p B h h0
      obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.mp h1
      have hih := Γ.gap_le n q B' hB' h2
      have hlt := Γ.satCount_lt hq h1 h2
      omega

/-- The first fuel at which the walk answers, above a fuel at which it does
not. -/
theorem exists_gap (Γ : Ctx s) : ∀ (n k : Nat) (p : Path s) (B : Block s),
    Γ.blockFuel (k + n) p = some B → Γ.blockFuel k p = none →
      ∃ m, k ≤ m ∧ Γ.blockFuel m p = none ∧ ∃ B', Γ.blockFuel (m+1) p = some B'
  | 0, k, p, B, h, h0 => by rw [Nat.add_zero, h0] at h; exact absurd h (by simp)
  | n+1, k, p, B, h, h0 => by
      cases hk : Γ.blockFuel (k+1) p with
      | some B' => exact ⟨k, Nat.le_refl _, h0, B', hk⟩
      | none =>
          obtain ⟨m, hm, hm0, hm1⟩ :=
            Γ.exists_gap n (k+1) p B (by rw [show k+1+n = k+(n+1) by omega]; exact h) hk
          exact ⟨m, by omega, hm0, hm1⟩

/-- **The budget suffices.**  A block the walk finds at any fuel is the block
`Ctx.lookupBlock` finds.  This is the pigeonhole of P1.3, and it is what a
context map into a context with a smaller budget needs. -/
theorem blockFuel_budget (Γ : Ctx s) {n : Nat} {p : Path s} {B : Block s}
    (h : Γ.blockFuel n p = some B) : Γ.lookupBlock p = some B := by
  show Γ.blockFuel Γ.aliasBudget p = some B
  rcases Nat.le_total n Γ.aliasBudget with hle | hge
  · exact Γ.blockFuel_mono hle h
  · cases hb : Γ.blockFuel Γ.aliasBudget p with
    | some B' =>
        obtain rfl : B' = B := by
          have := Γ.blockFuel_mono hge hb
          rw [this] at h
          exact Option.some.inj h
        rfl
    | none =>
        exfalso
        obtain ⟨m, hm, hm0, B', hm1⟩ :=
          Γ.exists_gap (n - Γ.aliasBudget) Γ.aliasBudget p B
            (by rw [show Γ.aliasBudget + (n - Γ.aliasBudget) = n by omega]; exact h) hb
        have hb1 := Γ.gap_le m p B' hm1 hm0
        have hb2 := Γ.satCount_le m
        simp only [aliasBudget] at hm
        omega

/-- At or above the budget the walk is the lookup. -/
theorem blockFuel_eq_lookupBlock (Γ : Ctx s) {n : Nat} (hn : Γ.aliasBudget ≤ n)
    (p : Path s) : Γ.blockFuel n p = Γ.lookupBlock p := by
  cases h : Γ.blockFuel n p with
  | some B => exact (Γ.blockFuel_budget h).symm
  | none =>
      cases hl : Γ.lookupBlock p with
      | none => rfl
      | some B =>
          rw [Γ.blockFuel_mono hn hl] at h
          exact absurd h (by simp)

/-- A renaming that carries the binder table carries the whole walk. -/
theorem blockPass_rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hb : ∀ x B, Γ.blockAt x = some B → Γ'.blockAt (ρ.var x) = some (B.rename ρ))
    {k : Path s1 → Option (Block s1)} {k' : Path s2 → Option (Block s2)}
    (hk : ∀ q B, k q = some B → k' (q.rename ρ) = some (B.rename ρ)) :
    ∀ (p : Path s1) (B : Block s1),
      Γ.blockPass k p = some B → Γ'.blockPass k' (p.rename ρ) = some (B.rename ρ)
  | .var x, B, h => by
      simp only [blockPass] at h
      simp only [Path.rename, blockPass]
      cases hx : Γ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q =>
              simp only [hx] at h
              simp only [hb x _ hx, Block.rename]
              exact hk q B h
          | obj W ls vls ch =>
              simp only [hx] at h
              obtain rfl : Block.obj W ls vls ch = B := by simpa using h
              simp only [hb x _ hx, Block.rename]
  | .sel p a, B, h => by
      simp only [blockPass] at h
      simp only [Path.rename, blockPass]
      cases hp : Γ.blockPass k p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              simp only [blockPass_rename hb hk p _ hp, Block.rename, Children.at?_rename]
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd q =>
                      simp only [hc] at h
                      simp only [hc, Option.map_some, Block.rename]
                      exact hk q B h
                  | obj W' ls' vls' ch' =>
                      simp only [hc] at h
                      obtain rfl : Block.obj W' ls' vls' ch' = B := by simpa using h
                      simp only [hc, Option.map_some, Block.rename]

theorem blockFuel_rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hb : ∀ x B, Γ.blockAt x = some B → Γ'.blockAt (ρ.var x) = some (B.rename ρ)) :
    ∀ (n : Nat) (p : Path s1) (B : Block s1),
      Γ.blockFuel n p = some B → Γ'.blockFuel n (p.rename ρ) = some (B.rename ρ)
  | 0, p, B, h => by rw [blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h => by
      simp only [blockFuel] at h ⊢
      exact blockPass_rename hb (fun q B' h' => blockFuel_rename hb n q B' h') p B h

/-- The block of a path survives a renaming that carries the table.  No
condition on the budget: the walk is carried at the source's fuel, and
`Ctx.blockFuel_budget` reads the answer off at the target's own budget. -/
theorem lookupBlock_rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hb : ∀ x B, Γ.blockAt x = some B → Γ'.blockAt (ρ.var x) = some (B.rename ρ))
    {p : Path s1} {B : Block s1}
    (h : Γ.lookupBlock p = some B) : Γ'.lookupBlock (p.rename ρ) = some (B.rename ρ) :=
  Γ'.blockFuel_budget (blockFuel_rename hb Γ.aliasBudget p B h)

/-- The definition of a block name survives such a renaming. -/
theorem lookupDefP_rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hb : ∀ x B, Γ.blockAt x = some B → Γ'.blockAt (ρ.var x) = some (B.rename ρ))
    {p : Path s1} {l : Label} {W : Ty s1}
    (h : Γ.lookupDefP p l = some W) :
    Γ'.lookupDefP (p.rename ρ) l = some (W.rename ρ) := by
  unfold lookupDefP at h ⊢
  cases hbk : Γ.lookupBlock p with
  | none => rw [hbk] at h; exact absurd h (by simp)
  | some B =>
      cases B with
      | fwd q => rw [hbk] at h; exact absurd h (by simp)
      | obj W₀ ls vls ch =>
          rw [hbk] at h
          obtain rfl : W₀.get l = W := by simpa using h
          simp only [lookupBlock_rename hb hbk, Block.rename, Witnesses.get_rename]

/-- The block of a path is stable under weakening the context: the walk from
a weakened path never reaches the new binder. -/
theorem lookupBlock_weaken (Γ : Ctx s) (b : Binding s) {p : Path s} {B : Block s}
    (h : Γ.lookupBlock p = some B) :
    (Γ.cons b).lookupBlock (p.weaken (k := .var)) = some (B.weaken (k := .var)) :=
  Ctx.lookupBlock_rename (Γ' := Γ.cons b) (ρ := Rename.succ)
    (fun x B' hB' => by rw [Rename.succ_var, Ctx.blockAt_there, hB']; rfl) h

/-- The definition of a block name is stable under weakening the context. -/
theorem lookupDefP_weaken (Γ : Ctx s) (b : Binding s) {p : Path s} {l : Label} {W : Ty s}
    (h : Γ.lookupDefP p l = some W) :
    (Γ.cons b).lookupDefP (p.weaken (k := .var)) l = some (W.weaken (k := .var)) :=
  Ctx.lookupDefP_rename (Γ' := Γ.cons b) (ρ := Rename.succ)
    (fun x B' hB' => by rw [Rename.succ_var, Ctx.blockAt_there, hB']; rfl) h

/-- L1 of P1.4.  A name whose lookup follows a forwarding has the same
definition as the name it forwards to.  This is what makes every alias
equality an instance of `EqCo.def`. -/
theorem lookupDefP_fwd (Γ : Ctx s) {p q : Path s} (h : Γ.lookupBlock p = Γ.lookupBlock q) :
    ∀ ℓ, Γ.lookupDefP p ℓ = Γ.lookupDefP q ℓ := by
  intro ℓ
  rw [lookupDefP, lookupDefP, h]

/-- The forwarding binder of a let over a path is not transparent in the
sense of `Ctx.IsTransparent`: a forwarding node lists no fields of its own.
This is what keeps the four binder fields of `Subst.Typed` off it. -/
theorem fwdAt_not_transparent (Γ : Ctx s) (q : Path s) :
    ¬ (Γ.cons (Binding.fwdAt q)).IsTransparent .here := by
  simp [Ctx.IsTransparent, Binding.fwdAt, lookupFields]

/-! ### The walk read off one node

`Ctx.follow` is the last step of the walk: an object node is the answer, and a
forwarding node hands the walk on to its target.  With it the walk has two
equations, one at a binder and one at a field step, and both hold at the
budget.  The field-step equation is what an alias under one field step reads
(T2 of P1.8) and what a context map over a forwarding binder reads. -/

/-- The answer the walk gives once it stands on a node. -/
def follow (Γ : Ctx s) : Block s → Option (Block s)
  | .fwd r => Γ.lookupBlock r
  | B => some B

/-- Every target of the context answers one unit below the budget whenever it
answers at all.  A walk that needed the last unit would have named
`Γ.fwdCount` distinct targets, by `Ctx.gap_le`, so every target of the
context answers at that fuel, and this one does not.  This is the counting
lemma in the idiom of `Ctx.gap_le` that the field-step equation needs. -/
theorem target_blockFuel (Γ : Ctx s) {r : Path s} (hr : r ∈ Γ.targets) :
    Γ.blockFuel Γ.fwdCount r = Γ.lookupBlock r := by
  cases h : Γ.blockFuel Γ.fwdCount r with
  | some B => rw [Γ.blockFuel_budget h]
  | none =>
      cases hl : Γ.lookupBlock r with
      | none => rfl
      | some B =>
          exfalso
          have hsome : Γ.blockFuel (Γ.fwdCount + 1) r = some B := hl
          have hgap := Γ.gap_le Γ.fwdCount r B hsome h
          have hle := Γ.satCount_le Γ.fwdCount
          have heq : Γ.satCount Γ.fwdCount = Γ.targets.length := by
            rw [Γ.length_targets]; omega
          have hall := countP_all Γ.targets r hr heq
          rw [h] at hall
          exact absurd hall (by simp)

/-- The walk at a binder: read the node off the table, then follow it. -/
theorem lookupBlock_var_eq (Γ : Ctx s) (x : BVar s .var) :
    Γ.lookupBlock (.var x) = (Γ.blockAt x).bind Γ.follow := by
  have hl : Γ.lookupBlock (.var x) = Γ.blockFuel (Γ.fwdCount + 1) (.var x) := rfl
  rw [hl, blockFuel_var]
  cases hx : Γ.blockAt x with
  | none => rfl
  | some B =>
      cases B with
      | obj W ls vls ch => rfl
      | fwd r =>
          show Γ.blockFuel Γ.fwdCount r = Γ.lookupBlock r
          exact Γ.target_blockFuel (Γ.blockAt_targets x _ hx r (by simp [Block.targets]))

/-- The walk at a field step: walk the prefix, read the child, then follow
it.  This is the `sel` case of T2. -/
theorem lookupBlock_sel (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.lookupBlock (.sel p a) =
      ((Γ.lookupBlock p).bind (fun B => B.childAt? a)).bind Γ.follow := by
  have hlp : Γ.lookupBlock p = Γ.blockFuel (Γ.fwdCount + 1) p := rfl
  have hls : Γ.lookupBlock (.sel p a) = Γ.blockFuel (Γ.fwdCount + 1) (.sel p a) := rfl
  rw [hls, blockFuel_sel, ← hlp]
  cases hb : Γ.lookupBlock p with
  | none => rfl
  | some B =>
      cases B with
      | fwd r => rfl
      | obj W ls vls ch =>
          show (match ch.at? a with
                | some (.fwd q) => Γ.blockFuel Γ.fwdCount q
                | b => b) = (ch.at? a).bind Γ.follow
          cases hc : ch.at? a with
          | none => rfl
          | some B' =>
              cases B' with
              | obj W' ls' vls' ch' => rfl
              | fwd r =>
                  show Γ.blockFuel Γ.fwdCount r = Γ.lookupBlock r
                  refine Γ.target_blockFuel ?_
                  refine Γ.blockFuel_targets Γ.aliasBudget p _ hb r ?_
                  exact Children.at?_targets ch a _ hc r (by simp [Block.targets])

/-! ### Strengthening the walk

A path rooted below a binder never reaches that binder, and every node it
reaches is a weakened node of the smaller context, so the walk in `Γ.cons b`
from a weakened path is the weakened walk in `Γ`.  This is the converse of
`Ctx.lookupBlock_weaken`, in the idiom of `Ctx.blockPass_rename`. -/

theorem blockPass_strengthen (Γ : Ctx s) (b : Binding s)
    {k : Path (s,x) → Option (Block (s,x))} {k₀ : Path s → Option (Block s)}
    (hk : ∀ (q : Path s) (C : Block (s,x)), k q.weaken = some C →
      ∃ C₀, k₀ q = some C₀ ∧ C = C₀.weaken) :
    ∀ (p : Path s) (B : Block (s,x)),
      (Γ.cons b).blockPass k p.weaken = some B →
        ∃ B₀, Γ.blockPass k₀ p = some B₀ ∧ B = B₀.weaken
  | .var y, B, h => by
      have hw : (Path.var y).weaken (k := .var) = Path.var (BVar.there y) := rfl
      rw [hw, blockPass, blockAt_there] at h
      rw [blockPass]
      cases hy : Γ.blockAt y with
      | none => rw [hy] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd r =>
              rw [hy] at h
              exact hk r B h
          | obj W ls vls ch =>
              rw [hy] at h
              exact ⟨.obj W ls vls ch, rfl, by
                simpa [Block.weaken, Block.rename] using h.symm⟩
  | .sel p a, B, h => by
      have hw : (Path.sel p a).weaken (k := .var)
          = Path.sel (p.weaken (k := .var)) a := rfl
      rw [hw] at h
      simp only [blockPass] at h ⊢
      cases hp : (Γ.cons b).blockPass k (p.weaken (k := .var)) with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₁ =>
          obtain ⟨B₀, hB₀, rfl⟩ := Γ.blockPass_strengthen b hk p B₁ hp
          cases B₀ with
          | fwd r =>
              simp only [hp, Block.weaken, Block.rename] at h
              exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hB₀]
              simp only [hp, Block.weaken, Block.rename, Children.at?_rename] at h
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₂ =>
                  simp only [hc] at h
                  cases B₂ with
                  | fwd r => exact hk r B h
                  | obj W' ls' vls' ch' =>
                      exact ⟨.obj W' ls' vls' ch', rfl, by
                        simpa [Block.weaken, Block.rename] using h.symm⟩

/-- **The walk strengthens.**  The walk in `Γ.cons b` from a weakened path is
the weakened walk in `Γ`, at the same fuel. -/
theorem blockFuel_strengthen (Γ : Ctx s) (b : Binding s) :
    ∀ (n : Nat) (p : Path s) (B : Block (s,x)),
      (Γ.cons b).blockFuel n p.weaken = some B →
        ∃ B₀, Γ.blockFuel n p = some B₀ ∧ B = B₀.weaken
  | 0, p, B, h => by rw [blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h => by
      simp only [blockFuel] at h ⊢
      exact Γ.blockPass_strengthen b
        (fun q C hC => Γ.blockFuel_strengthen b n q C hC) p B h

/-- The lookup strengthens, which is the converse of `Ctx.lookupBlock_weaken`. -/
theorem lookupBlock_strengthen (Γ : Ctx s) (b : Binding s) {p : Path s} {B : Block (s,x)}
    (h : (Γ.cons b).lookupBlock p.weaken = some B) :
    ∃ B₀, Γ.lookupBlock p = some B₀ ∧ B = B₀.weaken := by
  obtain ⟨B₀, hB₀, rfl⟩ := Γ.blockFuel_strengthen b (Γ.cons b).aliasBudget p B h
  exact ⟨B₀, Γ.blockFuel_budget hB₀, rfl⟩

/-! ### The node walk

`Ctx.nodeBlock` is `Ctx.blockPass` at the continuation that answers nothing,
so each fact about the pass holds for it at that continuation. -/

/-- A node is never a forwarding. -/
theorem nodeBlock_ne_fwd (Γ : Ctx s) :
    ∀ (p : Path s) (q : Path s), Γ.nodeBlock p ≠ some (.fwd q)
  | .var x, q, h => by
      simp only [nodeBlock, blockPass] at h
      cases hx : Γ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B =>
          cases B with
          | fwd r => simp only [hx] at h; exact absurd h (by simp)
          | obj W ls vls ch => simp only [hx] at h; exact absurd h (by simp)
  | .sel p a, q, h => by
      simp only [nodeBlock, blockPass] at h
      cases hp : Γ.blockPass (fun _ => none) p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B =>
          cases B with
          | fwd r => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd r => simp only [hc] at h; exact absurd h (by simp)
                  | obj W' ls' vls' ch' => simp only [hc] at h; exact absurd h (by simp)

/-- A node is the block the walk finds: `Ctx.blockPass_mono` at the first
unit of the budget. -/
theorem nodeBlock_lookupBlock (Γ : Ctx s) {p : Path s} {B : Block s}
    (h : Γ.nodeBlock p = some B) : Γ.lookupBlock p = some B :=
  Γ.blockPass_mono (k := fun _ => none) (k' := Γ.blockFuel Γ.fwdCount)
    (fun _ _ h' => absurd h' (by simp)) p B h

/-- A renaming that carries the binder table carries the node walk. -/
theorem nodeBlock_rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hb : ∀ x B, Γ.blockAt x = some B → Γ'.blockAt (ρ.var x) = some (B.rename ρ))
    {p : Path s1} {B : Block s1}
    (h : Γ.nodeBlock p = some B) : Γ'.nodeBlock (p.rename ρ) = some (B.rename ρ) :=
  blockPass_rename hb (k := fun _ => none) (k' := fun _ => none)
    (fun _ _ h' => absurd h' (by simp)) p B h

/-- The node of a path is stable under weakening the context. -/
theorem nodeBlock_weaken (Γ : Ctx s) (b : Binding s) {p : Path s} {B : Block s}
    (h : Γ.nodeBlock p = some B) :
    (Γ.cons b).nodeBlock (p.weaken (k := .var)) = some (B.weaken (k := .var)) :=
  Ctx.nodeBlock_rename (Γ' := Γ.cons b) (ρ := Rename.succ)
    (fun x B' hB' => by rw [Rename.succ_var, Ctx.blockAt_there, hB']; rfl) h

/-- The node walk strengthens, the converse of `Ctx.nodeBlock_weaken`. -/
theorem nodeBlock_strengthen (Γ : Ctx s) (b : Binding s) {p : Path s} {B : Block (s,x)}
    (h : (Γ.cons b).nodeBlock p.weaken = some B) :
    ∃ B₀, Γ.nodeBlock p = some B₀ ∧ B = B₀.weaken :=
  Γ.blockPass_strengthen b (k := fun _ => none) (k₀ := fun _ => none)
    (fun _ _ h' => absurd h' (by simp)) p B h

/-- The node walk is carried along a renaming as soon as it is carried at every
variable.  A step through a field reads the children of the node above it, and
a renaming acts on them label by label. -/
theorem nodeBlock_map {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hv : ∀ (x : BVar s1 .var) (B : Block s1), Γ.nodeBlock (.var x) = some B →
      Γ'.nodeBlock (.var (ρ.var x)) = some (B.rename ρ)) :
    ∀ (p : Path s1) (B : Block s1),
      Γ.nodeBlock p = some B → Γ'.nodeBlock (p.rename ρ) = some (B.rename ρ)
  | .var x, B, h => hv x B h
  | .sel p a, B, h => by
      simp only [nodeBlock, blockPass] at h
      simp only [Path.rename, nodeBlock, blockPass]
      cases hp : Γ.blockPass (fun _ => none) p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              have hp' := nodeBlock_map hv p _ hp
              simp only [nodeBlock] at hp'
              simp only [hp', Block.rename, Children.at?_rename]
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd q => simp only [hc] at h; exact absurd h (by simp)
                  | obj W' ls' vls' ch' =>
                      simp only [hc] at h
                      obtain rfl : Block.obj W' ls' vls' ch' = B := by simpa using h
                      simp only [Option.map_some, Block.rename]

/-- The node walk out of `Γ₁.cons b` is carried along a renaming that carries
the new binder's node by hand and every older binder's node through the node
walk of `Γ₁`.  The twin of `Ctx.lookupBlock_cons_map` for the walk that
follows no forwarding. -/
theorem nodeBlock_cons_map {s1 s2 : Sig} (Γ₁ : Ctx s1) (b : Binding s1)
    (Γ₂ : Ctx s2) (ρ : Rename (s1,x) s2)
    (hhere : ∀ B : Block (s1,x), (Γ₁.cons b).nodeBlock (.var .here) = some B →
      Γ₂.nodeBlock (.var (ρ.var .here)) = some (B.rename ρ))
    (hthere : ∀ (y : BVar s1 .var) (B : Block s1), Γ₁.nodeBlock (.var y) = some B →
      Γ₂.nodeBlock (.var (ρ.var (.there y))) = some ((B.weaken (k := .var)).rename ρ)) :
    ∀ (p : Path (s1,x)) (B : Block (s1,x)),
      (Γ₁.cons b).nodeBlock p = some B → Γ₂.nodeBlock (p.rename ρ) = some (B.rename ρ) := by
  refine nodeBlock_map ?_
  intro z B h
  cases z with
  | here => exact hhere B h
  | there y =>
      have hw : (Path.var (BVar.there y) : Path (s1,x)) = (Path.var y).weaken (k := .var) := rfl
      rw [hw] at h
      obtain ⟨B₀, hB₀, rfl⟩ := Γ₁.nodeBlock_strengthen b h
      exact hthere y B₀ hB₀

/-! ### Carrying the walk over one binder

A context map out of `Γ₁.cons b` reads the new binder's node by hand and
every older binder through the walk it already carries.  This is what a
substitution whose block field is `lookupB` can give, and it is what the
forwarding binder of a let over a path needs, whose node is a forwarding
while the atom's root has an object node. -/

theorem lookupBlock_cons_map {s1 s2 : Sig} (Γ₁ : Ctx s1) (b : Binding s1)
    (Γ₂ : Ctx s2) (ρ : Rename (s1,x) s2)
    (hhere : ∀ (B₀ : Block (s1,x)) (C : Block s2),
      (Γ₁.cons b).blockAt .here = some B₀ → Γ₂.follow (B₀.rename ρ) = some C →
        Γ₂.lookupBlock (.var (ρ.var .here)) = some C)
    (hthere : ∀ (y : BVar s1 .var) (B : Block s1), Γ₁.lookupBlock (.var y) = some B →
      Γ₂.lookupBlock (.var (ρ.var (.there y))) = some ((B.weaken (k := .var)).rename ρ)) :
    ∀ (n : Nat) (p : Path (s1,x)) (B : Block (s1,x)),
      (Γ₁.cons b).blockFuel n p = some B → Γ₂.lookupBlock (p.rename ρ) = some (B.rename ρ)
  | 0, p, B, h => by rw [blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h => by
      induction p generalizing B with
      | var z =>
          cases z with
          | there y =>
              have hw : (Path.var (BVar.there y) : Path (s1,x))
                  = (Path.var y).weaken (k := .var) := rfl
              rw [hw] at h
              obtain ⟨B₀, hB₀, rfl⟩ := Γ₁.blockFuel_strengthen b (n+1) (.var y) B h
              simpa [Path.rename] using hthere y B₀ (Γ₁.blockFuel_budget hB₀)
          | here =>
              rw [blockFuel_var] at h
              cases hx : (Γ₁.cons b).blockAt BVar.here with
              | none => rw [hx] at h; exact absurd h (by simp)
              | some B₀ =>
                  rw [hx] at h
                  cases B₀ with
                  | fwd r =>
                      refine hhere (.fwd r) _ hx ?_
                      show Γ₂.lookupBlock (r.rename ρ) = _
                      exact Γ₁.lookupBlock_cons_map b Γ₂ ρ hhere hthere n r B h
                  | obj W ls vls ch =>
                      obtain rfl : Block.obj W ls vls ch = B := by simpa using h
                      exact hhere _ _ hx rfl
      | sel p' a ih =>
          simp only [blockFuel_sel] at h
          cases hp : (Γ₁.cons b).blockFuel (n+1) p' with
          | none => simp only [hp] at h; exact absurd h (by simp)
          | some B₁ =>
              have hih := ih _ hp
              simp only [hp] at h
              cases B₁ with
              | fwd r => exact absurd h (by simp)
              | obj W ls vls ch =>
                  rw [Path.rename, Γ₂.lookupBlock_sel, hih]
                  simp only [Block.rename, Option.bind_some, Block.childAt?,
                    Children.at?_rename]
                  cases hc : ch.at? a with
                  | none => simp only [hc] at h; exact absurd h (by simp)
                  | some B₂ =>
                      simp only [hc] at h
                      cases B₂ with
                      | fwd r =>
                          simp only [Option.map_some, Option.bind_some, Block.rename]
                          show Γ₂.lookupBlock (r.rename ρ) = _
                          exact Γ₁.lookupBlock_cons_map b Γ₂ ρ hhere hthere n r B h
                      | obj W' ls' vls' ch' =>
                          obtain rfl : Block.obj W' ls' vls' ch' = B := by simpa using h
                          simp only [Option.map_some, Option.bind_some, Block.rename,
                            Ctx.follow]
end Ctx

end FCdot

end Paths
