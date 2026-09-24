import Coercions.Paths.FCdot.Normalizer
import Coercions.Paths.FCdot.Typing
import Coercions.Paths.FCdot.TypingRename

namespace Paths

/-!
# Alias-tolerant resolution through transparent definitions

`Ctx.resolve` follows the definitions the block forest gives a name
(`Ctx.next`, one step) with a fixed fuel budget `Γ.defPairs.length + 2`.
Aliases inside one block are allowed, so an alias chain need not reach a
shape: it either *settles* (a shape, or a name whose block is opaque) or is
cyclic, and a cyclic chain resolves to `⊤`.

The budget suffices because the definitions come from a finite forest.  After
one step a chain stands at the head name of a witness of a node, which
`Ctx.defPairs` lists by construction, and at every step it stands at a listed
*key*: the block its prefix denotes and its label.  A chain longer than the
list of pairs repeats a key, one step of a chain reads the name only through
its key, so from a repeat the chain is periodic and never settles.  Hence
resolution is stable in the fuel (`Ctx.resolveFuel_stable`), is idempotent
(`Ctx.resolve_resolve`), and commutes with one unfolding step
(`Ctx.resolve_sel_some`), all without any side condition on the context.

The first name of a chain need not itself be listed: the walk to its prefix
may follow a forwarding, so the name is the *base*'s name for a block that the
forest lists under another name.  That is the third disjunct of
`Ctx.lookupDefP_defPairs`, and the step of slack in the budget.
-/

namespace FCdot

/-! ## A pigeonhole lemma

Core Lean has no `List.Nodup.subperm`, so the two ingredients — a
repetition-free list is no longer than any list containing it, and a long
enough sequence of elements of a list repeats a value — are proved here from
scratch. -/

/-- Remove the first occurrence of a value from a list.  (`List.erase` would do,
but the core lemmas about it are proved classically.) -/
def dropFirst {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: l => if a = b then l else b :: dropFirst a l

theorem length_dropFirst {α : Type} [DecidableEq α] (a : α) :
    ∀ (l : List α), a ∈ l → (dropFirst a l).length + 1 = l.length
  | [], h => by simp at h
  | b :: l, h => by
      have hdec : Decidable (a = b) := inferInstance
      cases hdec with
      | isTrue hab => simp [dropFirst, hab]
      | isFalse hab =>
          have hm : a ∈ l := by
            rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hab
            · exact h'
          have hih := length_dropFirst a l hm
          simp only [dropFirst, if_neg hab, List.length_cons]
          omega

theorem mem_dropFirst {α : Type} [DecidableEq α] {a b : α} (hne : b ≠ a) :
    ∀ {l : List α}, b ∈ l → b ∈ dropFirst a l
  | [], h => by simp at h
  | c :: l, h => by
      have hdec : Decidable (a = c) := inferInstance
      cases hdec with
      | isTrue hac =>
          subst hac
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' hne
          · rw [show dropFirst a (a :: l) = l by simp [dropFirst]]
            exact h'
      | isFalse hac =>
          rw [show dropFirst a (c :: l) = c :: dropFirst a l by simp [dropFirst, hac]]
          rcases List.mem_cons.mp h with h' | h'
          · subst h'; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem c (mem_dropFirst hne h')

/-- A repetition-free list is no longer than any list containing its elements. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ a ∈ l₁, a ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l₁, l₂, hnd, hsub => by
      have ha : a ∈ l₂ := hsub a (by simp)
      have hnd' : a ∉ l₁ ∧ l₁.Nodup := List.nodup_cons.mp hnd
      have hsub' : ∀ b ∈ l₁, b ∈ dropFirst a l₂ := by
        intro b hb
        have hne : b ≠ a := by
          intro hba
          subst hba
          exact hnd'.1 hb
        exact mem_dropFirst hne (hsub b (by simp [hb]))
      have hle := nodup_length_le l₁ (dropFirst a l₂) hnd'.2 hsub'
      have hlen := length_dropFirst a l₂ ha
      simp only [List.length_cons]
      omega

/-- The first `n` values of a sequence, newest first. -/
def initSeq {α : Type} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => f n :: initSeq f n

theorem initSeq_length {α : Type} (f : Nat → α) : ∀ n : Nat, (initSeq f n).length = n
  | 0 => rfl
  | n + 1 => by simp [initSeq, initSeq_length f n]

theorem mem_initSeq {α : Type} {f : Nat → α} {a : α} :
    ∀ {n : Nat}, a ∈ initSeq f n → ∃ i, i < n ∧ f i = a
  | 0, h => by simp [initSeq] at h
  | n + 1, h => by
      rw [initSeq, List.mem_cons] at h
      cases h with
      | inl h => exact ⟨n, Nat.lt_succ_self n, h.symm⟩
      | inr h =>
          obtain ⟨i, hi, he⟩ := mem_initSeq h
          exact ⟨i, by omega, he⟩

theorem initSeq_nodup {α : Type} (f : Nat → α) :
    ∀ (n : Nat), (∀ i j, i < j → j < n → f i ≠ f j) → (initSeq f n).Nodup
  | 0, _ => by simp [initSeq]
  | n + 1, h => by
      rw [initSeq, List.nodup_cons]
      refine ⟨?_, initSeq_nodup f n (fun i j hij hjn => h i j hij (by omega))⟩
      intro hm
      obtain ⟨i, hi, he⟩ := mem_initSeq hm
      exact h i n hi (Nat.lt_succ_self n) he

/-- Bounded existential quantification over `Nat` is decidable; deciding, rather
than arguing by contradiction, keeps the pigeonhole argument choice-free. -/
instance decidableExistsLt (P : Nat → Prop) [DecidablePred P] :
    ∀ (n : Nat), Decidable (∃ i, i < n ∧ P i)
  | 0 => isFalse (fun h => h.elim fun _ hi => absurd hi.1 (Nat.not_lt_zero _))
  | n + 1 =>
      match decidableExistsLt P n with
      | isTrue h => isTrue (h.elim fun i hi => ⟨i, Nat.lt_succ_of_lt hi.1, hi.2⟩)
      | isFalse hf =>
          if hp : P n then isTrue ⟨n, Nat.lt_succ_self n, hp⟩
          else isFalse (fun h => h.elim fun i hi =>
            if he : i = n then hp (he ▸ hi.2)
            else hf ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi.1) he, hi.2⟩)

/-- Pigeonhole: a sequence of more than `l.length` elements of `l` repeats a value. -/
theorem exists_repeat {α : Type} [DecidableEq α] (f : Nat → α) (l : List α) (n : Nat)
    (hmem : ∀ i, i < n → f i ∈ l) (hlt : l.length < n) :
    ∃ j, j < n ∧ ∃ i, i < j ∧ f i = f j := by
  cases (@decidableExistsLt (fun j => ∃ i, i < j ∧ f i = f j)
      (fun j => decidableExistsLt (fun i => f i = f j) j) n) with
  | isTrue h => exact h
  | isFalse h =>
      exfalso
      have hnd : (initSeq f n).Nodup :=
        initSeq_nodup f n (fun i j hij hjn he => h ⟨j, hjn, i, hij, he⟩)
      have hle := nodup_length_le (initSeq f n) l hnd (by
        intro a ha
        obtain ⟨i, hi, he⟩ := mem_initSeq ha
        exact he ▸ hmem i hi)
      rw [initSeq_length] at hle
      omega

/-! ## One alias step -/

@[simp] theorem Ctx.next_sel (Γ : Ctx s) (p : Path s) (ℓ : Label) :
    Γ.next (.sel p ℓ) = Γ.lookupDefP p ℓ := rfl

@[simp] theorem Ctx.next_top (Γ : Ctx s) : Γ.next (⊤ : Ty s) = none := rfl

theorem Ctx.next_nonSel {Γ : Ctx s} {T : Ty s} (h : ∀ (p : Path s) (ℓ : Label), T ≠ .sel p ℓ) :
    Γ.next T = none := by
  cases T with
  | sel p ℓ => exact absurd rfl (h p ℓ)
  | bot => rfl
  | pi => rfl
  | obj => rfl

/-- At a binder that defines the label, the path lookup at the variable path
is the binder lookup: a forwarding node defines nothing, so the block of the
binder is an object node. -/
theorem Ctx.lookupDefP_var_of_lookupDef {Γ : Ctx s} {x : BVar s .var} {ℓ : Label} {W : Ty s}
    (h : Γ.lookupDef x ℓ = some W) : Γ.lookupDefP (.var x) ℓ = some W := by
  have hnf : ∀ r, Γ.blockAt x ≠ some (.fwd r) := by
    intro r hr
    rw [Ctx.lookupDef_eq_blockAt, hr] at h
    exact absurd h (by simp [Block.def?])
  rw [Ctx.lookupDefP_var Γ x ℓ hnf, h]

/-! ## Basic resolution equations -/

/-- A settled type resolves to itself, with any fuel. -/
theorem Ctx.resolveFuel_settled (Γ : Ctx s) {T : Ty s} (h : Γ.next T = none) :
    ∀ n : Nat, Γ.resolveFuel n T = T
  | 0 => by simp [Ctx.resolveFuel, h]
  | _ + 1 => by simp [Ctx.resolveFuel, h]

theorem Ctx.resolveFuel_nonSel (Γ : Ctx s) (n : Nat) {T : Ty s}
    (h : ∀ (p : Path s) (ℓ : Label), T ≠ .sel p ℓ) : Γ.resolveFuel n T = T :=
  Γ.resolveFuel_settled (Ctx.next_nonSel h) n

theorem Ctx.resolve_nonSel (Γ : Ctx s) {T : Ty s}
    (h : ∀ (p : Path s) (ℓ : Label), T ≠ .sel p ℓ) : Γ.resolve T = T :=
  Γ.resolveFuel_nonSel _ h

@[simp] theorem Ctx.resolve_top (Γ : Ctx s) : Γ.resolve (.top : Ty s) = .top :=
  Γ.resolve_nonSel (by intro p ℓ h; cases h)

@[simp] theorem Ctx.resolve_bot (Γ : Ctx s) : Γ.resolve (.bot : Ty s) = .bot :=
  Γ.resolve_nonSel (by intro p ℓ h; cases h)

@[simp] theorem Ctx.resolve_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) :
    Γ.resolve (.pi S T) = .pi S T :=
  Γ.resolve_nonSel (by intro p ℓ h; cases h)

@[simp] theorem Ctx.resolve_obj (Γ : Ctx s) (Tel : Telescope (s,x)) :
    Γ.resolve (.obj Tel) = .obj Tel :=
  Γ.resolve_nonSel (by intro p ℓ h; cases h)

theorem Ctx.resolveFuel_selP_none (Γ : Ctx s) (n : Nat) {p : Path s} {ℓ : Label}
    (h : Γ.lookupDefP p ℓ = none) : Γ.resolveFuel n (.sel p ℓ) = .sel p ℓ :=
  Γ.resolveFuel_settled (by simp [h]) n

theorem Ctx.resolve_selP_none (Γ : Ctx s) {p : Path s} {ℓ : Label}
    (h : Γ.lookupDefP p ℓ = none) : Γ.resolve (.sel p ℓ) = .sel p ℓ :=
  Γ.resolveFuel_selP_none _ h

theorem Ctx.resolveFuel_selP_some (Γ : Ctx s) (n : Nat) {p : Path s} {ℓ : Label}
    {W : Ty s} (h : Γ.lookupDefP p ℓ = some W) :
    Γ.resolveFuel (n + 1) (.sel p ℓ) = Γ.resolveFuel n W := by
  simp [Ctx.resolveFuel, h]

theorem Ctx.resolveFuel_sel_none (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefP (.var x) ℓ = none) : Γ.resolveFuel n (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_selP_none n h

theorem Ctx.resolve_sel_none (Γ : Ctx s) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefP (.var x) ℓ = none) : Γ.resolve (.sel x ℓ) = .sel x ℓ :=
  Γ.resolve_selP_none h

theorem Ctx.resolveFuel_sel_some (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    {W : Ty s} (h : Γ.lookupDef x ℓ = some W) :
    Γ.resolveFuel (n + 1) (.sel x ℓ) = Γ.resolveFuel n W :=
  Γ.resolveFuel_selP_some n (Ctx.lookupDefP_var_of_lookupDef h)

/-! ## Alias chains

The chain of a type is the sequence of its alias steps; it is `none` from the
point where the type has settled. -/

/-- `Γ.chain T i`: the type reached from `T` by `i` alias steps, if the chain
has not settled before. -/
def Ctx.chain (Γ : Ctx s) (T : Ty s) : Nat → Option (Ty s)
  | 0 => some T
  | i + 1 => (Γ.chain T i).bind Γ.next

@[simp] theorem Ctx.chain_zero (Γ : Ctx s) (T : Ty s) : Γ.chain T 0 = some T := rfl

theorem Ctx.chain_succ (Γ : Ctx s) (T : Ty s) (i : Nat) :
    Γ.chain T (i + 1) = (Γ.chain T i).bind Γ.next := rfl

/-- The chain may also be peeled at the front. -/
theorem Ctx.chain_succ_head (Γ : Ctx s) (T : Ty s) :
    ∀ i : Nat, Γ.chain T (i + 1) = (Γ.next T).bind (fun W => Γ.chain W i)
  | 0 => by cases h : Γ.next T <;> simp [Ctx.chain, h]
  | i + 1 => by
      rw [Ctx.chain_succ, Ctx.chain_succ_head Γ T i, Option.bind_assoc]
      cases h : Γ.next T with
      | none => rfl
      | some W => simp [Ctx.chain_succ]

theorem Ctx.chain_add (Γ : Ctx s) (k : Nat) :
    ∀ (i : Nat) (T : Ty s), Γ.chain T (i + k) = (Γ.chain T i).bind (fun U => Γ.chain U k)
  | 0, T => by simp [Ctx.chain]
  | i + 1, T => by
      rw [show i + 1 + k = (i + k) + 1 by omega, Ctx.chain_succ_head, Ctx.chain_succ_head,
        Option.bind_assoc]
      cases h : Γ.next T with
      | none => rfl
      | some W => simp [Ctx.chain_add Γ k i W]

theorem Ctx.chain_isSome_of_le (Γ : Ctx s) {T : Ty s} {m n : Nat} (hmn : m ≤ n)
    (h : (Γ.chain T n).isSome) : (Γ.chain T m).isSome := by
  rw [show n = m + (n - m) by omega, Ctx.chain_add] at h
  cases hc : Γ.chain T m with
  | none => rw [hc] at h; simp at h
  | some _ => simp

/-- If the chain settles within the available fuel, the settled type is the result. -/
theorem Ctx.resolveFuel_of_chain (Γ : Ctx s) :
    ∀ (i : Nat) {n : Nat} {T U : Ty s}, i ≤ n → Γ.chain T i = some U → Γ.next U = none →
      Γ.resolveFuel n T = U
  | 0, n, T, U, _, hc, hu => by
      have hTU : T = U := by simpa using hc
      subst hTU
      exact Γ.resolveFuel_settled hu n
  | i + 1, n, T, U, hle, hc, hu => by
      cases n with
      | zero => omega
      | succ m =>
          rw [Ctx.chain_succ_head] at hc
          cases hn : Γ.next T with
          | none => rw [hn] at hc; simp at hc
          | some W =>
              rw [hn] at hc
              have hc' : Γ.chain W i = some U := hc
              rw [show Γ.resolveFuel (m + 1) T = Γ.resolveFuel m W by
                simp [Ctx.resolveFuel, hn]]
              exact Ctx.resolveFuel_of_chain Γ i (by omega) hc' hu

/-- If every step within the available fuel is defined, the fuel runs out on a
cycle and the result is `⊤`. -/
theorem Ctx.resolveFuel_eq_top (Γ : Ctx s) :
    ∀ (n : Nat) {T : Ty s}, (Γ.chain T (n + 1)).isSome → Γ.resolveFuel n T = ⊤
  | 0, T, h => by
      rw [Ctx.chain_succ_head] at h
      cases hn : Γ.next T with
      | none => rw [hn] at h; simp at h
      | some W => simp [Ctx.resolveFuel, hn]
  | n + 1, T, h => by
      rw [Ctx.chain_succ_head] at h
      cases hn : Γ.next T with
      | none => rw [hn] at h; simp at h
      | some W =>
          rw [hn] at h
          have h' : (Γ.chain W (n + 1)).isSome := h
          rw [show Γ.resolveFuel (n + 1) T = Γ.resolveFuel n W by simp [Ctx.resolveFuel, hn]]
          exact Ctx.resolveFuel_eq_top Γ n h'

/-- A chain that is `none` at some point has settled at an earlier index. -/
theorem Ctx.chain_settles (Γ : Ctx s) {T : Ty s} :
    ∀ {n : Nat}, Γ.chain T (n + 1) = none →
      ∃ i U, i ≤ n ∧ Γ.chain T i = some U ∧ Γ.next U = none
  | 0, h => ⟨0, T, Nat.le_refl 0, rfl, by simpa [Ctx.chain] using h⟩
  | n + 1, h => by
      cases hc : Γ.chain T (n + 1) with
      | none =>
          obtain ⟨i, U, hi, hcU, hu⟩ := Γ.chain_settles hc
          exact ⟨i, U, by omega, hcU, hu⟩
      | some U =>
          refine ⟨n + 1, U, Nat.le_refl _, hc, ?_⟩
          rw [Ctx.chain_succ, hc] at h
          simpa using h

/-! ## The nodes of the forest

`Ctx.defPairs` is read off `Ctx.nodes`, so the two facts the argument needs
are facts of membership: every node contributes its own pairs and the head
names of its witnesses, and every block the walk returns is a node that the
walk reaches at that node's own path. -/

theorem mem_nodePairs {s : Sig} : ∀ (ns : List (Path s × Block s)) (n : Path s × Block s),
    n ∈ ns → ∀ pr ∈ n.2.pairsAt n.1, pr ∈ nodePairs ns
  | [], _, hn, _, _ => by simp at hn
  | n₀ :: ns, n, hn, pr, hpr => by
      rcases List.mem_cons.mp hn with h | h
      · subst h
        exact List.mem_append_left _ hpr
      · exact List.mem_append_right _ (mem_nodePairs ns n h pr hpr)

theorem Ctx.mem_defPairs_of_node {Γ : Ctx s} {q : Path s} {B : Block s}
    (h : (q, B) ∈ Γ.nodes) {pr : Path s × Label} (hpr : pr ∈ B.pairsAt q) :
    pr ∈ Γ.defPairs :=
  mem_nodePairs Γ.nodes (q, B) h pr hpr

/-- Every label of a node is a pair at the node's own path. -/
theorem Ctx.mem_defPairs_label {Γ : Ctx s} {q : Path s} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} (h : (q, Block.obj W ls vls ch) ∈ Γ.nodes)
    {ℓ : Label} (hℓ : ℓ ∈ W.labels) : (q, ℓ) ∈ Γ.defPairs :=
  Ctx.mem_defPairs_of_node h (by
    show (q, ℓ) ∈ W.labels.map (fun ℓ => (q, ℓ)) ++ W.headNames
    exact List.mem_append_left _ (List.mem_map_of_mem (f := fun ℓ => (q, ℓ)) hℓ))

/-- Every head name of a witness of a node is a pair. -/
theorem Ctx.mem_defPairs_headName {Γ : Ctx s} {q : Path s} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} (h : (q, Block.obj W ls vls ch) ∈ Γ.nodes)
    {pr : Path s × Label} (hpr : pr ∈ W.headNames) : pr ∈ Γ.defPairs :=
  Ctx.mem_defPairs_of_node h (by
    show pr ∈ W.labels.map (fun ℓ => (q, ℓ)) ++ W.headNames
    exact List.mem_append_right _ hpr)

/-- The head name of a witness is a head name of the list it comes from.  An
unlisted label reads as `⊤`, which has no head name. -/
theorem Witnesses.mem_headNames_get {s : Sig} : ∀ (W : Witnesses s) (ℓ : Label)
    {pr : Path s × Label}, (W.get ℓ).headName? = some pr → pr ∈ W.headNames
  | .nil, _, _, h => by simp [Witnesses.get, Ty.headName?, Ty.top] at h
  | .cons W ℓ' T, ℓ, pr, h => by
      show pr ∈ T.headName?.toList ++ W.headNames
      by_cases he : ℓ = ℓ'
      · have hT : T.headName? = some pr := by
          rw [show (Witnesses.cons W ℓ' T).get ℓ = T from by simp [Witnesses.get, he]] at h
          exact h
        rw [hT]
        exact List.mem_append_left _ (by simp)
      · have h' : (W.get ℓ).headName? = some pr := by
          rw [show (Witnesses.cons W ℓ' T).get ℓ = W.get ℓ from by simp [Witnesses.get, he]] at h
          exact h
        exact List.mem_append_right _ (Witnesses.mem_headNames_get W ℓ h')

theorem Block.mem_nodes_self {s : Sig} (B : Block s) (p : Path s) : (p, B) ∈ B.nodes p := by
  cases B with
  | obj W ls vls ch => exact List.mem_cons_self ..
  | fwd r => exact List.mem_cons_self ..

/-- The child a list of children selects is a node at the child's own path. -/
theorem Children.mem_nodes_at? {s : Sig} : ∀ (ch : Children s) (p : Path s) (a : Label)
    {B : Block s}, ch.at? a = some B → ((.sel p a : Path s), B) ∈ ch.nodes p
  | .nil, _, _, _, h => by simp [Children.at?] at h
  | .cons ch a' b, p, a, B, h => by
      show (Path.sel p a, B) ∈ b.nodes (.sel p a') ++ ch.nodes p
      by_cases he : a = a'
      · subst he
        have hB : b = B := by
          rw [show (Children.cons ch a b).at? a = some b from by simp [Children.at?]] at h
          exact Option.some.inj h
        subst hB
        exact List.mem_append_left _ (Block.mem_nodes_self b (.sel p a))
      · have h' : ch.at? a = some B := by
          rw [show (Children.cons ch a' b).at? a = ch.at? a from by
            simp [Children.at?, he]] at h
          exact h
        exact List.mem_append_right _ (Children.mem_nodes_at? ch p a h')

/-- A list of nodes is closed when every child of a node it lists is itself
listed, at the child's own path. -/
def NodesClosed {s : Sig} (ns : List (Path s × Block s)) : Prop :=
  ∀ (q : Path s) (W : Witnesses s) (ls vls : List Label) (ch : Children s),
    (q, Block.obj W ls vls ch) ∈ ns →
      ∀ (a : Label) (B : Block s), ch.at? a = some B → ((.sel q a : Path s), B) ∈ ns

theorem NodesClosed.append {s : Sig} {ns ms : List (Path s × Block s)}
    (h₁ : NodesClosed ns) (h₂ : NodesClosed ms) : NodesClosed (ns ++ ms) := by
  intro q W ls vls ch hmem a B hat
  rcases List.mem_append.mp hmem with h | h
  · exact List.mem_append_left _ (h₁ q W ls vls ch h a B hat)
  · exact List.mem_append_right _ (h₂ q W ls vls ch h a B hat)

theorem NodesClosed.map {s : Sig} {k : Kind} {ns : List (Path s × Block s)}
    (hns : NodesClosed ns) :
    NodesClosed (ns.map (fun n => ((n.1.weaken : Path (s,,k)), n.2.weaken))) := by
  intro q W ls vls ch hmem a B hat
  obtain ⟨n, hn, he⟩ := List.mem_map.mp hmem
  obtain ⟨p₀, B₀⟩ := n
  cases B₀ with
  | fwd r => exact absurd he (by simp [Block.weaken, Block.rename])
  | obj W₀ ls₀ vls₀ ch₀ =>
      have h₁ : (p₀.weaken : Path (s,,k)) = q := congrArg Prod.fst he
      have h₂ : ((Block.obj W₀ ls₀ vls₀ ch₀).weaken : Block (s,,k))
          = Block.obj W ls vls ch := congrArg Prod.snd he
      rw [show ((Block.obj W₀ ls₀ vls₀ ch₀).weaken : Block (s,,k))
            = Block.obj (W₀.rename Rename.succ) ls₀ vls₀ (ch₀.rename Rename.succ) from rfl] at h₂
      injection h₂ with _ _ _ e₄
      rw [← e₄, Children.at?_rename] at hat
      cases h₀ : ch₀.at? a with
      | none => rw [h₀] at hat; simp at hat
      | some B₁ =>
          rw [h₀] at hat
          have hB : (B₁.weaken : Block (s,,k)) = B := by
            simpa [Block.weaken] using hat
          rw [← h₁, ← hB]
          exact List.mem_map_of_mem (hns p₀ W₀ ls₀ vls₀ ch₀ hn a B₁ h₀)

mutual
theorem Block.nodes_closed {s : Sig} : ∀ (B : Block s) (p : Path s), NodesClosed (B.nodes p)
  | .obj W ls vls ch, p => by
      intro q W' ls' vls' ch' hmem a B hat
      show (Path.sel q a, B) ∈ (p, Block.obj W ls vls ch) :: ch.nodes p
      rcases List.mem_cons.mp hmem with h | h
      · cases h
        exact List.mem_cons_of_mem _ (Children.mem_nodes_at? ch p a hat)
      · exact List.mem_cons_of_mem _ (Children.nodes_closed ch p q W' ls' vls' ch' h a B hat)
  | .fwd r, p => by
      intro q W ls vls ch hmem a B _
      exact absurd hmem (by simp [Block.nodes])

theorem Children.nodes_closed {s : Sig} :
    ∀ (ch : Children s) (p : Path s), NodesClosed (ch.nodes p)
  | .nil, p => by
      intro q W ls vls ch hmem a B _
      exact absurd hmem (by simp [Children.nodes])
  | .cons ch a' b, p => by
      exact NodesClosed.append (Block.nodes_closed b (.sel p a')) (Children.nodes_closed ch p)
end

theorem Ctx.nodes_closed : ∀ {s : Sig} (Γ : Ctx s), NodesClosed Γ.nodes
  | _, .nil => by
      intro q W ls vls ch hmem a B _
      exact absurd hmem (by simp [Ctx.nodes])
  | _, .cons Γ b => by
      have hb : NodesClosed (match b with
          | .transparent _ B => B.nodes (.var .here)
          | .opaque _ => []) := by
        cases b with
        | «opaque» T => intro q W ls vls ch hmem a B _; exact absurd hmem (by simp)
        | transparent T B₀ => exact Block.nodes_closed B₀ (.var .here)
      exact NodesClosed.append (Ctx.nodes_closed Γ).map hb

/-- The block of a binder is a node of the forest, at the binder's own path. -/
theorem Ctx.mem_nodes_blockAt : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var) {B : Block s},
    Γ.blockAt x = some B → ((.var x : Path s), B) ∈ Γ.nodes
  | _, .cons Γ (.transparent T B₀), .here, B, h => by
      have hB : B₀ = B := Option.some.inj h
      subst hB
      exact List.mem_append_right _ (Block.mem_nodes_self B₀ (.var .here))
  | _, .cons Γ (.opaque T), .here, B, h => by simp [Ctx.blockAt] at h
  | _, .cons Γ b, .there y, B, h => by
      have hb : (Ctx.cons Γ b).blockAt (.there y) = (Γ.blockAt y).map Block.weaken := by
        cases b with
        | «opaque» T => rfl
        | transparent T B₀ => rfl
      rw [hb] at h
      cases hy : Γ.blockAt y with
      | none => rw [hy] at h; simp at h
      | some B₀ =>
          rw [hy] at h
          have hB : (B₀.weaken : Block _) = B := by simpa using h
          rw [← hB]
          exact List.mem_append_left _
            (List.mem_map_of_mem (Ctx.mem_nodes_blockAt Γ y hy))

/-! ### The walk, by cases

The equations of `Ctx.blockFuel` at a constructor of the block it finds.  They
are `Ctx.blockFuel_var` and `Ctx.blockFuel_sel` with the match evaluated. -/

theorem Ctx.blockFuel_var_obj {Γ : Ctx s} {x : BVar s .var} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} (n : Nat)
    (hx : Γ.blockAt x = some (.obj W ls vls ch)) :
    Γ.blockFuel (n + 1) (.var x) = some (.obj W ls vls ch) := by
  rw [Ctx.blockFuel_var, hx]

theorem Ctx.blockFuel_var_fwd {Γ : Ctx s} {x : BVar s .var} {r : Path s} (n : Nat)
    (hx : Γ.blockAt x = some (.fwd r)) :
    Γ.blockFuel (n + 1) (.var x) = Γ.blockFuel n r := by
  rw [Ctx.blockFuel_var, hx]

theorem Ctx.blockFuel_var_of_none {Γ : Ctx s} {x : BVar s .var} (n : Nat)
    (hx : Γ.blockAt x = none) : Γ.blockFuel (n + 1) (.var x) = none := by
  rw [Ctx.blockFuel_var, hx]

theorem Ctx.blockFuel_sel_of {Γ : Ctx s} {p : Path s} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} {a : Label} (n : Nat)
    (hp : Γ.blockFuel (n + 1) p = some (.obj W ls vls ch)) :
    Γ.blockFuel (n + 1) (.sel p a) =
      (match ch.at? a with
       | some (.fwd r) => Γ.blockFuel n r
       | b => b) := by
  rw [Ctx.blockFuel_sel, hp]
  rfl

theorem Ctx.blockFuel_sel_of_none {Γ : Ctx s} {p : Path s} {a : Label} (n : Nat)
    (hp : Γ.blockFuel (n + 1) p = none) : Γ.blockFuel (n + 1) (.sel p a) = none := by
  rw [Ctx.blockFuel_sel, hp]

theorem Ctx.blockFuel_sel_of_fwd {Γ : Ctx s} {p r : Path s} {a : Label} (n : Nat)
    (hp : Γ.blockFuel (n + 1) p = some (.fwd r)) :
    Γ.blockFuel (n + 1) (.sel p a) = none := by
  rw [Ctx.blockFuel_sel, hp]

/-- The walk never returns a forwarding node: it follows one.  The special
case of `Ctx.lookupBlock_sel` where both the prefix and the child are object
nodes, kept under its own name since the general equation now carries that
name (P1.8, T2). -/
theorem Ctx.lookupBlock_sel_obj {Γ : Ctx s} {p : Path s} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} {a : Label}
    {W' : Witnesses s} {ls' vls' : List Label} {ch' : Children s}
    (hp : Γ.lookupBlock p = some (.obj W ls vls ch))
    (ha : ch.at? a = some (.obj W' ls' vls' ch')) :
    Γ.lookupBlock (.sel p a) = some (.obj W' ls' vls' ch') := by
  show Γ.blockFuel (Γ.fwdCount + 1) (.sel p a) = _
  rw [Ctx.blockFuel_sel_of Γ.fwdCount hp, ha]

/-- L2's other half.  Every block the walk returns is a node of the forest,
reached by the walk at that node's own path. -/
theorem Ctx.blockFuel_node {s : Sig} (Γ : Ctx s) :
    ∀ (n : Nat) (p : Path s) {B : Block s}, Γ.blockFuel n p = some B →
      ∃ q, Γ.lookupBlock q = some B ∧ (q, B) ∈ Γ.nodes
  | 0, _, _, h => by simp at h
  | n + 1, p, B, h => by
      revert B
      induction p with
      | var x =>
          intro B h
          cases hx : Γ.blockAt x with
          | none => rw [Ctx.blockFuel_var_of_none n hx] at h; simp at h
          | some B₀ =>
              cases B₀ with
              | obj W ls vls ch =>
                  rw [Ctx.blockFuel_var_obj n hx] at h
                  have hB : Block.obj W ls vls ch = B := Option.some.inj h
                  subst hB
                  exact ⟨.var x, Ctx.lookupBlock_var Γ x hx (by intro r hr; cases hr),
                    Ctx.mem_nodes_blockAt Γ x hx⟩
              | fwd r =>
                  rw [Ctx.blockFuel_var_fwd n hx] at h
                  exact Ctx.blockFuel_node Γ n r h
      | sel p' a ih =>
          intro B h
          cases hp : Γ.blockFuel (n + 1) p' with
          | none => rw [Ctx.blockFuel_sel_of_none n hp] at h; simp at h
          | some B₀ =>
              cases B₀ with
              | fwd r => rw [Ctx.blockFuel_sel_of_fwd n hp] at h; simp at h
              | obj W ls vls ch =>
                  obtain ⟨q, hq, hqm⟩ := ih _ hp
                  rw [Ctx.blockFuel_sel_of n hp] at h
                  cases ha : ch.at? a with
                  | none => rw [ha] at h; simp at h
                  | some B₁ =>
                      cases B₁ with
                      | obj W' ls' vls' ch' =>
                          rw [ha] at h
                          have hB : Block.obj W' ls' vls' ch' = B := Option.some.inj h
                          subst hB
                          exact ⟨.sel q a, Ctx.lookupBlock_sel_obj hq ha,
                            Ctx.nodes_closed Γ q W ls vls ch hqm a _ ha⟩
                      | fwd r =>
                          rw [ha] at h
                          exact Ctx.blockFuel_node Γ n r h

theorem Ctx.lookupBlock_node {Γ : Ctx s} {p : Path s} {B : Block s}
    (h : Γ.lookupBlock p = some B) : ∃ q, Γ.lookupBlock q = some B ∧ (q, B) ∈ Γ.nodes :=
  Γ.blockFuel_node _ p h

/-! ## Defined names of a context -/

theorem Ctx.lookupDefP_of_none {Γ : Ctx s} {p : Path s} (ℓ : Label)
    (hb : Γ.lookupBlock p = none) : Γ.lookupDefP p ℓ = none := by
  rw [Ctx.lookupDefP_eq_bind, hb]
  rfl

theorem Ctx.lookupDefP_of_fwd {Γ : Ctx s} {p r : Path s} (ℓ : Label)
    (hb : Γ.lookupBlock p = some (.fwd r)) : Γ.lookupDefP p ℓ = none := by
  rw [Ctx.lookupDefP_eq_bind, hb]
  rfl

theorem Ctx.lookupDefP_of_obj {Γ : Ctx s} {p : Path s} (ℓ : Label) {W₀ : Witnesses s}
    {ls vls : List Label} {ch : Children s}
    (hb : Γ.lookupBlock p = some (.obj W₀ ls vls ch)) : Γ.lookupDefP p ℓ = some (W₀.get ℓ) := by
  rw [Ctx.lookupDefP_eq_bind, hb]
  rfl

theorem Ctx.nodes_cons_transparent (Γ : Ctx s) (T : Ty s) (B : Block (s,x)) :
    (Ctx.cons Γ (.transparent T B)).nodes =
      Γ.nodes.map (fun n => ((n.1.weaken : Path (s,x)), n.2.weaken)) ++ B.nodes (.var .here) :=
  rfl

theorem Ctx.nodes_cons_opaque (Γ : Ctx s) (T : Ty s) :
    (Ctx.cons Γ (.opaque T)).nodes =
      Γ.nodes.map (fun n => ((n.1.weaken : Path (s,x)), n.2.weaken)) := by
  simp [Ctx.nodes]

/-- L2.  A defined name is a listed pair, unless its definition is `⊤` or the
walk to it goes through a forwarding, in which case the name it forwards to is
a listed pair with the same block. -/
theorem Ctx.lookupDefP_defPairs (Γ : Ctx s) (p : Path s) (ℓ : Label) (W : Ty s)
    (h : Γ.lookupDefP p ℓ = some W) :
    (p, ℓ) ∈ Γ.defPairs ∨ W = ⊤ ∨
      ∃ q, Γ.lookupBlock p = Γ.lookupBlock q ∧ (q, ℓ) ∈ Γ.defPairs := by
  cases hb : Γ.lookupBlock p with
  | none => rw [Ctx.lookupDefP_of_none ℓ hb] at h; simp at h
  | some B =>
      cases B with
      | fwd r => rw [Ctx.lookupDefP_of_fwd ℓ hb] at h; simp at h
      | obj W₀ ls vls ch =>
          rw [Ctx.lookupDefP_of_obj ℓ hb] at h
          have hW : W₀.get ℓ = W := Option.some.inj h
          by_cases hm : ℓ ∈ W₀.labels
          · obtain ⟨q, hq, hqm⟩ := Ctx.lookupBlock_node hb
            exact Or.inr (Or.inr ⟨q, by rw [hq], Ctx.mem_defPairs_label hqm hm⟩)
          · exact Or.inr (Or.inl (by rw [← hW]; exact Witnesses.get_of_not_mem_labels W₀ hm))

/-- The type one step produces is a witness of a node, so if it is a name at
all then it is a listed pair. -/
theorem Ctx.next_mem_defPairs (Γ : Ctx s) {V W : Ty s} {p : Path s} {ℓ : Label}
    (h : Γ.next V = some W) (hW : W.headName? = some (p, ℓ)) : (p, ℓ) ∈ Γ.defPairs := by
  cases V with
  | bot => simp [Ctx.next] at h
  | pi => simp [Ctx.next] at h
  | obj => simp [Ctx.next] at h
  | sel p₀ ℓ₀ =>
      rw [Ctx.next_sel] at h
      cases hb : Γ.lookupBlock p₀ with
      | none => rw [Ctx.lookupDefP_of_none ℓ₀ hb] at h; simp at h
      | some B =>
          cases B with
          | fwd r => rw [Ctx.lookupDefP_of_fwd ℓ₀ hb] at h; simp at h
          | obj W₀ ls vls ch =>
              rw [Ctx.lookupDefP_of_obj ℓ₀ hb] at h
              have hW₀ : W₀.get ℓ₀ = W := Option.some.inj h
              obtain ⟨q, _, hqm⟩ := Ctx.lookupBlock_node hb
              exact Ctx.mem_defPairs_headName hqm
                (Witnesses.mem_headNames_get W₀ ℓ₀ (by rw [hW₀]; exact hW))

/-! ## Stability of the fuel

A chain that has not settled within its fuel stands, after its first step, at
a listed pair, and at every step at a listed *key*: the block its prefix
denotes and its label.  A chain longer than the list of pairs therefore
repeats a key, and from a repeated key it is periodic, so it never settles and
more fuel changes nothing. -/

theorem Ctx.chain_step (Γ : Ctx s) (T : Ty s) (i : Nat) {V : Ty s}
    (h : Γ.chain T i = some V) : Γ.chain T (i + 1) = Γ.next V := by
  rw [Ctx.chain_succ, h]
  rfl

/-- No type on an unsettled chain, save possibly the last, is `⊤`. -/
theorem Ctx.chain_ne_top (Γ : Ctx s) {T : Ty s} {n : Nat}
    (hsome : (Γ.chain T (n + 1)).isSome) (hne : Γ.chain T (n + 1) ≠ some ⊤)
    {i : Nat} (hi : i < n + 1) {W : Ty s} (hW : Γ.chain T (i + 1) = some W) : W ≠ ⊤ := by
  rcases Nat.lt_or_ge (i + 1) (n + 1) with hin | hin
  · intro hWtop
    have h2 : (Γ.chain T (i + 1 + 1)).isSome := Γ.chain_isSome_of_le (by omega) hsome
    rw [Ctx.chain_succ, hW, hWtop] at h2
    simp at h2
  · have hin' : i + 1 = n + 1 := by omega
    rw [hin'] at hW
    intro hWtop
    exact hne (by rw [hW, hWtop])

/-- L3.  After one step a chain stands at a listed pair.  The first name of a
chain need not be listed: the walk to its prefix may follow a forwarding, and
the name it forwards to is the listed one. -/
theorem Ctx.chain_mem_defPairs_succ (Γ : Ctx s) {T : Ty s} {n : Nat}
    (hsome : (Γ.chain T (n + 1)).isSome) :
    ∀ i, 1 ≤ i → i < n + 1 →
      Γ.chain T i ∈ Γ.defPairs.map (fun pr => some ((pr.1 : Path s) ∙ pr.2)) := by
  intro i hi1 hi
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  subst hj
  have h2 : (Γ.chain T (j + 1 + 1)).isSome := Γ.chain_isSome_of_le (by omega) hsome
  have h1 : (Γ.chain T (j + 1)).isSome := Γ.chain_isSome_of_le (by omega) hsome
  have h0 : (Γ.chain T j).isSome := Γ.chain_isSome_of_le (by omega) hsome
  cases hcj : Γ.chain T j with
  | none => rw [hcj] at h0; simp at h0
  | some V =>
      cases hcW : Γ.chain T (j + 1) with
      | none => rw [hcW] at h1; simp at h1
      | some W =>
          have hstep : Γ.next V = some W := by rw [← Γ.chain_step T j hcj]; exact hcW
          have hWs : (Γ.next W).isSome := by
            rw [← Γ.chain_step T (j + 1) hcW]; exact h2
          cases W with
          | bot => simp [Ctx.next] at hWs
          | pi S U => simp [Ctx.next] at hWs
          | obj Tel => simp [Ctx.next] at hWs
          | sel p ℓ =>
              exact List.mem_map_of_mem
                (f := fun pr => some ((pr.1 : Path s) ∙ pr.2))
                (Γ.next_mem_defPairs hstep rfl)

/-- The key of a name: the block its prefix denotes, and its label.  One step
of a chain reads the name only through its key. -/
def Ctx.key (Γ : Ctx s) : Ty s → Option (Option (Block s) × Label)
  | .sel p ℓ => some (Γ.lookupBlock p, ℓ)
  | _ => none

/-- The key a chain stands at. -/
def Ctx.chainKey (Γ : Ctx s) (T : Ty s) (i : Nat) : Option (Option (Block s) × Label) :=
  (Γ.chain T i).bind Γ.key

/-- The keys of the listed pairs.  One per pair, so the list is as long. -/
def Ctx.keyPairs (Γ : Ctx s) : List (Option (Option (Block s) × Label)) :=
  Γ.defPairs.map (fun pr => some (Γ.lookupBlock pr.1, pr.2))

theorem Ctx.keyPairs_length (Γ : Ctx s) : Γ.keyPairs.length = Γ.defPairs.length :=
  List.length_map ..

/-- One step of a chain is a function of the key it stands at. -/
theorem Ctx.chain_succ_key (Γ : Ctx s) (T : Ty s) (i : Nat) :
    Γ.chain T (i + 1) =
      (Γ.chainKey T i).bind (fun k => k.1.bind (fun B => B.def? k.2)) := by
  rw [Ctx.chain_succ, Ctx.chainKey]
  cases h : Γ.chain T i with
  | none => rfl
  | some V =>
      cases V with
      | bot => rfl
      | pi => rfl
      | obj => rfl
      | sel p ℓ =>
          show Γ.next (.sel p ℓ) = _
          rw [Ctx.next_sel, Ctx.lookupDefP_eq_bind]
          rfl

theorem Ctx.chain_succ_eq_of_key (Γ : Ctx s) {T : Ty s} {i j : Nat}
    (h : Γ.chainKey T i = Γ.chainKey T j) : Γ.chain T (i + 1) = Γ.chain T (j + 1) := by
  rw [Ctx.chain_succ_key, Ctx.chain_succ_key, h]

/-- Every key a chain stands at, before it settles, is a listed key.  At the
first index this is L2, whose third disjunct is what a forwarding name needs;
at every later index it is L3. -/
theorem Ctx.chainKey_mem_keyPairs (Γ : Ctx s) {T : Ty s} {n : Nat}
    (hsome : (Γ.chain T (n + 1)).isSome) (hne : Γ.chain T (n + 1) ≠ some ⊤) :
    ∀ i, i < n + 1 → Γ.chainKey T i ∈ Γ.keyPairs := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · subst hi0
    have h1 : (Γ.chain T 1).isSome := Γ.chain_isSome_of_le (by omega) hsome
    have hc1 : Γ.chain T 1 = Γ.next T := Γ.chain_step T 0 rfl
    cases hstep : Γ.next T with
    | none => rw [hc1, hstep] at h1; simp at h1
    | some W =>
        have hWne : W ≠ ⊤ := Γ.chain_ne_top hsome hne (by omega) (by rw [hc1]; exact hstep)
        cases T with
        | bot => simp [Ctx.next] at hstep
        | pi S U => simp [Ctx.next] at hstep
        | obj Tel => simp [Ctx.next] at hstep
        | sel p ℓ =>
            show some (Γ.lookupBlock p, ℓ) ∈ Γ.keyPairs
            have hlk : Γ.lookupDefP p ℓ = some W := hstep
            rcases Γ.lookupDefP_defPairs p ℓ W hlk with hmem | htop | ⟨q, hq, hqm⟩
            · exact List.mem_map_of_mem
                (f := fun pr => some (Γ.lookupBlock pr.1, pr.2)) hmem
            · exact absurd htop hWne
            · rw [hq]
              exact List.mem_map_of_mem
                (f := fun pr => some (Γ.lookupBlock pr.1, pr.2)) hqm
  · obtain ⟨pr, hpr, hc⟩ := List.mem_map.mp (Γ.chain_mem_defPairs_succ hsome i hi1 hi)
    have hkey : Γ.chainKey T i = some (Γ.lookupBlock pr.1, pr.2) := by
      rw [Ctx.chainKey, ← hc]
      rfl
    rw [hkey]
    exact List.mem_map_of_mem (f := fun pr => some (Γ.lookupBlock pr.1, pr.2)) hpr

/-- A repeated key makes the chain periodic from one step after the first
occurrence on. -/
theorem Ctx.chain_periodic (Γ : Ctx s) {T : Ty s} {i j : Nat} (hij : i ≤ j)
    (h : Γ.chain T i = Γ.chain T j) :
    ∀ m, i ≤ m → Γ.chain T (m + (j - i)) = Γ.chain T m := by
  intro m him
  rw [show m + (j - i) = j + (m - i) by omega, Ctx.chain_add, ← h, ← Ctx.chain_add,
    show i + (m - i) = m by omega]

/-- Once the fuel is at least the number of listed pairs, one more unit changes
nothing. -/
theorem Ctx.resolveFuel_succ_eq {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) (T : Ty s) :
    Γ.resolveFuel n T = Γ.resolveFuel (n + 1) T := by
  cases hcs : Γ.chain T (n + 1) with
  | none =>
      obtain ⟨i, U, hi, hcU, hu⟩ := Γ.chain_settles hcs
      have e1 : Γ.resolveFuel n T = U := Γ.resolveFuel_of_chain i (by omega) hcU hu
      have e2 : Γ.resolveFuel (n + 1) T = U := Γ.resolveFuel_of_chain i (by omega) hcU hu
      rw [e1, e2]
  | some U =>
      have hsome : (Γ.chain T (n + 1)).isSome := by rw [hcs]; rfl
      rw [Γ.resolveFuel_eq_top n hsome]
      have hdec : Decidable (U = ⊤) := inferInstance
      cases hdec with
      | isTrue htop =>
          have e : Γ.resolveFuel (n + 1) T = U :=
            Γ.resolveFuel_of_chain (n + 1) (Nat.le_refl _) hcs (by rw [htop]; rfl)
          rw [e, htop]
      | isFalse htop =>
          have hne : Γ.chain T (n + 1) ≠ some ⊤ := by
            rw [hcs]; intro hc; exact htop (Option.some.inj hc)
          have hmem := Γ.chainKey_mem_keyPairs hsome hne
          have hlen : Γ.keyPairs.length < n + 1 := by
            rw [Ctx.keyPairs_length]; omega
          obtain ⟨j, hjn, i, hij, heq⟩ :=
            exists_repeat (Γ.chainKey T) _ (n + 1) hmem hlen
          have hstep : Γ.chain T (i + 1) = Γ.chain T (j + 1) := Γ.chain_succ_eq_of_key heq
          have hper := Γ.chain_periodic (Nat.succ_le_succ (Nat.le_of_lt hij)) hstep
          have hkey : Γ.chain T (n + 1 + 1) = Γ.chain T (n + 2 - (j - i)) := by
            have hp := hper (n + 2 - (j - i)) (by omega)
            rw [show n + 2 - (j - i) + (j + 1 - (i + 1)) = n + 1 + 1 by omega] at hp
            exact hp
          have h2 : (Γ.chain T (n + 2 - (j - i))).isSome :=
            Γ.chain_isSome_of_le (by omega) hsome
          rw [Γ.resolveFuel_eq_top (n + 1) (by rw [hkey]; exact h2)]

theorem Ctx.resolveFuel_eq_of_le {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) :
    ∀ {m : Nat}, n ≤ m → ∀ (T : Ty s), Γ.resolveFuel n T = Γ.resolveFuel m T := by
  intro m
  induction m with
  | zero => intro hnm T; rw [show n = 0 by omega]
  | succ m ih =>
      intro hnm T
      rcases Nat.eq_or_lt_of_le hnm with h | h
      · rw [h]
      · rw [ih (by omega) T]
        exact Ctx.resolveFuel_succ_eq (by omega) T

/-- L4.  Any fuel beyond the number of listed pairs computes `Ctx.resolve`. -/
theorem Ctx.resolveFuel_stable {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) (T : Ty s) :
    Γ.resolveFuel n T = Γ.resolve T := by
  rw [Ctx.resolve,
    Ctx.resolveFuel_eq_of_le hn (m := n + Γ.defPairs.length + 2) (by omega) T,
    Ctx.resolveFuel_eq_of_le (n := Γ.defPairs.length + 2) (by omega)
      (m := n + Γ.defPairs.length + 2) (by omega) T]

/-! ## Resolution -/

/-- Resolution commutes with one unfolding step; no side condition on the
context is needed, a cyclic chain of aliases resolving to `⊤` on both sides. -/
theorem Ctx.resolve_selP_some {Γ : Ctx s} {p : Path s} {ℓ : Label} {W : Ty s}
    (h : Γ.lookupDefP p ℓ = some W) : Γ.resolve (.sel p ℓ) = Γ.resolve W := by
  rw [Ctx.resolve, Γ.resolveFuel_selP_some (Γ.defPairs.length + 1) h]
  exact Ctx.resolveFuel_stable (by omega) W

/-- The same at a binder, which is the path of depth zero. -/
theorem Ctx.resolve_sel_some {Γ : Ctx s} {x : BVar s .var} {ℓ : Label} {W : Ty s}
    (h : Γ.lookupDef x ℓ = some W) : Γ.resolve (.sel x ℓ) = Γ.resolve W :=
  Ctx.resolve_selP_some (Ctx.lookupDefP_var_of_lookupDef h)

/-- The result of resolution is settled: a shape, or a name without a definition. -/
theorem Ctx.resolve_settled (Γ : Ctx s) (T : Ty s) : Γ.next (Γ.resolve T) = none := by
  rw [Ctx.resolve]
  cases hcs : Γ.chain T (Γ.defPairs.length + 2 + 1) with
  | none =>
      obtain ⟨i, U, hi, hcU, hu⟩ := Γ.chain_settles hcs
      rw [Γ.resolveFuel_of_chain i hi hcU hu]
      exact hu
  | some U =>
      rw [Γ.resolveFuel_eq_top (Γ.defPairs.length + 2) (by rw [hcs]; rfl)]
      rfl

/-- Resolution is idempotent. -/
theorem Ctx.resolve_resolve {Γ : Ctx s} (T : Ty s) :
    Γ.resolve (Γ.resolve T) = Γ.resolve T :=
  Γ.resolveFuel_settled (Γ.resolve_settled T) _

end FCdot

end Paths
