import Coercions.Classifiers.FCdot.Normalizer
import Coercions.Classifiers.FCdot.Typing
import Coercions.Classifiers.FCdot.TypingRename
import Coercions.Classifiers.FCdot.Levels

namespace Classifiers

/-!
# Alias-tolerant resolution through transparent definitions

`Ctx.resolve` follows transparent definitions at the head of a type
(`Ctx.next`, one step) with a fixed fuel budget `Γ.defPairs.length + 1`.
Aliases inside one block are allowed, so an alias chain need not reach a
shape: it either *settles* (a shape, or a name whose binder is opaque) or is
cyclic, and a cyclic chain resolves to `⊤`.

The budget suffices because every step of a chain that has not settled is a
name defined by the context, and a chain longer than the list of all defined
names (`Ctx.defPairs`) repeats one of them, after which it is periodic and
never settles.  Hence resolution is stable in the fuel
(`Ctx.resolveFuel_stable`), is idempotent (`Ctx.resolve_resolve`), and
commutes with one unfolding step (`Ctx.resolve_sel_some`), all without any
side condition on the context.
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

@[simp] theorem Ctx.next_sel (Γ : Ctx s) (x : BVar s .var) (ℓ : Label) :
    Γ.next (.sel x ℓ) = Γ.lookupDef x ℓ := rfl

@[simp] theorem Ctx.next_top (Γ : Ctx s) : Γ.next (⊤ : Shape s) = none := rfl

theorem Ctx.next_nonSel {Γ : Ctx s} {T : Shape s} (h : ∀ x ℓ, T ≠ .sel x ℓ) :
    Γ.next T = none := by
  cases T with
  | sel x ℓ => exact absurd rfl (h x ℓ)
  | bot => rfl
  | pi => rfl
  | obj => rfl
  | box => rfl

/-! ## Basic resolution equations -/

/-- A settled type resolves to itself, with any fuel. -/
theorem Ctx.resolveFuel_settled (Γ : Ctx s) {T : Shape s} (h : Γ.next T = none) :
    ∀ n : Nat, Γ.resolveFuel n T = T
  | 0 => by simp [Ctx.resolveFuel, h]
  | _ + 1 => by simp [Ctx.resolveFuel, h]

theorem Ctx.resolveFuel_nonSel (Γ : Ctx s) (n : Nat) {T : Shape s}
    (h : ∀ x ℓ, T ≠ .sel x ℓ) : Γ.resolveFuel n T = T :=
  Γ.resolveFuel_settled (Ctx.next_nonSel h) n

theorem Ctx.resolve_nonSel (Γ : Ctx s) {T : Shape s} (h : ∀ x ℓ, T ≠ .sel x ℓ) :
    Γ.resolve T = T := Γ.resolveFuel_nonSel _ h

@[simp] theorem Ctx.resolve_top (Γ : Ctx s) : Γ.resolve (.top : Shape s) = .top :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_bot (Γ : Ctx s) : Γ.resolve (.bot : Shape s) = .bot :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_pi (Γ : Ctx s) (S : Dom s) (T : Cod s) :
    Γ.resolve (.pi S T) = .pi S T :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_obj (Γ : Ctx s) (Tel : Telescope (s,x)) :
    Γ.resolve (.obj Tel) = .obj Tel :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_box (Γ : Ctx s) (T : Ty s) :
    Γ.resolve (.box T) = .box T :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

theorem Ctx.resolveFuel_sel_none (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolveFuel n (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_settled (by simp [h]) n

theorem Ctx.resolve_sel_none (Γ : Ctx s) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolve (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_sel_none _ h

theorem Ctx.resolveFuel_sel_some (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    {W : Shape s} (h : Γ.lookupDef x ℓ = some W) :
    Γ.resolveFuel (n + 1) (.sel x ℓ) = Γ.resolveFuel n W := by
  simp [Ctx.resolveFuel, h]

/-! ## Alias chains

The chain of a type is the sequence of its alias steps; it is `none` from the
point where the type has settled. -/

/-- `Γ.chain T i`: the type reached from `T` by `i` alias steps, if the chain
has not settled before. -/
def Ctx.chain (Γ : Ctx s) (T : Shape s) : Nat → Option (Shape s)
  | 0 => some T
  | i + 1 => (Γ.chain T i).bind Γ.next

@[simp] theorem Ctx.chain_zero (Γ : Ctx s) (T : Shape s) : Γ.chain T 0 = some T := rfl

theorem Ctx.chain_succ (Γ : Ctx s) (T : Shape s) (i : Nat) :
    Γ.chain T (i + 1) = (Γ.chain T i).bind Γ.next := rfl

/-- The chain may also be peeled at the front. -/
theorem Ctx.chain_succ_head (Γ : Ctx s) (T : Shape s) :
    ∀ i : Nat, Γ.chain T (i + 1) = (Γ.next T).bind (fun W => Γ.chain W i)
  | 0 => by cases h : Γ.next T <;> simp [Ctx.chain, h]
  | i + 1 => by
      rw [Ctx.chain_succ, Ctx.chain_succ_head Γ T i, Option.bind_assoc]
      cases h : Γ.next T with
      | none => rfl
      | some W => simp [Ctx.chain_succ]

theorem Ctx.chain_add (Γ : Ctx s) (k : Nat) :
    ∀ (i : Nat) (T : Shape s), Γ.chain T (i + k) = (Γ.chain T i).bind (fun U => Γ.chain U k)
  | 0, T => by simp [Ctx.chain]
  | i + 1, T => by
      rw [show i + 1 + k = (i + k) + 1 by omega, Ctx.chain_succ_head, Ctx.chain_succ_head,
        Option.bind_assoc]
      cases h : Γ.next T with
      | none => rfl
      | some W => simp [Ctx.chain_add Γ k i W]

theorem Ctx.chain_isSome_of_le (Γ : Ctx s) {T : Shape s} {m n : Nat} (hmn : m ≤ n)
    (h : (Γ.chain T n).isSome) : (Γ.chain T m).isSome := by
  rw [show n = m + (n - m) by omega, Ctx.chain_add] at h
  cases hc : Γ.chain T m with
  | none => rw [hc] at h; simp at h
  | some _ => simp

/-- If the chain settles within the available fuel, the settled type is the result. -/
theorem Ctx.resolveFuel_of_chain (Γ : Ctx s) :
    ∀ (i : Nat) {n : Nat} {T U : Shape s}, i ≤ n → Γ.chain T i = some U → Γ.next U = none →
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
    ∀ (n : Nat) {T : Shape s}, (Γ.chain T (n + 1)).isSome → Γ.resolveFuel n T = ⊤
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
theorem Ctx.chain_settles (Γ : Ctx s) {T : Shape s} :
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

/-! ## Defined names of a context -/

theorem Ctx.defPairs_cons_transparent (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) :
    (Ctx.cons Γ (.transparent T W Wc Fs)).defPairs =
      Γ.defPairs.map (fun p => (BVar.there p.1, p.2)) ++
        W.labels.map (fun ℓ => (BVar.here, ℓ)) := rfl

theorem Ctx.defPairs_consC (Γ : Ctx s) (b : CapBound s) :
    (Ctx.consC Γ b).defPairs = Γ.defPairs.map (fun p => (BVar.there p.1, p.2)) := rfl

theorem Ctx.defPairs_cons_opaque (Γ : Ctx s) (T : Ty s) :
    (Ctx.cons Γ (.opaque T)).defPairs =
      Γ.defPairs.map (fun p => (BVar.there p.1, p.2)) := by
  simp [Ctx.defPairs]

/-- A name with a definition is one of the context's defined names, unless its
definition is the vacuous witness `⊤`. -/
theorem Ctx.lookupDef_defPairs : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var) (ℓ : Label)
    (W : Shape s), Γ.lookupDef x ℓ = some W → (x, ℓ) ∈ Γ.defPairs ∨ W = ⊤
  | _, .cons Γ (.transparent T W₀ Wc Fs), .here, ℓ, W, h => by
      rw [Ctx.lookupDef_here_transparent] at h
      have hW : W = W₀.get ℓ := (Option.some.inj h).symm
      have hdec : Decidable (ℓ ∈ W₀.labels) := inferInstance
      cases hdec with
      | isTrue hm =>
          refine Or.inl ?_
          rw [Ctx.defPairs_cons_transparent]
          exact List.mem_append_right _
            (List.mem_map_of_mem (f := fun ℓ => (BVar.here, ℓ)) hm)
      | isFalse hm =>
          exact Or.inr (by rw [hW]; exact Witnesses.get_of_not_mem_labels W₀ hm)
  | _, .cons Γ (.opaque T), .here, ℓ, W, h => by
      rw [Ctx.lookupDef_here_opaque] at h; simp at h
  | _, .consC Γ _, .there y, ℓ, W, h => by
      rw [Ctx.lookupDef_thereC] at h
      cases hd : Γ.lookupDef y ℓ with
      | none => rw [hd] at h; simp at h
      | some W₀ =>
          rw [hd] at h
          simp only [Option.map_some] at h
          have hW : W = W₀↑ := (Option.some.inj h).symm
          rcases Ctx.lookupDef_defPairs Γ y ℓ W₀ hd with hmem | htop
          · refine Or.inl ?_
            rw [Ctx.defPairs_consC]
            exact List.mem_map_of_mem (f := fun p => (BVar.there p.1, p.2)) hmem
          · exact Or.inr (by rw [hW, htop]; rfl)
  | _, .cons Γ b, .there y, ℓ, W, h => by
      rw [Ctx.lookupDef_there] at h
      cases hd : Γ.lookupDef y ℓ with
      | none => rw [hd] at h; simp at h
      | some W₀ =>
          rw [hd] at h
          simp only [Option.map_some] at h
          have hW : W = W₀↑ := (Option.some.inj h).symm
          rcases Ctx.lookupDef_defPairs Γ y ℓ W₀ hd with hmem | htop
          · refine Or.inl ?_
            cases b with
            | transparent T' W' Fs' =>
                rw [Ctx.defPairs_cons_transparent]
                exact List.mem_append_left _
                  (List.mem_map_of_mem (f := fun p => (BVar.there p.1, p.2)) hmem)
            | «opaque» T' =>
                rw [Ctx.defPairs_cons_opaque]
                exact List.mem_map_of_mem (f := fun p => (BVar.there p.1, p.2)) hmem
          · exact Or.inr (by rw [hW, htop]; rfl)

/-! ## Stability of the fuel

A chain that has not settled within its fuel consists of defined names; a
chain longer than `Ctx.defPairs` therefore repeats a name and is periodic from
that point on, so it never settles and more fuel changes nothing. -/

/-- The names on an unsettled chain, save one whose definition is `⊤`, are
defined names of the context. -/
theorem Ctx.chain_mem_defPairs (Γ : Ctx s) {T : Shape s} {n : Nat}
    (hsome : (Γ.chain T (n + 1)).isSome) (hne : Γ.chain T (n + 1) ≠ some ⊤) :
    ∀ i, i < n + 1 →
      Γ.chain T i ∈ Γ.defPairs.map (fun p => some ((p.1 : BVar s .var) ∙ p.2)) := by
  intro i hi
  have hi1 : (Γ.chain T (i + 1)).isSome := Γ.chain_isSome_of_le (by omega) hsome
  cases hci : Γ.chain T i with
  | none => rw [Ctx.chain_succ, hci] at hi1; simp at hi1
  | some V =>
      cases hnv : Γ.next V with
      | none =>
          have hv : (Γ.next V).isSome := by rw [Ctx.chain_succ, hci] at hi1; exact hi1
          rw [hnv] at hv; simp at hv
      | some W =>
          have hstep : Γ.chain T (i + 1) = some W := by
            rw [Ctx.chain_succ, hci]; exact hnv
          have hWne : W ≠ ⊤ := by
            rcases Nat.lt_or_ge (i + 1) (n + 1) with hin | hin
            · intro hWtop
              have h2 : (Γ.chain T (i + 1 + 1)).isSome := Γ.chain_isSome_of_le (by omega) hsome
              rw [Ctx.chain_succ, hstep, hWtop] at h2
              simp at h2
            · have hin' : i + 1 = n + 1 := by omega
              rw [hin'] at hstep
              intro hWtop
              exact hne (by rw [hstep, hWtop])
          cases V with
          | bot => simp [Ctx.next] at hnv
          | pi => simp [Ctx.next] at hnv
          | obj => simp [Ctx.next] at hnv
          | box => simp [Ctx.next] at hnv
          | sel y ℓ =>
              have hlk : Γ.lookupDef y ℓ = some W := by simpa using hnv
              rcases Ctx.lookupDef_defPairs Γ y ℓ W hlk with hmem | htop
              · exact List.mem_map_of_mem
                  (f := fun p => some ((p.1 : BVar s .var) ∙ p.2)) hmem
              · exact absurd htop hWne

/-- A repeated name makes the chain periodic from the first occurrence on. -/
theorem Ctx.chain_periodic (Γ : Ctx s) {T : Shape s} {i j : Nat} (hij : i ≤ j)
    (h : Γ.chain T i = Γ.chain T j) :
    ∀ m, i ≤ m → Γ.chain T (m + (j - i)) = Γ.chain T m := by
  intro m him
  rw [show m + (j - i) = j + (m - i) by omega, Ctx.chain_add, ← h, ← Ctx.chain_add,
    show i + (m - i) = m by omega]

/-- Once the fuel is at least the number of defined names, one more unit changes
nothing. -/
theorem Ctx.resolveFuel_succ_eq {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) (T : Shape s) :
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
          have hmem := Γ.chain_mem_defPairs hsome hne
          have hlen : (Γ.defPairs.map
              (fun p => some ((p.1 : BVar s .var) ∙ p.2))).length < n + 1 := by
            rw [List.length_map]; omega
          obtain ⟨j, hjn, i, hij, heq⟩ :=
            exists_repeat (Γ.chain T) _ (n + 1) hmem hlen
          have hper := Γ.chain_periodic (Nat.le_of_lt hij) heq
          have hkey : Γ.chain T (n + 1 + 1) = Γ.chain T (n + 2 - (j - i)) := by
            have hp := hper (n + 2 - (j - i)) (by omega)
            rw [show n + 2 - (j - i) + (j - i) = n + 1 + 1 by omega] at hp
            exact hp
          have h2 : (Γ.chain T (n + 2 - (j - i))).isSome :=
            Γ.chain_isSome_of_le (by omega) hsome
          rw [Γ.resolveFuel_eq_top (n + 1) (by rw [hkey]; exact h2)]

theorem Ctx.resolveFuel_eq_of_le {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) :
    ∀ {m : Nat}, n ≤ m → ∀ (T : Shape s), Γ.resolveFuel n T = Γ.resolveFuel m T := by
  intro m
  induction m with
  | zero => intro hnm T; rw [show n = 0 by omega]
  | succ m ih =>
      intro hnm T
      rcases Nat.eq_or_lt_of_le hnm with h | h
      · rw [h]
      · rw [ih (by omega) T]
        exact Ctx.resolveFuel_succ_eq (by omega) T

/-- Any fuel beyond the number of defined names computes `Ctx.resolve`. -/
theorem Ctx.resolveFuel_stable {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) (T : Shape s) :
    Γ.resolveFuel n T = Γ.resolve T := by
  rw [Ctx.resolve,
    Ctx.resolveFuel_eq_of_le hn (m := n + Γ.defPairs.length + 1) (by omega) T,
    Ctx.resolveFuel_eq_of_le (n := Γ.defPairs.length + 1) (by omega)
      (m := n + Γ.defPairs.length + 1) (by omega) T]

/-! ## Resolution -/

/-- Resolution commutes with one unfolding step; no side condition on the
context is needed, a cyclic chain of aliases resolving to `⊤` on both sides. -/
theorem Ctx.resolve_sel_some {Γ : Ctx s} {x : BVar s .var} {ℓ : Label} {W : Shape s}
    (h : Γ.lookupDef x ℓ = some W) : Γ.resolve (.sel x ℓ) = Γ.resolve W := by
  rw [Ctx.resolve, Γ.resolveFuel_sel_some Γ.defPairs.length h]
  exact Ctx.resolveFuel_stable (Nat.le_refl _) W

/-- The result of resolution is settled: a shape, or a name without a definition. -/
theorem Ctx.resolve_settled (Γ : Ctx s) (T : Shape s) : Γ.next (Γ.resolve T) = none := by
  rw [Ctx.resolve]
  cases hcs : Γ.chain T (Γ.defPairs.length + 1 + 1) with
  | none =>
      obtain ⟨i, U, hi, hcU, hu⟩ := Γ.chain_settles hcs
      rw [Γ.resolveFuel_of_chain i hi hcU hu]
      exact hu
  | some U =>
      rw [Γ.resolveFuel_eq_top (Γ.defPairs.length + 1) (by rw [hcs]; rfl)]
      rfl

/-- Resolution is idempotent. -/
theorem Ctx.resolve_resolve {Γ : Ctx s} (T : Shape s) :
    Γ.resolve (Γ.resolve T) = Γ.resolve T :=
  Γ.resolveFuel_settled (Γ.resolve_settled T) _

/-! ## Capture resolution: `caps`, `roots`, and subcapturing

`caps_Γ n C` resolves a capture set to the atoms it stands for, with fuel `n`
for the capture names.  A term binder stands for the capture set of its type,
a capture binder for itself when its bound is a root or `∗` and for the
resolution of its bound otherwise, and a capture name `x ∙ ℓ` for the
resolution of the capture witness of its block, read by `Ctx.lookupDefC`.

A capture witness may name a label of its own block, so the name clause is the
one that needs fuel: every other clause descends on the binder of the atom and
is well founded on the spine of the context, while a chain of names stays at
one binder.  Running out of fuel on a name means the chain is cyclic, and a
cycle resolves to `[]`, the least solution — the capture analogue of a cyclic
type alias resolving to `⊤`.  Resolution is monotone in the fuel
(`Ctx.caps_mono_fuel`), so the *roots* of a set are the atoms it resolves to
at some fuel: `Γ.Root a C`.  `roots_Γ n` is `caps_Γ n` here; the compiler's
line redefines it as `expand ∘ caps`.

`CapLe Γ C D` is the inclusion of roots; it is reflexive, transitive, implied
by `Subset`, closed under union on the left, invariant under replacing a set
by one with the same roots, and monotone under store extension.  The
resolution lemma of the capture sort, `Ctx.Root_name`, says that a defined
capture name has exactly the roots of its witness. -/

/-! `Ty.captureSet` and its two simp lemmas are stated in `Syntax.lean`,
where store typing already needs them. -/

@[simp] theorem Ctx.lookupCap_here (Γ : Ctx s) (b : CapBound s) :
    (Ctx.consC Γ b).lookupCap .here = b↑ := rfl

@[simp] theorem Ctx.lookupCap_there (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Ctx.cons Γ b).lookupCap (.there κ) = (Γ.lookupCap κ)↑ := rfl

@[simp] theorem Ctx.lookupCap_thereC (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Ctx.consC Γ b).lookupCap (.there κ) = (Γ.lookupCap κ)↑ := rfl

/-- Weakening a capture set preserves syntactic inclusion. -/
theorem CaptureSet.Subset.weaken {C D : CaptureSet s} (h : C.Subset D) :
    (C.weaken (k := k)).Subset D.weaken := by
  intro a ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha ⊢
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨b, h b hb, rfl⟩

mutual

/-- `caps_Γ n C`: the atoms the capture set `C` resolves to, atom by atom,
with fuel `n` for capture names. -/
def Ctx.caps : (Γ : Ctx s) → Nat → CaptureSet s → CaptureSet s
  | _, _, [] => []
  | Γ, n, a :: C => Γ.capsAtom n a ++ Γ.caps n C
termination_by Γ n C => (sizeOf Γ, n, sizeOf C)

/-- `caps_Γ n` on one atom: a term binder resolves to the capture set of its
type and a capture binder to itself or to its bound, both by descent on the
binder; a capture name follows the capture witness of its block, at the same
context, and so consumes one unit of fuel.  A name with no fuel left lies on
a cyclic chain and resolves to the empty set.  The universal root is a leaf:
it stands for itself.  A projection carries its kind along as data: the
filter is not applied here, it is applied by `Ctx.expandAtom`, which is the
second and last stage of `Ctx.roots`. -/
def Ctx.capsAtom : (Γ : Ctx s) → Nat → CapAtom s → CaptureSet s
  | .cons Γ b, n, .var .here => (Γ.caps n b.ty.captureSet).weaken
  | .cons Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC _ .root, _, .cvar .here => [.cvar .here]
  | .consC _ .star, _, .cvar .here => [.cvar .here]
  | .consC _ (.cls _), _, .cvar .here => [.cvar .here]
  | .consC Γ (.upper C), n, .cvar .here => (Γ.caps n C).weaken
  | .consC Γ (.inst C), n, .cvar .here => (Γ.caps n C).weaken
  | .cons Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | .consC Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | _, _, .top => [.top]
  | _, 0, .name _ _ => []
  | Γ, n + 1, .name x ℓ =>
      match Γ.lookupDefC x ℓ with
      | some C => Γ.caps n C
      | none => []
  | Γ, n, .proj a φ => (Γ.capsAtom n a).map (CapAtom.proj · φ)
termination_by Γ n a => (sizeOf Γ, n, sizeOf a)

end

@[simp] theorem Ctx.caps_nil (Γ : Ctx s) (n : Nat) : Γ.caps n [] = [] := by
  simp [Ctx.caps]

@[simp] theorem Ctx.caps_cons (Γ : Ctx s) (n : Nat) (a : CapAtom s) (C : CaptureSet s) :
    Γ.caps n (a :: C) = Γ.capsAtom n a ++ Γ.caps n C := by
  simp [Ctx.caps]

/-- The universal root is a leaf of resolution. -/
@[simp] theorem Ctx.capsAtom_top (Γ : Ctx s) (n : Nat) :
    Γ.capsAtom n (.top) = [CapAtom.top] := by
  cases Γ <;> cases n <;> simp [Ctx.capsAtom]

/-- A projection carries a subset to a subset. -/
theorem CaptureSet.Subset.mapProj {C D : CaptureSet s} (h : C.Subset D) (φ : Cls.Kind) :
    (C.map (CapAtom.proj · φ)).Subset (D.map (CapAtom.proj · φ)) := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact List.mem_map_of_mem (h b hb)

/-- The projection clause of resolution: the kind rides along as data. -/
@[simp] theorem Ctx.capsAtom_proj (Γ : Ctx s) (n : Nat) (a : CapAtom s) (φ : Cls.Kind) :
    Γ.capsAtom n (a ↾ φ) = (Γ.capsAtom n a).map (CapAtom.proj · φ) := by
  cases Γ <;> cases n <;> simp [Ctx.capsAtom]

/-- **L3.**  Every atom resolution produces carries a kind below the atom's
own.  The bare atom carries `⊤`, which contains everything. -/
theorem Ctx.capsAtom_kindOf (Γ : Ctx s) (n : Nat) : ∀ (a : CapAtom s),
    ∀ b ∈ Γ.capsAtom n a, ∀ c : Cls.Classifier, b.kindOf.Contains c → a.kindOf.Contains c
  | .top, _, _, c, _ => Cls.Kind.contains_top c
  | .var _, _, _, c, _ => Cls.Kind.contains_top c
  | .cvar _, _, _, c, _ => Cls.Kind.contains_top c
  | .name _ _, _, _, c, _ => Cls.Kind.contains_top c
  | .proj a φ, b, hb, c, hc => by
      rw [Ctx.capsAtom_proj] at hb
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      show (φ.interB a.kindOf).containsB c = true
      rw [Cls.Kind.contains_inter, Bool.and_eq_true]
      have h : (φ.interB d.kindOf).containsB c = true := hc
      rw [Cls.Kind.contains_inter, Bool.and_eq_true] at h
      exact ⟨h.1, Ctx.capsAtom_kindOf Γ n a d hd c h.2⟩

/-- A capture name with no fuel left resolves to the empty set. -/
@[simp] theorem Ctx.capsAtom_name_zero (Γ : Ctx s) (x : BVar s .var) (ℓ : Label) :
    Γ.capsAtom 0 (.name x ℓ) = [] := by
  cases Γ <;> simp [Ctx.capsAtom]

/-- The name clause: a capture name follows the capture witness of its block. -/
theorem Ctx.capsAtom_name_succ (Γ : Ctx s) (n : Nat) (x : BVar s .var) (ℓ : Label) :
    Γ.capsAtom (n + 1) (.name x ℓ) =
      (Γ.lookupDefC x ℓ).elim [] (fun C => Γ.caps n C) := by
  cases Γ with
  | nil => cases x
  | cons Γ b => cases h : (Ctx.cons Γ b).lookupDefC x ℓ <;> simp [Ctx.capsAtom, h]
  | consC Γ b => cases h : (Ctx.consC Γ b).lookupDefC x ℓ <;> simp [Ctx.capsAtom, h]

theorem Ctx.capsAtom_name_some {Γ : Ctx s} {x : BVar s .var} {ℓ : Label}
    {C : CaptureSet s} (h : Γ.lookupDefC x ℓ = some C) (n : Nat) :
    Γ.capsAtom (n + 1) (.name x ℓ) = Γ.caps n C := by
  rw [Ctx.capsAtom_name_succ, h]; rfl

theorem Ctx.capsAtom_name_none {Γ : Ctx s} {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefC x ℓ = none) (n : Nat) :
    Γ.capsAtom (n + 1) (.name x ℓ) = [] := by
  rw [Ctx.capsAtom_name_succ, h]; rfl

/-- `caps` of a union is the union of the `caps`. -/
theorem Ctx.caps_append (Γ : Ctx s) (n : Nat) :
    ∀ C D : CaptureSet s, Γ.caps n (C ++ D) = Γ.caps n C ++ Γ.caps n D
  | [], _ => by simp
  | a :: C, D => by
      simp only [List.cons_append, Ctx.caps_cons, Ctx.caps_append Γ n C D, List.append_assoc]

/-- The `caps` of an atom of a set are `caps` of the set. -/
theorem Ctx.capsAtom_mem (Γ : Ctx s) (n : Nat) (a : CapAtom s) :
    ∀ D : CaptureSet s, a ∈ D → (Γ.capsAtom n a).Subset (Γ.caps n D)
  | [], h => by simp at h
  | b :: D, h => by
      intro c hc
      rw [Ctx.caps_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_append_left _ hc
      · exact List.mem_append_right _ (Ctx.capsAtom_mem Γ n a D h c hc)

/-- `caps` is monotone in the syntactic inclusion of sets. -/
theorem Ctx.caps_subset {Γ : Ctx s} {n : Nat} :
    ∀ {C D : CaptureSet s}, C.Subset D → (Γ.caps n C).Subset (Γ.caps n D)
  | [], _, _ => by intro c hc; simp at hc
  | a :: C, D, h => by
      intro c hc
      rw [Ctx.caps_cons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact Ctx.capsAtom_mem Γ n a D (h a (List.mem_cons_self ..)) c hc
      · exact Ctx.caps_subset (fun b hb => h b (List.mem_cons_of_mem a hb)) c hc

/-! ### Monotonicity in the fuel

More fuel resolves more names: a chain that ran out of fuel contributed the
empty set, and one that did not is unchanged.  The atom half and the set half
are proven together, by induction on the fuel and then on the spine of the
context, because the name clause of the first calls the second at one unit
less fuel. -/

/-- The set half of a monotonicity statement follows from the atom half. -/
theorem Ctx.caps_of_capsAtom {Γ : Ctx s} {n m : Nat}
    (h : ∀ a : CapAtom s, (Γ.capsAtom n a).Subset (Γ.capsAtom m a)) :
    ∀ C : CaptureSet s, (Γ.caps n C).Subset (Γ.caps m C)
  | [] => by intro c hc; simp at hc
  | a :: C => by
      intro c hc
      rw [Ctx.caps_cons] at hc ⊢
      rcases List.mem_append.mp hc with hc | hc
      · exact List.mem_append_left _ (h a c hc)
      · exact List.mem_append_right _ (Ctx.caps_of_capsAtom h C c hc)

theorem Ctx.caps_succ_aux (n : Nat) : ∀ {s : Sig} (Γ : Ctx s),
    (∀ a : CapAtom s, (Γ.capsAtom n a).Subset (Γ.capsAtom (n + 1) a)) ∧
      (∀ C : CaptureSet s, (Γ.caps n C).Subset (Γ.caps (n + 1) C)) := by
  induction n with
  | zero =>
      intro s Γ
      induction Γ with
      | nil =>
          have hat : ∀ a : CapAtom [],
              (Ctx.nil.capsAtom 0 a).Subset (Ctx.nil.capsAtom 1 a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var x => cases x
            | cvar κ => cases κ
            | name x ℓ => cases x
            | proj a φ ih =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj ih φ
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom 0 a).Subset ((Ctx.cons Γ b).capsAtom 1 a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var y =>
                cases y with
                | here => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | name x ℓ =>
                intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
            | proj a φ iha =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj iha φ
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | consC Γ b ih =>
          have hat : ∀ a,
              ((Ctx.consC Γ b).capsAtom 0 a).Subset ((Ctx.consC Γ b).capsAtom 1 a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var y =>
                cases y with
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | here =>
                    cases b with
                    | root => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | star => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | cls c₀ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | name x ℓ =>
                intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
            | proj a φ iha =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj iha φ
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
  | succ n ihn =>
      intro s Γ
      induction Γ with
      | nil =>
          have hat : ∀ a : CapAtom [],
              (Ctx.nil.capsAtom (n + 1) a).Subset (Ctx.nil.capsAtom (n + 1 + 1) a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var x => cases x
            | cvar κ => cases κ
            | name x ℓ => cases x
            | proj a φ ih =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj ih φ
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom (n + 1) a).Subset
                ((Ctx.cons Γ b).capsAtom (n + 1 + 1) a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var y =>
                cases y with
                | here => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | proj a φ iha =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj iha φ
            | name x ℓ =>
                cases h : (Ctx.cons Γ b).lookupDefC x ℓ with
                | none =>
                    intro c hc
                    rw [Ctx.capsAtom_name_none h] at hc; simp at hc
                | some C =>
                    intro c hc
                    rw [Ctx.capsAtom_name_some h] at hc
                    rw [Ctx.capsAtom_name_some h]
                    exact (ihn (Ctx.cons Γ b)).2 C c hc
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | consC Γ b ih =>
          have hat : ∀ a,
              ((Ctx.consC Γ b).capsAtom (n + 1) a).Subset
                ((Ctx.consC Γ b).capsAtom (n + 1 + 1) a) := by
            intro a
            induction a with
            | top => intro c hc; simpa using hc
            | var y =>
                cases y with
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | here =>
                    cases b with
                    | root => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | star => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | cls c₀ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | proj a φ iha =>
                simp only [Ctx.capsAtom_proj]
                exact CaptureSet.Subset.mapProj iha φ
            | name x ℓ =>
                cases h : (Ctx.consC Γ b).lookupDefC x ℓ with
                | none =>
                    intro c hc
                    rw [Ctx.capsAtom_name_none h] at hc; simp at hc
                | some C =>
                    intro c hc
                    rw [Ctx.capsAtom_name_some h] at hc
                    rw [Ctx.capsAtom_name_some h]
                    exact (ihn (Ctx.consC Γ b)).2 C c hc
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩

theorem Ctx.capsAtom_succ (Γ : Ctx s) (n : Nat) (a : CapAtom s) :
    (Γ.capsAtom n a).Subset (Γ.capsAtom (n + 1) a) := (Ctx.caps_succ_aux n Γ).1 a

theorem Ctx.caps_succ (Γ : Ctx s) (n : Nat) (C : CaptureSet s) :
    (Γ.caps n C).Subset (Γ.caps (n + 1) C) := (Ctx.caps_succ_aux n Γ).2 C

/-- Resolution is monotone in the fuel. -/
theorem Ctx.caps_mono_fuel (Γ : Ctx s) {n m : Nat} (h : n ≤ m) (C : CaptureSet s) :
    (Γ.caps n C).Subset (Γ.caps m C) := by
  induction m with
  | zero => intro c hc; rw [Nat.le_zero.mp h] at hc; exact hc
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact fun c hc => Γ.caps_succ m C c (ih (Nat.le_of_lt_succ hlt) c hc)
      · intro c hc; rw [Nat.le_antisymm h hge] at hc; exact hc

theorem Ctx.capsAtom_mono_fuel (Γ : Ctx s) {n m : Nat} (h : n ≤ m) (a : CapAtom s) :
    (Γ.capsAtom n a).Subset (Γ.capsAtom m a) := by
  intro c hc
  have h1 : c ∈ Γ.caps n [a] := by rw [Ctx.caps_cons, Ctx.caps_nil]; simpa using hc
  have h2 := Γ.caps_mono_fuel h [a] c h1
  rw [Ctx.caps_cons, Ctx.caps_nil] at h2
  simpa using h2

/-! ### Monotonicity under store extension -/

theorem Ctx.caps_weaken_aux : ∀ (n : Nat) {s : Sig} (Γ : Ctx s) (b : Binding s),
    (∀ a : CapAtom s, (Ctx.cons Γ b).capsAtom n a.weaken = (Γ.capsAtom n a).weaken) ∧
      (∀ C : CaptureSet s, (Ctx.cons Γ b).caps n C.weaken = (Γ.caps n C).weaken) := by
  intro n
  induction n with
  | zero =>
      intro s Γ b
      have hatom : ∀ a : CapAtom s,
          (Ctx.cons Γ b).capsAtom 0 a.weaken = (Γ.capsAtom 0 a).weaken := by
        intro a
        induction a <;> simp_all [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
          CaptureSet.rename, Ctx.capsAtom, List.map_map, Function.comp_def]
      refine ⟨hatom, ?_⟩
      intro C
      induction C with
      | nil => simp [CaptureSet.weaken, CaptureSet.rename]
      | cons a C ihC =>
          show (Ctx.cons Γ b).caps 0 (CapAtom.weaken a :: CaptureSet.weaken C)
            = CaptureSet.weaken (Γ.caps 0 (a :: C))
          rw [Ctx.caps_cons, hatom, ihC, Ctx.caps_cons]
          simp [CaptureSet.weaken, CaptureSet.rename]
  | succ n ihn =>
      intro s Γ b
      have hatom : ∀ a : CapAtom s,
          (Ctx.cons Γ b).capsAtom (n + 1) a.weaken = (Γ.capsAtom (n + 1) a).weaken := by
        intro a
        induction a with
        | top =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename]
        | var y =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | cvar κ =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | proj a φ iha =>
            show (Ctx.cons Γ b).capsAtom (n + 1) ((a.weaken) ↾ φ) = _
            rw [Ctx.capsAtom_proj, iha, Ctx.capsAtom_proj]
            simp [CaptureSet.weaken, CaptureSet.rename, List.map_map, Function.comp_def,
              CapAtom.rename]
        | name x ℓ =>
            have hw : (CapAtom.name x ℓ).weaken (k := .var) = .name (.there x) ℓ := rfl
            rw [hw]
            cases h : Γ.lookupDefC x ℓ with
            | none =>
                rw [Ctx.capsAtom_name_none h,
                  Ctx.capsAtom_name_none (Γ := Ctx.cons Γ b)
                    (by rw [Ctx.lookupDefC_there, h]; rfl)]
                simp [CaptureSet.weaken, CaptureSet.rename]
            | some C =>
                rw [Ctx.capsAtom_name_some h,
                  Ctx.capsAtom_name_some (Γ := Ctx.cons Γ b) (C := C.weaken)
                    (by rw [Ctx.lookupDefC_there, h]; rfl)]
                exact (ihn Γ b).2 C
      refine ⟨hatom, ?_⟩
      intro C
      induction C with
      | nil => simp [CaptureSet.weaken, CaptureSet.rename]
      | cons a C ihC =>
          show (Ctx.cons Γ b).caps (n + 1) (CapAtom.weaken a :: CaptureSet.weaken C)
            = CaptureSet.weaken (Γ.caps (n + 1) (a :: C))
          rw [Ctx.caps_cons, hatom, ihC, Ctx.caps_cons]
          simp [CaptureSet.weaken, CaptureSet.rename]

theorem Ctx.caps_weakenC_aux : ∀ (n : Nat) {s : Sig} (Γ : Ctx s) (b : CapBound s),
    (∀ a : CapAtom s, (Ctx.consC Γ b).capsAtom n a.weaken = (Γ.capsAtom n a).weaken) ∧
      (∀ C : CaptureSet s, (Ctx.consC Γ b).caps n C.weaken = (Γ.caps n C).weaken) := by
  intro n
  induction n with
  | zero =>
      intro s Γ b
      have hatom : ∀ a : CapAtom s,
          (Ctx.consC Γ b).capsAtom 0 a.weaken = (Γ.capsAtom 0 a).weaken := by
        intro a
        induction a <;> simp_all [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
          CaptureSet.rename, Ctx.capsAtom, List.map_map, Function.comp_def]
      refine ⟨hatom, ?_⟩
      intro C
      induction C with
      | nil => simp [CaptureSet.weaken, CaptureSet.rename]
      | cons a C ihC =>
          show (Ctx.consC Γ b).caps 0 (CapAtom.weaken a :: CaptureSet.weaken C)
            = CaptureSet.weaken (Γ.caps 0 (a :: C))
          rw [Ctx.caps_cons, hatom, ihC, Ctx.caps_cons]
          simp [CaptureSet.weaken, CaptureSet.rename]
  | succ n ihn =>
      intro s Γ b
      have hatom : ∀ a : CapAtom s,
          (Ctx.consC Γ b).capsAtom (n + 1) a.weaken = (Γ.capsAtom (n + 1) a).weaken := by
        intro a
        induction a with
        | top =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename]
        | var y =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | cvar κ =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | proj a φ iha =>
            show (Ctx.consC Γ b).capsAtom (n + 1) ((a.weaken) ↾ φ) = _
            rw [Ctx.capsAtom_proj, iha, Ctx.capsAtom_proj]
            simp [CaptureSet.weaken, CaptureSet.rename, List.map_map, Function.comp_def,
              CapAtom.rename]
        | name x ℓ =>
            have hw : (CapAtom.name x ℓ).weaken (k := .cap) = .name (.there x) ℓ := rfl
            rw [hw]
            cases h : Γ.lookupDefC x ℓ with
            | none =>
                rw [Ctx.capsAtom_name_none h,
                  Ctx.capsAtom_name_none (Γ := Ctx.consC Γ b)
                    (by rw [Ctx.lookupDefC_thereC, h]; rfl)]
                simp [CaptureSet.weaken, CaptureSet.rename]
            | some C =>
                rw [Ctx.capsAtom_name_some h,
                  Ctx.capsAtom_name_some (Γ := Ctx.consC Γ b) (C := C.weaken)
                    (by rw [Ctx.lookupDefC_thereC, h]; rfl)]
                exact (ihn Γ b).2 C
      refine ⟨hatom, ?_⟩
      intro C
      induction C with
      | nil => simp [CaptureSet.weaken, CaptureSet.rename]
      | cons a C ihC =>
          show (Ctx.consC Γ b).caps (n + 1) (CapAtom.weaken a :: CaptureSet.weaken C)
            = CaptureSet.weaken (Γ.caps (n + 1) (a :: C))
          rw [Ctx.caps_cons, hatom, ihC, Ctx.caps_cons]
          simp [CaptureSet.weaken, CaptureSet.rename]

theorem Ctx.capsAtom_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (a : CapAtom s) :
    (Ctx.cons Γ b).capsAtom n a.weaken = (Γ.capsAtom n a).weaken :=
  (Ctx.caps_weaken_aux n Γ b).1 a

theorem Ctx.capsAtom_weakenC (Γ : Ctx s) (b : CapBound s) (n : Nat) (a : CapAtom s) :
    (Ctx.consC Γ b).capsAtom n a.weaken = (Γ.capsAtom n a).weaken :=
  (Ctx.caps_weakenC_aux n Γ b).1 a

theorem Ctx.caps_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (C : CaptureSet s) :
    (Ctx.cons Γ b).caps n C.weaken = (Γ.caps n C).weaken :=
  (Ctx.caps_weaken_aux n Γ b).2 C

theorem Ctx.caps_weakenC (Γ : Ctx s) (b : CapBound s) (n : Nat) (C : CaptureSet s) :
    (Ctx.consC Γ b).caps n C.weaken = (Γ.caps n C).weaken :=
  (Ctx.caps_weakenC_aux n Γ b).2 C

/-! ### The clauses of `caps` at a binder -/

/-- The term-binder clause: `caps_Γ {x}` is `caps_Γ` of the capture set of
`Γ.lookupTy x`, which mentions only binders older than `x`. -/
theorem Ctx.capsAtom_var : ∀ {s : Sig} (Γ : Ctx s) (n : Nat) (x : BVar s .var),
    Γ.capsAtom n (.var x) = Γ.caps n (Γ.lookupTy x).captureSet
  | _, .cons Γ b, n, .here => by
      rw [Ctx.lookupTy_here, Ty.captureSet_weaken, Ctx.caps_weaken]
      simp [Ctx.capsAtom]
  | _, .cons Γ b, n, .there y => by
      rw [Ctx.lookupTy_there, Ty.captureSet_weaken, Ctx.caps_weaken,
        ← Ctx.capsAtom_var Γ n y]
      simp [Ctx.capsAtom]
  | _, .consC Γ b, n, .there y => by
      rw [Ctx.lookupTy_thereC, Ty.captureSet_weaken, Ctx.caps_weakenC,
        ← Ctx.capsAtom_var Γ n y]
      simp [Ctx.capsAtom]

/-- The resolution of a capture bound at its binder: a root or `∗` is a leaf,
an upper bound or an instantiation resolves to its set. -/
def Ctx.capsBound (Γ : Ctx s) (n : Nat) (κ : BVar s .cap) : CapBound s → CaptureSet s
  | .root => [.cvar κ]
  | .star => [.cvar κ]
  | .upper C => Γ.caps n C
  | .inst C => Γ.caps n C
  | .cls _ => [.cvar κ]

theorem Ctx.capsBound_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.cons Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
  | cls c => rfl
  | upper C => exact Ctx.caps_weaken Γ b n C
  | inst C => exact Ctx.caps_weaken Γ b n C

theorem Ctx.capsBound_weakenC (Γ : Ctx s) (b : CapBound s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.consC Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
  | cls c => rfl
  | upper C => exact Ctx.caps_weakenC Γ b n C
  | inst C => exact Ctx.caps_weakenC Γ b n C

/-- The capture-binder clause: `caps_Γ {κ}` is `{κ}` when the bound of `κ` is
a root or `∗`, and `caps_Γ` of the bound otherwise. -/
theorem Ctx.capsAtom_cvar : ∀ {s : Sig} (Γ : Ctx s) (n : Nat) (κ : BVar s .cap),
    Γ.capsAtom n (.cvar κ) = Γ.capsBound n κ (Γ.lookupCap κ)
  | _, .consC Γ β, n, .here => by
      rw [Ctx.lookupCap_here]
      cases β with
      | root => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | star => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | cls c₀ => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | upper C => rw [Ctx.capsAtom]; exact (Ctx.caps_weakenC Γ _ n C).symm
      | inst C => rw [Ctx.capsAtom]; exact (Ctx.caps_weakenC Γ _ n C).symm
  | _, .cons Γ b, n, .there κ => by
      rw [Ctx.lookupCap_there, Ctx.capsBound_weaken Γ b n κ (Γ.lookupCap κ),
        ← Ctx.capsAtom_cvar Γ n κ]
      simp [Ctx.capsAtom]
  | _, .consC Γ b, n, .there κ => by
      rw [Ctx.lookupCap_thereC, Ctx.capsBound_weakenC Γ b n κ (Γ.lookupCap κ),
        ← Ctx.capsAtom_cvar Γ n κ]
      simp [Ctx.capsAtom]

/-! ### Expansion: a scope root opens into the binders it covers

A scope root stands for the universal root and for every opaque binder at
its level or outside it.  Everything else stands for itself.  Expansion is a
filter over the binders of `Γ` by flavour and by position, not a recursion
into their content, so it takes no fuel and the descent of resolution is
untouched. -/

/-- Filtering after a map is mapping after the transported filter. -/
theorem filter_of_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).filter p = (l.filter fun a => p (f a)).map f
  | [] => rfl
  | a :: l => by
      by_cases h : p (f a) = true <;>
        simp [h, filter_of_map f p l]

/-- Every capture binder of `Γ`. -/
def Ctx.capBinders : Ctx s → List (BVar s .cap)
  | .nil => []
  | .cons Γ _ => (Ctx.capBinders Γ).map .there
  | .consC Γ _ => .here :: (Ctx.capBinders Γ).map .there

@[simp] theorem Ctx.capBinders_cons (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).capBinders = Γ.capBinders.map .there := rfl

@[simp] theorem Ctx.capBinders_consC (Γ : Ctx s) (b : CapBound s) :
    (Γ.consC b).capBinders = .here :: Γ.capBinders.map .there := rfl

/-- Every capture binder is listed. -/
theorem Ctx.mem_capBinders {s : Sig} (Γ : Ctx s) : ∀ κ : BVar s .cap, κ ∈ Γ.capBinders := by
  induction Γ with
  | nil => intro κ; cases κ
  | cons Γ b ih =>
      intro κ
      cases κ with
      | there κ₀ =>
          simp only [Ctx.capBinders_cons, List.mem_map]
          exact ⟨κ₀, ih κ₀, rfl⟩
  | consC Γ b ih =>
      intro κ
      cases κ with
      | here => simp
      | there κ₀ =>
          simp only [Ctx.capBinders_consC, List.mem_cons, List.mem_map]
          exact Or.inr ⟨κ₀, ih κ₀, rfl⟩

/-- Expansion of one atom.  A projection is expanded and then filtered by
the kind it carries: this is the one place a kind is read, and it is the
last thing that happens, so nothing re-opens what a filter admitted.  A root
opens into the universal root and every opaque binder at its level or
outside it.  Everything else stands for itself. -/
def Ctx.expandAtom (Γ : Ctx s) : CapAtom s → CaptureSet s
  | .proj a φ => (Γ.expandAtom a).filter (fun b => Γ.admitsB b φ)
  | a =>
    if Γ.isRootB a then
      CapAtom.top :: (Γ.capBinders.filter fun κ =>
          (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) a).map CapAtom.cvar
    else [a]

/-- Expansion of a capture set. -/
def Ctx.expand (Γ : Ctx s) (C : CaptureSet s) : CaptureSet s := C.flatMap Γ.expandAtom

/-- **L1.**  Expansion consumes a projection as a filter. -/
@[simp] theorem Ctx.expandAtom_proj (Γ : Ctx s) (a : CapAtom s) (φ : Cls.Kind) :
    Γ.expandAtom (a ↾ φ) = (Γ.expandAtom a).filter (fun b => Γ.admitsB b φ) := rfl

/-- Two filters in a row are one filter by the conjunction. -/
theorem CaptureSet.filter_filter (p q : CapAtom s → Bool) :
    ∀ l : CaptureSet s, (l.filter p).filter q = l.filter (fun b => p b && q b)
  | [] => rfl
  | b :: l => by
      by_cases hp : p b = true <;> by_cases hq : q b = true <;>
        simp [List.filter_cons, hp, hq, CaptureSet.filter_filter p q l]

theorem CaptureSet.filter_congr' (p q : CapAtom s → Bool) (h : ∀ b, p b = q b) :
    ∀ l : CaptureSet s, l.filter p = l.filter q
  | [] => rfl
  | b :: l => by simp [List.filter_cons, h b, CaptureSet.filter_congr' p q h l]

/-- **L2.**  And expansion consumes the smart constructor the same way.  The
one use of the kind algebra in the stage: an intersection admits exactly what
both sides admit. -/
theorem Ctx.expandAtom_projBy (Γ : Ctx s) (a : CapAtom s) (φ : Cls.Kind) :
    Γ.expandAtom (CapAtom.projBy φ a) = (Γ.expandAtom a).filter (fun b => Γ.admitsB b φ) := by
  cases a with
  | top | var _ | cvar _ | name _ _ => rfl
  | proj c ψ =>
      show (Γ.expandAtom c).filter (fun b => (φ.interB ψ).containsB (Γ.classOf b))
        = ((Γ.expandAtom c).filter (fun b => ψ.containsB (Γ.classOf b))).filter _
      rw [CaptureSet.filter_filter]
      refine CaptureSet.filter_congr' _ _ (fun b => ?_) _
      show (φ.interB ψ).containsB (Γ.classOf b)
        = (ψ.containsB (Γ.classOf b) && φ.containsB (Γ.classOf b))
      rw [Cls.Kind.contains_inter, Bool.and_comm]

/-- The old body of expansion, at every atom that is its own base. -/
theorem Ctx.expandAtom_of_not_proj {Γ : Ctx s} : ∀ {a : CapAtom s}, a.base = a →
    Γ.expandAtom a = if Γ.isRootB a then
        CapAtom.top :: (Γ.capBinders.filter fun κ =>
          (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) a).map CapAtom.cvar
      else [a]
  | .top, _ => rfl
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .proj a φ, h => absurd h (CapAtom.base_ne_proj a a φ)

/-- A root is its own base: a projection is never a root. -/
theorem Ctx.base_of_isRootB {Γ : Ctx s} : ∀ {r : CapAtom s}, Γ.isRootB r = true → r.base = r
  | .top, _ => rfl
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .proj _ _, h => by simp [Ctx.isRootB] at h

theorem Ctx.expandAtom_of_root {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) :
    Γ.expandAtom r = CapAtom.top :: (Γ.capBinders.filter fun κ =>
        (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) r).map CapAtom.cvar := by
  rw [Ctx.expandAtom_of_not_proj (Ctx.base_of_isRootB hr), if_pos hr]

theorem Ctx.expandAtom_of_not_root {Γ : Ctx s} {a : CapAtom s} (ha : Γ.isRootB a = false)
    (hb : a.base = a) : Γ.expandAtom a = [a] := by
  rw [Ctx.expandAtom_of_not_proj hb, if_neg (by simp [ha])]

/-- The universal root is in the expansion of every root. -/
theorem Ctx.top_mem_expandAtom {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) :
    CapAtom.top ∈ Γ.expandAtom r := by
  rw [Ctx.expandAtom_of_root hr]
  exact List.mem_cons_self ..

/-- An opaque binder at or outside the level of a root is in its expansion. -/
theorem Ctx.cvar_mem_expandAtom {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r)
    {κ : BVar s .cap} (hop : (Γ.lookupCap κ).opaque = true) (hle : Γ.LvlLe (.cvar κ) r) :
    CapAtom.cvar κ ∈ Γ.expandAtom r := by
  rw [Ctx.expandAtom_of_root hr]
  refine List.mem_cons_of_mem _ (List.mem_map_of_mem ?_)
  exact List.mem_filter.mpr ⟨Γ.mem_capBinders κ, by simp [hop, hle]⟩

/-- And those are all of it. -/
theorem Ctx.mem_expandAtom_root {Γ : Ctx s} {r a : CapAtom s} (hr : Γ.IsRoot r)
    (h : a ∈ Γ.expandAtom r) :
    a = .top ∨ ∃ κ, a = .cvar κ ∧ (Γ.lookupCap κ).opaque = true ∧ Γ.LvlLe (.cvar κ) r := by
  rw [Ctx.expandAtom_of_root hr] at h
  rcases List.mem_cons.mp h with rfl | h
  · exact Or.inl rfl
  · rcases List.mem_map.mp h with ⟨κ, hκ, rfl⟩
    rcases List.mem_filter.mp hκ with ⟨_, hp⟩
    rw [Bool.and_eq_true] at hp
    exact Or.inr ⟨κ, rfl, hp.1, hp.2⟩

/-- **L5.**  Expansion produces projection-free atoms, which is Fact 4: the
three layers above `Ctx.expandAtom` never see a projection. -/
theorem Ctx.expandAtom_base_of_not_proj {Γ : Ctx s} {a : CapAtom s} (hb : a.base = a) :
    ∀ b ∈ Γ.expandAtom a, b.base = b := by
  rw [Ctx.expandAtom_of_not_proj hb]
  split
  · intro b hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · rfl
    · obtain ⟨κ, _, rfl⟩ := List.mem_map.mp hb'; rfl
  · intro b hb'
    rw [List.mem_singleton.mp hb']
    exact hb

theorem Ctx.expandAtom_base (Γ : Ctx s) : ∀ (a : CapAtom s), ∀ b ∈ Γ.expandAtom a, b.base = b
  | .top => Ctx.expandAtom_base_of_not_proj rfl
  | .var _ => Ctx.expandAtom_base_of_not_proj rfl
  | .cvar _ => Ctx.expandAtom_base_of_not_proj rfl
  | .name _ _ => Ctx.expandAtom_base_of_not_proj rfl
  | .proj a φ => fun b hb => Γ.expandAtom_base a b (List.mem_filter.mp hb).1

/-- An expansion is a sublist of the expansion of the base, because every
projection is consumed as a filter.  This is L1 iterated. -/
theorem Ctx.mem_expandAtom_base (Γ : Ctx s) :
    ∀ (a : CapAtom s), ∀ b ∈ Γ.expandAtom a, b ∈ Γ.expandAtom a.base
  | .top, _, h => h
  | .var _, _, h => h
  | .cvar _, _, h => h
  | .name _ _, _, h => h
  | .proj a φ, b, hb => Γ.mem_expandAtom_base a b (List.mem_filter.mp hb).1

theorem Ctx.expandAtom_subset_base (Γ : Ctx s) (a : CapAtom s) :
    (Γ.expandAtom a).Subset (Γ.expandAtom a.base) := by
  intro b hb
  exact Γ.mem_expandAtom_base a b hb

/-- **L4.**  Every atom an expansion produces is admitted by the kind the
atom it came from carried.  At a bare atom that kind is `⊤`. -/
theorem Ctx.expandAtom_kinded (Γ : Ctx s) : ∀ (a : CapAtom s),
    ∀ b ∈ Γ.expandAtom a, a.kindOf.Contains (Γ.classOf b)
  | .top, b, _ => Cls.Kind.contains_top (Γ.classOf b)
  | .var _, b, _ => Cls.Kind.contains_top (Γ.classOf b)
  | .cvar _, b, _ => Cls.Kind.contains_top (Γ.classOf b)
  | .name _ _, b, _ => Cls.Kind.contains_top (Γ.classOf b)
  | .proj a φ, b, hb => by
      have h := List.mem_filter.mp hb
      show (φ.interB a.kindOf).containsB (Γ.classOf b) = true
      rw [Cls.Kind.contains_inter, Bool.and_eq_true]
      exact ⟨h.2, Γ.expandAtom_kinded a b h.1⟩

/-- Expansion of an atom whose base is not a root: the base, when the kind
the atom carries admits it, and nothing at all when it does not. -/
theorem CapAtom.kindOf_of_base : ∀ {a : CapAtom s}, a.base = a → a.kindOf = Cls.Kind.top
  | .top, _ => rfl
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .proj a φ, h => absurd h (CapAtom.base_ne_proj a a φ)

theorem Ctx.expandAtom_of_base_not_root_aux {Γ : Ctx s} {a : CapAtom s} (hb : a.base = a)
    (h : Γ.isRootB a.base = false) :
    Γ.expandAtom a = if Γ.admitsB a.base a.kindOf then [a.base] else [] := by
  have hk : Γ.admitsB a.base a.kindOf = true := by
    rw [CapAtom.kindOf_of_base hb]
    exact Cls.Kind.contains_top _
  rw [if_pos hk, hb]
  exact Ctx.expandAtom_of_not_root (by rwa [hb] at h) hb

theorem Ctx.expandAtom_of_base_not_root {Γ : Ctx s} : ∀ {a : CapAtom s},
    Γ.isRootB a.base = false →
      Γ.expandAtom a = if Γ.admitsB a.base a.kindOf then [a.base] else []
  | .top, h => Ctx.expandAtom_of_base_not_root_aux rfl h
  | .var _, h => Ctx.expandAtom_of_base_not_root_aux rfl h
  | .cvar _, h => Ctx.expandAtom_of_base_not_root_aux rfl h
  | .name _ _, h => Ctx.expandAtom_of_base_not_root_aux rfl h
  | .proj a φ, h => by
      have hi : Γ.admitsB a.base (φ.interB a.kindOf)
          = (Γ.admitsB a.base a.kindOf && Γ.admitsB a.base φ) := by
        show (φ.interB a.kindOf).containsB (Γ.classOf a.base)
          = (a.kindOf.containsB (Γ.classOf a.base) && φ.containsB (Γ.classOf a.base))
        rw [Cls.Kind.contains_inter, Bool.and_comm]
      show (Γ.expandAtom a).filter (fun b => Γ.admitsB b φ)
        = if Γ.admitsB a.base (φ.interB a.kindOf) then [a.base] else []
      rw [Ctx.expandAtom_of_base_not_root (a := a) h, hi]
      cases hk : Γ.admitsB a.base a.kindOf with
      | false => simp [hk]
      | true =>
          cases hp : Γ.admitsB a.base φ with
          | false => simp [hk, hp, List.filter_cons]
          | true => simp [hk, hp, List.filter_cons]

/-- An atom is in its own expansion: `⊤ᶜ` heads its own, a root is its own
level, and everything else expands to its singleton.  A projection contributes
its base, and only when the kind it carries admits it. -/
theorem Ctx.mem_expandAtom_self_of_not_proj {Γ : Ctx s} {a : CapAtom s} (hb : a.base = a) :
    a ∈ Γ.expandAtom a := by
  cases h : Γ.isRootB a with
  | false =>
      rw [Ctx.expandAtom_of_not_root h hb]
      exact List.mem_cons_self ..
  | true =>
      cases a with
      | top => exact Ctx.top_mem_expandAtom h
      | var x => simp [Ctx.isRootB] at h
      | name x ℓ => simp [Ctx.isRootB] at h
      | proj a φ => simp [Ctx.isRootB] at h
      | cvar κ =>
          have hroot : (Γ.lookupCap κ).isRoot = true := by simpa [Ctx.isRootB] using h
          exact Ctx.cvar_mem_expandAtom h (CapBound.opaque_of_isRoot hroot)
            (Ctx.LvlLe.refl_of_root h)

theorem Ctx.mem_expandAtom_self (Γ : Ctx s) : ∀ (a : CapAtom s),
    Γ.admitsB a.base a.kindOf = true → a.base ∈ Γ.expandAtom a
  | .top, _ => Ctx.mem_expandAtom_self_of_not_proj rfl
  | .var _, _ => Ctx.mem_expandAtom_self_of_not_proj rfl
  | .cvar _, _ => Ctx.mem_expandAtom_self_of_not_proj rfl
  | .name _ _, _ => Ctx.mem_expandAtom_self_of_not_proj rfl
  | .proj a φ, h => by
      have h' : (φ.interB a.kindOf).containsB (Γ.classOf a.base) = true := h
      rw [Cls.Kind.contains_inter, Bool.and_eq_true] at h'
      show a.base ∈ (Γ.expandAtom a).filter (fun b => Γ.admitsB b φ)
      exact List.mem_filter.mpr ⟨Γ.mem_expandAtom_self a h'.2, h'.1⟩

@[simp] theorem Ctx.expand_nil (Γ : Ctx s) : Γ.expand ([] : CaptureSet s) = [] := by
  simp [Ctx.expand]

@[simp] theorem Ctx.expand_cons (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) :
    Γ.expand (a :: C) = Γ.expandAtom a ++ Γ.expand C := by
  simp [Ctx.expand]

theorem Ctx.expand_append (Γ : Ctx s) : ∀ C D : CaptureSet s,
    Γ.expand (C ++ D) = Γ.expand C ++ Γ.expand D
  | [], _ => by simp
  | a :: C, D => by
      rw [List.cons_append, Ctx.expand_cons, Ctx.expand_cons,
        Ctx.expand_append Γ C D, List.append_assoc]

theorem Ctx.mem_expand {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} :
    a ∈ Γ.expand C ↔ ∃ b ∈ C, a ∈ Γ.expandAtom b := by
  simp [Ctx.expand]

theorem Ctx.expand_subset {Γ : Ctx s} {C D : CaptureSet s} (h : C.Subset D) :
    (Γ.expand C).Subset (Γ.expand D) := by
  intro a ha
  rcases Ctx.mem_expand.mp ha with ⟨b, hb, hab⟩
  exact Ctx.mem_expand.mpr ⟨b, h b hb, hab⟩

/-- A set is contained in its own expansion, by the bases of the atoms its
own kinds admit. -/
theorem Ctx.subset_expand (Γ : Ctx s) (C : CaptureSet s)
    (h : ∀ a ∈ C, Γ.admitsB a.base a.kindOf = true) :
    ∀ a ∈ C, a.base ∈ Γ.expand C := by
  intro a ha
  exact Ctx.mem_expand.mpr ⟨a, ha, Γ.mem_expandAtom_self a (h a ha)⟩

/-- A set of non-roots that carries no projection is its own expansion. -/
theorem Ctx.expand_eq_self {Γ : Ctx s} : ∀ {C : CaptureSet s},
    (∀ a ∈ C, Γ.isRootB a = false) → (∀ a ∈ C, a.base = a) → Γ.expand C = C
  | [], _, _ => by simp
  | a :: C, h, hb => by
      rw [Ctx.expand_cons,
        Ctx.expandAtom_of_not_root (h a (List.mem_cons_self ..)) (hb a (List.mem_cons_self ..)),
        Ctx.expand_eq_self (fun c hc => h c (List.mem_cons_of_mem a hc))
          (fun c hc => hb c (List.mem_cons_of_mem a hc))]
      rfl

/-- A set whose atoms all have a non-root base expands to the bases its own
kinds admit.  This is the shape `Ctx.roots_eq_caps_of_rootFree` needs. -/
theorem Ctx.expand_eq_filter_base {Γ : Ctx s} : ∀ {L : CaptureSet s},
    (∀ a ∈ L, Γ.isRootB a.base = false) →
      Γ.expand L = (L.filter (fun a => Γ.admitsB a.base a.kindOf)).map CapAtom.base
  | [], _ => rfl
  | a :: L, h => by
      rw [Ctx.expand_cons, Ctx.expandAtom_of_base_not_root (h a (List.mem_cons_self ..)),
        Ctx.expand_eq_filter_base (fun b hb => h b (List.mem_cons_of_mem a hb))]
      cases hk : Γ.admitsB a.base a.kindOf with
      | true => simp [hk, List.filter_cons]
      | false => simp [hk, List.filter_cons]

/-- Every kind admits an atom that is its own base, because such an atom
carries the root kind `⊤`. -/
@[simp] theorem Ctx.admitsB_top (Γ : Ctx s) (a : CapAtom s) :
    Γ.admitsB a Cls.Kind.top = true := Cls.Kind.contains_top _

/-- On a set of atoms that are their own base the filter of
`Ctx.roots_eq_caps_of_rootFree` admits everything and `base` is the identity,
so the right hand side of that equation is the set itself. -/
theorem Ctx.filter_map_base_eq_self {Γ : Ctx s} : ∀ {L : CaptureSet s},
    (∀ a ∈ L, a.base = a) →
      (L.filter (fun a => Γ.admitsB a.base a.kindOf)).map CapAtom.base = L
  | [], _ => rfl
  | a :: L, h => by
      have ha : a.base = a := h a (List.mem_cons_self ..)
      have hk : Γ.admitsB a a.kindOf = true := by
        rw [CapAtom.kindOf_of_base ha]
        exact Γ.admitsB_top a
      have ih := Ctx.filter_map_base_eq_self (Γ := Γ)
        (fun b hb => h b (List.mem_cons_of_mem a hb))
      simp [List.filter_cons, ha, hk, ih]

/-- A capture bound keeps its classifier under a renaming, which is Fact 1. -/
@[simp] theorem CapBound.classifier_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).classifier = b.classifier := by cases b <;> rfl

@[simp] theorem CapBound.classifier_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).classifier = b.classifier :=
  CapBound.classifier_rename b _

/-- And so an atom keeps its classifier, and every kind admits it as before. -/
@[simp] theorem Ctx.classOf_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).classOf (CapAtom.weaken (k := .var) a) = Γ.classOf a := by
  cases a <;> simp [Ctx.classOf, CapAtom.weaken, CapAtom.rename, Ctx.lookupCap_there]

@[simp] theorem Ctx.classOf_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).classOf (CapAtom.weaken (k := .cap) a) = Γ.classOf a := by
  cases a <;> simp [Ctx.classOf, CapAtom.weaken, CapAtom.rename, Ctx.lookupCap_thereC]

@[simp] theorem Ctx.admitsB_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) (φ : Cls.Kind) :
    (Γ.cons b).admitsB (CapAtom.weaken (k := .var) a) φ = Γ.admitsB a φ := by
  unfold Ctx.admitsB; rw [Ctx.classOf_weaken]

@[simp] theorem Ctx.admitsB_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s)
    (φ : Cls.Kind) :
    (Γ.consC b).admitsB (CapAtom.weaken (k := .cap) a) φ = Γ.admitsB a φ := by
  unfold Ctx.admitsB; rw [Ctx.classOf_weakenC]

/-! ### Expansion and weakening

Appending a term binder is invisible to expansion.  Appending a capture
binder is invisible only when its bound is not opaque: a rigid binder
appended to a root-free context enlarges the expansion of `⊤ᶜ`, which is
what a store is forbidden to do. -/

theorem Ctx.expandAtom_weaken_of_not_proj (Γ : Ctx s) (b : Binding s) {a : CapAtom s}
    (hbase : a.base = a) :
    (Γ.cons b).expandAtom a.weaken = (Γ.expandAtom a).weaken := by
  have hbw : (CapAtom.weaken (k := .var) a).base = a.weaken := by
    rw [CapAtom.weaken, CapAtom.base_rename, hbase]
  by_cases h : Γ.isRootB a = true
  · have h' : (Γ.cons b).isRootB (CapAtom.weaken (k := .var) a) = true := by
      rw [Ctx.isRootB_weaken]; exact h
    rw [Ctx.expandAtom_of_root h', Ctx.expandAtom_of_root h,
      Ctx.capBinders_cons, filter_of_map]
    simp only [CaptureSet.weaken, CaptureSet.rename, List.map_cons, List.map_map]
    congr 1
    refine congrArg (List.map _) (List.filter_congr ?_)
    intro κ _
    show (((Γ.lookupCap κ)↑).opaque &&
        (Γ.cons b).lvlLeB (CapAtom.weaken (k := .var) (.cvar κ))
          (CapAtom.weaken (k := .var) a)) = _
    rw [CapBound.opaque_weaken, Ctx.lvlLeB_weaken]
  · rw [Bool.not_eq_true] at h
    have h' : (Γ.cons b).isRootB (CapAtom.weaken (k := .var) a) = false := by
      rw [Ctx.isRootB_weaken]; exact h
    rw [Ctx.expandAtom_of_not_root h' hbw, Ctx.expandAtom_of_not_root h hbase]
    rfl

/-- A projection commutes because `Ctx.classOf` does, which is Fact 1. -/
theorem Ctx.expandAtom_weaken (Γ : Ctx s) (b : Binding s) : ∀ (a : CapAtom s),
    (Γ.cons b).expandAtom a.weaken = (Γ.expandAtom a).weaken
  | .top => Ctx.expandAtom_weaken_of_not_proj Γ b rfl
  | .var _ => Ctx.expandAtom_weaken_of_not_proj Γ b rfl
  | .cvar _ => Ctx.expandAtom_weaken_of_not_proj Γ b rfl
  | .name _ _ => Ctx.expandAtom_weaken_of_not_proj Γ b rfl
  | .proj a φ => by
      show ((Γ.cons b).expandAtom a.weaken).filter (fun c => (Γ.cons b).admitsB c φ) = _
      rw [Ctx.expandAtom_weaken Γ b a]
      show ((Γ.expandAtom a).map (fun c => c.rename Rename.succ)).filter _
        = ((Γ.expandAtom a).filter (fun c => Γ.admitsB c φ)).map (fun c => c.rename Rename.succ)
      rw [filter_of_map]
      exact congrArg (List.map _)
        (CaptureSet.filter_congr' _ _ (fun c => Ctx.admitsB_weaken Γ b c φ) _)

theorem Ctx.expandAtom_weakenC_of_not_proj (Γ : Ctx s) (b : CapBound s)
    (hb : b.opaque = false) {a : CapAtom s} (hbase : a.base = a) :
    (Γ.consC b).expandAtom a.weaken = (Γ.expandAtom a).weaken := by
  have hbw : (CapAtom.weaken (k := .cap) a).base = a.weaken := by
    rw [CapAtom.weaken, CapAtom.base_rename, hbase]
  by_cases h : Γ.isRootB a = true
  · have h' : (Γ.consC b).isRootB (CapAtom.weaken (k := .cap) a) = true := by
      rw [Ctx.isRootB_weakenC]; exact h
    rw [Ctx.expandAtom_of_root h', Ctx.expandAtom_of_root h, Ctx.capBinders_consC,
      List.filter_cons_of_neg (by
        show ¬ (((b↑).opaque && _) = true)
        rw [CapBound.opaque_weaken, hb]; simp),
      filter_of_map]
    simp only [CaptureSet.weaken, CaptureSet.rename, List.map_cons, List.map_map]
    congr 1
    refine congrArg (List.map _) (List.filter_congr ?_)
    intro κ _
    show (((Γ.lookupCap κ)↑).opaque &&
        (Γ.consC b).lvlLeB (CapAtom.weaken (k := .cap) (.cvar κ))
          (CapAtom.weaken (k := .cap) a)) = _
    rw [CapBound.opaque_weaken, Ctx.lvlLeB_weakenC]
  · rw [Bool.not_eq_true] at h
    have h' : (Γ.consC b).isRootB (CapAtom.weaken (k := .cap) a) = false := by
      rw [Ctx.isRootB_weakenC]; exact h
    rw [Ctx.expandAtom_of_not_root h' hbw, Ctx.expandAtom_of_not_root h hbase]
    rfl

theorem Ctx.expandAtom_weakenC (Γ : Ctx s) (b : CapBound s) (hb : b.opaque = false) :
    ∀ (a : CapAtom s), (Γ.consC b).expandAtom a.weaken = (Γ.expandAtom a).weaken
  | .top => Ctx.expandAtom_weakenC_of_not_proj Γ b hb rfl
  | .var _ => Ctx.expandAtom_weakenC_of_not_proj Γ b hb rfl
  | .cvar _ => Ctx.expandAtom_weakenC_of_not_proj Γ b hb rfl
  | .name _ _ => Ctx.expandAtom_weakenC_of_not_proj Γ b hb rfl
  | .proj a φ => by
      show ((Γ.consC b).expandAtom a.weaken).filter (fun c => (Γ.consC b).admitsB c φ) = _
      rw [Ctx.expandAtom_weakenC Γ b hb a]
      show ((Γ.expandAtom a).map (fun c => c.rename Rename.succ)).filter _
        = ((Γ.expandAtom a).filter (fun c => Γ.admitsB c φ)).map (fun c => c.rename Rename.succ)
      rw [filter_of_map]
      exact congrArg (List.map _)
        (CaptureSet.filter_congr' _ _ (fun c => Ctx.admitsB_weakenC Γ b c φ) _)

theorem Ctx.expand_weaken (Γ : Ctx s) (b : Binding s) : ∀ C : CaptureSet s,
    (Γ.cons b).expand C.weaken = (Γ.expand C).weaken
  | [] => by simp [CaptureSet.weaken, CaptureSet.rename]
  | a :: C => by
      show (Γ.cons b).expand (CapAtom.weaken a :: CaptureSet.weaken C)
        = CaptureSet.weaken (Γ.expand (a :: C))
      rw [Ctx.expand_cons, Ctx.expandAtom_weaken, Ctx.expand_weaken Γ b C,
        Ctx.expand_cons]
      simp [CaptureSet.weaken, CaptureSet.rename]

theorem Ctx.expand_weakenC (Γ : Ctx s) (b : CapBound s) (hb : b.opaque = false) :
    ∀ C : CaptureSet s, (Γ.consC b).expand C.weaken = (Γ.expand C).weaken
  | [] => by simp [CaptureSet.weaken, CaptureSet.rename]
  | a :: C => by
      show (Γ.consC b).expand (CapAtom.weaken a :: CaptureSet.weaken C)
        = CaptureSet.weaken (Γ.expand (a :: C))
      rw [Ctx.expand_cons, Ctx.expandAtom_weakenC Γ b hb, Ctx.expand_weakenC Γ b hb C,
        Ctx.expand_cons]
      simp [CaptureSet.weaken, CaptureSet.rename]

/-- The expansion of an atom that resolution can produce is contained in the
expansion of any root it is at or outside of. -/
theorem Ctx.expandAtom_mono {Γ : Ctx s} {a r : CapAtom s} (hr : Γ.IsRoot r)
    (ha : a = .top ∨ ∃ κ, a = .cvar κ ∧ (Γ.lookupCap κ).opaque = true)
    (hle : Γ.LvlLe a r) : (Γ.expandAtom a).Subset (Γ.expandAtom r) := by
  intro c hc
  cases hb : Γ.isRootB a with
  | false =>
      rw [Ctx.expandAtom_of_not_root hb
        (by rcases ha with rfl | ⟨κ, rfl, _⟩ <;> rfl)] at hc
      have hca : c = a := List.mem_singleton.mp hc
      subst hca
      rcases ha with rfl | ⟨κ, rfl, hop⟩
      · exact absurd hb (by simp [Ctx.isRootB])
      · exact Ctx.cvar_mem_expandAtom hr hop hle
  | true =>
      rcases Ctx.mem_expandAtom_root hb hc with rfl | ⟨κ, rfl, hop, hκ⟩
      · exact Ctx.top_mem_expandAtom hr
      · exact Ctx.cvar_mem_expandAtom hr hop (Ctx.LvlLe.trans hb hκ hle)

/-! ### Resolution lands in opaque atoms

Every atom of `Γ.caps n C` is the universal root or a capture binder whose
bound stands for itself.  A term binder resolves to the capture set of its
type, a bounded capture binder to its bound, and both descend; only a root, a
rigid binder and `⊤ᶜ` are leaves. -/

/-- What an atom of a resolution can be.  The disjunction reads the base of
the atom: resolution carries a projection along, and what sits under it is
`⊤ᶜ` or a capture binder whose bound is opaque, exactly as before. -/
abbrev Ctx.OpaqueAtom (Γ : Ctx s) (c : CapAtom s) : Prop :=
  c.base = .top ∨ ∃ κ, c.base = .cvar κ ∧ (Γ.lookupCap κ).opaque = true

theorem Ctx.opaqueAtom_weaken {Γ : Ctx s} (b : Binding s) {L : CaptureSet s}
    {c : CapAtom (s,x)} (hL : ∀ c₀ ∈ L, Γ.OpaqueAtom c₀)
    (hc : c ∈ CaptureSet.weaken (k := .var) L) : (Γ.cons b).OpaqueAtom c := by
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rcases hL c₀ hc₀ with h0 | ⟨κ, h0, hop⟩
  · exact Or.inl (by rw [CapAtom.base_rename, h0]; rfl)
  · refine Or.inr ⟨.there κ, by rw [CapAtom.base_rename, h0]; rfl, ?_⟩
    rw [Ctx.lookupCap_there, CapBound.opaque_weaken]
    exact hop

theorem Ctx.opaqueAtom_weakenC {Γ : Ctx s} (b : CapBound s) {L : CaptureSet s}
    {c : CapAtom (s,c)} (hL : ∀ c₀ ∈ L, Γ.OpaqueAtom c₀)
    (hc : c ∈ CaptureSet.weaken (k := .cap) L) : (Γ.consC b).OpaqueAtom c := by
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rcases hL c₀ hc₀ with h0 | ⟨κ, h0, hop⟩
  · exact Or.inl (by rw [CapAtom.base_rename, h0]; rfl)
  · refine Or.inr ⟨.there κ, by rw [CapAtom.base_rename, h0]; rfl, ?_⟩
    rw [Ctx.lookupCap_thereC, CapBound.opaque_weaken]
    exact hop

/-- The set half follows from the atom half. -/
theorem Ctx.caps_opaque_of_atom {Γ : Ctx s} {n : Nat}
    (h : ∀ (a c : CapAtom s), c ∈ Γ.capsAtom n a → Γ.OpaqueAtom c) :
    ∀ (C : CaptureSet s) (c : CapAtom s), c ∈ Γ.caps n C → Γ.OpaqueAtom c
  | [], c, hc => by simp at hc
  | a :: C, c, hc => by
      rw [Ctx.caps_cons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h a c hc
      · exact Ctx.caps_opaque_of_atom h C c hc

/-- The projection clause of the opacity lemma: the base of a projected atom
is the base of the atom under it. -/
theorem Ctx.opaqueAtom_proj {Γ : Ctx s} {L : CaptureSet s} {c : CapAtom s} {φ : Cls.Kind}
    (hL : ∀ c₀ ∈ L, Γ.OpaqueAtom c₀) (hc : c ∈ L.map (CapAtom.proj · φ)) :
    Γ.OpaqueAtom c := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hL d hd

theorem Ctx.capsAtom_opaque_aux : ∀ (n : Nat) {s : Sig} (Γ : Ctx s) (a c : CapAtom s),
    c ∈ Γ.capsAtom n a → Γ.OpaqueAtom c := by
  intro n
  induction n with
  | zero =>
      intro s Γ
      induction Γ with
      | nil =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
      | cons Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
          | name x ℓ => rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          | var y =>
              cases y with
              | here =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (Ctx.caps_opaque_of_atom ih _) hc
              | there y₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (fun _ => ih (.var y₀) _) hc
          | cvar κ =>
              cases κ with
              | there κ₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (fun _ => ih (.cvar κ₀) _) hc
      | consC Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
          | name x ℓ => rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          | var y =>
              cases y with
              | there y₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weakenC b (fun _ => ih (.var y₀) _) hc
          | cvar κ =>
              cases κ with
              | here =>
                  cases b with
                  | root =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | star =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | cls c₀ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | upper C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | inst C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
              | there κ₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weakenC b (fun _ => ih (.cvar κ₀) _) hc
  | succ n ihn =>
      intro s Γ
      induction Γ with
      | nil =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
      | cons Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
          | name x ℓ =>
              cases hd : (Ctx.cons Γ b).lookupDefC x ℓ with
              | none => rw [Ctx.capsAtom_name_none hd] at hc; simp at hc
              | some C =>
                  rw [Ctx.capsAtom_name_some hd] at hc
                  exact Ctx.caps_opaque_of_atom (ihn (Ctx.cons Γ b)) C c hc
          | var y =>
              cases y with
              | here =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (Ctx.caps_opaque_of_atom ih _) hc
              | there y₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (fun _ => ih (.var y₀) _) hc
          | cvar κ =>
              cases κ with
              | there κ₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weaken b (fun _ => ih (.cvar κ₀) _) hc
      | consC Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj] at hc
              exact Ctx.opaqueAtom_proj (fun d hd => iha d hd) hc
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
          | name x ℓ =>
              cases hd : (Ctx.consC Γ b).lookupDefC x ℓ with
              | none => rw [Ctx.capsAtom_name_none hd] at hc; simp at hc
              | some C =>
                  rw [Ctx.capsAtom_name_some hd] at hc
                  exact Ctx.caps_opaque_of_atom (ihn (Ctx.consC Γ b)) C c hc
          | var y =>
              cases y with
              | there y₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weakenC b (fun _ => ih (.var y₀) _) hc
          | cvar κ =>
              cases κ with
              | here =>
                  cases b with
                  | root =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | star =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | cls c₀ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | upper C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | inst C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
              | there κ₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weakenC b (fun _ => ih (.cvar κ₀) _) hc

/-- Resolution lands in opaque atoms.  The disjunction reads `a.base`, which
is `a` itself on every atom the copied representation could build. -/
theorem Ctx.caps_opaque {Γ : Ctx s} {n : Nat} {C : CaptureSet s} {a : CapAtom s}
    (h : a ∈ Γ.caps n C) :
    a.base = .top ∨ ∃ κ, a.base = .cvar κ ∧ (Γ.lookupCap κ).opaque = true :=
  Ctx.caps_opaque_of_atom (Ctx.capsAtom_opaque_aux n Γ) C a h

/-! ### Resolution keeps the level

Resolution never lowers the level: what a capture set resolves to is at or
outside every root the set itself is at or outside of.  This is the fact the
level rule rests on.  The induction is on the fuel and then on the spine of
the context, the order the rest of this file uses, which is the lexicographic
measure of `Ctx.caps` and `Ctx.capsAtom` read the other way round: the name
clause drops the fuel at the same context, and every other clause keeps the
fuel and drops the context. -/

/-- The capture witness of a block is at or outside the level of its binder:
the witness lives in the scope that includes the binder itself. -/
theorem Ctx.lookupDefC_confined {s : Sig} (Γ : Ctx s) :
    ∀ (x : BVar s .var) (ℓ : Label) (C : CaptureSet s),
      Γ.lookupDefC x ℓ = some C → Γ.Confined C (Γ.lvlOf (.var x)) := by
  induction Γ with
  | nil => intro x _ _ _; cases x
  | cons Γ b ih =>
      intro x ℓ C h
      cases x with
      | here =>
          rw [Ctx.lvlOf_cons_here, ← Ctx.rootAtom_cons]
          exact (Γ.cons b).confined_rootAtom C
      | there y =>
          rw [Ctx.lookupDefC_there] at h
          cases hy : Γ.lookupDefC y ℓ with
          | none => rw [hy] at h; exact absurd h (by simp)
          | some C₀ =>
              rw [hy] at h
              have hC : C = CaptureSet.weaken (k := .var) C₀ := by
                simpa using h.symm
              subst hC
              have hlv : (Ctx.cons Γ b).lvlOf (CapAtom.var (BVar.there y))
                  = CapAtom.weaken (k := .var) (Γ.lvlOf (.var y)) :=
                Ctx.lvlOf_weaken Γ b (.var y)
              rw [hlv]
              exact Ctx.Confined.weaken b (ih y ℓ C₀ hy)
  | consC Γ b ih =>
      intro x ℓ C h
      cases x with
      | there y =>
          rw [Ctx.lookupDefC_thereC] at h
          cases hy : Γ.lookupDefC y ℓ with
          | none => rw [hy] at h; exact absurd h (by simp)
          | some C₀ =>
              rw [hy] at h
              have hC : C = CaptureSet.weaken (k := .cap) C₀ := by
                simpa using h.symm
              subst hC
              have hlv : (Ctx.consC Γ b).lvlOf (CapAtom.var (BVar.there y))
                  = CapAtom.weaken (k := .cap) (Γ.lvlOf (.var y)) :=
                Ctx.lvlOf_weakenC Γ b (.var y)
              rw [hlv]
              exact Ctx.Confined.weakenC b (ih y ℓ C₀ hy)

/-- The set half of a confinement statement follows from the atom half. -/
theorem Ctx.caps_confined_of_atom {Γ : Ctx s} {n : Nat} {r : CapAtom s}
    (h : ∀ a : CapAtom s, Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r) :
    ∀ C : CaptureSet s, Γ.Confined C r → Γ.Confined (Γ.caps n C) r
  | [], _ => by intro c hc; simp at hc
  | a :: C, hC => by
      intro c hc
      rw [Ctx.caps_cons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h a (hC a (List.mem_cons_self ..)) c hc
      · exact Ctx.caps_confined_of_atom h C
          (fun b hb => hC b (List.mem_cons_of_mem a hb)) c hc

/-- The two `.there` clauses of `Ctx.capsAtom`, at a term binder. -/
theorem Ctx.capsAtom_confined_there {s : Sig} {Γ : Ctx s} (b : Binding s) {n : Nat}
    (ih : ∀ (a r : CapAtom s), Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r)
    (a₀ : CapAtom s) (r : CapAtom (s,x))
    (h : (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) a₀) r) :
    (Γ.cons b).Confined (CaptureSet.weaken (k := .var) (Γ.capsAtom n a₀)) r := by
  have h1 := Ctx.Confined.weaken (Γ := Γ) b (ih a₀ (Γ.lvlOf a₀) (Γ.lvlLe_lvlOf a₀))
  rw [← Ctx.lvlOf_weaken Γ b a₀] at h1
  exact Ctx.confined_trans h1 h

/-- The two `.there` clauses of `Ctx.capsAtom`, at a capture binder. -/
theorem Ctx.capsAtom_confined_thereC {s : Sig} {Γ : Ctx s} (b : CapBound s) {n : Nat}
    (ih : ∀ (a r : CapAtom s), Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r)
    (a₀ : CapAtom s) (r : CapAtom (s,c))
    (h : (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) a₀) r) :
    (Γ.consC b).Confined (CaptureSet.weaken (k := .cap) (Γ.capsAtom n a₀)) r := by
  have h1 := Ctx.Confined.weakenC (Γ := Γ) b (ih a₀ (Γ.lvlOf a₀) (Γ.lvlLe_lvlOf a₀))
  rw [← Ctx.lvlOf_weakenC Γ b a₀] at h1
  exact Ctx.confined_trans h1 h

/-- The clause of `Ctx.capsAtom` at the term binder a context adds. -/
theorem Ctx.capsAtom_confined_here {s : Sig} {Γ : Ctx s} (b : Binding s) {n : Nat}
    (ih : ∀ (a r : CapAtom s), Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r)
    (D : CaptureSet s) (r : CapAtom (s,x))
    (h : (Γ.cons b).LvlLe (.var .here) r) :
    (Γ.cons b).Confined (CaptureSet.weaken (k := .var) (Γ.caps n D)) r := by
  have h0 : Γ.Confined (Γ.caps n D) Γ.rootAtom :=
    Ctx.caps_confined_of_atom (fun a => ih a Γ.rootAtom) D (Γ.confined_rootAtom D)
  have h1 := Ctx.Confined.weaken (Γ := Γ) b h0
  rw [← Ctx.lvlOf_cons_here Γ b] at h1
  exact Ctx.confined_trans h1 h

/-- The clause of `Ctx.capsAtom` at a capture binder with a bound. -/
theorem Ctx.capsAtom_confined_hereC {s : Sig} {Γ : Ctx s} (b : CapBound s)
    (hb : b.isRoot = false) {n : Nat}
    (ih : ∀ (a r : CapAtom s), Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r)
    (D : CaptureSet s) (r : CapAtom (s,c))
    (h : (Γ.consC b).LvlLe (.cvar .here) r) :
    (Γ.consC b).Confined (CaptureSet.weaken (k := .cap) (Γ.caps n D)) r := by
  have h0 : Γ.Confined (Γ.caps n D) Γ.rootAtom :=
    Ctx.caps_confined_of_atom (fun a => ih a Γ.rootAtom) D (Γ.confined_rootAtom D)
  have h1 := Ctx.Confined.weakenC (Γ := Γ) b h0
  rw [← Ctx.lvlOf_consC_here Γ b hb] at h1
  exact Ctx.confined_trans h1 h

/-- The name clause, at one unit more fuel. -/
theorem Ctx.capsAtom_confined_name {s : Sig} (Γ : Ctx s) (n : Nat)
    (ihn : ∀ (a r : CapAtom s), Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r)
    (x : BVar s .var) (ℓ : Label) (r : CapAtom s) (h : Γ.LvlLe (.name x ℓ) r) :
    Γ.Confined (Γ.capsAtom (n + 1) (.name x ℓ)) r := by
  cases hd : Γ.lookupDefC x ℓ with
  | none => intro c hc; rw [Ctx.capsAtom_name_none hd] at hc; simp at hc
  | some C =>
      intro c hc
      rw [Ctx.capsAtom_name_some hd] at hc
      have hCC : Γ.Confined C (Γ.lvlOf (.name x ℓ)) := Γ.lookupDefC_confined x ℓ C hd
      exact Ctx.caps_confined_of_atom (fun a₀ => ihn a₀ r) C
        (Ctx.confined_trans hCC h) c hc

/-- The projection clause of the confinement lemma: a projection is at the
level of what it projects, so its resolution is confined where that one is. -/
theorem Ctx.confined_proj {Γ : Ctx s} {L : CaptureSet s} {r : CapAtom s} {φ : Cls.Kind}
    (h : Γ.Confined L r) : Γ.Confined (L.map (CapAtom.proj · φ)) r := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact h d hd

theorem Ctx.capsAtom_confined_aux : ∀ (n : Nat) {s : Sig} (Γ : Ctx s) (a r : CapAtom s),
    Γ.LvlLe a r → Γ.Confined (Γ.capsAtom n a) r := by
  intro n
  induction n with
  | zero =>
      intro s Γ
      induction Γ with
      | nil =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
      | cons Γ b ih =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
          | name x ℓ => intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          | var y =>
              cases y with
              | here =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_here b ih _ r h
              | there y₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_there b ih (.var y₀) r h
          | cvar κ =>
              cases κ with
              | there κ₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_there b ih (.cvar κ₀) r h
      | consC Γ b ih =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
          | name x ℓ => intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          | var y =>
              cases y with
              | there y₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_thereC b ih (.var y₀) r h
          | cvar κ =>
              cases κ with
              | here =>
                  cases b with
                  | root =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | star =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | cls c₀ =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | upper C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.upper C) rfl ih C r h
                  | inst C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.inst C) rfl ih C r h
              | there κ₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_thereC b ih (.cvar κ₀) r h
  | succ n ihn =>
      intro s Γ
      induction Γ with
      | nil =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
      | cons Γ b ih =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
          | name x ℓ => exact Ctx.capsAtom_confined_name (Γ.cons b) n (ihn (Γ.cons b)) x ℓ r h
          | var y =>
              cases y with
              | here =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_here b ih _ r h
              | there y₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_there b ih (.var y₀) r h
          | cvar κ =>
              cases κ with
              | there κ₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_there b ih (.cvar κ₀) r h
      | consC Γ b ih =>
          intro a r h
          induction a with
          | proj a φ iha =>
              rw [Ctx.capsAtom_proj]
              exact Ctx.confined_proj (iha h)
          | top =>
              intro c hc
              rw [Ctx.capsAtom_top] at hc
              rw [List.mem_singleton.mp hc]
              exact h
          | name x ℓ => exact Ctx.capsAtom_confined_name (Γ.consC b) n (ihn (Γ.consC b)) x ℓ r h
          | var y =>
              cases y with
              | there y₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_thereC b ih (.var y₀) r h
          | cvar κ =>
              cases κ with
              | here =>
                  cases b with
                  | root =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | star =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | cls c₀ =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | upper C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.upper C) rfl ih C r h
                  | inst C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.inst C) rfl ih C r h
              | there κ₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_thereC b ih (.cvar κ₀) r h

/-- Resolution of one atom keeps the level. -/
theorem Ctx.capsAtom_confined {s : Sig} (Γ : Ctx s) (n : Nat) (a r : CapAtom s)
    (h : Γ.Confined [a] r) : Γ.Confined (Γ.capsAtom n a) r :=
  Ctx.capsAtom_confined_aux n Γ a r (h a (List.mem_cons_self ..))

/-- Resolution keeps the level: what a capture set resolves to is at or
outside every root the set itself is at or outside of. -/
theorem Ctx.caps_confined {s : Sig} (Γ : Ctx s) (n : Nat) (C : CaptureSet s) (r : CapAtom s)
    (h : Γ.Confined C r) : Γ.Confined (Γ.caps n C) r :=
  Ctx.caps_confined_of_atom (fun a ha => Ctx.capsAtom_confined_aux n Γ a r ha) C h

/-! ### Roots and subcapturing -/

/-- The roots of a capture set at a given fuel: resolution followed by
expansion.  Name, signature and fuel are those of the DOT way, and on a
root-free context that mentions no `⊤ᶜ` this is `caps` again
(`Ctx.roots_eq_caps_of_rootFree`). -/
def Ctx.roots (Γ : Ctx s) (n : Nat) (C : CaptureSet s) : CaptureSet s :=
  Γ.expand (Γ.caps n C)

@[simp] theorem Ctx.roots_eq_expand_caps (Γ : Ctx s) (n : Nat) (C : CaptureSet s) :
    Γ.roots n C = Γ.expand (Γ.caps n C) := rfl

/-- Resolution lands in the roots, by the bases of the atoms their own kinds
admit.  A projected atom that its own kind excludes is not a root. -/
theorem Ctx.caps_subset_roots (Γ : Ctx s) (n : Nat) (C : CaptureSet s)
    (h : ∀ a ∈ Γ.caps n C, Γ.admitsB a.base a.kindOf = true) :
    ∀ a ∈ Γ.caps n C, a.base ∈ Γ.roots n C := Γ.subset_expand _ h

/-- Nothing outside a scope sees the change.  On a root-free context whose
resolution does not mention `⊤ᶜ`, `roots` is `caps`, so every statement about
roots on the platform prefix and on a store context means today what it meant
before. -/
theorem Ctx.roots_eq_caps_of_rootFree {Γ : Ctx s} {n : Nat} {C : CaptureSet s}
    (h : Γ.root? = none) (hC : CapAtom.top ∉ (Γ.caps n C).map CapAtom.base) :
    Γ.roots n C
      = ((Γ.caps n C).filter (fun a => Γ.admitsB a.base a.kindOf)).map CapAtom.base := by
  rw [Ctx.roots_eq_expand_caps]
  refine Ctx.expand_eq_filter_base ?_
  intro a ha
  rcases Ctx.caps_opaque ha with h0 | ⟨κ, h0, _⟩
  · exact absurd (h0 ▸ List.mem_map_of_mem ha) hC
  · rw [h0]
    show (Γ.lookupCap κ).isRoot = false
    exact Γ.root?_none_isRoot h κ

/-- `a` is a root of `C`: `C` resolves to `a` at some fuel.  Resolution is
monotone in the fuel, so this is the least solution of the resolution
equations, in which a cyclic chain of capture names contributes nothing. -/
def Ctx.Root (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) : Prop :=
  ∃ n : Nat, a ∈ Γ.roots n C

theorem Ctx.Root.of_mem_caps {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {n : Nat}
    (h : a ∈ Γ.caps n C) (hk : Γ.admitsB a.base a.kindOf = true) : Γ.Root a.base C :=
  ⟨n, Ctx.mem_expand.mpr ⟨a, h, Γ.mem_expandAtom_self a hk⟩⟩

/-- Subcapturing as a proposition: the roots of `C` are among the roots of
`D`. -/
abbrev CapLe (Γ : Ctx s) (C D : CaptureSet s) : Prop :=
  ∀ a : CapAtom s, Γ.Root a C → Γ.Root a D

/-- Two capture sets have the same roots. -/
abbrev RootsEq (Γ : Ctx s) (C D : CaptureSet s) : Prop :=
  ∀ a : CapAtom s, Γ.Root a C ↔ Γ.Root a D

theorem CapLe.refl (Γ : Ctx s) (C : CaptureSet s) : CapLe Γ C C := fun _ h => h

theorem CapLe.trans {Γ : Ctx s} {C D E : CaptureSet s}
    (h₁ : CapLe Γ C D) (h₂ : CapLe Γ D E) : CapLe Γ C E := fun a h => h₂ a (h₁ a h)

theorem CapLe.of_subset {Γ : Ctx s} {C D : CaptureSet s} (h : C.Subset D) :
    CapLe Γ C D :=
  fun _ hr => hr.elim fun n hn => ⟨n, Ctx.expand_subset (Ctx.caps_subset h) _ hn⟩

theorem CapLe.union {Γ : Ctx s} {C D E : CaptureSet s}
    (h₁ : CapLe Γ C E) (h₂ : CapLe Γ D E) : CapLe Γ (C ∪ D) E := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps, CaptureSet.union_def, Ctx.caps_append,
    Ctx.expand_append] at ha
  rcases List.mem_append.mp ha with h | h
  · exact h₁ a ⟨n, h⟩
  · exact h₂ a ⟨n, h⟩

/-- Replacing either side by a set with the same roots changes nothing. -/
theorem CapLe.congr_roots {Γ : Ctx s} {C C' D D' : CaptureSet s}
    (hC : RootsEq Γ C C') (hD : RootsEq Γ D D')
    (h : CapLe Γ C D) : CapLe Γ C' D' :=
  fun a ha => (hD a).mp (h a ((hC a).mpr ha))

theorem RootsEq.refl (Γ : Ctx s) (C : CaptureSet s) : RootsEq Γ C C := fun _ => Iff.rfl

theorem RootsEq.symm {Γ : Ctx s} {C D : CaptureSet s} (h : RootsEq Γ C D) :
    RootsEq Γ D C := fun a => (h a).symm

theorem RootsEq.trans {Γ : Ctx s} {C D E : CaptureSet s}
    (h₁ : RootsEq Γ C D) (h₂ : RootsEq Γ D E) : RootsEq Γ C E :=
  fun a => (h₁ a).trans (h₂ a)

theorem RootsEq.le {Γ : Ctx s} {C D : CaptureSet s} (h : RootsEq Γ C D) :
    CapLe Γ C D := fun a ha => (h a).mp ha

theorem RootsEq.of_le {Γ : Ctx s} {C D : CaptureSet s}
    (h₁ : CapLe Γ C D) (h₂ : CapLe Γ D C) : RootsEq Γ C D :=
  fun a => ⟨h₁ a, h₂ a⟩

theorem CapLe.weaken {Γ : Ctx s} {C D : CaptureSet s} (b : Binding s)
    (h : CapLe Γ C D) : CapLe (Ctx.cons Γ b) C.weaken D.weaken := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weaken, Ctx.expand_weaken] at ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨m, hm⟩ := h c ⟨n, hc⟩
  refine ⟨m, ?_⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weaken, Ctx.expand_weaken]
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map]
  exact ⟨c, hm, rfl⟩

/-- Weakening by a capture binder whose bound is not opaque.  An opaque
binder appended to a root-free context enlarges the expansion of `⊤ᶜ`, so the
premise is what makes the two sides agree; B0.7 forbids a store to append
one, and the theorem has no other caller. -/
theorem CapLe.weakenC {Γ : Ctx s} {C D : CaptureSet s} (b : CapBound s)
    (hb : b.opaque = false)
    (h : CapLe Γ C D) : CapLe (Ctx.consC Γ b) C.weaken D.weaken := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weakenC, Ctx.expand_weakenC Γ b hb] at ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨m, hm⟩ := h c ⟨n, hc⟩
  refine ⟨m, ?_⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weakenC, Ctx.expand_weakenC Γ b hb]
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map]
  exact ⟨c, hm, rfl⟩

/-! ### The resolution lemma of the capture sort -/

/-- A defined capture name has exactly the roots of its capture witness: this
is the capture-sort analogue of `Ctx.resolve_sel_some`, and the fact that
`defC` evidence needs. -/
theorem Ctx.Root_name {Γ : Ctx s} {x : BVar s .var} {ℓ : Label} {C : CaptureSet s}
    (h : Γ.lookupDefC x ℓ = some C) : RootsEq Γ [CapAtom.name x ℓ] C := by
  intro a
  constructor
  · rintro ⟨n, hn⟩
    rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil] at hn
    cases n with
    | zero => rw [Ctx.capsAtom_name_zero, Ctx.expand_nil] at hn; simp at hn
    | succ n => rw [Ctx.capsAtom_name_some h] at hn; exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil,
      Ctx.capsAtom_name_some h]
    exact hn

/-- An instance binder has exactly the roots of the set it was opened at.
This is what `CapEq.HasType.instC` needs, and it is the capture-sort analogue
of `Ctx.Root_name` at a capture binder rather than at a block name.  An
instance binder consumes no fuel, so the two directions run at the same
`n`. -/
theorem Ctx.Root_inst {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s}
    (h : Γ.InstOf a C) : RootsEq Γ [a] C := by
  cases a with
  | cvar κ =>
      have h' : (Γ.lookupCap κ).instSet? = some C := h
      have hlk : Γ.lookupCap κ = .inst C := by
        cases hb : Γ.lookupCap κ with
        | root => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | star => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | cls c₀ => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | upper D => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | inst D =>
            rw [hb] at h'
            simp only [CapBound.instSet?, Option.some.injEq] at h'
            rw [h']
      intro b
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil,
          Ctx.capsAtom_cvar, hlk] at hn
        rw [Ctx.roots_eq_expand_caps]
        exact hn
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil,
          Ctx.capsAtom_cvar, hlk]
        rw [Ctx.roots_eq_expand_caps] at hn
        exact hn
  | var _ => simp [Ctx.InstOf, Ctx.instSet?] at h
  | name _ _ => simp [Ctx.InstOf, Ctx.instSet?] at h
  | top => simp [Ctx.InstOf, Ctx.instSet?] at h
  | proj _ _ => simp [Ctx.InstOf, Ctx.instSet?] at h

/-- A capture name with no definition has no roots. -/
theorem Ctx.Root_name_none {Γ : Ctx s} {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefC x ℓ = none) (a : CapAtom s) : ¬ Γ.Root a [CapAtom.name x ℓ] := by
  rintro ⟨n, hn⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil] at hn
  cases n with
  | zero => rw [Ctx.capsAtom_name_zero, Ctx.expand_nil] at hn; simp at hn
  | succ n => rw [Ctx.capsAtom_name_none h, Ctx.expand_nil] at hn; simp at hn


/-! ## K0.5 and K0.6: projected sets and the kinding of a resolved set

The filter a projection carries is consumed inside `Ctx.expandAtom`, and
`Ctx.roots` is `Ctx.expand` of `Ctx.caps`, so the roots of a projected set are
the roots of the set filtered by the kind.  That is T1, and everything else of
the stage reads off it. -/

/-- Expansion of a mapped projection is the filtered expansion.  This is L1
read on a whole list, and it is the engine of T1. -/
theorem Ctx.expand_map_proj (Γ : Ctx s) (φ : Cls.Kind) : ∀ L : CaptureSet s,
    Γ.expand (L.map (CapAtom.proj · φ)) = (Γ.expand L).filter (fun b => Γ.admitsB b φ)
  | [] => rfl
  | a :: L => by
      rw [List.map_cons, Ctx.expand_cons, Ctx.expand_cons, Ctx.expandAtom_proj,
        Ctx.expand_map_proj Γ φ L, List.filter_append]

/-- The one-atom form of T1: resolving and expanding a projected atom is
resolving and expanding the atom and then filtering.  Two cases, and the
projected one is the only place the kind algebra is used in K0. -/
theorem Ctx.expand_capsAtom_projBy (Γ : Ctx s) (n : Nat) (φ : Cls.Kind) (a : CapAtom s) :
    Γ.expand (Γ.capsAtom n (CapAtom.projBy φ a))
      = (Γ.expand (Γ.capsAtom n a)).filter (fun b => Γ.admitsB b φ) := by
  cases a with
  | top | var _ | cvar _ | name _ _ =>
      rw [show CapAtom.projBy φ _ = CapAtom.proj _ φ from rfl, Ctx.capsAtom_proj,
        Ctx.expand_map_proj]
  | proj c ψ =>
      rw [show CapAtom.projBy φ (CapAtom.proj c ψ) = CapAtom.proj c (φ.interB ψ) from rfl,
        Ctx.capsAtom_proj, Ctx.expand_map_proj, Ctx.capsAtom_proj, Ctx.expand_map_proj,
        CaptureSet.filter_filter]
      refine CaptureSet.filter_congr' _ _ (fun b => ?_) _
      show (φ.interB ψ).containsB (Γ.classOf b)
        = (ψ.containsB (Γ.classOf b) && φ.containsB (Γ.classOf b))
      rw [Cls.Kind.contains_inter, Bool.and_comm]

/-- **T1.**  The roots of a projected set are the roots of the set that the
kind admits.  No induction on the context and none on the fuel: both sides are
`flatMap`s over `C`, and `List.filter` distributes over `++`. -/
theorem Ctx.roots_proj (Γ : Ctx s) (n : Nat) : ∀ (C : CaptureSet s) (φ : Cls.Kind),
    Γ.roots n (CaptureSet.proj C φ) = (Γ.roots n C).filter (fun b => Γ.admitsB b φ)
  | [], _ => by simp [CaptureSet.proj]
  | a :: C, φ => by
      rw [Ctx.roots_eq_expand_caps, Ctx.roots_eq_expand_caps,
        show CaptureSet.proj (a :: C) φ = CapAtom.projBy φ a :: CaptureSet.proj C φ from rfl,
        Ctx.caps_cons, Ctx.caps_cons, Ctx.expand_append, Ctx.expand_append,
        List.filter_append, Ctx.expand_capsAtom_projBy]
      have ih := Ctx.roots_proj Γ n C φ
      rw [Ctx.roots_eq_expand_caps, Ctx.roots_eq_expand_caps] at ih
      rw [ih]

/-- **T1**, membership form.  A root of a projected set is a root of the set
that the kind admits, and conversely. -/
theorem Ctx.Root_proj {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {φ : Cls.Kind} :
    Γ.Root a (CaptureSet.proj C φ) ↔ (Γ.Root a C ∧ Γ.admitsB a φ = true) := by
  constructor
  · rintro ⟨n, hn⟩
    rw [Ctx.roots_proj] at hn
    exact ⟨⟨n, (List.mem_filter.mp hn).1⟩, (List.mem_filter.mp hn).2⟩
  · rintro ⟨⟨n, hn⟩, hφ⟩
    refine ⟨n, ?_⟩
    rw [Ctx.roots_proj]
    exact List.mem_filter.mpr ⟨hn, hφ⟩

/-- **T1** at the root kind: projecting by `⊤` changes no root.  This is
Capless(K)'s `CaptureSet.proj_top`, which is an equation there and is an
equality of roots here. -/
theorem Ctx.rootsEq_proj_top (Γ : Ctx s) (C : CaptureSet s) :
    RootsEq Γ (CaptureSet.proj C Cls.Kind.top) C := by
  intro a
  rw [Ctx.Root_proj]
  exact ⟨fun h => h.1, fun h => ⟨h, Γ.admitsB_top a⟩⟩

/-- Every root of `C` carries a classifier that `φ` admits.  The classifier
twin of `CapLe`, stated beside it.  This is the plan's canonical form of
closed kinding, as a proposition. -/
def Ctx.KindLe (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) : Prop :=
  ∀ a : CapAtom s, Γ.Root a C → φ.Contains (Γ.classOf a)

/-- Every atom resolution produces carries a kind below the kind of an atom of
the set it came from.  L3 on a whole capture set. -/
theorem Ctx.caps_kindOf (Γ : Ctx s) (n : Nat) : ∀ (C : CaptureSet s),
    ∀ b ∈ Γ.caps n C, ∃ a ∈ C, ∀ c : Cls.Classifier,
      b.kindOf.Contains c → a.kindOf.Contains c
  | [], b, hb => by simp at hb
  | a :: C, b, hb => by
      rw [Ctx.caps_cons] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨a, List.mem_cons_self .., Γ.capsAtom_kindOf n a b hb⟩
      · obtain ⟨d, hd, hkd⟩ := Γ.caps_kindOf n C b hb
        exact ⟨d, List.mem_cons_of_mem a hd, hkd⟩

/-- **T2.**  A set whose atoms all carry kinds inside `φ` is kinded by `φ`.
L3 followed by L4: a root is an atom of the expansion of an atom of
`Γ.caps n C`, L3 bounds that atom's kind by the kind of the atom of `C` it
came from, and L4 says the root is admitted by it. -/
theorem Ctx.kindLe_of_kinds {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (h : ∀ a ∈ C, ∀ c : Cls.Classifier, a.kindOf.Contains c → φ.Contains c) :
    Γ.KindLe C φ := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps] at ha
  obtain ⟨b, hb, hab⟩ := Ctx.mem_expand.mp ha
  obtain ⟨d, hd, hkd⟩ := Γ.caps_kindOf n C b hb
  exact h d hd (Γ.classOf a) (hkd (Γ.classOf a) (Γ.expandAtom_kinded b a hab))

/-- **T2**, the form the stage uses: a projected set is kinded by construction,
whatever the set was.  This is what the refuted design lost. -/
theorem Ctx.kindLe_proj (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) :
    Γ.KindLe (CaptureSet.proj C φ) φ := fun _ ha => (Ctx.Root_proj.mp ha).2

/-- **T3.**  Kinding is antitone along subcapturing. -/
theorem Ctx.KindLe.mono {Γ : Ctx s} {C D : CaptureSet s} {φ : Cls.Kind}
    (hle : CapLe Γ C D) (h : Γ.KindLe D φ) : Γ.KindLe C φ :=
  fun a ha => h a (hle a ha)

/-- **T3.**  And monotone along subkinding.  The only consumer of subkinding
in K0. -/
theorem Ctx.KindLe.sub {Γ : Ctx s} {C : CaptureSet s} {φ ψ : Cls.Kind}
    (h : Γ.KindLe C φ) (hs : φ.Subkind ψ) : Γ.KindLe C ψ :=
  fun a ha => Cls.Kind.Subkind.contains hs (h a ha)

/-- **T3.**  A union is kinded when both sides are. -/
theorem Ctx.KindLe.union {Γ : Ctx s} {C D : CaptureSet s} {φ : Cls.Kind}
    (h₁ : Γ.KindLe C φ) (h₂ : Γ.KindLe D φ) : Γ.KindLe (C ∪ D) φ := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps, CaptureSet.union_def, Ctx.caps_append,
    Ctx.expand_append] at ha
  rcases List.mem_append.mp ha with h | h
  · exact h₁ a ⟨n, h⟩
  · exact h₂ a ⟨n, h⟩

/-! ### Item 6 of the canonical-forms theorem

`cap_canon`, the statement that closed capture evidence includes roots, no
longer fits here: `CapCo.HasType` is now mutual with atom typing, so `capvar`
needs item 7 of the theorem and `member` needs the view of an atom.  The
statement moves, unchanged, into the mutual induction of `CanonicalForms.lean`
(plan-5c A1.6); the four constructors it had in A0 are still discharged by
`CapLe.refl`, `CapLe.trans`, `CapLe.of_subset` and `CapLe.union`, and `defC`
by `Ctx.Root_name` above. -/

end FCdot

end Classifiers
