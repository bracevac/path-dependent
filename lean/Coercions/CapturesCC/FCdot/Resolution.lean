import Coercions.CapturesCC.FCdot.Normalizer
import Coercions.CapturesCC.FCdot.Typing
import Coercions.CapturesCC.FCdot.TypingRename

namespace CapturesCC

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

@[simp] theorem Ctx.resolve_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) :
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
termination_by Γ n C => (sizeOf Γ, n, C.length + 1)

/-- `caps_Γ n` on one atom: a term binder resolves to the capture set of its
type and a capture binder to itself or to its bound, both by descent on the
binder; a capture name follows the capture witness of its block, at the same
context, and so consumes one unit of fuel.  A name with no fuel left lies on
a cyclic chain and resolves to the empty set. -/
def Ctx.capsAtom : (Γ : Ctx s) → Nat → CapAtom s → CaptureSet s
  | .cons Γ b, n, .var .here => (Γ.caps n b.ty.captureSet).weaken
  | .cons Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC _ .root, _, .cvar .here => [.cvar .here]
  | .consC _ .star, _, .cvar .here => [.cvar .here]
  | .consC Γ (.upper C), n, .cvar .here => (Γ.caps n C).weaken
  | .consC Γ (.inst C), n, .cvar .here => (Γ.caps n C).weaken
  | .cons Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | .consC Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | _, 0, .name _ _ => []
  | Γ, n + 1, .name x ℓ =>
      match Γ.lookupDefC x ℓ with
      | some C => Γ.caps n C
      | none => []
termination_by Γ n _ => (sizeOf Γ, n, 0)

end

@[simp] theorem Ctx.caps_nil (Γ : Ctx s) (n : Nat) : Γ.caps n [] = [] := by
  simp [Ctx.caps]

@[simp] theorem Ctx.caps_cons (Γ : Ctx s) (n : Nat) (a : CapAtom s) (C : CaptureSet s) :
    Γ.caps n (a :: C) = Γ.capsAtom n a ++ Γ.caps n C := by
  simp [Ctx.caps]

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
            cases a with
            | var x => cases x
            | cvar κ => cases κ
            | name x ℓ => cases x
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom 0 a).Subset ((Ctx.cons Γ b).capsAtom 1 a) := by
            intro a
            cases a with
            | var y =>
                cases y with
                | here => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | name x ℓ =>
                intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | consC Γ b ih =>
          have hat : ∀ a,
              ((Ctx.consC Γ b).capsAtom 0 a).Subset ((Ctx.consC Γ b).capsAtom 1 a) := by
            intro a
            cases a with
            | var y =>
                cases y with
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | here =>
                    cases b with
                    | root => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | star => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | name x ℓ =>
                intro c hc; rw [Ctx.capsAtom_name_zero] at hc; simp at hc
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
  | succ n ihn =>
      intro s Γ
      induction Γ with
      | nil =>
          have hat : ∀ a : CapAtom [],
              (Ctx.nil.capsAtom (n + 1) a).Subset (Ctx.nil.capsAtom (n + 1 + 1) a) := by
            intro a
            cases a with
            | var x => cases x
            | cvar κ => cases κ
            | name x ℓ => cases x
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom (n + 1) a).Subset
                ((Ctx.cons Γ b).capsAtom (n + 1 + 1) a) := by
            intro a
            cases a with
            | var y =>
                cases y with
                | here => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
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
            cases a with
            | var y =>
                cases y with
                | there y => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
            | cvar κ =>
                cases κ with
                | here =>
                    cases b with
                    | root => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | star => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                | there κ => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.1 _)
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
        cases a <;> simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
          CaptureSet.rename, Ctx.capsAtom]
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
        cases a with
        | var y =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | cvar κ =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
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
        cases a <;> simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
          CaptureSet.rename, Ctx.capsAtom]
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
        cases a with
        | var y =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
        | cvar κ =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename, Ctx.capsAtom]
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

theorem Ctx.capsBound_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.cons Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
  | upper C => exact Ctx.caps_weaken Γ b n C
  | inst C => exact Ctx.caps_weaken Γ b n C

theorem Ctx.capsBound_weakenC (Γ : Ctx s) (b : CapBound s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.consC Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
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

/-! ### Roots and subcapturing -/

/-- The roots of a capture set at a given fuel.  In this stage `roots` is
`caps`; the compiler's line redefines it as `expand ∘ caps`. -/
def Ctx.roots (Γ : Ctx s) (n : Nat) (C : CaptureSet s) : CaptureSet s := Γ.caps n C

@[simp] theorem Ctx.roots_eq_caps (Γ : Ctx s) (n : Nat) (C : CaptureSet s) :
    Γ.roots n C = Γ.caps n C := rfl

/-- `a` is a root of `C`: `C` resolves to `a` at some fuel.  Resolution is
monotone in the fuel, so this is the least solution of the resolution
equations, in which a cyclic chain of capture names contributes nothing. -/
def Ctx.Root (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) : Prop :=
  ∃ n : Nat, a ∈ Γ.roots n C

theorem Ctx.Root.of_mem_caps {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {n : Nat}
    (h : a ∈ Γ.caps n C) : Γ.Root a C := ⟨n, h⟩

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
    CapLe Γ C D := fun _ hr => hr.elim fun n hn => ⟨n, Ctx.caps_subset h _ hn⟩

theorem CapLe.union {Γ : Ctx s} {C D E : CaptureSet s}
    (h₁ : CapLe Γ C E) (h₂ : CapLe Γ D E) : CapLe Γ (C ∪ D) E := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_caps, CaptureSet.union_def, Ctx.caps_append] at ha
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
  rw [Ctx.roots_eq_caps, Ctx.caps_weaken] at ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨m, hm⟩ := h c ⟨n, hc⟩
  refine ⟨m, ?_⟩
  rw [Ctx.roots_eq_caps, Ctx.caps_weaken]
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map]
  exact ⟨c, hm, rfl⟩

theorem CapLe.weakenC {Γ : Ctx s} {C D : CaptureSet s} (b : CapBound s)
    (h : CapLe Γ C D) : CapLe (Ctx.consC Γ b) C.weaken D.weaken := by
  rintro a ⟨n, ha⟩
  rw [Ctx.roots_eq_caps, Ctx.caps_weakenC] at ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨m, hm⟩ := h c ⟨n, hc⟩
  refine ⟨m, ?_⟩
  rw [Ctx.roots_eq_caps, Ctx.caps_weakenC]
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
    rw [Ctx.roots_eq_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil] at hn
    cases n with
    | zero => rw [Ctx.capsAtom_name_zero] at hn; simp at hn
    | succ n => rw [Ctx.capsAtom_name_some h] at hn; exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [Ctx.roots_eq_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil,
      Ctx.capsAtom_name_some h]
    exact hn

/-- A capture name with no definition has no roots. -/
theorem Ctx.Root_name_none {Γ : Ctx s} {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefC x ℓ = none) (a : CapAtom s) : ¬ Γ.Root a [CapAtom.name x ℓ] := by
  rintro ⟨n, hn⟩
  rw [Ctx.roots_eq_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil] at hn
  cases n with
  | zero => rw [Ctx.capsAtom_name_zero] at hn; simp at hn
  | succ n => rw [Ctx.capsAtom_name_none h] at hn; simp at hn

/-! ### Item 6 of the canonical-forms theorem

`cap_canon`, the statement that closed capture evidence includes roots, no
longer fits here: `CapCo.HasType` is now mutual with atom typing, so `capvar`
needs item 7 of the theorem and `member` needs the view of an atom.  The
statement moves, unchanged, into the mutual induction of `CanonicalForms.lean`
(plan-5c A1.6); the four constructors it had in A0 are still discharged by
`CapLe.refl`, `CapLe.trans`, `CapLe.of_subset` and `CapLe.union`, and `defC`
by `Ctx.Root_name` above. -/

end FCdot

end CapturesCC
