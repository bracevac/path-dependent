import Coercions.FCdot.Normalizer
import Coercions.FCdot.Typing
import Coercions.FCdot.TypingRename

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

@[simp] theorem Ctx.next_top (Γ : Ctx s) : Γ.next (⊤ : Ty s) = none := rfl

theorem Ctx.next_nonSel {Γ : Ctx s} {T : Ty s} (h : ∀ x ℓ, T ≠ .sel x ℓ) :
    Γ.next T = none := by
  cases T with
  | sel x ℓ => exact absurd rfl (h x ℓ)
  | bot => rfl
  | pi => rfl
  | obj => rfl

/-! ## Basic resolution equations -/

/-- A settled type resolves to itself, with any fuel. -/
theorem Ctx.resolveFuel_settled (Γ : Ctx s) {T : Ty s} (h : Γ.next T = none) :
    ∀ n : Nat, Γ.resolveFuel n T = T
  | 0 => by simp [Ctx.resolveFuel, h]
  | _ + 1 => by simp [Ctx.resolveFuel, h]

theorem Ctx.resolveFuel_nonSel (Γ : Ctx s) (n : Nat) {T : Ty s}
    (h : ∀ x ℓ, T ≠ .sel x ℓ) : Γ.resolveFuel n T = T :=
  Γ.resolveFuel_settled (Ctx.next_nonSel h) n

theorem Ctx.resolve_nonSel (Γ : Ctx s) {T : Ty s} (h : ∀ x ℓ, T ≠ .sel x ℓ) :
    Γ.resolve T = T := Γ.resolveFuel_nonSel _ h

@[simp] theorem Ctx.resolve_top (Γ : Ctx s) : Γ.resolve (.top : Ty s) = .top :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_bot (Γ : Ctx s) : Γ.resolve (.bot : Ty s) = .bot :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_pi (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) :
    Γ.resolve (.pi S T) = .pi S T :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_obj (Γ : Ctx s) (Tel : Telescope (s,x)) :
    Γ.resolve (.obj Tel) = .obj Tel :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

theorem Ctx.resolveFuel_sel_none (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolveFuel n (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_settled (by simp [h]) n

theorem Ctx.resolve_sel_none (Γ : Ctx s) {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDef x ℓ = none) : Γ.resolve (.sel x ℓ) = .sel x ℓ :=
  Γ.resolveFuel_sel_none _ h

theorem Ctx.resolveFuel_sel_some (Γ : Ctx s) (n : Nat) {x : BVar s .var} {ℓ : Label}
    {W : Ty s} (h : Γ.lookupDef x ℓ = some W) :
    Γ.resolveFuel (n + 1) (.sel x ℓ) = Γ.resolveFuel n W := by
  simp [Ctx.resolveFuel, h]

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

/-! ## Defined names of a context -/

theorem Ctx.defPairs_cons_transparent (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Fs : List Label) :
    (Ctx.cons Γ (.transparent T W Fs)).defPairs =
      Γ.defPairs.map (fun p => (BVar.there p.1, p.2)) ++
        W.labels.map (fun ℓ => (BVar.here, ℓ)) := rfl

theorem Ctx.defPairs_cons_opaque (Γ : Ctx s) (T : Ty s) :
    (Ctx.cons Γ (.opaque T)).defPairs =
      Γ.defPairs.map (fun p => (BVar.there p.1, p.2)) := by
  simp [Ctx.defPairs]

/-- A name with a definition is one of the context's defined names, unless its
definition is the vacuous witness `⊤`. -/
theorem Ctx.lookupDef_defPairs : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var) (ℓ : Label)
    (W : Ty s), Γ.lookupDef x ℓ = some W → (x, ℓ) ∈ Γ.defPairs ∨ W = ⊤
  | _, .cons Γ (.transparent T W₀ Fs), .here, ℓ, W, h => by
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
theorem Ctx.chain_mem_defPairs (Γ : Ctx s) {T : Ty s} {n : Nat}
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
          | sel y ℓ =>
              have hlk : Γ.lookupDef y ℓ = some W := by simpa using hnv
              rcases Ctx.lookupDef_defPairs Γ y ℓ W hlk with hmem | htop
              · exact List.mem_map_of_mem
                  (f := fun p => some ((p.1 : BVar s .var) ∙ p.2)) hmem
              · exact absurd htop hWne

/-- A repeated name makes the chain periodic from the first occurrence on. -/
theorem Ctx.chain_periodic (Γ : Ctx s) {T : Ty s} {i j : Nat} (hij : i ≤ j)
    (h : Γ.chain T i = Γ.chain T j) :
    ∀ m, i ≤ m → Γ.chain T (m + (j - i)) = Γ.chain T m := by
  intro m him
  rw [show m + (j - i) = j + (m - i) by omega, Ctx.chain_add, ← h, ← Ctx.chain_add,
    show i + (m - i) = m by omega]

/-- Once the fuel is at least the number of defined names, one more unit changes
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

/-- Any fuel beyond the number of defined names computes `Ctx.resolve`. -/
theorem Ctx.resolveFuel_stable {Γ : Ctx s} {n : Nat} (hn : Γ.defPairs.length ≤ n) (T : Ty s) :
    Γ.resolveFuel n T = Γ.resolve T := by
  rw [Ctx.resolve,
    Ctx.resolveFuel_eq_of_le hn (m := n + Γ.defPairs.length + 1) (by omega) T,
    Ctx.resolveFuel_eq_of_le (n := Γ.defPairs.length + 1) (by omega)
      (m := n + Γ.defPairs.length + 1) (by omega) T]

/-! ## Resolution -/

/-- Resolution commutes with one unfolding step; no side condition on the
context is needed, a cyclic chain of aliases resolving to `⊤` on both sides. -/
theorem Ctx.resolve_sel_some {Γ : Ctx s} {x : BVar s .var} {ℓ : Label} {W : Ty s}
    (h : Γ.lookupDef x ℓ = some W) : Γ.resolve (.sel x ℓ) = Γ.resolve W := by
  rw [Ctx.resolve, Γ.resolveFuel_sel_some Γ.defPairs.length h]
  exact Ctx.resolveFuel_stable (Nat.le_refl _) W

/-- The result of resolution is settled: a shape, or a name without a definition. -/
theorem Ctx.resolve_settled (Γ : Ctx s) (T : Ty s) : Γ.next (Γ.resolve T) = none := by
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
theorem Ctx.resolve_resolve {Γ : Ctx s} (T : Ty s) :
    Γ.resolve (Γ.resolve T) = Γ.resolve T :=
  Γ.resolveFuel_settled (Γ.resolve_settled T) _

end FCdot
