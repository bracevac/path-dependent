import Coercions.Separation.FCdot.Normalizer
import Coercions.Separation.FCdot.Typing
import Coercions.Separation.FCdot.TypingRename
import Coercions.Separation.FCdot.Levels

namespace Separation

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
  | cell => rfl
  | reader => rfl

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

@[simp] theorem Ctx.resolve_cell (Γ : Ctx s) (T : Ty s) :
    Γ.resolve (.cell T) = .cell T :=
  Γ.resolve_nonSel (by intro x ℓ h; cases h)

@[simp] theorem Ctx.resolve_reader (Γ : Ctx s) (T : Ty s) :
    Γ.resolve (.reader T) = .reader T :=
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

theorem Ctx.defPairs_cons_formal (Γ : Ctx s) (T : Ty s) :
    (Ctx.cons Γ (.formal T)).defPairs =
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
            | formal T' =>
                rw [Ctx.defPairs_cons_formal]
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
          | cell => simp [Ctx.next] at hnv
          | reader => simp [Ctx.next] at hnv
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
it stands for itself.  A moded atom carries its mode along through the meet
`CapAtom.withMode`: the mode is not read here, it is dropped by
`Ctx.expandAtom` and kept by `Ctx.expandAtomM`. -/
def Ctx.capsAtom : (Γ : Ctx s) → Nat → CapAtom s → CaptureSet s
  | .cons Γ b, n, .var .here => (Γ.caps n b.ty.captureSet).weaken
  | .cons Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC Γ _, n, .var (.there y) => (Γ.capsAtom n (.var y)).weaken
  | .consC _ .root, _, .cvar .here => [.cvar .here]
  | .consC _ .star, _, .cvar .here => [.cvar .here]
  | .consC Γ (.upper C), n, .cvar .here => (Γ.caps n C).weaken
  | .consC Γ (.inst C), n, .cvar .here => (Γ.caps n C).weaken
  | .consC _ (.loc _ _), _, .cvar .here => [.cvar .here]
  | .consC _ (.param _), _, .cvar .here => [.cvar .here]
  | .consC Γ (.own _ W), n, .cvar .here => (Γ.caps n W).weaken
  | .cons Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | .consC Γ _, n, .cvar (.there κ) => (Γ.capsAtom n (.cvar κ)).weaken
  | _, _, .top => [.top]
  | _, 0, .name _ _ => []
  | Γ, n + 1, .name x ℓ =>
      match Γ.lookupDefC x ℓ with
      | some C => Γ.caps n C
      | none => []
  | Γ, n, .mode m a =>
      if m = .consume ∧ a.base.isTermB = true then Γ.capsAtom n a
      else (Γ.capsAtom n a).map (CapAtom.withMode m)
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

/-- The meet carries a subset to a subset. -/
theorem CaptureSet.Subset.mapMode {C D : CaptureSet s} (h : C.Subset D) (m : Mode) :
    (C.map (CapAtom.withMode m)).Subset (D.map (CapAtom.withMode m)) := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact List.mem_map_of_mem (h b hb)

/-- What the mode clause of resolution does to the resolution `L` of the atom
under the wrapper: the mode rides along through the meet, except that
`consume` on a term binder or a capture name raises nothing (plan-5h
decision 39). -/
def CaptureSet.modeWrap (m : Mode) (a : CapAtom s) (L : CaptureSet s) : CaptureSet s :=
  if m = .consume ∧ a.base.isTermB = true then L else L.map (CapAtom.withMode m)

/-- The mode clause of resolution. -/
@[simp] theorem Ctx.capsAtom_mode (Γ : Ctx s) (n : Nat) (m : Mode) (a : CapAtom s) :
    Γ.capsAtom n (.mode m a) = CaptureSet.modeWrap m a (Γ.capsAtom n a) := by
  cases Γ <;> cases n <;> simp [Ctx.capsAtom, CaptureSet.modeWrap]

/-- A member of a wrapped resolution is a member, or a member under the meet. -/
theorem CaptureSet.mem_modeWrap {m : Mode} {a c : CapAtom s} {L : CaptureSet s}
    (h : c ∈ CaptureSet.modeWrap m a L) : c ∈ L ∨ c ∈ L.map (CapAtom.withMode m) := by
  unfold CaptureSet.modeWrap at h
  split at h
  · exact Or.inl h
  · exact Or.inr h

/-- The wrapper carries a subset to a subset. -/
theorem CaptureSet.Subset.modeWrap {C D : CaptureSet s} (h : C.Subset D) (m : Mode)
    (a : CapAtom s) : (CaptureSet.modeWrap m a C).Subset (CaptureSet.modeWrap m a D) := by
  unfold CaptureSet.modeWrap
  split
  · exact h
  · exact CaptureSet.Subset.mapMode h m

/-- The wrapper changes no base. -/
theorem CaptureSet.map_base_modeWrap (m : Mode) (a : CapAtom s) (L : CaptureSet s) :
    (CaptureSet.modeWrap m a L).map CapAtom.base = L.map CapAtom.base := by
  unfold CaptureSet.modeWrap
  split
  · rfl
  · rw [List.map_map]; exact List.map_congr_left (fun b _ => CapAtom.base_withMode m b)

/-- A renaming commutes with the wrapper. -/
theorem CaptureSet.modeWrap_rename (m : Mode) (a : CapAtom s1) (L : CaptureSet s1)
    (ρ : Rename s1 s2) :
    (CaptureSet.modeWrap m a L).rename ρ = CaptureSet.modeWrap m (a.rename ρ) (L.rename ρ) := by
  unfold CaptureSet.modeWrap
  rw [CapAtom.base_rename, CapAtom.isTermB_rename]
  split
  · rfl
  · simp only [CaptureSet.rename, List.map_map, Function.comp_def]
    exact List.map_congr_left (fun a _ => CapAtom.withMode_rename m a _)

theorem CaptureSet.weaken_modeWrap (m : Mode) (a : CapAtom s) (L : CaptureSet s) :
    CaptureSet.weaken (k := k) (CaptureSet.modeWrap m a L)
      = CaptureSet.modeWrap m (CapAtom.weaken (k := k) a) (CaptureSet.weaken (k := k) L) :=
  CaptureSet.modeWrap_rename m a L _

/-- Weakening is structural on the mode wrapper. -/
theorem CapAtom.weaken_mode (m : Mode) (a : CapAtom s) :
    CapAtom.weaken (k := k) (.mode m a) = .mode m a.weaken := rfl

/-- Weakening commutes with the meet, set-wise. -/
theorem CaptureSet.weaken_map_withMode (m : Mode) (C : CaptureSet s) :
    CaptureSet.weaken (k := k) (C.map (CapAtom.withMode m))
      = (CaptureSet.weaken (k := k) C).map (CapAtom.withMode m) := by
  simp only [CaptureSet.weaken, CaptureSet.rename, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun a _ => CapAtom.withMode_rename m a _)

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
            | mode m a ih =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap ih m a
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom 0 a).Subset ((Ctx.cons Γ b).capsAtom 1 a) := by
            intro a
            induction a with
            | mode m a iha =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap iha m a
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
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | consC Γ b ih =>
          have hat : ∀ a,
              ((Ctx.consC Γ b).capsAtom 0 a).Subset ((Ctx.consC Γ b).capsAtom 1 a) := by
            intro a
            induction a with
            | mode m a iha =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap iha m a
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
                    | loc _ _ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | param _ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | own _ C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
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
            induction a with
            | top => intro c hc; simpa using hc
            | var x => cases x
            | cvar κ => cases κ
            | name x ℓ => cases x
            | mode m a ih =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap ih m a
          exact ⟨hat, Ctx.caps_of_capsAtom hat⟩
      | cons Γ b ih =>
          have hat : ∀ a,
              ((Ctx.cons Γ b).capsAtom (n + 1) a).Subset
                ((Ctx.cons Γ b).capsAtom (n + 1 + 1) a) := by
            intro a
            induction a with
            | mode m a iha =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap iha m a
            | top => intro c hc; simpa using hc
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
            induction a with
            | mode m a iha =>
                simp only [Ctx.capsAtom_mode]
                exact CaptureSet.Subset.modeWrap iha m a
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
                    | loc _ _ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | param _ => intro c hc; simp only [Ctx.capsAtom] at hc ⊢; exact hc
                    | upper C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | inst C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
                    | own _ C => simp only [Ctx.capsAtom]; exact CaptureSet.Subset.weaken (ih.2 _)
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
        induction a with
        | mode m a iha =>
            rw [CapAtom.weaken_mode, Ctx.capsAtom_mode, Ctx.capsAtom_mode, iha,
              CaptureSet.weaken_modeWrap]
        | _ => simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
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
        induction a with
        | mode m a iha =>
            rw [CapAtom.weaken_mode, Ctx.capsAtom_mode, Ctx.capsAtom_mode, iha,
              CaptureSet.weaken_modeWrap]
        | top =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename]
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
        induction a with
        | mode m a iha =>
            rw [CapAtom.weaken_mode, Ctx.capsAtom_mode, Ctx.capsAtom_mode, iha,
              CaptureSet.weaken_modeWrap]
        | _ => simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
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
        induction a with
        | mode m a iha =>
            rw [CapAtom.weaken_mode, Ctx.capsAtom_mode, Ctx.capsAtom_mode, iha,
              CaptureSet.weaken_modeWrap]
        | top =>
            simp [CapAtom.weaken, CapAtom.rename, CaptureSet.weaken,
              CaptureSet.rename]
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
  | .loc _ _ => [.cvar κ]
  | .param _ => [.cvar κ]
  | .own _ W => Γ.caps n W

theorem Ctx.capsBound_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.cons Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
  | loc _ _ => rfl
  | param _ => rfl
  | upper C => exact Ctx.caps_weaken Γ b n C
  | inst C => exact Ctx.caps_weaken Γ b n C
  | own _ C => exact Ctx.caps_weaken Γ b n C

theorem Ctx.capsBound_weakenC (Γ : Ctx s) (b : CapBound s) (n : Nat) (κ : BVar s .cap)
    (β : CapBound s) :
    (Ctx.consC Γ b).capsBound n (.there κ) β.weaken = (Γ.capsBound n κ β).weaken := by
  cases β with
  | root => rfl
  | star => rfl
  | loc _ _ => rfl
  | param _ => rfl
  | upper C => exact Ctx.caps_weakenC Γ b n C
  | inst C => exact Ctx.caps_weakenC Γ b n C
  | own _ C => exact Ctx.caps_weakenC Γ b n C

/-- The capture-binder clause: `caps_Γ {κ}` is `{κ}` when the bound of `κ` is
a root or `∗`, and `caps_Γ` of the bound otherwise. -/
theorem Ctx.capsAtom_cvar : ∀ {s : Sig} (Γ : Ctx s) (n : Nat) (κ : BVar s .cap),
    Γ.capsAtom n (.cvar κ) = Γ.capsBound n κ (Γ.lookupCap κ)
  | _, .consC Γ β, n, .here => by
      rw [Ctx.lookupCap_here]
      cases β with
      | root => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | star => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | loc _ _ => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | param _ => simp [Ctx.capsAtom, Ctx.capsBound, CapBound.weaken, CapBound.rename]
      | upper C => rw [Ctx.capsAtom]; exact (Ctx.caps_weakenC Γ _ n C).symm
      | inst C => rw [Ctx.capsAtom]; exact (Ctx.caps_weakenC Γ _ n C).symm
      | own _ C => rw [Ctx.capsAtom]; exact (Ctx.caps_weakenC Γ _ n C).symm
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
untouched.  The list of capture binders, `Ctx.capBinders`, is defined in
`Names.lean`, which the level rule's premise needs before typing. -/

/-- Filtering after a map is mapping after the transported filter. -/
theorem filter_of_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).filter p = (l.filter fun a => p (f a)).map f
  | [] => rfl
  | a :: l => by
      by_cases h : p (f a) = true <;>
        simp [h, filter_of_map f p l]

/-- Expansion of one atom.  A moded atom expands as its base: roots are mode
free, so expansion strips every mode, and the layers above it never see one.
A root opens into the universal root and every opaque binder at its level or
outside it.  Everything else stands for itself. -/
def Ctx.expandAtom (Γ : Ctx s) : CapAtom s → CaptureSet s
  | .mode _ a => Γ.expandAtom a
  | a =>
    if Γ.isRootB a then
      CapAtom.top :: (Γ.capBinders.filter fun κ =>
          (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) a).map CapAtom.cvar
    else [a]

/-- Expansion of a capture set. -/
def Ctx.expand (Γ : Ctx s) (C : CaptureSet s) : CaptureSet s := C.flatMap Γ.expandAtom

/-- Expansion strips a mode. -/
@[simp] theorem Ctx.expandAtom_mode (Γ : Ctx s) (m : Mode) (a : CapAtom s) :
    Γ.expandAtom (.mode m a) = Γ.expandAtom a := rfl

/-- Expansion reads only the base. -/
theorem Ctx.expandAtom_base_eq (Γ : Ctx s) : ∀ a : CapAtom s,
    Γ.expandAtom a.base = Γ.expandAtom a
  | .top | .var _ | .cvar _ | .name _ _ => rfl
  | .mode _ a => Γ.expandAtom_base_eq a

/-- So the meet changes no expansion. -/
@[simp] theorem Ctx.expandAtom_withMode (Γ : Ctx s) (m : Mode) (a : CapAtom s) :
    Γ.expandAtom (CapAtom.withMode m a) = Γ.expandAtom a := by
  cases m with
  | ro => exact Γ.expandAtom_base_eq a
  | consume =>
      simp only [CapAtom.withMode]
      split
      · rfl
      · exact Γ.expandAtom_base_eq a

/-- The old body of expansion, at every atom that is its own base. -/
theorem Ctx.expandAtom_of_not_mode {Γ : Ctx s} : ∀ {a : CapAtom s}, a.base = a →
    Γ.expandAtom a = if Γ.isRootB a then
        CapAtom.top :: (Γ.capBinders.filter fun κ =>
          (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) a).map CapAtom.cvar
      else [a]
  | .top, _ => rfl
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .mode m a, h => absurd h (CapAtom.base_ne_mode a m a)

/-- A root is its own base: a moded atom is never a root. -/
theorem Ctx.base_of_isRootB {Γ : Ctx s} : ∀ {r : CapAtom s}, Γ.isRootB r = true → r.base = r
  | .top, _ => rfl
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .mode _ _, h => by simp [Ctx.isRootB] at h

theorem Ctx.expandAtom_of_root {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) :
    Γ.expandAtom r = CapAtom.top :: (Γ.capBinders.filter fun κ =>
        (Γ.lookupCap κ).opaque && Γ.lvlLeB (.cvar κ) r).map CapAtom.cvar := by
  rw [Ctx.expandAtom_of_not_mode (Ctx.base_of_isRootB hr), if_pos hr]

/-- Restated with `a.base = a` (plan-5f K0.8): a moded atom is never a root and
expands as its base, so the old statement is false at `ro ⊤ᶜ`.  Every atom of
a base program is its own base. -/
theorem Ctx.expandAtom_of_not_root {Γ : Ctx s} {a : CapAtom s} (ha : Γ.isRootB a = false)
    (hb : a.base = a) : Γ.expandAtom a = [a] := by
  rw [Ctx.expandAtom_of_not_mode hb, if_neg (by simp [ha])]

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

/-- An atom that is its own base is in its own expansion: `⊤ᶜ` heads its
own, a root is its own level, and everything else expands to its singleton. -/
theorem Ctx.mem_expandAtom_self_of_base {Γ : Ctx s} {a : CapAtom s} (hb : a.base = a) :
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
      | mode m a => simp [Ctx.isRootB] at h
      | cvar κ =>
          have hroot : (Γ.lookupCap κ).isRoot = true := by simpa [Ctx.isRootB] using h
          exact Ctx.cvar_mem_expandAtom h (CapBound.opaque_of_isRoot hroot)
            (Ctx.LvlLe.refl_of_root h)

/-- The base of an atom is in its expansion.  Restated with `base`
(plan-5f K0.8): on an atom of a base program `a.base = a`. -/
theorem Ctx.mem_expandAtom_self (Γ : Ctx s) (a : CapAtom s) : a.base ∈ Γ.expandAtom a := by
  rw [← Γ.expandAtom_base_eq a]
  exact Ctx.mem_expandAtom_self_of_base (CapAtom.base_base a)

/-- Expansion produces mode-free atoms: the three layers above
`Ctx.expandAtom` never see a mode. -/
theorem Ctx.base_of_mem_expandAtom {Γ : Ctx s} : ∀ {a b : CapAtom s},
    b ∈ Γ.expandAtom a → b.base = b
  | .mode _ a, _, h => Ctx.base_of_mem_expandAtom (a := a) h
  | .top, b, h | .var _, b, h | .cvar _, b, h | .name _ _, b, h => by
      rw [Ctx.expandAtom_of_not_mode rfl] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h
        · rfl
        · obtain ⟨κ, _, rfl⟩ := List.mem_map.mp h; rfl
      · rw [List.mem_singleton.mp h]; rfl

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

/-- A set is contained in its own expansion, by the bases of its atoms.
Restated with `base` (plan-5f K0.8). -/
theorem Ctx.subset_expand (Γ : Ctx s) (C : CaptureSet s) : ∀ a ∈ C, a.base ∈ Γ.expand C := by
  intro a ha
  exact Ctx.mem_expand.mpr ⟨a, ha, Γ.mem_expandAtom_self a⟩

/-- A set of non-roots that carries no mode is its own expansion.  The
premise `∀ a ∈ C, a.base = a` is new (plan-5f K0.8) and holds on every set of
a base program. -/
theorem Ctx.expand_eq_self {Γ : Ctx s} : ∀ {C : CaptureSet s},
    (∀ a ∈ C, Γ.isRootB a = false) → (∀ a ∈ C, a.base = a) → Γ.expand C = C
  | [], _, _ => by simp
  | a :: C, h, hb => by
      rw [Ctx.expand_cons,
        Ctx.expandAtom_of_not_root (h a (List.mem_cons_self ..)) (hb a (List.mem_cons_self ..)),
        Ctx.expand_eq_self (fun c hc => h c (List.mem_cons_of_mem a hc))
          (fun c hc => hb c (List.mem_cons_of_mem a hc))]
      rfl

/-- A set whose atoms all have a non-root base expands to their bases.  This
is the shape `Ctx.roots_eq_caps_of_rootFree` needs. -/
theorem Ctx.expand_eq_map_base {Γ : Ctx s} : ∀ {L : CaptureSet s},
    (∀ a ∈ L, Γ.isRootB a.base = false) → Γ.expand L = L.map CapAtom.base
  | [], _ => rfl
  | a :: L, h => by
      rw [Ctx.expand_cons, ← Γ.expandAtom_base_eq a,
        Ctx.expandAtom_of_not_root (h a (List.mem_cons_self ..)) (CapAtom.base_base a),
        Ctx.expand_eq_map_base (fun b hb => h b (List.mem_cons_of_mem a hb))]
      rfl

/-! ### Expansion and weakening

Appending a term binder is invisible to expansion.  Appending a capture
binder is invisible only when its bound is not opaque: a rigid binder
appended to a root-free context enlarges the expansion of `⊤ᶜ`, which is
what a store is forbidden to do. -/

theorem Ctx.expandAtom_weaken_of_base (Γ : Ctx s) (b : Binding s) {a : CapAtom s}
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

theorem Ctx.expandAtom_weaken (Γ : Ctx s) (b : Binding s) : ∀ (a : CapAtom s),
    (Γ.cons b).expandAtom a.weaken = (Γ.expandAtom a).weaken
  | .top => Ctx.expandAtom_weaken_of_base Γ b rfl
  | .var _ => Ctx.expandAtom_weaken_of_base Γ b rfl
  | .cvar _ => Ctx.expandAtom_weaken_of_base Γ b rfl
  | .name _ _ => Ctx.expandAtom_weaken_of_base Γ b rfl
  | .mode _ a => Ctx.expandAtom_weaken Γ b a

theorem Ctx.expandAtom_weakenC_of_base (Γ : Ctx s) (b : CapBound s) (hb : b.opaque = false)
    {a : CapAtom s} (hbase : a.base = a) :
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
  | .top => Ctx.expandAtom_weakenC_of_base Γ b hb rfl
  | .var _ => Ctx.expandAtom_weakenC_of_base Γ b hb rfl
  | .cvar _ => Ctx.expandAtom_weakenC_of_base Γ b hb rfl
  | .name _ _ => Ctx.expandAtom_weakenC_of_base Γ b hb rfl
  | .mode _ a => Ctx.expandAtom_weakenC Γ b hb a

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
the atom: resolution carries a mode along, and what sits under it is `⊤ᶜ` or
a capture binder whose bound is opaque, exactly as before. -/
abbrev Ctx.OpaqueAtom (Γ : Ctx s) (c : CapAtom s) : Prop :=
  c.base = .top ∨ ∃ κ, c.base = .cvar κ ∧ (Γ.lookupCap κ).opaque = true

/-- The expansion of an atom whose base resolution can produce is contained
in the expansion of any root it is at or outside of.  The form of
`Ctx.expandAtom_mono` that reads the base. -/
theorem Ctx.expandAtom_mono_base {Γ : Ctx s} {a r : CapAtom s} (hr : Γ.IsRoot r)
    (ha : Γ.OpaqueAtom a) (hle : Γ.LvlLe a r) : (Γ.expandAtom a).Subset (Γ.expandAtom r) := by
  rw [← Γ.expandAtom_base_eq a]
  refine Ctx.expandAtom_mono hr ?_ (Ctx.lvlLe_base_left.mp hle)
  rcases ha with h0 | ⟨κ, h0, hop⟩
  · exact Or.inl h0
  · exact Or.inr ⟨κ, h0, hop⟩

/-- The mode clause of the opacity lemma: the meet keeps the base. -/
theorem Ctx.opaqueAtom_mode {Γ : Ctx s} {L : CaptureSet s} {c : CapAtom s} {m : Mode}
    (hL : ∀ c₀ ∈ L, Γ.OpaqueAtom c₀) (hc : c ∈ L.map (CapAtom.withMode m)) :
    Γ.OpaqueAtom c := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  unfold Ctx.OpaqueAtom
  rw [CapAtom.base_withMode]
  exact hL d hd

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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
      | cons Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
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
                  | loc _ _ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | param _ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | upper C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | inst C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | own _ C =>
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
          | var x => cases x
          | cvar κ => cases κ
          | name x ℓ => cases x
          | top =>
              rw [Ctx.capsAtom_top] at hc
              exact Or.inl (by rw [List.mem_singleton.mp hc]; rfl)
      | cons Γ b ih =>
          intro a c hc
          induction a generalizing c with
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode] at hc
              rcases CaptureSet.mem_modeWrap hc with hc | hc
              · exact iha c hc
              · exact Ctx.opaqueAtom_mode (fun d hd => iha d hd) hc
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
                  | loc _ _ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | param _ =>
                      simp only [Ctx.capsAtom] at hc
                      exact Or.inr ⟨.here, by rw [List.mem_singleton.mp hc]; rfl, rfl⟩
                  | upper C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | inst C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
                  | own _ C =>
                      simp only [Ctx.capsAtom] at hc
                      exact Ctx.opaqueAtom_weakenC _ (Ctx.caps_opaque_of_atom ih _) hc
              | there κ₀ =>
                  simp only [Ctx.capsAtom] at hc
                  exact Ctx.opaqueAtom_weakenC b (fun _ => ih (.cvar κ₀) _) hc

/-- Resolution lands in opaque atoms.  The disjunction reads `a.base`
(plan-5f K0.8), which is `a` itself on every atom of a base program. -/
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

/-- A moded atom is at the level of its base, so the meet keeps the level. -/
theorem Ctx.lvlAtom_withMode (Γ : Ctx s) (m : Mode) (a : CapAtom s) :
    Γ.lvlAtom (CapAtom.withMode m a) = Γ.lvlAtom a := by
  rw [← Γ.lvlAtom_base (CapAtom.withMode m a), CapAtom.base_withMode, Γ.lvlAtom_base]

/-- The mode clause of the confinement lemma. -/
theorem Ctx.confined_mode {Γ : Ctx s} {L : CaptureSet s} {r : CapAtom s} {m : Mode}
    (h : Γ.Confined L r) : Γ.Confined (L.map (CapAtom.withMode m)) r := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have := h d hd
  unfold Ctx.LvlLe Ctx.lvlLeB at this ⊢
  rw [Γ.lvlAtom_withMode]
  exact this

theorem Ctx.confined_modeWrap {Γ : Ctx s} {L : CaptureSet s} {r : CapAtom s} {m : Mode}
    {a : CapAtom s} (h : Γ.Confined L r) : Γ.Confined (CaptureSet.modeWrap m a L) r := by
  unfold CaptureSet.modeWrap
  split
  · exact h
  · exact Ctx.confined_mode h

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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
                  | loc _ _ =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | param _ =>
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
                  | own k C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.own k C) rfl ih C r h
              | there κ₀ =>
                  simp only [Ctx.capsAtom]
                  exact Ctx.capsAtom_confined_thereC b ih (.cvar κ₀) r h
  | succ n ihn =>
      intro s Γ
      induction Γ with
      | nil =>
          intro a r h
          induction a with
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
          | mode m a iha =>
              rw [Ctx.capsAtom_mode]
              exact Ctx.confined_modeWrap (iha h)
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
                  | loc _ _ =>
                      intro c hc
                      simp only [Ctx.capsAtom] at hc
                      rw [List.mem_singleton.mp hc]
                      exact h
                  | param _ =>
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
                  | own k C =>
                      simp only [Ctx.capsAtom]
                      exact Ctx.capsAtom_confined_hereC (.own k C) rfl ih C r h
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

/-- Resolution lands in the roots, by the bases of its atoms.  Restated with
`base` (plan-5f K0.8): on a set of a base program `base` is the identity. -/
theorem Ctx.caps_subset_roots (Γ : Ctx s) (n : Nat) (C : CaptureSet s) :
    ∀ a ∈ Γ.caps n C, a.base ∈ Γ.roots n C := Γ.subset_expand _

/-- Nothing outside a scope sees the change.  On a root-free context whose
resolution does not mention `⊤ᶜ`, `roots` is `caps`, so every statement about
roots on the platform prefix and on a store context means today what it meant
before. -/
theorem Ctx.roots_eq_caps_of_rootFree {Γ : Ctx s} {n : Nat} {C : CaptureSet s}
    (h : Γ.root? = none) (hC : CapAtom.top ∉ (Γ.caps n C).map CapAtom.base) :
    Γ.roots n C = (Γ.caps n C).map CapAtom.base := by
  rw [Ctx.roots_eq_expand_caps]
  refine Ctx.expand_eq_map_base ?_
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

/-- Restated with `base` (plan-5f K0.8). -/
theorem Ctx.Root.of_mem_caps {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {n : Nat}
    (h : a ∈ Γ.caps n C) : Γ.Root a.base C := ⟨n, Γ.caps_subset_roots n C a h⟩

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
        | loc _ _ => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | own _ _ => rw [hb] at h'; simp [CapBound.instSet?] at h'
        | param _ => rw [hb] at h'; simp [CapBound.instSet?] at h'
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
  | mode _ _ => simp [Ctx.InstOf, Ctx.instSet?] at h

/-- An heir resolves to what it owns. -/
theorem Ctx.caps_own {Γ : Ctx s} {a : CapAtom s} {W : CaptureSet s} (hO : Γ.OwnOf a W)
    (n : Nat) : Γ.caps n [a] = Γ.caps n W := by
  cases a with
  | cvar κ =>
      have h' : (Γ.lookupCap κ).ownSet? = some W := hO
      rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_cvar]
      cases hb : Γ.lookupCap κ with
      | own k W₀ =>
          rw [hb] at h'
          simp only [CapBound.ownSet?, Option.some.injEq] at h'
          subst h'
          rfl
      | root | star | upper _ | inst _ | loc _ _ | param _ =>
          rw [hb] at h'; simp [CapBound.ownSet?] at h'
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.OwnOf, Ctx.ownSet?] at hO

/-- An heir has exactly the roots of what it owns, at every fuel.  This is
what `CapCo.HasType.ownLe` needs. -/
theorem Ctx.Root_own {Γ : Ctx s} {a : CapAtom s} {W : CaptureSet s} (hO : Γ.OwnOf a W) :
    RootsEq Γ [a] W := fun b => by
  simp only [Ctx.Root, Ctx.roots_eq_expand_caps, Ctx.caps_own hO]

/-- A capture name with no definition has no roots. -/
theorem Ctx.Root_name_none {Γ : Ctx s} {x : BVar s .var} {ℓ : Label}
    (h : Γ.lookupDefC x ℓ = none) (a : CapAtom s) : ¬ Γ.Root a [CapAtom.name x ℓ] := by
  rintro ⟨n, hn⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil] at hn
  cases n with
  | zero => rw [Ctx.capsAtom_name_zero, Ctx.expand_nil] at hn; simp at hn
  | succ n => rw [Ctx.capsAtom_name_none h, Ctx.expand_nil] at hn; simp at hn

/-! ### Modes: roots read no mode, and the second expansion keeps them

Resolution carries a mode through the meet and `Ctx.expandAtom` strips it, so
the roots of a moded set are the roots of its bases.  The moded roots come
from a second expansion over the same resolution, `Ctx.expandAtomM`, which
keeps every mode.  `CapLeM` and `Ctx.KindRo` read the moded roots.  The
read-only lemmas are `capsM_fix_ro`, `expandM_fix_ro` and `kind_canon_fix` of
the refutation's scratch module (`Scratch_SepModes.lean.txt:209-242`), with the
meet as the wrapper. -/

/-- The meet changes no expansion, set-wise. -/
theorem Ctx.expand_map_withMode (Γ : Ctx s) (m : Mode) : ∀ L : CaptureSet s,
    Γ.expand (L.map (CapAtom.withMode m)) = Γ.expand L
  | [] => rfl
  | a :: L => by
      rw [List.map_cons, Ctx.expand_cons, Ctx.expand_cons, Ctx.expandAtom_withMode,
        Ctx.expand_map_withMode Γ m L]

/-- Nor does the wrapper of the mode clause. -/
theorem Ctx.expand_modeWrap (Γ : Ctx s) (m : Mode) (a : CapAtom s) (L : CaptureSet s) :
    Γ.expand (CaptureSet.modeWrap m a L) = Γ.expand L := by
  unfold CaptureSet.modeWrap
  split
  · rfl
  · exact Γ.expand_map_withMode m L

/-- Resolving and expanding reads only the base of an atom. -/
theorem Ctx.expand_capsAtom_base (Γ : Ctx s) (n : Nat) : ∀ a : CapAtom s,
    Γ.expand (Γ.capsAtom n a.base) = Γ.expand (Γ.capsAtom n a)
  | .top | .var _ | .cvar _ | .name _ _ => rfl
  | .mode m a => by
      rw [Ctx.capsAtom_mode, Ctx.expand_modeWrap]
      exact Ctx.expand_capsAtom_base Γ n a

/-- So the meet changes no root of one atom. -/
theorem Ctx.expand_capsAtom_withMode (Γ : Ctx s) (n : Nat) (m : Mode) (a : CapAtom s) :
    Γ.expand (Γ.capsAtom n (CapAtom.withMode m a)) = Γ.expand (Γ.capsAtom n a) := by
  rw [← Γ.expand_capsAtom_base n (CapAtom.withMode m a), CapAtom.base_withMode,
    Γ.expand_capsAtom_base n a]

/-- The roots of a singleton are the roots of its base. -/
theorem Ctx.roots_base (Γ : Ctx s) (n : Nat) (a : CapAtom s) :
    Γ.roots n [a.base] = Γ.roots n [a] := by
  simp only [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil]
  exact Γ.expand_capsAtom_base n a

/-- The meet changes no root, set-wise. -/
theorem Ctx.roots_map_withMode (Γ : Ctx s) (n : Nat) (m : Mode) : ∀ C : CaptureSet s,
    Γ.roots n (C.map (CapAtom.withMode m)) = Γ.roots n C
  | [] => rfl
  | a :: C => by
      have ih := Ctx.roots_map_withMode Γ n m C
      simp only [Ctx.roots_eq_expand_caps] at ih ⊢
      rw [List.map_cons, Ctx.caps_cons, Ctx.caps_cons, Ctx.expand_append, Ctx.expand_append,
        Γ.expand_capsAtom_withMode, ih]

/-- The read-only view of a set has the roots of the set. -/
theorem Ctx.rootsEq_ro (Γ : Ctx s) (C : CaptureSet s) : RootsEq Γ C.ro C := fun a =>
  ⟨fun ⟨n, h⟩ => ⟨n, by rwa [CaptureSet.ro, Ctx.roots_map_withMode] at h⟩,
   fun ⟨n, h⟩ => ⟨n, by rwa [CaptureSet.ro, Ctx.roots_map_withMode]⟩⟩

/-- An atom at any effective mode has the roots of its base. -/
theorem Ctx.roots_atMode (Γ : Ctx s) (n : Nat) (a : CapAtom s) (m : EMode) :
    Γ.roots n [a.atMode m] = Γ.roots n [a.base] := by
  rw [← Γ.roots_base n (a.atMode m), CapAtom.base_atMode]

theorem Ctx.rootsEq_atMode (Γ : Ctx s) (a : CapAtom s) (m m' : EMode) :
    RootsEq Γ [a.atMode m] [a.atMode m'] := fun r =>
  ⟨fun ⟨n, h⟩ => ⟨n, by rw [Ctx.roots_atMode] at h ⊢; exact h⟩,
   fun ⟨n, h⟩ => ⟨n, by rw [Ctx.roots_atMode] at h ⊢; exact h⟩⟩

/-- Expansion that keeps modes: the second expansion, for the moded roots. -/
def Ctx.expandAtomM (Γ : Ctx s) : CapAtom s → CaptureSet s
  | .mode m a => (Γ.expandAtomM a).map (CapAtom.withMode m)
  | a => Γ.expandAtom a

/-- The moded roots of a set: resolution followed by the second expansion. -/
def Ctx.rootsM (Γ : Ctx s) (n : Nat) (C : CaptureSet s) : CaptureSet s :=
  (Γ.caps n C).flatMap Γ.expandAtomM

/-- `a` is a moded root of `C`. -/
def Ctx.RootM (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) : Prop := ∃ n, a ∈ Γ.rootsM n C

/-- Subcapturing with modes: every moded root of `C` is dominated by a moded
root of `D` at the same base. -/
def CapLeM (Γ : Ctx s) (C D : CaptureSet s) : Prop :=
  ∀ a, Γ.RootM a C → ∃ b, Γ.RootM b D ∧ a.base = b.base ∧ a.effMode ≤ b.effMode

/-- A set is read-only when every moded root is. -/
def Ctx.KindRo (Γ : Ctx s) (C : CaptureSet s) : Prop := ∀ a, Γ.RootM a C → a.effMode = .ro

@[simp] theorem Ctx.expandAtomM_mode (Γ : Ctx s) (m : Mode) (a : CapAtom s) :
    Γ.expandAtomM (.mode m a) = (Γ.expandAtomM a).map (CapAtom.withMode m) := rfl

/-- Expansion produces mode-free atoms, so forgetting modes changes nothing. -/
theorem Ctx.map_base_expandAtom (Γ : Ctx s) (a : CapAtom s) :
    (Γ.expandAtom a).map CapAtom.base = Γ.expandAtom a :=
  (List.map_congr_left (fun _ hb => Ctx.base_of_mem_expandAtom hb)).trans (List.map_id _)

/-- Forgetting the modes of the second expansion gives the first. -/
theorem Ctx.map_base_expandAtomM (Γ : Ctx s) : ∀ a : CapAtom s,
    (Γ.expandAtomM a).map CapAtom.base = Γ.expandAtom a
  | .mode m a => by
      rw [Ctx.expandAtomM_mode, List.map_map, Ctx.expandAtom_mode,
        ← Ctx.map_base_expandAtomM Γ a]
      exact List.map_congr_left (fun b _ => CapAtom.base_withMode m b)
  | .top => Γ.map_base_expandAtom _
  | .var _ => Γ.map_base_expandAtom _
  | .cvar _ => Γ.map_base_expandAtom _
  | .name _ _ => Γ.map_base_expandAtom _

/-- The moded roots, with their modes forgotten, are the roots. -/
theorem Ctx.map_base_rootsM (Γ : Ctx s) (n : Nat) (C : CaptureSet s) :
    (Γ.rootsM n C).map CapAtom.base = Γ.roots n C := by
  simp only [Ctx.rootsM, Ctx.roots_eq_expand_caps, Ctx.expand, List.map_flatMap,
    Ctx.map_base_expandAtomM]

/-- A moded root has a root as its base. -/
theorem Ctx.RootM.root_base {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s}
    (h : Γ.RootM a C) : Γ.Root a.base C := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, Γ.map_base_rootsM n C ▸ List.mem_map_of_mem hn⟩

/-- And every root is the base of a moded root. -/
theorem Ctx.Root.exists_rootM {Γ : Ctx s} {r : CapAtom s} {C : CaptureSet s}
    (h : Γ.Root r C) : ∃ a, Γ.RootM a C ∧ a.base = r := by
  obtain ⟨n, hn⟩ := h
  rw [← Γ.map_base_rootsM n C] at hn
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
  exact ⟨a, ⟨n, ha⟩, rfl⟩

/-- Subcapturing with modes forgets to subcapturing. -/
theorem CapLeM.capLe {Γ : Ctx s} {C D : CaptureSet s} (h : CapLeM Γ C D) : CapLe Γ C D := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := hr.exists_rootM
  obtain ⟨b, hb, hab, -⟩ := h a ha
  rw [hab]
  exact hb.root_base

theorem CapLeM.refl (Γ : Ctx s) (C : CaptureSet s) : CapLeM Γ C C :=
  fun a ha => ⟨a, ha, rfl, Nat.le_refl _⟩

theorem CapLeM.trans {Γ : Ctx s} {C D E : CaptureSet s}
    (h₁ : CapLeM Γ C D) (h₂ : CapLeM Γ D E) : CapLeM Γ C E := by
  intro a ha
  obtain ⟨b, hb, hab, hm⟩ := h₁ a ha
  obtain ⟨c, hc, hbc, hm'⟩ := h₂ b hb
  exact ⟨c, hc, hab.trans hbc, Nat.le_trans hm hm'⟩

/-- The meet keeps a read-only atom read-only (`capsM_fix_ro` of the scratch
module): every atom resolution produces from a read-only atom is read-only. -/
theorem Ctx.capsAtom_ro (Γ : Ctx s) (n : Nat) :
    ∀ a : CapAtom s, a.effMode = .ro → ∀ x ∈ Γ.capsAtom n a, x.effMode = .ro
  | .mode .ro a, _, x, hx => by
      rw [Ctx.capsAtom_mode] at hx
      unfold CaptureSet.modeWrap at hx
      rw [if_neg (fun h => by cases h.1)] at hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact CapAtom.effMode_withMode_ro y
  | .mode .consume a, h, x, hx => by
      have ha : a.effMode = .ro := by
        cases hm : a.effMode <;> simp [CapAtom.effMode, hm] at h ⊢
      rw [Ctx.capsAtom_mode] at hx
      rcases CaptureSet.mem_modeWrap hx with hx | hx
      · exact Ctx.capsAtom_ro Γ n a ha x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact CapAtom.effMode_withMode_of_ro (Ctx.capsAtom_ro Γ n a ha y hy)
  | .top, h, _, _ | .var _, h, _, _ | .cvar _, h, _, _ | .name _ _, h, _, _ => by
      simp [CapAtom.effMode] at h

/-- And so does the second expansion (`expandM_fix_ro` of the scratch module). -/
theorem Ctx.expandAtomM_ro (Γ : Ctx s) :
    ∀ a : CapAtom s, a.effMode = .ro → ∀ x ∈ Γ.expandAtomM a, x.effMode = .ro
  | .mode .ro a, _, x, hx => by
      rw [Ctx.expandAtomM_mode] at hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact CapAtom.effMode_withMode_ro y
  | .mode .consume a, h, x, hx => by
      have ha : a.effMode = .ro := by
        cases hm : a.effMode <;> simp [CapAtom.effMode, hm] at h ⊢
      rw [Ctx.expandAtomM_mode] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact CapAtom.effMode_withMode_of_ro (Ctx.expandAtomM_ro Γ a ha y hy)
  | .top, h, _, _ | .var _, h, _, _ | .cvar _, h, _, _ | .name _ _, h, _, _ => by
      simp [CapAtom.effMode] at h

/-- An atom of a resolution comes from one atom of the set. -/
theorem Ctx.mem_caps_exists {Γ : Ctx s} (n : Nat) : ∀ (C : CaptureSet s) (x : CapAtom s),
    x ∈ Γ.caps n C → ∃ y ∈ C, x ∈ Γ.capsAtom n y
  | [], x, hx => by simp at hx
  | a :: C, x, hx => by
      rw [Ctx.caps_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨a, List.mem_cons_self .., hx⟩
      · obtain ⟨y, hy, hxy⟩ := Ctx.mem_caps_exists n C x hx
        exact ⟨y, List.mem_cons_of_mem a hy, hxy⟩

/-- **A set of read-only atoms is read-only** (`kind_canon_fix` of the scratch
module).  This is the statement the overwriting wrapper of the design broke at
`consume (ro ℓ)` (`kind_canon_fails`), and the meet repairs. -/
theorem Ctx.kindRo_of_allRo (Γ : Ctx s) {C : CaptureSet s} (h : C.AllRo) : Γ.KindRo C := by
  rintro a ⟨n, hn⟩
  obtain ⟨x, hx, ha⟩ := List.mem_flatMap.mp hn
  obtain ⟨y, hy, hxy⟩ := Ctx.mem_caps_exists n C x hx
  exact Γ.expandAtomM_ro x (Γ.capsAtom_ro n y (h y hy) x hxy) a ha

/-! ### Item 6 of the canonical-forms theorem

`cap_canon`, the statement that closed capture evidence includes roots, no
longer fits here: `CapCo.HasType` is now mutual with atom typing, so `capvar`
needs item 7 of the theorem and `member` needs the view of an atom.  The
statement moves, unchanged, into the mutual induction of `CanonicalForms.lean`
(plan-5c A1.6); the four constructors it had in A0 are still discharged by
`CapLe.refl`, `CapLe.trans`, `CapLe.of_subset` and `CapLe.union`, and `defC`
by `Ctx.Root_name` above. -/

/-! ## The store invariant of separation

Plan V-D, Fact 1.  A store context carries no kill and no claim, and its
consumable names are locations and heirs.  Masking is derived: a name is
masked when some heir owns it.  The separation half of the invariant says
that the context is root free, that every bit is live, that a cell sits at a
location, that each heir owns distinct consumable names, that a name has at
most one owner, that two distinct unmasked consumable names share no
location, that the names one heir owns share no location, and that a
consumable name resolves to locations only.

T0.1 is the effect of appending a capture binder on the roots of an old set.
T0.2 is the preservation of the invariant by the five ways a store context
grows.  T0.3 is the full disjointness separation evidence reads. -/

/-! ### Bounds under weakening

The weakening facts for atoms and sets that this section uses are stated in
`Names.lean`. -/

theorem CapBound.weaken_eq_own {b : CapBound s} {k' : Bool} {W' : CaptureSet (s,,k)}
    (h : CapBound.weaken (k := k) b = .own k' W') :
    ∃ W, b = .own k' W ∧ W' = CaptureSet.weaken (k := k) W := by
  cases b <;> simp [CapBound.weaken, CapBound.rename] at h
  case own k₀ W₀ => exact ⟨W₀, by rw [h.1], h.2.symm⟩

theorem CapBound.weaken_eq_loc_nil {b : CapBound s} {k' : Bool} :
    CapBound.weaken (k := k) b = .loc k' [] ↔ b = .loc k' [] := by
  cases b <;> simp [CapBound.weaken, CapBound.rename, CaptureSet.rename]

/-! ### Ownership under weakening -/

/-- An owner is younger than what it owns. -/
theorem Ctx.ownsB_depth : ∀ {s : Sig} (Γ : Ctx s) (h κ : BVar s .cap),
    Γ.ownsB h κ = true → h.depth < κ.depth
  | _, .cons Γ _, .there h, κ, hh => by
      obtain ⟨κ₀, rfl, h₀⟩ := CapBound.ownsB_weaken_inv (b := Γ.lookupCap h) hh
      have := Ctx.ownsB_depth Γ h κ₀ h₀
      simp only [BVar.depth_there]
      omega
  | _, .consC Γ b, .here, κ, hh => by
      obtain ⟨κ₀, rfl, -⟩ := CapBound.ownsB_weaken_inv (b := b) hh
      simp
  | _, .consC Γ _, .there h, κ, hh => by
      obtain ⟨κ₀, rfl, h₀⟩ := CapBound.ownsB_weaken_inv (b := Γ.lookupCap h) hh
      have := Ctx.ownsB_depth Γ h κ₀ h₀
      simp only [BVar.depth_there]
      omega

/-! ### Masking and liveness

`Ctx.Masked` is defined in `Names.lean`, beside `Ctx.Consumable`, which a
typing premise reads. -/

/-- An unmasked consumable name. -/
def Ctx.Live (Γ : Ctx s) (κ : BVar s .cap) : Prop :=
  (Γ.lookupCap κ).consumable = true ∧ ¬ Γ.Masked κ

instance Ctx.Live.instDecidable (Γ : Ctx s) (κ : BVar s .cap) : Decidable (Γ.Live κ) := by
  unfold Ctx.Live; infer_instance

theorem Ctx.live_cons_iff (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Γ.cons b).Live (.there κ) ↔ Γ.Live κ := by
  unfold Ctx.Live
  rw [Ctx.masked_cons_iff, Ctx.lookupCap_there, CapBound.consumable_weaken]

theorem Ctx.live_consC_iff (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Γ.consC b).Live (.there κ) ↔ Γ.Live κ ∧ b.ownsB κ = false := by
  unfold Ctx.Live
  rw [Ctx.masked_consC_iff, Ctx.lookupCap_thereC, CapBound.consumable_weaken]
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨⟨hc, fun h => hm (Or.inl h)⟩, ?_⟩
    cases hb : b.ownsB κ with
    | false => rfl
    | true => exact absurd (Or.inr hb) hm
  · rintro ⟨⟨hc, hm⟩, hb⟩
    refine ⟨hc, ?_⟩
    rintro (h | h)
    · exact hm h
    · rw [hb] at h; exact Bool.false_ne_true h

theorem Ctx.Live.not_owned {Γ : Ctx s} {κ h : BVar s .cap} (hl : Γ.Live κ) :
    Γ.ownsB h κ = false := by
  cases hh : Γ.ownsB h κ with
  | false => rfl
  | true => exact absurd (Ctx.masked_iff.mpr ⟨h, hh⟩) hl.2

/-! ### Locations -/

/-- A location atom.  (With the mode wrapper of S0.1 the atom is read at its
base.) -/
def Ctx.IsLocAtom (Γ : Ctx s) (a : CapAtom s) : Prop :=
  ∃ ℓ b, a.base = .cvar ℓ ∧ Γ.lookupCap ℓ = .loc b []

/-- Two names share no location. -/
def Ctx.LocDisj (Γ : Ctx s) (κ₁ κ₂ : BVar s .cap) : Prop :=
  ∀ a, Γ.IsLocAtom a → Γ.Root a [.cvar κ₁] → Γ.Root a [.cvar κ₂] → False

/-- A root the run allocated: a location that is no image of `ρ`. -/
def Ctx.FreshLoc (ρ : Rename s s') (Γ' : Ctx s') (a : CapAtom s') : Prop :=
  Γ'.IsLocAtom a ∧ ∀ κ, a.base ≠ .cvar (ρ.var κ)

/-- Subcapturing up to the locations a run allocated (plan-5h Fact 5). -/
def CapLeFresh (ρ : Rename s s') (Γ' : Ctx s') (C D : CaptureSet s') : Prop :=
  ∀ a, Γ'.Root a C → Γ'.Root a D ∨ Γ'.FreshLoc ρ a

/-- The same with modes. -/
def CapLeMFresh (ρ : Rename s s') (Γ' : Ctx s') (C D : CaptureSet s') : Prop :=
  ∀ a, Γ'.RootM a C →
    (∃ b, Γ'.RootM b D ∧ a.base = b.base ∧ a.effMode ≤ b.effMode) ∨ Γ'.FreshLoc ρ a

/-- Plain subcapturing is subcapturing up to fresh locations. -/
theorem CapLe.fresh {Γ' : Ctx s'} {C D : CaptureSet s'} (h : CapLe Γ' C D) (ρ : Rename s s') :
    CapLeFresh ρ Γ' C D := fun a ha => Or.inl (h a ha)

theorem CapLeM.fresh {Γ' : Ctx s'} {C D : CaptureSet s'} (h : CapLeM Γ' C D)
    (ρ : Rename s s') : CapLeMFresh ρ Γ' C D := fun a ha => Or.inl (h a ha)

/-- The flavour of a store binder: no consumer parameter, and a location that
claims nothing. -/
def Ctx.StoreFlavour (Γ : Ctx s) (κ : BVar s .cap) : Prop :=
  (Γ.lookupCap κ).storeFlavour = true

theorem Ctx.LocDisj.symm {Γ : Ctx s} {κ₁ κ₂ : BVar s .cap} (h : Γ.LocDisj κ₁ κ₂) :
    Γ.LocDisj κ₂ κ₁ := fun a ha r₁ r₂ => h a ha r₂ r₁

theorem Ctx.not_isLocAtom_top (Γ : Ctx s) : ¬ Γ.IsLocAtom .top := by
  rintro ⟨_, _, h, _⟩
  cases h

theorem Ctx.isLocAtom_weaken_iff (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).IsLocAtom (CapAtom.weaken (k := .var) a) ↔ Γ.IsLocAtom a := by
  constructor
  · rintro ⟨ℓ', k, ha, hl⟩
    rw [CapAtom.weaken, CapAtom.base_rename] at ha
    cases hab : a.base with
    | cvar ℓ =>
        rw [hab] at ha
        simp only [CapAtom.rename, Rename.succ_var, CapAtom.cvar.injEq] at ha
        subst ha
        rw [Ctx.lookupCap_there, CapBound.weaken_eq_loc_nil] at hl
        exact ⟨ℓ, k, hab, hl⟩
    | var _ => rw [hab] at ha; simp [CapAtom.rename] at ha
    | name _ _ => rw [hab] at ha; simp [CapAtom.rename] at ha
    | top => rw [hab] at ha; simp [CapAtom.rename] at ha
    | mode m c => exact absurd hab (CapAtom.base_ne_mode a m c)
  · rintro ⟨ℓ, k, hab, hl⟩
    refine ⟨.there ℓ, k, ?_, by rw [Ctx.lookupCap_there, CapBound.weaken_eq_loc_nil]; exact hl⟩
    rw [CapAtom.weaken, CapAtom.base_rename, hab]; rfl

theorem Ctx.isLocAtom_weakenC_iff (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).IsLocAtom (CapAtom.weaken (k := .cap) a) ↔ Γ.IsLocAtom a := by
  constructor
  · rintro ⟨ℓ', k, ha, hl⟩
    rw [CapAtom.weaken, CapAtom.base_rename] at ha
    cases hab : a.base with
    | cvar ℓ =>
        rw [hab] at ha
        simp only [CapAtom.rename, Rename.succ_var, CapAtom.cvar.injEq] at ha
        subst ha
        rw [Ctx.lookupCap_thereC, CapBound.weaken_eq_loc_nil] at hl
        exact ⟨ℓ, k, hab, hl⟩
    | var _ => rw [hab] at ha; simp [CapAtom.rename] at ha
    | name _ _ => rw [hab] at ha; simp [CapAtom.rename] at ha
    | top => rw [hab] at ha; simp [CapAtom.rename] at ha
    | mode m c => exact absurd hab (CapAtom.base_ne_mode a m c)
  · rintro ⟨ℓ, k, hab, hl⟩
    refine ⟨.there ℓ, k, ?_, by rw [Ctx.lookupCap_thereC, CapBound.weaken_eq_loc_nil]; exact hl⟩
    rw [CapAtom.weaken, CapAtom.base_rename, hab]; rfl

/-! ### Root-free contexts -/

/-- Over a root-free context the only root atom is the universal root. -/
theorem Ctx.isRootB_of_rootFree {Γ : Ctx s} (hΓ : Γ.root? = none) (a : CapAtom s) :
    Γ.isRootB a = true ↔ a = CapAtom.top := by
  cases a with
  | var x => simp [Ctx.isRootB]
  | name x ℓ => simp [Ctx.isRootB]
  | top => simp [Ctx.isRootB]
  | mode m a => simp [Ctx.isRootB]
  | cvar κ =>
      simp only [Ctx.isRootB, reduceCtorEq, iff_false]
      rw [Γ.root?_none_isRoot hΓ κ]
      simp

theorem Ctx.rootFree_consC {Γ : Ctx s} (hΓ : Γ.root? = none) {b : CapBound s}
    (hbr : b.isRoot = false) : (Γ.consC b).root? = none := by
  rw [Ctx.root?_consC_of_not_root _ _ hbr, hΓ]; rfl

theorem Ctx.rootFree_cons {Γ : Ctx s} (hΓ : Γ.root? = none) (b : Binding s) :
    (Γ.cons b).root? = none := by
  rw [Ctx.root?_cons, hΓ]; rfl

/-! ### T0.1, freshness of allocated roots -/

/-- The expansion of the universal root after an opaque binder is appended to
a root-free context: the old expansion, weakened, and the new binder. -/
theorem Ctx.mem_expandAtom_top_consC_opaque {Γ : Ctx s} (hΓ : Γ.root? = none)
    {b : CapBound s} (hbo : b.opaque = true) (hbr : b.isRoot = false) (x : CapAtom (s,c)) :
    x ∈ (Γ.consC b).expandAtom CapAtom.top ↔
      (∃ y ∈ Γ.expandAtom CapAtom.top, x = CapAtom.weaken (k := .cap) y) ∨
        x = CapAtom.cvar .here := by
  have hr' : (Γ.consC b).IsRoot CapAtom.top := rfl
  have hr : Γ.IsRoot CapAtom.top := rfl
  constructor
  · intro hx
    rcases Ctx.mem_expandAtom_root hr' hx with rfl | ⟨κ, rfl, hop, hle⟩
    · exact Or.inl ⟨CapAtom.top, Ctx.top_mem_expandAtom hr, rfl⟩
    · cases κ with
      | here => exact Or.inr rfl
      | there κ₀ =>
          refine Or.inl ⟨CapAtom.cvar κ₀, ?_, rfl⟩
          have hop' : (Γ.lookupCap κ₀).opaque = true := by
            simpa [Ctx.lookupCap_thereC] using hop
          have hle' : Γ.LvlLe (CapAtom.cvar κ₀) CapAtom.top := by
            have := Ctx.lvlLeB_weakenC Γ b (CapAtom.cvar κ₀) CapAtom.top
            unfold Ctx.LvlLe at hle ⊢
            rw [← this]; exact hle
          exact Ctx.cvar_mem_expandAtom hr hop' hle'
  · rintro (⟨y, hy, rfl⟩ | rfl)
    · rcases Ctx.mem_expandAtom_root hr hy with rfl | ⟨κ, rfl, hop, hle⟩
      · exact Ctx.top_mem_expandAtom hr'
      · refine Ctx.cvar_mem_expandAtom hr' (κ := κ.there) ?_ ?_
        · simpa [Ctx.lookupCap_thereC] using hop
        · have := Ctx.lvlLeB_weakenC Γ b (CapAtom.cvar κ) CapAtom.top
          unfold Ctx.LvlLe at hle ⊢
          exact this.trans hle
    · refine Ctx.cvar_mem_expandAtom hr' ?_ ?_
      · simpa [Ctx.lookupCap_here] using hbo
      · show Ctx.lvlLeB _ _ _ = true
        simp [Ctx.lvlLeB, Ctx.lvlAtom, Ctx.lvl_consC_here_of_not_root _ _ hbr, hΓ,
          depthGe]

/-- Expansion of a weakened atom after an opaque binder is appended to a
root-free context, at an atom that is its own base. -/
theorem Ctx.mem_expandAtom_weakenC_opaque_of_base {Γ : Ctx s} (hΓ : Γ.root? = none)
    {b : CapBound s} (hbo : b.opaque = true) (hbr : b.isRoot = false)
    {a : CapAtom s} (hb : a.base = a) (x : CapAtom (s,c)) :
    x ∈ (Γ.consC b).expandAtom (CapAtom.weaken (k := .cap) a) ↔
      (∃ y ∈ Γ.expandAtom a, x = CapAtom.weaken (k := .cap) y) ∨
        (x = CapAtom.cvar .here ∧ a = CapAtom.top) := by
  have hbw : (CapAtom.weaken (k := .cap) a).base = a.weaken := by
    rw [CapAtom.weaken, CapAtom.base_rename, hb]
  by_cases ha : a = CapAtom.top
  · subst ha
    rw [show CapAtom.weaken (k := .cap) (CapAtom.top : CapAtom s) = CapAtom.top from rfl,
      Ctx.mem_expandAtom_top_consC_opaque hΓ hbo hbr]
    simp
  · have h1 : Γ.isRootB a = false := by
      cases h : Γ.isRootB a
      · rfl
      · exact absurd ((Ctx.isRootB_of_rootFree hΓ a).mp h) ha
    have h2 : (Γ.consC b).isRootB (CapAtom.weaken (k := .cap) a) = false := by
      rw [Ctx.isRootB_weakenC]; exact h1
    rw [Ctx.expandAtom_of_not_root h2 hbw, Ctx.expandAtom_of_not_root h1 hb]
    simp [ha]

/-- Expansion of a weakened atom after an opaque binder is appended to a
root-free context.  The new binder enters exactly when the base of the atom is
the universal root. -/
theorem Ctx.mem_expandAtom_weakenC_opaque {Γ : Ctx s} (hΓ : Γ.root? = none)
    {b : CapBound s} (hbo : b.opaque = true) (hbr : b.isRoot = false)
    (a : CapAtom s) (x : CapAtom (s,c)) :
    x ∈ (Γ.consC b).expandAtom (CapAtom.weaken (k := .cap) a) ↔
      (∃ y ∈ Γ.expandAtom a, x = CapAtom.weaken (k := .cap) y) ∨
        (x = CapAtom.cvar .here ∧ a.base = CapAtom.top) := by
  have hw : (Γ.consC b).expandAtom (CapAtom.weaken (k := .cap) a)
      = (Γ.consC b).expandAtom (CapAtom.weaken (k := .cap) a.base) := by
    rw [← (Γ.consC b).expandAtom_base_eq (CapAtom.weaken (k := .cap) a), CapAtom.weaken,
      CapAtom.base_rename]; rfl
  rw [hw, Ctx.mem_expandAtom_weakenC_opaque_of_base hΓ hbo hbr (CapAtom.base_base a) x,
    Γ.expandAtom_base_eq a]

/-- **T0.1, freshness of allocated roots**, in the membership form.  The
roots of an old set after an opaque binder is appended to a root-free context
are the old roots weakened, together with the new binder exactly when the set
resolves to the universal root under some mode.  The resolution is read by
its bases, since a mode rides on what resolution produces and expansion
strips it. -/
theorem mem_roots_weakenC_opaque {Γ : Ctx s} (hΓ : Γ.root? = none)
    {b : CapBound s} (hbo : b.opaque = true) (hbr : b.isRoot = false)
    (n : Nat) (C : CaptureSet s) (x : CapAtom (s,c)) :
    x ∈ (Γ.consC b).roots n C.weaken ↔
      (∃ y ∈ Γ.roots n C, x = y.weaken) ∨
        (x = .cvar .here ∧ ⊤ᶜ ∈ (Γ.caps n C).map CapAtom.base) := by
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weakenC, Ctx.roots_eq_expand_caps, Ctx.mem_expand]
  constructor
  · rintro ⟨a', ha', hx⟩
    obtain ⟨a, ha, rfl⟩ := CaptureSet.mem_weaken.mp ha'
    rcases (Ctx.mem_expandAtom_weakenC_opaque hΓ hbo hbr a x).mp hx with
      ⟨y, hy, rfl⟩ | ⟨rfl, hat⟩
    · exact Or.inl ⟨y, Ctx.mem_expand.mpr ⟨a, ha, hy⟩, rfl⟩
    · exact Or.inr ⟨rfl, hat ▸ List.mem_map_of_mem ha⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨rfl, htop⟩)
    · obtain ⟨a, ha, hya⟩ := Ctx.mem_expand.mp hy
      exact ⟨CapAtom.weaken (k := .cap) a, CaptureSet.mem_weaken.mpr ⟨a, ha, rfl⟩,
        (Ctx.mem_expandAtom_weakenC_opaque hΓ hbo hbr a _).mpr (Or.inl ⟨y, hya, rfl⟩)⟩
    · obtain ⟨a, ha, hat⟩ := List.mem_map.mp htop
      exact ⟨CapAtom.weaken (k := .cap) a, CaptureSet.mem_weaken.mpr ⟨a, ha, rfl⟩,
        (Ctx.mem_expandAtom_weakenC_opaque hΓ hbo hbr a _).mpr (Or.inr ⟨rfl, hat⟩)⟩

/-- A non-opaque capture binder is invisible to the roots of an old set. -/
theorem Ctx.roots_weakenC_nonopaque (Γ : Ctx s) {b : CapBound s} (hb : b.opaque = false)
    (n : Nat) (C : CaptureSet s) :
    (Γ.consC b).roots n (CaptureSet.weaken (k := .cap) C) =
      CaptureSet.weaken (k := .cap) (Γ.roots n C) := by
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weakenC, Ctx.expand_weakenC Γ b hb,
    Ctx.roots_eq_expand_caps]

/-- A term binder is invisible to the roots of an old set. -/
theorem Ctx.roots_weaken (Γ : Ctx s) (b : Binding s) (n : Nat) (C : CaptureSet s) :
    (Γ.cons b).roots n (CaptureSet.weaken (k := .var) C) =
      CaptureSet.weaken (k := .var) (Γ.roots n C) := by
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_weaken, Ctx.expand_weaken, Ctx.roots_eq_expand_caps]

/-- **T0.1.  Old atoms keep their roots** across any non-root capture binder
appended to a root-free context, opaque or not. -/
theorem Root_weakenC_old {Γ : Ctx s} (hΓ : Γ.root? = none) {b : CapBound s}
    (hbr : b.isRoot = false) (a : CapAtom s) (C : CaptureSet s) :
    (Γ.consC b).Root a.weaken C.weaken ↔ Γ.Root a C := by
  cases hbo : b.opaque with
  | false =>
      constructor
      · rintro ⟨n, hn⟩
        rw [Ctx.roots_weakenC_nonopaque Γ hbo] at hn
        obtain ⟨y, hy, hyx⟩ := CaptureSet.mem_weaken.mp hn
        exact ⟨n, (CapAtom.weaken_inj hyx) ▸ hy⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by
          rw [Ctx.roots_weakenC_nonopaque Γ hbo]; exact CaptureSet.mem_weaken.mpr ⟨a, hn, rfl⟩⟩
  | true =>
      constructor
      · rintro ⟨n, hn⟩
        rcases (mem_roots_weakenC_opaque hΓ hbo hbr n C _).mp hn with ⟨y, hy, hyx⟩ | ⟨h, -⟩
        · exact ⟨n, (CapAtom.weaken_inj hyx) ▸ hy⟩
        · exact absurd h.symm (CapAtom.cvar_here_ne_weaken a)
      · rintro ⟨n, hn⟩
        exact ⟨n, (mem_roots_weakenC_opaque hΓ hbo hbr n C _).mpr (Or.inl ⟨a, hn, rfl⟩)⟩

/-- **T0.1.  The fresh binder is a root of an old set exactly when that set
resolves to the universal root**, under some mode. -/
theorem Root_weakenC_here {Γ : Ctx s} (hΓ : Γ.root? = none) {b : CapBound s}
    (hbo : b.opaque = true) (hbr : b.isRoot = false) (C : CaptureSet s) :
    (Γ.consC b).Root (.cvar .here) C.weaken ↔ ∃ n, ⊤ᶜ ∈ (Γ.caps n C).map CapAtom.base := by
  constructor
  · rintro ⟨n, hn⟩
    rcases (mem_roots_weakenC_opaque hΓ hbo hbr n C _).mp hn with ⟨y, -, hyx⟩ | ⟨-, ht⟩
    · exact absurd hyx (CapAtom.cvar_here_ne_weaken y)
    · exact ⟨n, ht⟩
  · rintro ⟨n, ht⟩
    exact ⟨n, (mem_roots_weakenC_opaque hΓ hbo hbr n C _).mpr (Or.inr ⟨rfl, ht⟩)⟩

theorem Ctx.Root_weaken_old (Γ : Ctx s) (b : Binding s) (a : CapAtom s) (C : CaptureSet s) :
    (Γ.cons b).Root (CapAtom.weaken (k := .var) a) (CaptureSet.weaken (k := .var) C) ↔
      Γ.Root a C := by
  constructor
  · rintro ⟨n, hn⟩
    rw [Ctx.roots_weaken] at hn
    obtain ⟨y, hy, hyx⟩ := CaptureSet.mem_weaken.mp hn
    exact ⟨n, (CapAtom.weaken_inj hyx) ▸ hy⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [Ctx.roots_weaken]; exact CaptureSet.mem_weaken.mpr ⟨a, hn, rfl⟩⟩

/-- A root of an old set after a term binder is a weakened old root. -/
theorem Ctx.Root_cons_old (Γ : Ctx s) (b : Binding s) {C : CaptureSet s} {x : CapAtom (s,x)}
    (hx : (Γ.cons b).Root x (CaptureSet.weaken (k := .var) C)) :
    ∃ a, x = CapAtom.weaken (k := .var) a ∧ Γ.Root a C := by
  obtain ⟨n, hn⟩ := hx
  rw [Ctx.roots_weaken] at hn
  obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp hn
  exact ⟨y, rfl, n, hy⟩

/-- A root of an old set that never resolves to `⊤ᶜ`, after a non-root
capture binder, is a weakened old root. -/
theorem Ctx.Root_consC_old {Γ : Ctx s} (hΓ : Γ.root? = none) {b : CapBound s}
    (hbr : b.isRoot = false) {C : CaptureSet s}
    (hnt : ∀ n, ⊤ᶜ ∉ (Γ.caps n C).map CapAtom.base)
    {x : CapAtom (s,c)} (hx : (Γ.consC b).Root x (CaptureSet.weaken (k := .cap) C)) :
    ∃ a, x = CapAtom.weaken (k := .cap) a ∧ Γ.Root a C := by
  obtain ⟨n, hn⟩ := hx
  cases hbo : b.opaque with
  | false =>
      rw [Ctx.roots_weakenC_nonopaque Γ hbo] at hn
      obtain ⟨y, hy, rfl⟩ := CaptureSet.mem_weaken.mp hn
      exact ⟨y, rfl, n, hy⟩
  | true =>
      rcases (mem_roots_weakenC_opaque hΓ hbo hbr n C x).mp hn with ⟨y, hy, rfl⟩ | ⟨-, ht⟩
      · exact ⟨y, rfl, n, hy⟩
      · exact absurd ht (hnt n)

/-- **T0.1, the roots of an heir** are the roots of what it owns. -/
theorem roots_heir (Γ : Ctx s) (W : CaptureSet s) (n : Nat) :
    (Γ.consC (.own b W)).roots n [.cvar .here] = (Γ.roots n W).weaken := by
  have hcaps : (Γ.consC (.own b W)).caps n [CapAtom.cvar .here] =
      CaptureSet.weaken (k := .cap) (Γ.caps n W) := by
    rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_cvar, Ctx.lookupCap_here]
    show (Γ.consC (.own b W)).caps n (CaptureSet.weaken (k := .cap) W) = _
    exact Ctx.caps_weakenC Γ _ n W
  rw [Ctx.roots_eq_expand_caps, hcaps, Ctx.expand_weakenC Γ _ rfl, Ctx.roots_eq_expand_caps]

/-- An opaque non-root binder resolves and expands to itself. -/
theorem Ctx.roots_here_of_opaque (Γ : Ctx s) {b : CapBound s} (hbo : b.opaque = true)
    (hbr : b.isRoot = false) (n : Nat) :
    (Γ.consC b).roots n [.cvar .here] = [.cvar .here] := by
  have hcaps : (Γ.consC b).caps n [CapAtom.cvar .here] = [CapAtom.cvar .here] := by
    rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_cvar, Ctx.lookupCap_here]
    cases b <;> first | rfl | simp [CapBound.opaque] at hbo
  rw [Ctx.roots_eq_expand_caps, hcaps, Ctx.expand_cons, Ctx.expand_nil, List.append_nil,
    Ctx.expandAtom_of_not_root _ rfl]
  simp [Ctx.isRootB, Ctx.lookupCap_here, hbr]

/-- A root of a set is a root of one of its atoms. -/
theorem Ctx.Root.exists_mem {Γ : Ctx s} {x : CapAtom s} {C : CaptureSet s}
    (h : Γ.Root x C) : ∃ a ∈ C, Γ.Root x [a] := by
  obtain ⟨n, hn⟩ := h
  rw [Ctx.roots_eq_expand_caps, Ctx.mem_expand] at hn
  obtain ⟨c, hc, hx⟩ := hn
  induction C with
  | nil => simp at hc
  | cons a C ih =>
      rw [Ctx.caps_cons] at hc
      rcases List.mem_append.mp hc with hc | hc
      · refine ⟨a, List.mem_cons_self .., n, ?_⟩
        rw [Ctx.roots_eq_expand_caps, Ctx.mem_expand]
        exact ⟨c, by rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil]; exact hc, hx⟩
      · obtain ⟨a', ha', hr⟩ := ih hc
        exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

/-- What a name owns resolves below it. -/
theorem Ctx.Root.of_ownsB {Γ : Ctx s} {h κ : BVar s .cap} {x : CapAtom s}
    (hh : Γ.ownsB h κ = true) (hx : Γ.Root x [.cvar κ]) : Γ.Root x [.cvar h] := by
  obtain ⟨k, W, hlk, hκ⟩ := CapBound.ownsB_eq_true.mp hh
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  have hcaps : Γ.caps n [CapAtom.cvar h] = Γ.caps n W := by
    rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_cvar, hlk]
    rfl
  rw [Ctx.roots_eq_expand_caps, hcaps]
  rw [Ctx.roots_eq_expand_caps] at hn
  refine Ctx.expand_subset (Ctx.caps_subset ?_) x hn
  intro a ha
  rw [List.mem_singleton.mp ha]
  exact hκ

/-! ### The invariant -/

/-- A cell shape (plan-5h S0.4). -/
def Shape.isCell : Shape s → Bool
  | .cell _ => true
  | _ => false

theorem Shape.isCell_rename (S : Shape s1) (ρ : Rename s1 s2) :
    (S.rename ρ).isCell = S.isCell := by
  cases S <;> rfl

theorem Shape.isCell_iff {S : Shape s} : S.isCell = true ↔ ∃ T, S = .cell T := by
  cases S <;> simp [Shape.isCell]

/-- A term binding declares a cell only at a location of `Γ`. -/
def Binding.CellAtLoc (b : Binding s) (Γ : Ctx s) : Prop :=
  ∀ T C, b.ty = (Shape.cell T) ^ C →
    ∃ ℓ, C = [CapAtom.cvar ℓ] ∧ ∃ k, Γ.lookupCap ℓ = .loc k []

/-- `Binding.CellAtLoc` read through `Shape.isCell`. -/
theorem Binding.CellAtLoc.isCell {b : Binding s} {Γ : Ctx s} (h : b.CellAtLoc Γ)
    {C : CaptureSet s} {S : Shape s} (hb : b.ty = Ty.capt C S) (hc : S.isCell = true) :
    ∃ ℓ, C = [CapAtom.cvar ℓ] ∧ ∃ k, Γ.lookupCap ℓ = .loc k [] := by
  obtain ⟨T, rfl⟩ := Shape.isCell_iff.mp hc
  exact h T C hb

/-- **The separation half of the store invariant** (plan-5h, Fact 1). -/
structure Ctx.SepInv (Γ : Ctx s) : Prop where
  /-- (S2) Root freedom, T-B0.7 of the base. -/
  rootFree : Γ.root? = none
  /-- (S3) A store kills nothing: every kill bit is live.  Kills are lexical. -/
  allLive : ∀ κ, (Γ.lookupCap κ).live = true
  /-- (S3) A store holds no consumer parameter and no claim: a location claims
      nothing, and an heir is the only flavour that owns. -/
  storeFlavours : ∀ κ, Γ.StoreFlavour κ
  /-- (S4) Freshness: a cell is declared at its own location. -/
  cellLoc : ∀ r T C, Γ.lookupTy r = (Shape.cell T) ^ C →
    ∃ ℓ, C = [CapAtom.cvar ℓ] ∧ ∃ b, Γ.lookupCap ℓ = .loc b []
  /-- (S5) An heir owns distinct, consumable, older names. -/
  ownNames : ∀ h b W, Γ.lookupCap h = .own b W →
    W.IsNames ∧ W.Nodup ∧ ∀ κ, CapAtom.cvar κ ∈ W → (Γ.lookupCap κ).consumable = true
  /-- (S5) Linearity: a name has at most one owner. -/
  linear : ∀ h₁ h₂ κ, Γ.ownsB h₁ κ = true → Γ.ownsB h₂ κ = true → h₁ = h₂
  /-- (S6) Two distinct unmasked consumable names share no location. -/
  disj : ∀ κ₁ κ₂, κ₁ ≠ κ₂ → Γ.Live κ₁ → Γ.Live κ₂ → Γ.LocDisj κ₁ κ₂
  /-- (S6) The names one heir owns share no location pairwise. -/
  sib : ∀ h κ₁ κ₂, κ₁ ≠ κ₂ → Γ.ownsB h κ₁ = true → Γ.ownsB h κ₂ = true → Γ.LocDisj κ₁ κ₂
  /-- (S6') A consumable name resolves to locations only, never to `⊤ᶜ`. -/
  locOnly : ∀ κ, (Γ.lookupCap κ).consumable = true →
    ∀ a, Γ.Root a [CapAtom.cvar κ] → Γ.IsLocAtom a

namespace Ctx.SepInv

variable {Γ : Ctx s}

/-- (S4) read through `Shape.isCell`. -/
theorem cellLoc_isCell (hs : Γ.SepInv) {r : BVar s .var} {C : CaptureSet s} {S : Shape s}
    (hr : Γ.lookupTy r = Ty.capt C S) (hc : S.isCell = true) :
    ∃ ℓ, C = [CapAtom.cvar ℓ] ∧ ∃ b, Γ.lookupCap ℓ = .loc b [] := by
  obtain ⟨T, rfl⟩ := Shape.isCell_iff.mp hc
  exact hs.cellLoc r T C hr

/-- A consumable name never resolves to the universal root, under any mode. -/
theorem noTop (hs : Γ.SepInv) {κ : BVar s .cap} (hc : (Γ.lookupCap κ).consumable = true)
    (n : Nat) : ⊤ᶜ ∉ (Γ.caps n [CapAtom.cvar κ]).map CapAtom.base := fun ht => by
  obtain ⟨a, ha, hat⟩ := List.mem_map.mp ht
  have hr := Ctx.Root.of_mem_caps ha
  rw [hat] at hr
  exact Γ.not_isLocAtom_top (hs.locOnly κ hc _ hr)

/-- What an heir owns is consumable. -/
theorem consumable_of_ownsB (hs : Γ.SepInv) {h κ : BVar s .cap} (hh : Γ.ownsB h κ = true) :
    (Γ.lookupCap κ).consumable = true := by
  obtain ⟨k, W, hlk, hκ⟩ := CapBound.ownsB_eq_true.mp hh
  exact (hs.ownNames h k W hlk).2.2 κ hκ

/-- An owner is consumable. -/
theorem consumable_owner {h κ : BVar s .cap} (hh : Γ.ownsB h κ = true) :
    (Γ.lookupCap h).consumable = true := by
  obtain ⟨k, W, hlk, -⟩ := CapBound.ownsB_eq_true.mp hh
  rw [hlk]; rfl

end Ctx.SepInv

/-- Disjointness survives a non-root capture binder, when one side never
resolves to `⊤ᶜ`. -/
theorem Ctx.LocDisj.weakenC {Γ : Ctx s} (hΓ : Γ.root? = none) {b : CapBound s}
    (hbr : b.isRoot = false) {κ₁ κ₂ : BVar s .cap}
    (hnt : ∀ n, ⊤ᶜ ∉ (Γ.caps n [CapAtom.cvar κ₁]).map CapAtom.base) (h : Γ.LocDisj κ₁ κ₂) :
    (Γ.consC b).LocDisj (.there κ₁) (.there κ₂) := by
  intro x hx r₁ r₂
  rw [CaptureSet.singleton_cvar_there] at r₁ r₂
  obtain ⟨a, rfl, ha⟩ := Ctx.Root_consC_old hΓ hbr hnt r₁
  rw [Root_weakenC_old hΓ hbr] at r₂
  exact h a ((Ctx.isLocAtom_weakenC_iff Γ b a).mp hx) ha r₂

theorem Ctx.LocDisj.weaken {Γ : Ctx s} (b : Binding s) {κ₁ κ₂ : BVar s .cap}
    (h : Γ.LocDisj κ₁ κ₂) : (Γ.cons b).LocDisj (.there κ₁) (.there κ₂) := by
  intro x hx r₁ r₂
  rw [CaptureSet.singleton_cvar_there] at r₁ r₂
  obtain ⟨a, rfl, ha⟩ := Ctx.Root_cons_old Γ b r₁
  rw [Ctx.Root_weaken_old] at r₂
  exact h a ((Ctx.isLocAtom_weaken_iff Γ b a).mp hx) ha r₂

/-! ### T0.2, the invariant is preserved -/

namespace Ctx.SepInv

variable {Γ : Ctx s}

/-- The common case of a capture binder appended to a store context: every
clause about old names carries over, and the new binder brings its own facts
about what it owns and where it resolves. -/
theorem consC_of (hs : Γ.SepInv) {b : CapBound s}
    (hbr : b.isRoot = false) (hlive : b.live = true) (hfl : b.storeFlavour = true)
    (hown : ∀ κ, b.ownsB κ = true → Γ.Live κ)
    (hon : ∀ k W, b = .own k W → W.IsNames ∧ W.Nodup)
    (hloc : b.consumable = true →
      ∀ a, (Γ.consC b).Root a [CapAtom.cvar .here] → (Γ.consC b).IsLocAtom a)
    (hdisj : b.consumable = true → ∀ κ, Γ.Live κ → b.ownsB κ = false →
      (Γ.consC b).LocDisj .here (.there κ)) :
    (Γ.consC b).SepInv := by
  have hΓ := hs.rootFree
  refine ⟨Ctx.rootFree_consC hΓ hbr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- allLive
    intro κ
    cases κ with
    | here => rw [Ctx.lookupCap_here, CapBound.live_weaken]; exact hlive
    | there κ₀ => rw [Ctx.lookupCap_thereC, CapBound.live_weaken]; exact hs.allLive κ₀
  · -- storeFlavours
    intro κ
    unfold Ctx.StoreFlavour
    cases κ with
    | here => rw [Ctx.lookupCap_here, CapBound.storeFlavour_weaken]; exact hfl
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.storeFlavour_weaken]; exact hs.storeFlavours κ₀
  · -- cellLoc
    intro r T C hr
    have hc : (Shape.cell T).isCell = true := rfl
    generalize Shape.cell T = S at hr hc
    cases r with
    | there r₀ =>
        rw [Ctx.lookupTy_thereC] at hr
        cases hT : Γ.lookupTy r₀ with
        | capt C₀ S₀ =>
            rw [hT] at hr
            simp only [Ty.weaken, Ty.rename, Ty.capt.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            rw [Shape.isCell_rename] at hc
            obtain ⟨ℓ, rfl, k, hl⟩ := hs.cellLoc_isCell hT hc
            exact ⟨.there ℓ, rfl, k, by rw [Ctx.lookupCap_thereC, hl]; rfl⟩
  · -- ownNames
    intro h k W hh
    cases h with
    | here =>
        rw [Ctx.lookupCap_here] at hh
        obtain ⟨W₀, rfl, rfl⟩ := CapBound.weaken_eq_own hh
        obtain ⟨hn, hnd⟩ := hon k W₀ rfl
        refine ⟨hn.weaken, CaptureSet.nodup_weaken hnd, ?_⟩
        intro κ hκ
        obtain ⟨κ₀, rfl, hκ₀⟩ := CaptureSet.cvar_mem_weaken hκ
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]
        exact (hown κ₀ (CapBound.ownsB_eq_true.mpr ⟨k, W₀, rfl, hκ₀⟩)).1
    | there h₀ =>
        rw [Ctx.lookupCap_thereC] at hh
        obtain ⟨W₀, hh₀, rfl⟩ := CapBound.weaken_eq_own hh
        obtain ⟨hn, hnd, hcons⟩ := hs.ownNames h₀ k W₀ hh₀
        refine ⟨hn.weaken, CaptureSet.nodup_weaken hnd, ?_⟩
        intro κ hκ
        obtain ⟨κ₀, rfl, hκ₀⟩ := CaptureSet.cvar_mem_weaken hκ
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]
        exact hcons κ₀ hκ₀
  · -- linear
    intro h₁ h₂ κ o₁ o₂
    cases κ with
    | here => rw [Ctx.ownsB_consC_right_here] at o₁; exact absurd o₁ Bool.false_ne_true
    | there κ₀ =>
        cases h₁ with
        | here =>
            cases h₂ with
            | here => rfl
            | there h₂ =>
                rw [Ctx.ownsB_consC_here_there] at o₁
                rw [Ctx.ownsB_consC_there] at o₂
                rw [(hown κ₀ o₁).not_owned] at o₂
                exact absurd o₂ Bool.false_ne_true
        | there h₁ =>
            cases h₂ with
            | here =>
                rw [Ctx.ownsB_consC_here_there] at o₂
                rw [Ctx.ownsB_consC_there] at o₁
                rw [(hown κ₀ o₂).not_owned] at o₁
                exact absurd o₁ Bool.false_ne_true
            | there h₂ =>
                rw [Ctx.ownsB_consC_there] at o₁ o₂
                rw [hs.linear h₁ h₂ κ₀ o₁ o₂]
  · -- disj
    intro κ₁ κ₂ hne l₁ l₂
    cases κ₁ with
    | here =>
        cases κ₂ with
        | here => exact absurd rfl hne
        | there κ =>
            have hc : b.consumable = true := by
              have := l₁.1
              rwa [Ctx.lookupCap_here, CapBound.consumable_weaken] at this
            obtain ⟨hl, hno⟩ := (Ctx.live_consC_iff Γ b κ).mp l₂
            exact hdisj hc κ hl hno
    | there κ₁ =>
        cases κ₂ with
        | here =>
            have hc : b.consumable = true := by
              have := l₂.1
              rwa [Ctx.lookupCap_here, CapBound.consumable_weaken] at this
            obtain ⟨hl, hno⟩ := (Ctx.live_consC_iff Γ b κ₁).mp l₁
            exact (hdisj hc κ₁ hl hno).symm
        | there κ₂ =>
            obtain ⟨hl₁, -⟩ := (Ctx.live_consC_iff Γ b κ₁).mp l₁
            obtain ⟨hl₂, -⟩ := (Ctx.live_consC_iff Γ b κ₂).mp l₂
            exact (hs.disj κ₁ κ₂ (fun e => hne (e ▸ rfl)) hl₁ hl₂).weakenC hΓ hbr
              (hs.noTop hl₁.1)
  · -- sib
    intro h κ₁ κ₂ hne o₁ o₂
    cases κ₁ with
    | here => rw [Ctx.ownsB_consC_right_here] at o₁; exact absurd o₁ Bool.false_ne_true
    | there κ₁ =>
        cases κ₂ with
        | here => rw [Ctx.ownsB_consC_right_here] at o₂; exact absurd o₂ Bool.false_ne_true
        | there κ₂ =>
            have hne' : κ₁ ≠ κ₂ := fun e => hne (e ▸ rfl)
            cases h with
            | here =>
                rw [Ctx.ownsB_consC_here_there] at o₁ o₂
                have hl₁ := hown κ₁ o₁
                exact (hs.disj κ₁ κ₂ hne' hl₁ (hown κ₂ o₂)).weakenC hΓ hbr (hs.noTop hl₁.1)
            | there h₀ =>
                rw [Ctx.ownsB_consC_there] at o₁ o₂
                exact (hs.sib h₀ κ₁ κ₂ hne' o₁ o₂).weakenC hΓ hbr
                  (hs.noTop (hs.consumable_of_ownsB o₁))
  · -- locOnly
    intro κ hc a ha
    cases κ with
    | here =>
        rw [Ctx.lookupCap_here, CapBound.consumable_weaken] at hc
        exact hloc hc a ha
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
        rw [CaptureSet.singleton_cvar_there] at ha
        obtain ⟨a₀, rfl, ha₀⟩ := Ctx.Root_consC_old hΓ hbr (hs.noTop hc) ha
        exact (Ctx.isLocAtom_weakenC_iff Γ b a₀).mpr (hs.locOnly κ₀ hc a₀ ha₀)

/-- **T0.2.**  The empty store context. -/
theorem nil : (Ctx.nil).SepInv where
  rootFree := rfl
  allLive := fun κ => nomatch κ
  storeFlavours := fun κ => nomatch κ
  cellLoc := fun r => nomatch r
  ownNames := fun h => nomatch h
  linear := fun h => nomatch h
  disj := fun κ => nomatch κ
  sib := fun h => nomatch h
  locOnly := fun κ => nomatch κ

/-- **T0.2.**  A platform capability, a rigid binder that is not consumable. -/
theorem platform (hs : Γ.SepInv) : (Γ.consC .star).SepInv :=
  hs.consC_of rfl rfl rfl (fun _ h => absurd h Bool.false_ne_true)
    (fun _ _ h => nomatch h) (fun h => absurd h Bool.false_ne_true)
    (fun h => absurd h Bool.false_ne_true)

/-- **T0.2.**  Allocation: a fresh live location that claims nothing. -/
theorem alloc (hs : Γ.SepInv) : (Γ.consC (.loc true [])).SepInv := by
  have hΓ := hs.rootFree
  refine hs.consC_of rfl rfl rfl (fun _ h => absurd h Bool.false_ne_true)
    (fun _ _ h => nomatch h) ?_ ?_
  · intro _ a ha
    obtain ⟨n, hn⟩ := ha
    rw [Ctx.roots_here_of_opaque Γ rfl rfl, List.mem_singleton] at hn
    subst hn
    exact ⟨.here, true, rfl, rfl⟩
  · intro _ κ hl _ x _ r₁ r₂
    obtain ⟨n, hn⟩ := r₁
    rw [Ctx.roots_here_of_opaque Γ rfl rfl, List.mem_singleton] at hn
    subst hn
    rw [CaptureSet.singleton_cvar_there, Root_weakenC_here hΓ rfl rfl] at r₂
    obtain ⟨m, hm⟩ := r₂
    exact hs.noTop hl.1 m hm

/-- **T0.2.**  A term binder: a literal, a payload, or a cell declared at its
location. -/
theorem cons (hs : Γ.SepInv) (b : Binding s) (hb : b.CellAtLoc Γ) : (Γ.cons b).SepInv := by
  refine ⟨Ctx.rootFree_cons hs.rootFree b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro κ
    cases κ with
    | there κ₀ => rw [Ctx.lookupCap_there, CapBound.live_weaken]; exact hs.allLive κ₀
  · intro κ
    unfold Ctx.StoreFlavour
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.storeFlavour_weaken]; exact hs.storeFlavours κ₀
  · intro r T C hr
    have hc : (Shape.cell T).isCell = true := rfl
    generalize Shape.cell T = S at hr hc
    cases r with
    | here =>
        rw [Ctx.lookupTy_here] at hr
        cases hT : b.ty with
        | capt C₀ S₀ =>
            rw [hT] at hr
            simp only [Ty.weaken, Ty.rename, Ty.capt.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            rw [Shape.isCell_rename] at hc
            obtain ⟨ℓ, rfl, k, hl⟩ := hb.isCell hT hc
            exact ⟨.there ℓ, rfl, k, by rw [Ctx.lookupCap_there, hl]; rfl⟩
    | there r₀ =>
        rw [Ctx.lookupTy_there] at hr
        cases hT : Γ.lookupTy r₀ with
        | capt C₀ S₀ =>
            rw [hT] at hr
            simp only [Ty.weaken, Ty.rename, Ty.capt.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            rw [Shape.isCell_rename] at hc
            obtain ⟨ℓ, rfl, k, hl⟩ := hs.cellLoc_isCell hT hc
            exact ⟨.there ℓ, rfl, k, by rw [Ctx.lookupCap_there, hl]; rfl⟩
  · intro h k W hh
    cases h with
    | there h₀ =>
        rw [Ctx.lookupCap_there] at hh
        obtain ⟨W₀, hh₀, rfl⟩ := CapBound.weaken_eq_own hh
        obtain ⟨hn, hnd, hcons⟩ := hs.ownNames h₀ k W₀ hh₀
        refine ⟨hn.weaken, CaptureSet.nodup_weaken hnd, ?_⟩
        intro κ hκ
        obtain ⟨κ₀, rfl, hκ₀⟩ := CaptureSet.cvar_mem_weaken hκ
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken]
        exact hcons κ₀ hκ₀
  · intro h₁ h₂ κ o₁ o₂
    cases h₁ with
    | there h₁ =>
        cases h₂ with
        | there h₂ =>
            cases κ with
            | there κ₀ =>
                rw [Ctx.ownsB_cons_there] at o₁ o₂
                rw [hs.linear h₁ h₂ κ₀ o₁ o₂]
  · intro κ₁ κ₂ hne l₁ l₂
    cases κ₁ with
    | there κ₁ =>
        cases κ₂ with
        | there κ₂ =>
            rw [Ctx.live_cons_iff] at l₁ l₂
            exact (hs.disj κ₁ κ₂ (fun e => hne (e ▸ rfl)) l₁ l₂).weaken b
  · intro h κ₁ κ₂ hne o₁ o₂
    cases h with
    | there h₀ =>
        cases κ₁ with
        | there κ₁ =>
            cases κ₂ with
            | there κ₂ =>
                rw [Ctx.ownsB_cons_there] at o₁ o₂
                exact (hs.sib h₀ κ₁ κ₂ (fun e => hne (e ▸ rfl)) o₁ o₂).weaken b
  · intro κ hc a ha
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc
        rw [CaptureSet.singleton_cvar_there] at ha
        obtain ⟨a₀, rfl, ha₀⟩ := Ctx.Root_cons_old Γ b ha
        exact (Ctx.isLocAtom_weaken_iff Γ b a₀).mpr (hs.locOnly κ₀ hc a₀ ha₀)

/-- **T0.2.**  An heir: the step that consumes the distinct unmasked names
`W`.  The heir replaces `W` in the live set, owns names that had no owner,
and its names are pairwise disjoint because they were live and distinct. -/
theorem heir (hs : Γ.SepInv) {W : CaptureSet s} (hW : W.IsNames) (hnd : W.Nodup)
    (hlive : ∀ κ, CapAtom.cvar κ ∈ W → Γ.Live κ) : (Γ.consC (.own true W)).SepInv := by
  have hΓ := hs.rootFree
  have hbr : (CapBound.own true W).isRoot = false := rfl
  refine hs.consC_of hbr rfl rfl ?_ ?_ ?_ ?_
  · intro κ h
    exact hlive κ ((CaptureSet.elem_iff _).mp h)
  · intro k W' h
    cases h
    exact ⟨hW, hnd⟩
  · intro _ a ha
    obtain ⟨n, hn⟩ := ha
    rw [roots_heir, CaptureSet.mem_weaken] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨w, hw, hyw⟩ := Ctx.Root.exists_mem (Γ := Γ) ⟨n, hy⟩
    obtain ⟨κ, rfl⟩ := hW w hw
    exact (Ctx.isLocAtom_weakenC_iff Γ _ y).mpr (hs.locOnly κ (hlive κ hw).1 y hyw)
  · intro _ κ hl hno x hx r₁ r₂
    obtain ⟨n, hn⟩ := r₁
    rw [roots_heir, CaptureSet.mem_weaken] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨w, hw, hyw⟩ := Ctx.Root.exists_mem (Γ := Γ) ⟨n, hy⟩
    obtain ⟨κ', rfl⟩ := hW w hw
    rw [CaptureSet.singleton_cvar_there, Root_weakenC_old hΓ hbr] at r₂
    have hne : κ' ≠ κ := by
      rintro rfl
      have : (CapBound.own true W).ownsB κ' = true := (CaptureSet.elem_iff _).mpr hw
      rw [hno] at this
      exact Bool.false_ne_true this
    exact hs.disj κ' κ hne (hlive κ' hw) hl y ((Ctx.isLocAtom_weakenC_iff Γ _ y).mp hx) hyw r₂

/-- A root-free store context of the copied base satisfies the invariant: it
has no consumable binder and declares no cell, so every clause about
consumable binders is vacuous (S0.11, the row of `State.Typed`). -/
theorem of_noConsumable (hΓ : Γ.root? = none)
    (hc : ∀ κ, (Γ.lookupCap κ).consumable = false)
    (hcell : ∀ r C S, Γ.lookupTy r = Ty.capt C S → S.isCell = false) : Γ.SepInv := by
  have hown : ∀ h κ, Γ.ownsB h κ = false := by
    intro h κ
    cases ho : Γ.ownsB h κ with
    | false => rfl
    | true =>
        obtain ⟨k, W, hlk, -⟩ := CapBound.ownsB_eq_true.mp ho
        have := hc h
        rw [hlk] at this
        simp [CapBound.consumable] at this
  refine ⟨hΓ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro κ
    have := hc κ
    cases hb : Γ.lookupCap κ <;> rw [hb] at this <;>
      first | rfl | simp [CapBound.consumable] at this
  · intro κ
    unfold Ctx.StoreFlavour
    have := hc κ
    cases hb : Γ.lookupCap κ <;> rw [hb] at this <;>
      first | rfl | simp [CapBound.consumable] at this
  · intro r T C hr
    have hS := hcell r C _ hr
    simp [Shape.isCell] at hS
  · intro h k W hh
    have := hc h
    rw [hh] at this
    simp [CapBound.consumable] at this
  · intro h₁ _ κ o₁ _
    rw [hown h₁ κ] at o₁
    exact absurd o₁ Bool.false_ne_true
  · intro κ₁ _ _ l₁ _
    have := l₁.1
    rw [hc κ₁] at this
    exact absurd this Bool.false_ne_true
  · intro h κ₁ _ _ o₁ _
    rw [hown h κ₁] at o₁
    exact absurd o₁ Bool.false_ne_true
  · intro κ hκ
    rw [hc κ] at hκ
    exact absurd hκ Bool.false_ne_true

end Ctx.SepInv

/-! ### T0.3, full disjointness -/

namespace Ctx.SepInv

variable {Γ : Ctx s}

/-- In a store context a name claims exactly what it owns. -/
theorem claimsB_eq_ownsB (hs : Γ.SepInv) (h κ : BVar s .cap) :
    Γ.claimsB h κ = Γ.ownsB h κ := by
  have hfl := hs.storeFlavours h
  unfold Ctx.StoreFlavour at hfl
  unfold Ctx.claimsB Ctx.ownsB
  cases hb : Γ.lookupCap h with
  | loc k C =>
      rw [hb] at hfl
      simp only [CapBound.storeFlavour, List.isEmpty_iff] at hfl
      subst hfl
      rfl
  | param k => rw [hb] at hfl; simp [CapBound.storeFlavour] at hfl
  | own k W => rfl
  | root => rfl
  | star => rfl
  | upper C => rfl
  | inst C => rfl

theorem mayOwn_iff_owns (hs : Γ.SepInv) {h κ : BVar s .cap} : Γ.MayOwn h κ ↔ Γ.Owns h κ := by
  constructor
  · intro hm
    induction hm with
    | direct hd => exact .direct (by rw [← hs.claimsB_eq_ownsB]; exact hd)
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  · exact Ctx.MayOwn.of_owns

/-- Possible ownership moves roots up. -/
theorem MayOwn_root (hs : Γ.SepInv) {h κ : BVar s .cap} (hm : Γ.MayOwn h κ) {x : CapAtom s}
    (hx : Γ.Root x [.cvar κ]) : Γ.Root x [.cvar h] := by
  induction hm with
  | direct hd => exact Ctx.Root.of_ownsB (by rw [← hs.claimsB_eq_ownsB]; exact hd) hx
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hx)

end Ctx.SepInv

/-- The first step of a chain of possible ownership. -/
theorem Ctx.MayOwn.head {Γ : Ctx s} {h κ : BVar s .cap} (hm : Γ.MayOwn h κ) :
    ∃ c, Γ.claimsB h c = true ∧ (c = κ ∨ Γ.MayOwn c κ) := by
  induction hm with
  | direct hd => exact ⟨_, hd, Or.inl rfl⟩
  | trans _ h₂ ih₁ _ =>
      obtain ⟨c, hc, hcm⟩ := ih₁
      rcases hcm with rfl | hcm
      · exact ⟨c, hc, Or.inr h₂⟩
      · exact ⟨c, hc, Or.inr (.trans hcm h₂)⟩

namespace Ctx.SepInv

variable {Γ : Ctx s}

/-- The climbing step of full disjointness: a masked name is replaced by its
owner, which is younger. -/
theorem disj_unrelated_aux (hs : Γ.SepInv) : ∀ N : Nat, ∀ κ₁ κ₂ : BVar s .cap,
    κ₁.depth + κ₂.depth < N → κ₁ ≠ κ₂ →
    (Γ.lookupCap κ₁).consumable = true → (Γ.lookupCap κ₂).consumable = true →
    ¬ Γ.Related κ₁ κ₂ → Γ.LocDisj κ₁ κ₂
  | 0, _, _, hN, _, _, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, κ₁, κ₂, hN, hne, h₁, h₂, hr => by
      -- One masked name climbs to its owner.
      have step : ∀ κ₁ κ₂ : BVar s .cap, κ₁.depth + κ₂.depth < N + 1 → κ₁ ≠ κ₂ →
          (Γ.lookupCap κ₂).consumable = true → ¬ Γ.Related κ₁ κ₂ → Γ.Masked κ₁ →
          Γ.LocDisj κ₁ κ₂ := by
        intro κ₁ κ₂ hN hne h₂ hr hm x hx r₁ r₂
        obtain ⟨o, ho⟩ := Ctx.masked_iff.mp hm
        have hdo := Γ.ownsB_depth o κ₁ ho
        have r₁' := Ctx.Root.of_ownsB ho r₁
        by_cases heq : o = κ₂
        · subst heq
          exact hr (Or.inr (.direct (Ctx.claimsB_of_ownsB ho)))
        · have key : ¬ Γ.Related o κ₂ := by
            rintro (hm' | hm')
            · obtain ⟨c, hc, hcκ⟩ := hm'.head
              rw [hs.claimsB_eq_ownsB] at hc
              by_cases hcκ₁ : c = κ₁
              · subst hcκ₁
                rcases hcκ with rfl | hcκ
                · exact hne rfl
                · exact hr (Or.inl hcκ)
              · have r₂' : Γ.Root x [.cvar c] := by
                  rcases hcκ with rfl | hcκ
                  · exact r₂
                  · exact hs.MayOwn_root hcκ r₂
                exact hs.sib o κ₁ c (fun e => hcκ₁ e.symm) ho hc x hx r₁ r₂'
            · exact hr (Or.inr (.trans hm' (.direct (Ctx.claimsB_of_ownsB ho))))
          exact disj_unrelated_aux hs N o κ₂ (by omega) heq
            (Ctx.SepInv.consumable_owner ho) h₂ key x hx r₁' r₂
      by_cases hm₁ : Γ.Masked κ₁
      · exact step κ₁ κ₂ hN hne h₂ hr hm₁
      · by_cases hm₂ : Γ.Masked κ₂
        · exact (step κ₂ κ₁ (by omega) (Ne.symm hne) h₁ (fun h => hr (Or.symm h)) hm₂).symm
        · exact hs.disj κ₁ κ₂ hne ⟨h₁, hm₁⟩ ⟨h₂, hm₂⟩

/-- **T0.3, full disjointness.**  Two distinct consumable names that are not
related by ownership share no location, masked or not.  Climb each to its
unmasked ancestor, apply S6 if the ancestors differ and the sibling clause if
they meet. -/
theorem disj_unrelated (hs : Γ.SepInv) {κ₁ κ₂ : BVar s .cap} (hne : κ₁ ≠ κ₂)
    (h₁ : (Γ.lookupCap κ₁).consumable = true) (h₂ : (Γ.lookupCap κ₂).consumable = true)
    (hr : ¬ Γ.Related κ₁ κ₂) : Γ.LocDisj κ₁ κ₂ :=
  hs.disj_unrelated_aux _ κ₁ κ₂ (Nat.lt_succ_self _) hne h₁ h₂ hr

end Ctx.SepInv

/-! ### T0.4, names cover roots

The names of a set stop where resolution stops, or at an heir, whose names
may own what the heir resolves to, and they follow capture names at least as
far as resolution does, since the search for self references is closed
(`CapWitnesses.reachPairs_closed`).  So every atom resolution reaches is
covered by a name at a mode at least its own: the same base, or a name that
may own it (`Ctx.caps_covered`).  Opening roots on both sides gives
`Ctx.names_cover_roots`. -/

/-- `z` covers `x`: at least its mode, and the same base or a name that may own
it. -/
def Ctx.Covers (Γ : Ctx s) (x z : CapAtom s) : Prop :=
  x.effMode ≤ z.effMode ∧
    (x.base = z.base ∨ ∃ h κ, z.base = .cvar h ∧ x.base = .cvar κ ∧ Γ.MayOwn h κ)

theorem Ctx.Covers.refl (Γ : Ctx s) (x : CapAtom s) : Γ.Covers x x :=
  ⟨EMode.le_refl _, Or.inl rfl⟩

/-- Covering reads only bases and effective modes. -/
theorem Ctx.Covers.congr {Γ : Ctx s} {x x' z z' : CapAtom s} (h : Γ.Covers x z)
    (hxb : x'.base = x.base) (hxe : x'.effMode = x.effMode)
    (hzb : z'.base = z.base) (hze : z'.effMode = z.effMode) : Γ.Covers x' z' := by
  obtain ⟨hm, hb⟩ := h
  refine ⟨by rw [hxe, hze]; exact hm, ?_⟩
  rw [hxb, hzb]
  exact hb

theorem Ctx.Covers.applyEMode {Γ : Ctx s} {x z : CapAtom s} (h : Γ.Covers x z) (m : EMode) :
    Γ.Covers (x.applyEMode m) (z.applyEMode m) := by
  obtain ⟨hm, hb⟩ := h
  refine ⟨?_, ?_⟩
  · rw [CapAtom.effMode_applyEMode, CapAtom.effMode_applyEMode]
    exact EMode.comb_mono m hm
  · rw [CapAtom.base_applyEMode, CapAtom.base_applyEMode]
    exact hb

theorem Ctx.MayOwn.weaken {Γ : Ctx s} {h κ : BVar s .cap} (hm : Γ.MayOwn h κ) (b : Binding s) :
    (Γ.cons b).MayOwn h.there κ.there := by
  induction hm with
  | direct hd => exact .direct (by rw [Ctx.claimsB_cons_there]; exact hd)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Ctx.Covers.weaken {Γ : Ctx s} {x z : CapAtom s} (h : Γ.Covers x z) (b : Binding s) :
    (Γ.cons b).Covers (CapAtom.weaken x) (CapAtom.weaken z) := by
  obtain ⟨hm, hb⟩ := h
  refine ⟨by simpa [CapAtom.weaken] using hm, ?_⟩
  simp only [CapAtom.weaken, CapAtom.base_rename]
  rcases hb with hb | ⟨h', κ, hz, hx, hmo⟩
  · exact Or.inl (by rw [hb])
  · exact Or.inr ⟨h'.there, κ.there, by rw [hz]; rfl, by rw [hx]; rfl, hmo.weaken b⟩

theorem Ctx.Covers.weakenC {Γ : Ctx s} {x z : CapAtom s} (h : Γ.Covers x z) (b : CapBound s) :
    (Γ.consC b).Covers (CapAtom.weaken x) (CapAtom.weaken z) := by
  obtain ⟨hm, hb⟩ := h
  refine ⟨by simpa [CapAtom.weaken] using hm, ?_⟩
  simp only [CapAtom.weaken, CapAtom.base_rename]
  rcases hb with hb | ⟨h', κ, hz, hx, hmo⟩
  · exact Or.inl (by rw [hb])
  · exact Or.inr ⟨h'.there, κ.there, by rw [hz]; rfl, by rw [hx]; rfl, hmo.weakenC b⟩

/-- Every heir owns consumable names only.  A clause of `Ctx.SepInv`, and it
passes to every prefix. -/
def Ctx.OwnWF (Γ : Ctx s) : Prop :=
  ∀ h b W, Γ.lookupCap h = .own b W →
    W.IsNames ∧ ∀ κ, CapAtom.cvar κ ∈ W → (Γ.lookupCap κ).consumable = true

theorem Ctx.SepInv.ownWF {Γ : Ctx s} (hs : Γ.SepInv) : Γ.OwnWF :=
  fun h b W hl => ⟨(hs.ownNames h b W hl).1, (hs.ownNames h b W hl).2.2⟩

theorem CaptureSet.IsNames.unweaken {W : CaptureSet s}
    (h : (CaptureSet.weaken (k := k) W).IsNames) : W.IsNames := by
  intro a ha
  obtain ⟨κ, hκ⟩ := h _ (CaptureSet.weaken_mem_weaken.mpr ha)
  cases a with
  | cvar κ₀ => exact ⟨κ₀, rfl⟩
  | var _ | name _ _ | top | mode _ _ => simp [CapAtom.weaken, CapAtom.rename] at hκ

theorem Ctx.OwnWF.prefix_cons {Γ : Ctx s} {b : Binding s} (h : (Γ.cons b).OwnWF) : Γ.OwnWF := by
  intro h₀ k W hl
  have hl' : (Γ.cons b).lookupCap (.there h₀) = .own k (CaptureSet.weaken W) := by
    show CapBound.weaken (Γ.lookupCap h₀) = _
    rw [hl]; rfl
  obtain ⟨hn, hc⟩ := h _ _ _ hl'
  refine ⟨hn.unweaken, fun κ hκ => ?_⟩
  have := hc κ.there (CaptureSet.weaken_mem_weaken.mpr hκ)
  simpa [Ctx.lookupCap] using this

theorem Ctx.OwnWF.prefix_consC {Γ : Ctx s} {b : CapBound s} (h : (Γ.consC b).OwnWF) :
    Γ.OwnWF := by
  intro h₀ k W hl
  have hl' : (Γ.consC b).lookupCap (.there h₀) = .own k (CaptureSet.weaken W) := by
    show CapBound.weaken (Γ.lookupCap h₀) = _
    rw [hl]; rfl
  obtain ⟨hn, hc⟩ := h _ _ _ hl'
  refine ⟨hn.unweaken, fun κ hκ => ?_⟩
  have := hc κ.there (CaptureSet.weaken_mem_weaken.mpr hκ)
  simpa [Ctx.lookupCap] using this

/-- Resolution carries the use mode of an atom on top of the resolution of
its base (plan-5h decision 39). -/
theorem Ctx.capsAtom_eq_map_useApply (Γ : Ctx s) (n : Nat) :
    ∀ c : CapAtom s, Γ.capsAtom n c = (Γ.capsAtom n c.base).map c.useApply
  | .mode m c => by
      rw [Ctx.capsAtom_mode, Ctx.capsAtom_eq_map_useApply Γ n c]
      show _ = List.map (CapAtom.mode m c).useApply (Γ.capsAtom n c.base)
      unfold CaptureSet.modeWrap
      split
      · rename_i h
        apply List.map_congr_left
        intro x _
        rw [CapAtom.useApply_mode, if_pos h]
      · rename_i h
        rw [List.map_map]
        apply List.map_congr_left
        intro x _
        rw [CapAtom.useApply_mode, if_neg h]
        rfl
  | .var _ | .cvar _ | .name _ _ | .top => by
      rw [List.map_congr_left (fun x _ => CapAtom.useApply_of_base rfl x)]
      exact (List.map_id' _).symm

/-- So does the second expansion. -/
theorem Ctx.expandAtomM_eq_map_reapply (Γ : Ctx s) :
    ∀ c : CapAtom s, Γ.expandAtomM c = (Γ.expandAtom c.base).map c.reapply
  | .mode m c => by
      rw [Ctx.expandAtomM_mode, Ctx.expandAtomM_eq_map_reapply Γ c, List.map_map]
      rfl
  | .var _ | .cvar _ | .name _ _ | .top => (List.map_id _).symm

/-- The meet is putting an effective mode on top. -/
theorem CapAtom.withMode_eq_applyEMode (m : Mode) (a : CapAtom s) :
    CapAtom.withMode m a = a.applyEMode (match m with | .ro => .ro | .consume => .consume) := by
  cases m <;> rfl

theorem CapAtom.reapply_of_base : ∀ {c : CapAtom s}, c.base = c → ∀ x : CapAtom s, c.reapply x = x
  | .var _, _, _ | .cvar _, _, _ | .name _ _, _, _ | .top, _, _ => rfl
  | .mode m c, h, _ => absurd h (CapAtom.base_ne_mode c m c)

theorem Ctx.mem_namesCapsP_of_base (p : Bool) {Γ : Ctx s} {c z : CapAtom s} (hc : c.base = c)
    (hz : z ∈ (Γ.namesCapsP p c.base).map c.useApply) : z ∈ Γ.namesCapsP p c := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  rw [CapAtom.useApply_of_base hc]
  rw [hc] at hy
  exact hy

theorem Ctx.mem_namesCaps_of_base {Γ : Ctx s} {c z : CapAtom s} (hc : c.base = c)
    (hz : z ∈ (Γ.namesCaps c.base).map c.useApply) : z ∈ Γ.namesCaps c :=
  Ctx.mem_namesCapsP_of_base false hc hz

/-- The term-binder clause at the newest binder. -/
theorem Ctx.capsAtom_var_here (Γ : Ctx s) (b : Binding s) (n : Nat) :
    (Γ.cons b).capsAtom n (.var .here) = CaptureSet.weaken (Γ.caps n b.ty.captureSet) := by
  rw [Ctx.capsAtom_var, Ctx.lookupTy_here, Ty.captureSet_weaken, Ctx.caps_weaken]

/-- The capture-binder clause at the newest binder, for a bound that stands
for a set. -/
theorem Ctx.capsAtom_cvar_here_set (Γ : Ctx s) (n : Nat) {b : CapBound s} {C : CaptureSet s}
    (hb : b = .upper C ∨ b = .inst C ∨ ∃ k, b = .own k C) :
    (Γ.consC b).capsAtom n (.cvar .here) = CaptureSet.weaken (Γ.caps n C) := by
  rw [Ctx.capsAtom_cvar, Ctx.lookupCap_here]
  rcases hb with rfl | rfl | ⟨k, rfl⟩ <;> exact Ctx.caps_weakenC Γ _ n C

/-- And for a leaf. -/
theorem Ctx.capsAtom_cvar_here_leaf (Γ : Ctx s) (n : Nat) {b : CapBound s}
    (hb : b = .root ∨ b = .star ∨ (∃ k C, b = .loc k C) ∨ ∃ k, b = .param k) :
    (Γ.consC b).capsAtom n (.cvar .here) = [.cvar .here] := by
  rw [Ctx.capsAtom_cvar, Ctx.lookupCap_here]
  rcases hb with rfl | rfl | ⟨k, C, rfl⟩ | ⟨k, rfl⟩ <;> rfl

/-- It suffices to cover the resolution of base atoms. -/
theorem Ctx.covered_of_base {Γ : Ctx s} {n : Nat}
    (h : ∀ c : CapAtom s, c.base = c → ∀ x ∈ Γ.capsAtom n c, ∃ z ∈ Γ.namesCaps c, Γ.Covers x z) :
    ∀ (c x : CapAtom s), x ∈ Γ.capsAtom n c →
      ∃ z ∈ (Γ.namesCaps c.base).map c.useApply, Γ.Covers x z
  | .mode m c, x, hx => by
      rw [Ctx.capsAtom_mode] at hx
      unfold CaptureSet.modeWrap at hx
      split at hx
      · rename_i hmt
        obtain ⟨z', hz', hc⟩ := Ctx.covered_of_base h c x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz'
        refine ⟨(CapAtom.mode m c).useApply y, List.mem_map_of_mem hy, ?_⟩
        rw [CapAtom.useApply_mode, if_pos hmt]
        exact hc
      · rename_i hmt
        obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
        obtain ⟨z', hz', hc⟩ := Ctx.covered_of_base h c x' hx'
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz'
        refine ⟨(CapAtom.mode m c).useApply y, List.mem_map_of_mem hy, ?_⟩
        rw [CapAtom.useApply_mode, if_neg hmt, CapAtom.withMode_eq_applyEMode,
          CapAtom.withMode_eq_applyEMode]
        exact hc.applyEMode _
  | .var y, x, hx => by
      obtain ⟨z, hz, hc⟩ := h (.var y) rfl x hx
      exact ⟨z, List.mem_map.mpr ⟨z, hz, rfl⟩, hc⟩
  | .cvar κ, x, hx => by
      obtain ⟨z, hz, hc⟩ := h (.cvar κ) rfl x hx
      exact ⟨z, List.mem_map.mpr ⟨z, hz, rfl⟩, hc⟩
  | .name y l, x, hx => by
      obtain ⟨z, hz, hc⟩ := h (.name y l) rfl x hx
      exact ⟨z, List.mem_map.mpr ⟨z, hz, rfl⟩, hc⟩
  | .top, x, hx => by
      obtain ⟨z, hz, hc⟩ := h .top rfl x hx
      exact ⟨z, List.mem_map.mpr ⟨z, hz, rfl⟩, hc⟩

/-- A set is covered atom by atom. -/
theorem Ctx.covered_set {Γ : Ctx s} {n : Nat}
    (ih : ∀ (c x : CapAtom s), x ∈ Γ.capsAtom n c →
      ∃ z ∈ (Γ.namesCaps c.base).map c.useApply, Γ.Covers x z)
    (C : CaptureSet s) (x : CapAtom s) (hx : x ∈ Γ.caps n C) :
    ∃ z ∈ C.flatMap (fun (a : CapAtom s) => (Γ.namesCaps a.base).map a.useApply),
      Γ.Covers x z := by
  obtain ⟨c, hc, hxc⟩ := Ctx.mem_caps_exists n C x hx
  obtain ⟨z, hz, hcov⟩ := ih c x hxc
  exact ⟨z, List.mem_flatMap.mpr ⟨c, hc, hz⟩, hcov⟩

/-- A weakened set, covered in the prefix, is covered in the extension. -/
theorem Ctx.covered_weaken_set {Γ : Ctx s} (b : Binding s) {L M : CaptureSet s}
    (h : ∀ x ∈ L, ∃ z ∈ M, Γ.Covers x z) :
    ∀ x ∈ CaptureSet.weaken (k := .var) L, ∃ z ∈ CaptureSet.weaken (k := .var) M,
      (Γ.cons b).Covers x z := by
  intro x hx
  obtain ⟨x₀, hx₀, rfl⟩ := CaptureSet.mem_weaken.mp hx
  obtain ⟨z₀, hz₀, hc⟩ := h x₀ hx₀
  exact ⟨CapAtom.weaken z₀, CaptureSet.weaken_mem_weaken.mpr hz₀, hc.weaken b⟩

theorem Ctx.covered_weakenC_set {Γ : Ctx s} (b : CapBound s) {L M : CaptureSet s}
    (h : ∀ x ∈ L, ∃ z ∈ M, Γ.Covers x z) :
    ∀ x ∈ CaptureSet.weaken (k := .cap) L, ∃ z ∈ CaptureSet.weaken (k := .cap) M,
      (Γ.consC b).Covers x z := by
  intro x hx
  obtain ⟨x₀, hx₀, rfl⟩ := CaptureSet.mem_weaken.mp hx
  obtain ⟨z₀, hz₀, hc⟩ := h x₀ hx₀
  exact ⟨CapAtom.weaken z₀, CaptureSet.weaken_mem_weaken.mpr hz₀, hc.weakenC b⟩

/-- A base atom of the witness scope, one binder out: the names it stands for
are the names of the atom. -/
theorem Ctx.selfInner_weaken (Γ : Ctx s) (T : Ty s) :
    ∀ c : CapAtom s, c.base = c →
      Ctx.selfInner (fun a => Γ.namesCaps a) T (CapAtom.weaken (k := .var) c) = Γ.namesCaps c
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .top, _ => by cases Γ <;> rfl
  | .mode m c, h => absurd h (CapAtom.base_ne_mode c m c)

/-- What the capture name of a transparent binder covers at fuel `n`, from
what it covers at the fuel below. -/
theorem Ctx.covered_name_step {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)}
    {Wc : CapWitnesses (s,x)} {Fs : List Label} (ℓ : Label)
    (ih : ∀ (n : Nat) (c x : CapAtom s), x ∈ Γ.capsAtom n c →
      ∃ z ∈ (Γ.namesCaps c.base).map c.useApply, Γ.Covers x z) (n : Nat)
    (ihn : ∀ n', n = n' + 1 → ∀ (p : Label × EMode), p ∈ Wc.reachPairs ℓ → ∀ c ∈ Wc.get p.1,
      ∀ x ∈ (Γ.cons (.transparent T W Wc Fs)).capsAtom n' c,
        ∃ z ∈ (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ),
          (Γ.cons (.transparent T W Wc Fs)).Covers (x.applyEMode p.2) z) :
    ∀ (p : Label × EMode), p ∈ Wc.reachPairs ℓ → ∀ c ∈ Wc.get p.1,
      ∀ x ∈ (Γ.cons (.transparent T W Wc Fs)).capsAtom n c,
        ∃ z ∈ (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ),
          (Γ.cons (.transparent T W Wc Fs)).Covers (x.applyEMode p.2) z := by
  intro p hp c hc x hx
  rw [Ctx.capsAtom_eq_map_useApply] at hx
  obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp hx
  -- the names of the capture name, unfolded
  have hnames : (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ)
      = CaptureSet.weaken ((Wc.reach ℓ).flatMap
          (Ctx.namesSelfWith (fun a => Γ.namesCaps a) T)) := rfl
  cases hs : c.selfLabel? with
  | some l =>
      have hb : c.base = .name .here l := CapAtom.selfLabel?_eq_some.mp hs
      rw [hb] at hx₁
      cases n with
      | zero => rw [Ctx.capsAtom_name_zero] at hx₁; cases hx₁
      | succ n' =>
          rw [Ctx.capsAtom_name_some (Ctx.lookupDefC_here_transparent Γ T W Wc Fs l)] at hx₁
          obtain ⟨c', hc', hx'⟩ := Ctx.mem_caps_exists n' _ x₁ hx₁
          have hp' := CapWitnesses.reachPairs_step hp hc hb
          obtain ⟨z, hz, hcov⟩ := ihn n' rfl _ hp' c' hc' x₁ hx'
          refine ⟨z, hz, hcov.congr ?_ ?_ rfl rfl⟩
          · simp [CapAtom.useApply]
          · simp only [CapAtom.effMode_useApply, CapAtom.effMode_applyEMode]
            rw [EMode.comb_assoc]
  | none =>
      have hr : c.applyEMode p.2 ∈ Wc.reach ℓ := CapWitnesses.mem_reach hp hc hs
      rw [hnames]
      -- the atom of the witness, read one binder out
      have key : ∀ y ∈ (Γ.cons (.transparent T W Wc Fs)).capsAtom n c.base,
          ∃ w ∈ CaptureSet.weaken (Ctx.selfInner (fun a => Γ.namesCaps a) T c.base),
            (Γ.cons (.transparent T W Wc Fs)).Covers y w := by
        generalize hcb : c.base = cb
        have hcbb : cb.base = cb := by rw [← hcb, CapAtom.base_base]
        cases cb with
        | var v =>
            cases v with
            | here =>
                intro y hy
                show ∃ w ∈ CaptureSet.weaken (T.captureSet.flatMap fun (d : CapAtom s) =>
                  (Γ.namesCaps d.base).map d.useApply), _
                have hy' : y ∈ CaptureSet.weaken (Γ.caps n T.captureSet) := by
                  rw [Ctx.capsAtom_var_here] at hy; exact hy
                exact Ctx.covered_weaken_set _
                  (fun x hx => Ctx.covered_set (ih n) T.captureSet x hx) y hy'
            | there v =>
                intro y hy
                rw [show (CapAtom.var (.there v) : CapAtom (s,x)) = CapAtom.weaken (.var v) from rfl,
                  Ctx.capsAtom_weaken] at hy
                rw [show (CapAtom.var (.there v) : CapAtom (s,x)) = CapAtom.weaken (.var v) from rfl,
                  Ctx.selfInner_weaken Γ T _ rfl]
                refine Ctx.covered_weaken_set _ (fun x₀ hx₀ => ?_) y hy
                obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.var v) x₀ hx₀
                exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
        | cvar κ =>
            cases κ with
            | there κ =>
                intro y hy
                rw [show (CapAtom.cvar (.there κ) : CapAtom (s,x)) = CapAtom.weaken (.cvar κ)
                  from rfl, Ctx.capsAtom_weaken] at hy
                rw [show (CapAtom.cvar (.there κ) : CapAtom (s,x)) = CapAtom.weaken (.cvar κ)
                  from rfl, Ctx.selfInner_weaken Γ T _ rfl]
                refine Ctx.covered_weaken_set _ (fun x₀ hx₀ => ?_) y hy
                obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.cvar κ) x₀ hx₀
                exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
        | name v l =>
            cases v with
            | here =>
                exfalso
                have : c.selfLabel? = some l := CapAtom.selfLabel?_eq_some.mpr hcb
                rw [hs] at this
                cases this
            | there v =>
                intro y hy
                rw [show (CapAtom.name (.there v) l : CapAtom (s,x)) = CapAtom.weaken (.name v l)
                  from rfl, Ctx.capsAtom_weaken] at hy
                rw [show (CapAtom.name (.there v) l : CapAtom (s,x)) = CapAtom.weaken (.name v l)
                  from rfl, Ctx.selfInner_weaken Γ T _ rfl]
                refine Ctx.covered_weaken_set _ (fun x₀ hx₀ => ?_) y hy
                obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.name v l) x₀ hx₀
                exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
        | top =>
            intro y hy
            rw [Ctx.capsAtom_top] at hy
            rw [List.mem_singleton.mp hy]
            exact ⟨.top, by simp [Ctx.selfInner, CaptureSet.weaken, CaptureSet.rename,
              CapAtom.rename], Ctx.Covers.refl _ _⟩
        | mode m b => exact absurd hcbb (CapAtom.base_ne_mode b m b)
      obtain ⟨w, hw, hcov⟩ := key x₁ hx₁
      obtain ⟨w₀, hw₀, rfl⟩ := CaptureSet.mem_weaken.mp hw
      refine ⟨CapAtom.weaken (w₀.applyEMode (c.applyEMode p.2).useMode),
        CaptureSet.weaken_mem_weaken.mpr
          (List.mem_flatMap.mpr ⟨_, hr, by
            unfold Ctx.namesSelfWith
            rw [CapAtom.base_applyEMode]
            exact List.mem_map_of_mem hw₀⟩), ?_⟩
      have h2 := (hcov.applyEMode c.useMode).applyEMode p.2
      refine h2.congr ?_ ?_ ?_ ?_
      · simp [CapAtom.useApply]
      · simp [CapAtom.useApply]
      · simp [CapAtom.weaken, CapAtom.applyEMode_rename]
      · simp only [CapAtom.weaken, CapAtom.effMode_rename, CapAtom.effMode_applyEMode]
        rw [CapAtom.useMode_applyEMode (Wc.reachPairs_ne_consume ℓ _ p hp), EMode.comb_assoc]

/-- The capture name of a transparent binder covers what it resolves to. -/
theorem Ctx.covered_name_transparent {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)}
    {Wc : CapWitnesses (s,x)} {Fs : List Label} (ℓ : Label)
    (ih : ∀ (n : Nat) (c x : CapAtom s), x ∈ Γ.capsAtom n c →
      ∃ z ∈ (Γ.namesCaps c.base).map c.useApply, Γ.Covers x z) :
    ∀ (n : Nat) (p : Label × EMode), p ∈ Wc.reachPairs ℓ → ∀ c ∈ Wc.get p.1,
      ∀ x ∈ (Γ.cons (.transparent T W Wc Fs)).capsAtom n c,
        ∃ z ∈ (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ),
          (Γ.cons (.transparent T W Wc Fs)).Covers (x.applyEMode p.2) z := by
  intro n
  induction n with
  | zero => exact Ctx.covered_name_step ℓ ih 0 (fun n' h => by cases h)
  | succ n ihn =>
      exact Ctx.covered_name_step ℓ ih (n + 1) (fun n' h => by
        cases Nat.succ.inj h
        exact ihn)

/-- **Names cover resolution.**  In a context whose heirs own consumable
names, every atom a set resolves to is covered by a name of the set. -/
theorem Ctx.caps_covered : ∀ {s : Sig} (Γ : Ctx s), Γ.OwnWF → ∀ (n : Nat) (c x : CapAtom s),
    x ∈ Γ.capsAtom n c → ∃ z ∈ (Γ.namesCaps c.base).map c.useApply, Γ.Covers x z
  | _, .nil, _, n, c, x, hx => by
      refine Ctx.covered_of_base (fun c hcb x hx => ?_) c x hx
      cases c with
      | top =>
          rw [Ctx.capsAtom_top] at hx
          rw [List.mem_singleton.mp hx]
          exact ⟨.top, by simp [Ctx.namesCapsP], Ctx.Covers.refl _ _⟩
      | var y => cases y
      | cvar κ => cases κ
      | name y _ => cases y
      | mode m c => exact absurd hcb (CapAtom.base_ne_mode c m c)
  | _, .cons Γ b, hwf, n, c, x, hx => by
      have ih := Ctx.caps_covered Γ hwf.prefix_cons
      refine Ctx.covered_of_base (fun c hcb x hx => ?_) c x hx
      cases c with
      | top =>
          rw [Ctx.capsAtom_top] at hx
          rw [List.mem_singleton.mp hx]
          exact ⟨.top, by simp [Ctx.namesCapsP], Ctx.Covers.refl _ _⟩
      | mode m c => exact absurd hcb (CapAtom.base_ne_mode c m c)
      | var y =>
          cases y with
          | here =>
              have hx' : x ∈ CaptureSet.weaken (Γ.caps n b.ty.captureSet) := by
                rw [Ctx.capsAtom_var_here] at hx; exact hx
              exact Ctx.covered_weaken_set b
                (fun x hx => Ctx.covered_set (ih n) b.ty.captureSet x hx) x hx'
          | there y =>
              rw [show (CapAtom.var (.there y) : CapAtom (_,x)) = CapAtom.weaken (.var y)
                from rfl, Ctx.capsAtom_weaken] at hx
              rw [show (CapAtom.var (.there y) : CapAtom (_,x)) = CapAtom.weaken (.var y)
                from rfl, Ctx.namesCaps_weaken]
              refine Ctx.covered_weaken_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.var y) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
      | cvar κ =>
          cases κ with
          | there κ =>
              rw [show (CapAtom.cvar (.there κ) : CapAtom (_,x)) = CapAtom.weaken (.cvar κ)
                from rfl, Ctx.capsAtom_weaken] at hx
              rw [show (CapAtom.cvar (.there κ) : CapAtom (_,x)) = CapAtom.weaken (.cvar κ)
                from rfl, Ctx.namesCaps_weaken]
              refine Ctx.covered_weaken_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.cvar κ) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
      | name y l =>
          cases y with
          | there y =>
              rw [show (CapAtom.name (.there y) l : CapAtom (_,x)) = CapAtom.weaken (.name y l)
                from rfl, Ctx.capsAtom_weaken] at hx
              rw [show (CapAtom.name (.there y) l : CapAtom (_,x)) = CapAtom.weaken (.name y l)
                from rfl, Ctx.namesCaps_weaken]
              refine Ctx.covered_weaken_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.name y l) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
          | here =>
              cases b with
              | «opaque» T =>
                  cases n with
                  | zero => rw [Ctx.capsAtom_name_zero] at hx; cases hx
                  | succ n =>
                      rw [Ctx.capsAtom_name_none (by rfl)] at hx
                      cases hx
              | formal T =>
                  cases n with
                  | zero => rw [Ctx.capsAtom_name_zero] at hx; cases hx
                  | succ n =>
                      rw [Ctx.capsAtom_name_none (by rfl)] at hx
                      cases hx
              | transparent T W Wc Fs =>
                  cases n with
                  | zero => rw [Ctx.capsAtom_name_zero] at hx; cases hx
                  | succ n =>
                      rw [Ctx.capsAtom_name_some (Ctx.lookupDefC_here_transparent Γ T W Wc Fs l)]
                        at hx
                      obtain ⟨c', hc', hx'⟩ := Ctx.mem_caps_exists n _ x hx
                      obtain ⟨z, hz, hcov⟩ := Ctx.covered_name_transparent l ih n (l, .eps)
                        (CapWitnesses.start_mem_reachPairs Wc l) c' hc' x hx'
                      exact ⟨z, hz, hcov.congr rfl rfl rfl rfl⟩
  | _, .consC Γ b, hwf, n, c, x, hx => by
      have ih := Ctx.caps_covered Γ hwf.prefix_consC
      refine Ctx.covered_of_base (fun c hcb x hx => ?_) c x hx
      cases c with
      | top =>
          rw [Ctx.capsAtom_top] at hx
          rw [List.mem_singleton.mp hx]
          exact ⟨.top, by simp [Ctx.namesCapsP], Ctx.Covers.refl _ _⟩
      | mode m c => exact absurd hcb (CapAtom.base_ne_mode c m c)
      | var y =>
          cases y with
          | there y =>
              rw [show (CapAtom.var (.there y) : CapAtom (_,c)) = CapAtom.weaken (.var y)
                from rfl, Ctx.capsAtom_weakenC] at hx
              rw [show (CapAtom.var (.there y) : CapAtom (_,c)) = CapAtom.weaken (.var y)
                from rfl, Ctx.namesCaps_weakenC]
              refine Ctx.covered_weakenC_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.var y) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
      | name y l =>
          cases y with
          | there y =>
              rw [show (CapAtom.name (.there y) l : CapAtom (_,c)) = CapAtom.weaken (.name y l)
                from rfl, Ctx.capsAtom_weakenC] at hx
              rw [show (CapAtom.name (.there y) l : CapAtom (_,c)) = CapAtom.weaken (.name y l)
                from rfl, Ctx.namesCaps_weakenC]
              refine Ctx.covered_weakenC_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.name y l) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
      | cvar κ =>
          cases κ with
          | there κ =>
              rw [show (CapAtom.cvar (.there κ) : CapAtom (_,c)) = CapAtom.weaken (.cvar κ)
                from rfl, Ctx.capsAtom_weakenC] at hx
              rw [show (CapAtom.cvar (.there κ) : CapAtom (_,c)) = CapAtom.weaken (.cvar κ)
                from rfl, Ctx.namesCaps_weakenC]
              refine Ctx.covered_weakenC_set b (fun x₀ hx₀ => ?_) x hx
              obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.cvar κ) x₀ hx₀
              exact ⟨z₀, Ctx.mem_namesCaps_of_base rfl hz₀, hc₀⟩
          | here =>
              cases b with
              | root | star | loc _ _ | param _ =>
                  have hx' : x ∈ [CapAtom.cvar .here] := by
                    rw [Ctx.capsAtom_cvar_here_leaf] at hx
                    · exact hx
                    · simp
                  rw [List.mem_singleton.mp hx']
                  exact ⟨.cvar .here, List.mem_singleton_self _, Ctx.Covers.refl _ _⟩
              | upper C =>
                  have hx' : x ∈ CaptureSet.weaken (Γ.caps n C) := by
                    rw [Ctx.capsAtom_cvar_here_set Γ n (Or.inl rfl)] at hx; exact hx
                  exact Ctx.covered_weakenC_set _
                    (fun x hx => Ctx.covered_set (ih n) C x hx) x hx'
              | inst C =>
                  have hx' : x ∈ CaptureSet.weaken (Γ.caps n C) := by
                    rw [Ctx.capsAtom_cvar_here_set Γ n (Or.inr (Or.inl rfl))] at hx; exact hx
                  exact Ctx.covered_weakenC_set _
                    (fun x hx => Ctx.covered_set (ih n) C x hx) x hx'
              | own k W =>
                  have hx' : x ∈ CaptureSet.weaken (Γ.caps n W) := by
                    rw [Ctx.capsAtom_cvar_here_set Γ n (Or.inr (Or.inr ⟨k, rfl⟩))] at hx
                    exact hx
                  obtain ⟨x₀, hx₀, rfl⟩ := CaptureSet.mem_weaken.mp hx'
                  obtain ⟨w, hw, hxw⟩ := Ctx.mem_caps_exists n W x₀ hx₀
                  obtain ⟨hn, hcons⟩ := hwf .here k (CaptureSet.weaken W) rfl
                  obtain ⟨κ₀, rfl⟩ := hn.unweaken w hw
                  have hcκ : (Γ.lookupCap κ₀).consumable = true := by
                    have := hcons κ₀.there (CaptureSet.weaken_mem_weaken.mpr hw)
                    simpa [Ctx.lookupCap] using this
                  obtain ⟨z₀, hz₀, hc₀⟩ := ih n (.cvar κ₀) x₀ hxw
                  have hz₀' : z₀ = .cvar κ₀ := by
                    have := Ctx.mem_namesCaps_of_base rfl hz₀
                    rw [Ctx.namesCaps_consumable Γ κ₀ hcκ] at this
                    exact List.mem_singleton.mp this
                  subst hz₀'
                  obtain ⟨hm, hb⟩ := hc₀
                  have hcl : (Γ.consC (.own k W)).claimsB .here κ₀.there = true := by
                    show (CaptureSet.weaken (k := .cap) W).elem
                      (CapAtom.weaken (k := .cap) (.cvar κ₀)) = true
                    rw [CaptureSet.elem_weaken, CaptureSet.elem_iff]
                    exact hw
                  refine ⟨.cvar .here, List.mem_singleton_self _, ?_, ?_⟩
                  · simpa [CapAtom.weaken] using hm
                  · right
                    rcases hb with hb | ⟨h', κ', hz, hx, hmo⟩
                    · refine ⟨.here, κ₀.there, rfl, ?_, .direct hcl⟩
                      simp only [CapAtom.weaken, CapAtom.base_rename, hb]
                      rfl
                    · have hh : CapAtom.cvar κ₀ = CapAtom.cvar h' := hz
                      cases hh
                      refine ⟨.here, κ'.there, rfl, ?_, .trans (.direct hcl) (hmo.weakenC _)⟩
                      simp only [CapAtom.weaken, CapAtom.base_rename, hx]
                      rfl

/-- **T0.4, names cover roots.**  Every moded root of `C` is reached through a
name of `C` at a mode at least its own: the name is the root, or it may own
the root. -/
theorem Ctx.names_cover_roots {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {ℓ : BVar s .cap}
    (hs : Γ.SepInv) (h : Γ.RootM a C) (hℓ : a.base = .cvar ℓ) :
    ∃ b ∈ Γ.names C, ∃ κ, b.base = .cvar κ ∧ (κ = ℓ ∨ Γ.MayOwn κ ℓ) ∧
      a.effMode ≤ b.effMode := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨x, hx, ha⟩ := List.mem_flatMap.mp hn
  obtain ⟨c, hc, hxc⟩ := Ctx.mem_caps_exists n C x hx
  obtain ⟨z, hz, hmz, hbz⟩ := Ctx.caps_covered Γ hs.ownWF n c x hxc
  rw [Ctx.expandAtomM_eq_map_reapply] at ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  have hyb : y.base = y := Ctx.base_of_mem_expandAtom hy
  have hyl : y = .cvar ℓ := by rw [← hyb, ← hℓ, CapAtom.base_reapply]
  have hae : (x.reapply y).effMode = x.effMode := by
    rw [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, hyl]
    exact EMode.comb_eps _
  have hzmem : ∀ w ∈ Γ.expandNames z, w ∈ Γ.names C := fun w hw =>
    List.mem_flatMap.mpr ⟨c, hc, List.mem_flatMap.mpr ⟨z, hz, hw⟩⟩
  rw [hae]
  cases hroot : Γ.isRootB x.base with
  | true =>
      have hxt : x.base = .top := (Ctx.isRootB_of_rootFree hs.rootFree _).mp hroot
      have hzt : z.base = .top := by
        rcases hbz with hbz | ⟨_, _, _, hx', _⟩
        · rw [← hbz, hxt]
        · rw [hxt] at hx'; cases hx'
      rw [hxt] at hy
      refine ⟨z.reapply (.cvar ℓ), hzmem _ ?_, ℓ, by rw [CapAtom.base_reapply]; rfl,
        Or.inl rfl, ?_⟩
      · unfold Ctx.expandNames
        rw [hzt, if_pos (show Γ.isRootB CapAtom.top = true from rfl)]
        refine List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_filter.mpr
          ⟨Γ.mem_capBinders ℓ, ?_⟩))
        rw [Γ.root?_none_isRoot hs.rootFree ℓ]
        rfl
      · rw [CapAtom.reapply_eq, CapAtom.effMode_applyEMode,
          show (CapAtom.cvar ℓ).effMode = EMode.eps from rfl, EMode.comb_eps]
        exact hmz
  | false =>
      have hy' : y = x.base := by
        rw [Ctx.expandAtom_of_not_root hroot (CapAtom.base_base x)] at hy
        exact List.mem_singleton.mp hy
      have hxl : x.base = .cvar ℓ := by rw [← hy', hyl]
      refine ⟨z, hzmem z (Γ.mem_expandNames_self z), ?_⟩
      rcases hbz with hbz | ⟨h', κ, hz', hx', hmo⟩
      · exact ⟨ℓ, by rw [← hbz, hxl], Or.inl rfl, hmz⟩
      · rw [hxl] at hx'
        cases hx'
        exact ⟨h', hz', Or.inr hmo, hmz⟩

end FCdot

end Separation
