import Coercions.Nominal.FCn.Context
import Coercions.Nominal.FCn.Erasure

/-!
# The canonical walk of FCn (plan X, T.6 amended)

The walk `canonPass` follows the blocks of a context, and `canonFuel` iterates it with fuel.  The
budget `Ctx.aliasBudget` is one more than the number of forwarding targets in the context's blocks,
and `Ctx.canonWalk` is the walk at the budget.  `Ctx.canon` is the canonical name, and `none` is the
one name of every cyclic path.

The budget lemma `canonFuel_stable` is proved by stabilization over the forwarding targets, with no
pigeonhole on paths.  Then come the laws `canon_none_iff`, `canon_idem`, `canon_sel`,
`canon_ext_congr`, `canon_node`, `canon_fwd` and `canon_opaque`.  The laws under binders are
`canon_weaken`, `canon_here` and `canon_substPath` at an opaque binder.  `canon_rename` holds for a
renaming that carries the blocks, and gives `canon_weaken_any` past any binder and `canon_refine`.

At the end the walk is read on the runtime.  `canon_lookup` says that in a typed store the name of
a path is reached from the path by lookup in the erased store.  It does not say that the name is a
location.  `canon_cyclic` says that a path named `none` is cyclic there, as `PDot.Runtime.CyclicPath`
states it.  Its infinite lookup is `lookSeq`, which iterates the computed step `PDot.Runtime.lookPath`.
The prototype states both laws and proves neither, so their proofs, from `Defs.getFld_of_kids_get`
on, are new.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- Where a walk lands: a path and the block there (`none` at an opaque binder, a missing child, or
below a closure). -/
abbrev Landing (s : Sig) := Path s × Option (Block s)

/-- One pass of the walk.  `k` walks a forwarding target with one unit less. -/
def canonPass (Γ : Ctx s) (k : Path s → Option (Landing s)) : Path s → Option (Landing s)
  | .var x =>
      match Γ.blockAt x with
      | none => some (.var x, none)
      | some (.node W C) => some (.var x, some (.node W C))
      | some .clo => some (.var x, some .clo)
      | some (.fwd q) => k q
  | .sel p a =>
      match canonPass Γ k p with
      | none => none
      | some (c, none) => some (.sel c a, none)
      | some (c, some .clo) => some (.sel c a, none)
      | some (c, some (.fwd _)) => some (.sel c a, none)
      | some (c, some (.node _ C)) =>
          match C.get a with
          | none => some (.sel c a, none)
          | some (.node W' C') => some (.sel c a, some (.node W' C'))
          | some .clo => some (.sel c a, some .clo)
          | some (.fwd q) => k q

def canonFuel (Γ : Ctx s) : Nat → Path s → Option (Landing s)
  | 0, _ => none
  | n+1, p => canonPass Γ (canonFuel Γ n) p

/-! ## Forwarding targets and the budget -/

mutual
def Block.fwds : Block s → List (Path s)
  | .node _ C => C.fwds
  | .fwd q => [q]
  | .clo => []
def Kids.fwds : Kids s → List (Path s)
  | .nil => []
  | .cons C _ B => B.fwds ++ C.fwds
end

def Binding.fwds : Binding s → List (Path (s,x))
  | .opaque _ => []
  | .transparent _ B => B.fwds

def Ctx.fwds : Ctx s → List (Path s)
  | .nil => []
  | .cons Γ b => Γ.fwds.map (·.rename Rename.succ) ++ b.fwds  -- z bound in b's block

/-- One more than the number of forwarding children in the context's blocks. -/
def Ctx.aliasBudget (Γ : Ctx s) : Nat := Γ.fwds.length + 1
def Ctx.canonWalk (Γ : Ctx s) (p : Path s) : Option (Landing s) := canonFuel Γ Γ.aliasBudget p
/-- The canonical name.  `none` names every cyclic path. -/
def Ctx.canon (Γ : Ctx s) (p : Path s) : Option (Path s) := (Γ.canonWalk p).map Prod.fst

mutual
theorem Block.fwds_rename : ∀ (B : Block s₁) (ρ : Rename s₁ s₂), (B.rename ρ).fwds = B.fwds.map (·.rename ρ)
  | .node _ C, ρ => Kids.fwds_rename C ρ
  | .fwd _, _ => rfl
  | .clo, _ => rfl
theorem Kids.fwds_rename : ∀ (C : Kids s₁) (ρ : Rename s₁ s₂), (C.rename ρ).fwds = C.fwds.map (·.rename ρ)
  | .nil, _ => rfl
  | .cons C a B, ρ => by
      show (B.rename ρ).fwds ++ (C.rename ρ).fwds = (B.fwds ++ C.fwds).map _
      rw [Block.fwds_rename B ρ, Kids.fwds_rename C ρ, List.map_append]
end

theorem Kids.get_fwds : ∀ (C : Kids s) (a : Label) (B : Block s), C.get a = some B → ∀ q ∈ B.fwds, q ∈ C.fwds
  | .nil, _, _, h => by cases h
  | .cons C a' B', a, B, h => by
      intro q hq
      show q ∈ B'.fwds ++ C.fwds
      by_cases e : a = a'
      · have : Kids.get (.cons C a' B') a = some B' := by simp [Kids.get, e]
        rw [this] at h
        cases h
        exact List.mem_append_left _ hq
      · have : Kids.get (.cons C a' B') a = C.get a := by simp [Kids.get, e]
        rw [this] at h
        exact List.mem_append_right _ (Kids.get_fwds C a B h q hq)

theorem Block.child_fwds (B : Block s) (a : Label) (B' : Block s) (h : B.child a = some B') :
    ∀ q ∈ B'.fwds, q ∈ B.fwds := by
  cases B with
  | node W C => exact Kids.get_fwds C a B' h
  | fwd q => cases h
  | clo => cases h

theorem Ctx.blockAt_fwds : ∀ (Γ : Ctx s) (x : BVar s .var) (B : Block s), Γ.blockAt x = some B →
    ∀ q ∈ B.fwds, q ∈ Γ.fwds
  | .cons Γ (.opaque _), .here, _, h => by cases h
  | .cons Γ (.transparent _ B'), .here, B, h => by
      cases h
      intro q hq
      exact List.mem_append_right _ hq
  | .cons Γ b, .there y, B, h => by
      intro q hq
      have h' : (Γ.blockAt y).map (Block.rename · Rename.succ) = some B := by cases b <;> exact h
      cases hy : Γ.blockAt y with
      | none => rw [hy] at h'; cases h'
      | some B₀ =>
          rw [hy] at h'
          cases h'
          rw [Block.fwds_rename] at hq
          obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
          exact List.mem_append_left _ (List.mem_map.mpr ⟨q₀, Ctx.blockAt_fwds Γ y B₀ hy q₀ hq₀, rfl⟩)

theorem Ctx.nodeAt_fwds (Γ : Ctx s) : ∀ (p : Path s) (B : Block s), Γ.nodeAt p = some B → ∀ q ∈ B.fwds, q ∈ Γ.fwds
  | .var x, B, h => Ctx.blockAt_fwds Γ x B h
  | .sel p a, B, h => by
      have h' : (Γ.nodeAt p).bind (·.child a) = some B := h
      cases hp : Γ.nodeAt p with
      | none => rw [hp] at h'; cases h'
      | some B₀ =>
          rw [hp] at h'
          intro q hq
          exact Ctx.nodeAt_fwds Γ p B₀ hp q (Block.child_fwds B₀ a B h' q hq)

/-! ## Landings stay inside the context, and the pass reads its continuation only at targets -/

def GoodL (Γ : Ctx s) (L : Option (Landing s)) : Prop :=
  ∀ c B, L = some (c, some B) → ∀ q ∈ B.fwds, q ∈ Γ.fwds

theorem canonPass_good (Γ : Ctx s) (k : Path s → Option (Landing s)) (hk : ∀ q, GoodL Γ (k q)) :
    ∀ p, GoodL Γ (canonPass Γ k p)
  | .var x => by
      intro c B h
      simp only [canonPass] at h
      split at h
      · cases h
      · rename_i W C hx
        cases h
        exact Ctx.blockAt_fwds Γ x _ hx
      · cases h
        intro q hq; cases hq
      · exact hk _ c B h
  | .sel p a => by
      intro c B h
      have ih := canonPass_good Γ k hk p
      simp only [canonPass] at h
      split at h
      · cases h
      · cases h
      · cases h
      · cases h
      · rename_i c' W C hp
        split at h
        · cases h
        · rename_i W' C' ha
          cases h
          intro q hq
          exact ih c' (.node W C) hp q (Kids.get_fwds C a _ ha q hq)
        · cases h
          intro q hq; cases hq
        · exact hk _ c B h

theorem canonFuel_good (Γ : Ctx s) : ∀ n q, GoodL Γ (canonFuel Γ n q)
  | 0, _ => by intro c B h; cases h
  | n+1, q => canonPass_good Γ _ (canonFuel_good Γ n) q

theorem canonPass_congr (Γ : Ctx s) (k k' : Path s → Option (Landing s)) (hk : ∀ q, GoodL Γ (k q))
    (he : ∀ q ∈ Γ.fwds, k q = k' q) : ∀ p, canonPass Γ k p = canonPass Γ k' p
  | .var x => by
      simp only [canonPass]
      split
      · rfl
      · rfl
      · rfl
      · rename_i q hx
        exact he q (Ctx.blockAt_fwds Γ x _ hx q (by simp [Block.fwds]))
  | .sel p a => by
      have ih := canonPass_congr Γ k k' hk he p
      have hg := canonPass_good Γ k hk p
      simp only [canonPass]
      rw [← ih]
      split
      · rfl
      · rfl
      · rfl
      · rfl
      · rename_i c W C hp
        split
        · rfl
        · rfl
        · rfl
        · rename_i q ha
          exact he q (hg c (.node W C) hp q (Kids.get_fwds C a _ ha q (by simp [Block.fwds])))

theorem canonPass_mono (Γ : Ctx s) (k k' : Path s → Option (Landing s))
    (hm : ∀ q L, k q = some L → k' q = some L) : ∀ p L, canonPass Γ k p = some L → canonPass Γ k' p = some L
  | .var x, L, h => by
      simp only [canonPass] at h ⊢
      cases hx : Γ.blockAt x with
      | none => rw [hx] at h; exact h
      | some B =>
          rw [hx] at h
          cases B with
          | node W C => exact h
          | clo => exact h
          | fwd q => exact hm _ _ h
  | .sel p a, L, h => by
      simp only [canonPass] at h ⊢
      cases hp : canonPass Γ k p with
      | none => rw [hp] at h; cases h
      | some l =>
          rw [canonPass_mono Γ k k' hm p l hp]
          rw [hp] at h
          obtain ⟨c, b⟩ := l
          cases b with
          | none => exact h
          | some B =>
              cases B with
              | clo => exact h
              | fwd _ => exact h
              | node W C =>
                  simp only at h ⊢
                  cases ha : C.get a with
                  | none => rw [ha] at h; exact h
                  | some B' =>
                      rw [ha] at h
                      cases B' with
                      | node W' C' => exact h
                      | clo => exact h
                      | fwd q => exact hm _ _ h

theorem canonFuel_mono (Γ : Ctx s) : ∀ n p L, canonFuel Γ n p = some L → canonFuel Γ (n+1) p = some L
  | 0, _, _, h => by cases h
  | n+1, p, L, h => canonPass_mono Γ _ _ (canonFuel_mono Γ n) p L h

/-! ## A generic stabilization lemma

A family of Boolean predicates on a finite list that only switch from false to true, and that is
stable from one step on as soon as it is stable at one step, is stable at the length of the list. -/

theorem filter_length_le {α : Type} (P Q : α → Bool) :
    ∀ (L : List α), (∀ x ∈ L, Q x = true → P x = true) → (L.filter Q).length ≤ (L.filter P).length
  | [], _ => Nat.le_refl _
  | y :: L, h => by
      have ih := filter_length_le P Q L (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hy := h y (List.mem_cons_self ..)
      simp only [List.filter_cons]
      cases hQ : Q y <;> cases hP : P y <;> simp_all <;> omega

theorem filter_length_lt {α : Type} (P Q : α → Bool) :
    ∀ (L : List α), (∀ x ∈ L, Q x = true → P x = true) → (∃ x ∈ L, P x = true ∧ Q x = false) →
      (L.filter Q).length < (L.filter P).length
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | y :: L, h, ⟨x, hx, hPx, hQx⟩ => by
      have hle := filter_length_le P Q L (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hy := h y (List.mem_cons_self ..)
      simp only [List.filter_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hPx, hQx]; simp only [ite_true]; simp; omega
      · have ih := filter_length_lt P Q L (fun x hx => h x (List.mem_cons_of_mem _ hx)) ⟨x, hx', hPx, hQx⟩
        cases hQ : Q y <;> cases hP : P y <;> simp_all <;> omega

theorem exists_ne_of_not_forall {α : Type} (f g : α → Bool) :
    ∀ (L : List α), ¬ (∀ x ∈ L, f x = g x) → ∃ x ∈ L, f x ≠ g x
  | [], h => absurd (fun x hx => by cases hx) h
  | y :: L, h => by
      by_cases hy : f y = g y
      · obtain ⟨x, hx, hne⟩ := exists_ne_of_not_forall f g L (fun hall => h (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hy
          · exact hall x hx'))
        exact ⟨x, List.mem_cons_of_mem _ hx, hne⟩
      · exact ⟨y, List.mem_cons_self .., hy⟩

theorem stabilize {α : Type} (L : List α) (b : Nat → α → Bool)
    (mono : ∀ n x, b n x = true → b (n+1) x = true)
    (prop : ∀ n, (∀ x ∈ L, b n x = b (n+1) x) → ∀ x ∈ L, b (n+1) x = b (n+2) x) :
    ∀ x ∈ L, b L.length x = b (L.length + 1) x := by
  let stable : Nat → Prop := fun n => ∀ x ∈ L, b n x = b (n+1) x
  let Φ : Nat → Nat := fun n => (L.filter (fun x => !b n x)).length
  have hstep : ∀ n, ¬ stable n → Φ (n+1) < Φ n := by
    intro n hn
    have : ∃ x ∈ L, b n x ≠ b (n+1) x := exists_ne_of_not_forall (b n) (b (n+1)) L hn
    obtain ⟨x, hx, hne⟩ := this
    apply filter_length_lt
    · intro y _ hy
      cases hb : b n y
      · rfl
      · rw [mono n y hb] at hy; cases hy
    · refine ⟨x, hx, ?_, ?_⟩
      · cases hb : b n x
        · rfl
        · rw [hb, mono n x hb] at hne; exact absurd rfl hne
      · cases hb : b n x
        · rw [hb] at hne
          cases hb' : b (n+1) x
          · rw [hb'] at hne; exact absurd rfl hne
          · rfl
        · rw [mono n x hb]; rfl
  have hle : ∀ n, Φ n ≤ L.length := fun n => List.length_filter_le _ _
  have hprop : ∀ n m, stable n → stable (n + m) := by
    intro n m hn
    induction m with
    | zero => exact hn
    | succ m ih => exact prop (n + m) ih
  have key : ∀ n, (∃ m, m ≤ n ∧ stable m) ∨ Φ n + n ≤ L.length := by
    intro n
    induction n with
    | zero => exact .inr (by simpa using hle 0)
    | succ n ih =>
        rcases ih with ⟨m, hm, hs⟩ | h
        · exact .inl ⟨m, by omega, hs⟩
        · by_cases hs : stable n
          · exact .inl ⟨n, by omega, hs⟩
          · have := hstep n hs
            exact .inr (by omega)
  rcases key L.length with ⟨m, hm, hs⟩ | h
  · have := hprop m (L.length - m) hs
    rw [show m + (L.length - m) = L.length by omega] at this
    exact this
  · have h0 : Φ L.length = 0 := by omega
    intro x hx
    have : b L.length x = true := by
      cases hb : b L.length x
      · exfalso
        have : 0 < Φ L.length := by
          apply List.length_pos_of_mem (a := x)
          exact List.mem_filter.mpr ⟨hx, by simp [hb]⟩
        omega
      · rfl
    rw [this, mono _ _ this]

/-! ## The walk is stable at the budget -/

theorem canonFuel_isSome_mono (Γ : Ctx s) (n : Nat) (q : Path s) :
    (canonFuel Γ n q).isSome = true → (canonFuel Γ (n+1) q).isSome = true := by
  intro h
  cases hq : canonFuel Γ n q with
  | none => rw [hq] at h; cases h
  | some L => rw [canonFuel_mono Γ n q L hq]; rfl

theorem canonFuel_eq_of_isSome (Γ : Ctx s) (n : Nat) (q : Path s)
    (h : (canonFuel Γ n q).isSome = (canonFuel Γ (n+1) q).isSome) : canonFuel Γ n q = canonFuel Γ (n+1) q := by
  cases hq : canonFuel Γ n q with
  | none =>
      rw [hq] at h
      cases hq' : canonFuel Γ (n+1) q with
      | none => rfl
      | some _ => rw [hq'] at h; cases h
  | some L => rw [canonFuel_mono Γ n q L hq]

theorem canonFuel_stable_targets (Γ : Ctx s) :
    ∀ q ∈ Γ.fwds, canonFuel Γ Γ.fwds.length q = canonFuel Γ (Γ.fwds.length + 1) q := by
  intro q hq
  apply canonFuel_eq_of_isSome
  refine stabilize Γ.fwds (fun n q => (canonFuel Γ n q).isSome) (canonFuel_isSome_mono Γ) ?_ q hq
  intro n hn q' hq'
  have he : ∀ r ∈ Γ.fwds, canonFuel Γ n r = canonFuel Γ (n+1) r :=
    fun r hr => canonFuel_eq_of_isSome Γ n r (hn r hr)
  show (canonPass Γ (canonFuel Γ n) q').isSome = (canonPass Γ (canonFuel Γ (n+1)) q').isSome
  rw [canonPass_congr Γ _ _ (canonFuel_good Γ n) he q']

theorem canonFuel_stable (Γ : Ctx s) : ∀ k p, canonFuel Γ (Γ.aliasBudget + k) p = Γ.canonWalk p := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
      intro p
      show canonPass Γ (canonFuel Γ (Γ.fwds.length + 1 + k)) p = canonPass Γ (canonFuel Γ Γ.fwds.length) p
      apply canonPass_congr Γ _ _ (canonFuel_good Γ _)
      intro q hq
      rw [show Γ.fwds.length + 1 + k = Γ.aliasBudget + k from rfl, ih q]
      exact (canonFuel_stable_targets Γ q hq).symm

/-- The walk of a forwarding target at one unit less than the budget is its walk at the budget. -/
theorem canonFuel_pred_target (Γ : Ctx s) (q : Path s) (hq : q ∈ Γ.fwds) :
    canonFuel Γ Γ.fwds.length q = Γ.canonWalk q :=
  canonFuel_stable_targets Γ q hq

theorem canonFuel_mono_le (Γ : Ctx s) {n : Nat} {p : Path s} {L : Landing s} (h : canonFuel Γ n p = some L) :
    ∀ k, canonFuel Γ (n + k) p = some L
  | 0 => h
  | k+1 => canonFuel_mono Γ (n + k) p L (canonFuel_mono_le Γ h k)

/-- The one name `none`: a path is named `none` exactly when its walk lands at no fuel. -/
theorem canon_none_iff (Γ : Ctx s) (p : Path s) : Γ.canon p = none ↔ ∀ n, canonFuel Γ n p = none := by
  constructor
  · intro h n
    have hw : Γ.canonWalk p = none := by
      unfold Ctx.canon at h
      cases hw : Γ.canonWalk p with
      | none => rfl
      | some _ => rw [hw] at h; cases h
    cases hn : canonFuel Γ n p with
    | none => rfl
    | some L =>
        exfalso
        by_cases hle : n ≤ Γ.aliasBudget
        · have := canonFuel_mono_le Γ hn (Γ.aliasBudget - n)
          rw [show n + (Γ.aliasBudget - n) = Γ.aliasBudget by omega] at this
          rw [show Γ.canonWalk p = canonFuel Γ Γ.aliasBudget p from rfl, this] at hw
          cases hw
        · have := canonFuel_stable Γ (n - Γ.aliasBudget) p
          rw [show Γ.aliasBudget + (n - Γ.aliasBudget) = n by omega, hn, hw] at this
          cases this
  · intro h
    unfold Ctx.canon Ctx.canonWalk
    rw [h]
    rfl

/-! ## A landing walks to itself -/

theorem canonFuel_fix (Γ : Ctx s) : ∀ (n : Nat) (p c : Path s) (b : Option (Block s)),
    canonFuel Γ n p = some (c, b) → ∀ m, 0 < m → canonFuel Γ m c = some (c, b) := by
  intro n
  induction n with
  | zero => intro p c b h; cases h
  | succ n ihn =>
    intro p
    induction p with
    | var x =>
        intro c b h m hm
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h' : canonPass Γ (canonFuel Γ n) (.var x) = some (c, b) := h
        show canonPass Γ (canonFuel Γ m') c = some (c, b)
        simp only [canonPass] at h'
        cases hx : Γ.blockAt x with
        | none => rw [hx] at h'; cases h'; simp only [canonPass, hx]
        | some B =>
            rw [hx] at h'
            cases B with
            | node W C => cases h'; simp only [canonPass, hx]
            | clo => cases h'; simp only [canonPass, hx]
            | fwd q => exact ihn _ c b h' (m' + 1) (by omega)
    | sel p a ihp =>
        intro c b h m hm
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h' : canonPass Γ (canonFuel Γ n) (.sel p a) = some (c, b) := h
        show canonPass Γ (canonFuel Γ m') c = some (c, b)
        simp only [canonPass] at h'
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rw [hp] at h'; cases h'
        | some l =>
            obtain ⟨c', b'⟩ := l
            rw [hp] at h'
            have hfix : canonPass Γ (canonFuel Γ m') c' = some (c', b') :=
              ihp c' b' hp (m' + 1) (by omega)
            cases b' with
            | none => cases h'; simp only [canonPass, hfix]
            | some B =>
                cases B with
                | clo => cases h'; simp only [canonPass, hfix]
                | fwd r => cases h'; simp only [canonPass, hfix]
                | node W C =>
                    simp only at h'
                    cases ha : C.get a with
                    | none => rw [ha] at h'; cases h'; simp only [canonPass, hfix, ha]
                    | some B' =>
                        rw [ha] at h'
                        cases B' with
                        | node W' C' => cases h'; simp only [canonPass, hfix, ha]
                        | clo => cases h'; simp only [canonPass, hfix, ha]
                        | fwd q => exact ihn _ c b h' (m' + 1) (by omega)

theorem aliasBudget_pos (Γ : Ctx s) : 0 < Γ.aliasBudget := Nat.succ_pos _

theorem canonWalk_fix (Γ : Ctx s) {p c : Path s} {b : Option (Block s)} (h : Γ.canonWalk p = some (c, b)) :
    Γ.canonWalk c = some (c, b) :=
  canonFuel_fix Γ _ p c b h _ (aliasBudget_pos Γ)

theorem canon_idem (Γ : Ctx s) {p c : Path s} (h : Γ.canon p = some c) : Γ.canon c = some c := by
  unfold Ctx.canon at h ⊢
  cases hw : Γ.canonWalk p with
  | none => rw [hw] at h; cases h
  | some l =>
      obtain ⟨c', b⟩ := l
      rw [hw] at h
      cases h
      rw [canonWalk_fix Γ hw]
      rfl

theorem canonWalk_sel (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.canonWalk (.sel p a) = (Γ.canonWalk p).bind (fun l => Γ.canonWalk (.sel l.1 a)) := by
  cases hw : Γ.canonWalk p with
  | none =>
      show canonPass Γ (canonFuel Γ Γ.fwds.length) (.sel p a) = none
      have : canonPass Γ (canonFuel Γ Γ.fwds.length) p = none := hw
      simp only [canonPass, this]
  | some l =>
      obtain ⟨c, b⟩ := l
      have hfix := canonWalk_fix Γ hw
      show canonPass Γ (canonFuel Γ Γ.fwds.length) (.sel p a) = canonPass Γ (canonFuel Γ Γ.fwds.length) (.sel c a)
      have h1 : canonPass Γ (canonFuel Γ Γ.fwds.length) p = some (c, b) := hw
      have h2 : canonPass Γ (canonFuel Γ Γ.fwds.length) c = some (c, b) := hfix
      simp only [canonPass, h1, h2]

/-- `canon_sel`: the name of `p.a` is read off the name of `p`. -/
theorem canon_sel (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.canon (.sel p a) = (Γ.canon p).bind (fun c => Γ.canon (.sel c a)) := by
  unfold Ctx.canon
  rw [canonWalk_sel]
  cases Γ.canonWalk p <;> rfl

/-- One step of `canon_ext_congr`. -/
theorem canon_sel_congr (Γ : Ctx s) {p q : Path s} (h : Γ.canon p = Γ.canon q) (a : Label) :
    Γ.canon (.sel p a) = Γ.canon (.sel q a) := by
  rw [canon_sel, canon_sel, h]

/-- `canon_ext_congr`, over X0's `Path.nomExt`. -/
theorem canon_ext_congr (Γ : Ctx s) {p q : Path s} (h : Γ.canon p = Γ.canon q) :
    ∀ bs, Γ.canon (p.nomExt bs) = Γ.canon (q.nomExt bs)
  | [] => h
  | a :: bs => canon_ext_congr Γ (canon_sel_congr Γ h a) bs

/-! ## Where the walk lands in a typed store -/

theorem canonPass_node (Γ : Ctx s) (k : Path s → Option (Landing s)) :
    ∀ (p : Path s) (W : TyDefs s) (C : Kids s), Γ.nodeAt p = some (.node W C) →
      canonPass Γ k p = some (p, some (.node W C))
  | .var x, W, C, h => by
      have h' : Γ.blockAt x = some (.node W C) := h
      simp only [canonPass, h']
  | .sel p a, W, C, h => by
      have h' : (Γ.nodeAt p).bind (·.child a) = some (.node W C) := h
      cases hp : Γ.nodeAt p with
      | none => rw [hp] at h'; cases h'
      | some B =>
          rw [hp] at h'
          cases B with
          | fwd _ => cases h'
          | clo => cases h'
          | node W₀ C₀ =>
              have ih := canonPass_node Γ k p W₀ C₀ hp
              have ha : C₀.get a = some (.node W C) := h'
              simp only [canonPass, ih, ha]

theorem canonWalk_node (Γ : Ctx s) {p : Path s} {W : TyDefs s} {C : Kids s} (h : Γ.nodeAt p = some (.node W C)) :
    Γ.canonWalk p = some (p, some (.node W C)) :=
  canonPass_node Γ _ p W C h

theorem canon_node (Γ : Ctx s) {p : Path s} {W : TyDefs s} {C : Kids s} (h : Γ.nodeAt p = some (.node W C)) :
    Γ.canon p = some p := by
  unfold Ctx.canon; rw [canonWalk_node Γ h]; rfl

/-- A forwarding child names its target. -/
theorem canon_fwd (Γ : Ctx s) {l q : Path s} {W : TyDefs s} {C : Kids s} {a : Label}
    (hl : Γ.nodeAt l = some (.node W C)) (ha : C.get a = some (.fwd q)) :
    Γ.canon (.sel l a) = Γ.canon q := by
  have hq : q ∈ Γ.fwds := Ctx.nodeAt_fwds Γ l _ hl q (Kids.get_fwds C a _ ha q (by simp [Block.fwds]))
  unfold Ctx.canon
  show (canonPass Γ (canonFuel Γ Γ.fwds.length) (.sel l a)).map Prod.fst = _
  have h1 := canonPass_node Γ (canonFuel Γ Γ.fwds.length) l W C hl
  simp only [canonPass, h1, ha]
  rw [canonFuel_pred_target Γ q hq]

theorem canon_opaque (Γ : Ctx s) {x : BVar s .var} (h : Γ.blockAt x = none) : Γ.canon (.var x) = some (.var x) := by
  unfold Ctx.canon
  show (canonPass Γ (canonFuel Γ Γ.fwds.length) (.var x)).map Prod.fst = _
  simp only [canonPass, h]
  rfl

/-! ## The walk under binders

Past an opaque binder the walk of a weakened path is the weakened walk, and a path rooted at the
binder names itself.  `canon_substPath` follows from the two with `canon_idem`. -/

def Landing.weaken (l : Landing s) : Landing (s,x) := (l.1.rename Rename.succ, l.2.map (Block.rename · Rename.succ))

theorem canonFuel_weaken (Γ : Ctx s) (T : Ty s) : ∀ (n : Nat) (p : Path s),
    canonFuel (Γ.cons (.opaque T)) n (p.rename Rename.succ) = (canonFuel Γ n p).map Landing.weaken := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ihn =>
    intro p
    induction p with
    | var y =>
        show canonPass _ _ (.var (.there y)) = (canonPass Γ (canonFuel Γ n) (.var y)).map _
        have hb : (Γ.cons (.opaque T)).blockAt (.there y) = (Γ.blockAt y).map (Block.rename · Rename.succ) := rfl
        simp only [canonPass, hb]
        cases hy : Γ.blockAt y with
        | none => rfl
        | some B =>
            cases B with
            | node W C => rfl
            | clo => rfl
            | fwd q => exact ihn q
    | sel p a ihp =>
        show canonPass _ _ (.sel (p.rename Rename.succ) a) = (canonPass Γ (canonFuel Γ n) (.sel p a)).map _
        have ihp' : canonPass (Γ.cons (.opaque T)) (canonFuel (Γ.cons (.opaque T)) n) (p.rename Rename.succ) =
            (canonPass Γ (canonFuel Γ n) p).map Landing.weaken := ihp
        simp only [canonPass, ihp']
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rfl
        | some l =>
            obtain ⟨c, b⟩ := l
            cases b with
            | none => rfl
            | some B =>
                cases B with
                | clo => rfl
                | fwd _ => rfl
                | node W C =>
                    simp only [Landing.weaken, Option.map, Block.rename]
                    rw [Kids.get_rename]
                    cases ha : C.get a with
                    | none => rfl
                    | some B' =>
                        cases B' with
                        | node W' C' => rfl
                        | clo => rfl
                        | fwd q => exact ihn q

theorem Ctx.fwds_opaque (Γ : Ctx s) (T : Ty s) : (Γ.cons (.opaque T)).fwds.length = Γ.fwds.length := by
  simp [Ctx.fwds, Binding.fwds]

/-- `canon_weaken`: past an opaque binder, names are weakened names. -/
theorem canon_weaken (Γ : Ctx s) (T : Ty s) (p : Path s) :
    (Γ.cons (.opaque T)).canon (p.rename Rename.succ) = (Γ.canon p).map (·.rename Rename.succ) := by
  unfold Ctx.canon Ctx.canonWalk Ctx.aliasBudget
  rw [Ctx.fwds_opaque, canonFuel_weaken]
  cases canonFuel Γ (Γ.fwds.length + 1) p <;> rfl

theorem canonFuel_here (Γ : Ctx s) (T : Ty s) (n : Nat) :
    ∀ p : Path (s,x), p.root = .here → canonFuel (Γ.cons (.opaque T)) (n+1) p = some (p, none)
  | .var .here, _ => rfl
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      have ih := canonFuel_here Γ T n p h
      show canonPass _ _ (.sel p a) = _
      have ih' : canonPass (Γ.cons (.opaque T)) (canonFuel (Γ.cons (.opaque T)) n) p = some (p, none) := ih
      simp only [canonPass, ih']

/-- `canon_here`: a path rooted at the newest opaque binder names itself. -/
theorem canon_here (Γ : Ctx s) (T : Ty s) (p : Path (s,x)) (h : p.root = .here) :
    (Γ.cons (.opaque T)).canon p = some p := by
  unfold Ctx.canon Ctx.canonWalk Ctx.aliasBudget
  rw [canonFuel_here Γ T _ p h]
  rfl

/-- `canon_substPath` at the newest opaque binder of the context. -/
theorem canon_substPath (Γ : Ctx s) (T : Ty s) (p : Path (s,x)) (q : Path s) :
    Γ.canon (p.substPath q) = ((Γ.cons (.opaque T)).canon p).bind (fun c => Γ.canon (c.substPath q)) := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · rw [canon_here Γ T p hr]; rfl
  · rw [show p₀.weaken (k := .var) = p₀.rename Rename.succ from rfl, canon_weaken,
      show (p₀.rename Rename.succ).substPath q = p₀ from Path.weaken_substPath p₀ q]
    cases hc : Γ.canon p₀ with
    | none => rfl
    | some c =>
        simp only [Option.map_some, Option.bind_some]
        rw [show (c.rename Rename.succ).substPath q = c from Path.weaken_substPath c q]
        exact (canon_idem Γ hc).symm

/-! ## `canon_rename` and `canon_refine` (repair 4)

Neither is read by the canonical forms of a typed store, nor by preservation: `Store.Typed` reads no
`canon`, no typing rule reads it (T.5), and every reading is recomputed over the new store by the
mutual theorem.  They are laws of the walk, proved as the refuter proved `canon_refine`
(`scratch-refute/R4_CanonRefine.lean`), with the weakening generalized to any renaming that carries
the blocks. -/

/-- `ρ` carries the blocks of `Γ` to `Δ`. -/
def Rename.CarriesBlocks (Γ : Ctx s₁) (ρ : Rename s₁ s₂) (Δ : Ctx s₂) : Prop :=
  ∀ y, Δ.blockAt (ρ.var y) = (Γ.blockAt y).map (Block.rename · ρ)

def Landing.rename (l : Landing s₁) (ρ : Rename s₁ s₂) : Landing s₂ :=
  (l.1.rename ρ, l.2.map (Block.rename · ρ))

/-- The walk of a renamed path is the renamed walk, at every fuel. -/
theorem canonFuel_rename (Γ : Ctx s₁) (ρ : Rename s₁ s₂) (Δ : Ctx s₂) (hρ : Rename.CarriesBlocks Γ ρ Δ) :
    ∀ (n : Nat) (p : Path s₁), canonFuel Δ n (p.rename ρ) = (canonFuel Γ n p).map (Landing.rename · ρ) := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ihn =>
    intro p
    induction p with
    | var y =>
        show canonPass _ _ (.var (ρ.var y)) = (canonPass Γ (canonFuel Γ n) (.var y)).map _
        simp only [canonPass, hρ y]
        cases hy : Γ.blockAt y with
        | none => rfl
        | some B =>
            cases B with
            | node W C => rfl
            | clo => rfl
            | fwd q => exact ihn q
    | sel p a ihp =>
        show canonPass _ _ (.sel (p.rename ρ) a) = (canonPass Γ (canonFuel Γ n) (.sel p a)).map _
        have ihp' : canonPass Δ (canonFuel Δ n) (p.rename ρ) =
            (canonPass Γ (canonFuel Γ n) p).map (Landing.rename · ρ) := ihp
        simp only [canonPass, ihp']
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rfl
        | some l =>
            obtain ⟨c, bl⟩ := l
            cases bl with
            | none => rfl
            | some B =>
                cases B with
                | clo => rfl
                | fwd _ => rfl
                | node W C =>
                    simp only [Landing.rename, Option.map, Block.rename]
                    rw [Kids.get_rename]
                    cases ha : C.get a with
                    | none => rfl
                    | some B' =>
                        cases B' with
                        | node W' C' => rfl
                        | clo => rfl
                        | fwd q => exact ihn q

/-- `canon_rename`: a renaming that carries the blocks carries the names. -/
theorem canon_rename (Γ : Ctx s₁) (ρ : Rename s₁ s₂) (Δ : Ctx s₂) (hρ : Rename.CarriesBlocks Γ ρ Δ) (p : Path s₁) :
    Δ.canon (p.rename ρ) = (Γ.canon p).map (·.rename ρ) := by
  have e₁ := canonFuel_stable Δ Γ.aliasBudget (p.rename ρ)
  have e₂ := canonFuel_stable Γ Δ.aliasBudget p
  unfold Ctx.canon
  rw [← e₁, canonFuel_rename Γ ρ Δ hρ,
    show Δ.aliasBudget + Γ.aliasBudget = Γ.aliasBudget + Δ.aliasBudget from Nat.add_comm _ _, e₂]
  cases Γ.canonWalk p <;> rfl

theorem Rename.carriesBlocks_succ (Γ : Ctx s) (b : Binding s) :
    Rename.CarriesBlocks Γ (Rename.succ (k := .var)) (Γ.cons b) := by
  intro y
  cases b <;> rfl

/-- Names of older paths are weakened names past any binder, opaque or transparent. -/
theorem canon_weaken_any (Γ : Ctx s) (b : Binding s) (p : Path s) :
    (Γ.cons b).canon (p.rename Rename.succ) = (Γ.canon p).map (·.rename Rename.succ) :=
  canon_rename Γ Rename.succ (Γ.cons b) (Rename.carriesBlocks_succ Γ b) p

/-- `canon_refine`: making the newest opaque binder transparent refines every name. -/
theorem canon_refine (Γ : Ctx s) (T : Ty s) (B : Block (s,x)) (p : Path (s,x)) :
    (Γ.cons (.transparent T B)).canon p = ((Γ.cons (.opaque T)).canon p).bind (Γ.cons (.transparent T B)).canon := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · rw [canon_here Γ T p hr]; rfl
  · rw [show p₀.weaken (k := .var) = p₀.rename Rename.succ from rfl, canon_weaken_any, canon_weaken Γ T]
    cases hc : Γ.canon p₀ with
    | none => rfl
    | some c =>
        simp only [Option.map_some, Option.bind_some]
        rw [canon_weaken_any, canon_idem Γ hc]
        rfl

end Nominal.FCn

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The walk read on the runtime (X3 g3)

`canon_lookup` and `canon_cyclic` compare the closed reading with the runtime.  The lemmas from
`Store.erase_get` to `Runtime.Rhs.substPath_var` are the prototype's (`C0_Final.lean:2315-2357`,
`:2499-2502`), moved here from X4 g3's list. -/

theorem Store.erase_get : ∀ (σ : Store s) (x : BVar s .var), σ.erase.get x = (σ.get x).erase
  | .cons σ v, .here => by
      show (v.erase).rename Rename.succ = (v.rename Rename.succ).erase
      rw [Value.erase_rename]
  | .cons σ v, .there y => by
      show (σ.erase.get y).rename Rename.succ = ((σ.get y).rename Rename.succ).erase
      rw [Store.erase_get σ y, Value.erase_rename]

/-! ## The field at a label -/

def Defs.getFld : Defs s → Label → Option (Rhs s)
  | .nil, _ => none
  | .typ ds _ _, a => ds.getFld a
  | .fld ds a' rhs, a => if a' = a then some rhs else ds.getFld a
  | .cls ds _ _, a => ds.getFld a

theorem Defs.erase_getFld : ∀ (ds : Defs s) (a : Label), ds.erase.get a = (ds.getFld a).map Rhs.erase
  | .nil, _ => rfl
  | .typ ds _ _, a => Defs.erase_getFld ds a
  | .cls ds _ _, a => Defs.erase_getFld ds a
  | .fld ds a' rhs, a => by
      simp only [Defs.erase, PDot.Runtime.Defs.get, Defs.getFld]
      split
      · rfl
      · exact Defs.erase_getFld ds a

theorem Defs.getFld_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂) (a : Label),
    (ds.rename ρ).getFld a = (ds.getFld a).map (·.rename ρ)
  | .nil, _, _ => rfl
  | .typ ds _ _, ρ, a => Defs.getFld_rename ds ρ a
  | .cls ds _ _, ρ, a => Defs.getFld_rename ds ρ a
  | .fld ds a' rhs, ρ, a => by
      simp only [Defs.rename, Defs.getFld]
      split
      · rfl
      · exact Defs.getFld_rename ds ρ a

theorem Defs.kids_get_of_getFld : ∀ (ds : Defs s) (a : Label) (rhs : Rhs s), ds.getFld a = some rhs →
    ds.kids.get a = some rhs.child
  | .nil, _, _, h => by cases h
  | .typ ds _ _, a, rhs, h => Defs.kids_get_of_getFld ds a rhs h
  | .cls ds _ _, a, rhs, h => Defs.kids_get_of_getFld ds a rhs h
  | .fld ds a' rhs', a, rhs, h => by
      simp only [Defs.getFld] at h
      simp only [Defs.kids, Kids.get]
      by_cases e : a' = a
      · rw [if_pos e] at h; cases h; rw [if_pos e.symm]
      · rw [if_neg e] at h; rw [if_neg (Ne.symm e)]; exact Defs.kids_get_of_getFld ds a rhs h

theorem Runtime.Rhs.substPath_var (r : PDot.Runtime.Rhs (s,x)) (x : BVar s .var) :
    r.substPath (.var x) = r.rename (Rename.subst x) := by
  rw [PDot.Runtime.Rhs.substPath, PathSubst.one_var, PDot.Runtime.Rhs.subst_ofRename]

/-! ## Nodes of a typed store (new) -/

/-- The converse of `Defs.kids_get_of_getFld`. -/
theorem Defs.getFld_of_kids_get : ∀ (ds : Defs s) (a : Label) (B : Block s), ds.kids.get a = some B →
    ∃ rhs, ds.getFld a = some rhs ∧ rhs.child = B
  | .nil, _, _, h => by cases h
  | .typ ds _ _, a, B, h => Defs.getFld_of_kids_get ds a B h
  | .cls ds _ _, a, B, h => Defs.getFld_of_kids_get ds a B h
  | .fld ds a' rhs, a, B, h => by
      simp only [Defs.kids, Kids.get] at h
      simp only [Defs.getFld]
      by_cases e : a' = a
      · rw [if_pos e.symm] at h
        cases h
        exact ⟨rhs, by rw [if_pos e], rfl⟩
      · rw [if_neg (Ne.symm e)] at h
        rw [if_neg e]
        exact Defs.getFld_of_kids_get ds a B h

/-- The node of the context at `l` is the block of the definitions `dsF`, and each field of `dsF`
is one lookup step from `l.a` in the erased store. -/
structure NodeFacts (σ : Store s) (Γ : Ctx s) (l : Path s) (dsF : Defs s) : Prop where
  node : Γ.nodeAt l = some dsF.block
  fld : ∀ a rhs, dsF.getFld a = some rhs → PDot.Runtime.LStep σ.erase (.defp (l.sel a)) rhs.erase

/-- A literal of a typed store is a node at its variable (`C0_Final.lean:2504-2535`, the fields
`node` and `fld` of `Store.Typed.locFacts`). -/
theorem Store.Typed.nodeFacts_var {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {x : BVar s .var}
    {Tel : Telescope (s,x)} {ds : Defs (s,x)} (hx : σ.get x = .obj Tel ds) :
    NodeFacts σ Γ (.var x) (ds.rename (Rename.subst x)) where
  node := by
    rcases hσ.get_shape x with ⟨S, t, T, e, _, _⟩ | ⟨Tel', ds', e, _, hb⟩
    · rw [hx] at e; cases e
    · rw [hx] at e
      injection e with _ _ e2
      show Γ.blockAt x = _
      rw [hb, e2]
  fld := fun a rhs ha => by
    have hv : σ.erase.get x = .new ds.erase := by rw [Store.erase_get, hx]; rfl
    rw [Defs.getFld_rename] at ha
    cases h0 : ds.getFld a with
    | none => rw [h0] at ha; cases ha
    | some rhs₀ =>
        rw [h0] at ha
        cases ha
        have h1 : PDot.Runtime.LStep σ.erase (.defp (.var x)) (.defv (.new ds.erase)) := by rw [← hv]; exact .var
        have h2 := PDot.Runtime.LStep.selV (a := a) (r := rhs₀.erase) h1 (by rw [Defs.erase_getFld, h0]; rfl)
        rw [Runtime.Rhs.substPath_var, ← Rhs.erase_rename] at h2
        exact h2

/-- The child of a node at a nested field is a node (`C0_Final.lean:2432-2450`, the fields `node`
and `fld` of `LocFacts.nest`). -/
theorem NodeFacts.nest {σ : Store s} {Γ : Ctx s} {l : Path s} {dsF : Defs s} (hL : NodeFacts σ Γ l dsF)
    {a : Label} {Tel' : Telescope (s,x)} {ds' : Defs s} (ha : dsF.getFld a = some (.nest Tel' ds')) :
    NodeFacts σ Γ (l.sel a) ds' where
  node := by
    show (Γ.nodeAt l).bind (·.child a) = _
    rw [hL.node]
    show dsF.kids.get a = _
    rw [Defs.kids_get_of_getFld dsF a _ ha]
    rfl
  fld := fun b rhs hb => by
    have h1 : PDot.Runtime.LStep σ.erase (.defp (l.sel a)) (.nest ds'.erase) := hL.fld a _ ha
    refine .selN h1 ?_
    rw [Defs.erase_getFld, hb]
    rfl

/-- Every node of a typed store's context is the block of some definitions, with their facts. -/
theorem Store.Typed.nodeFacts {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    ∀ (l : Path s) {W : TyDefs s} {C : Kids s}, Γ.nodeAt l = some (.node W C) →
      ∃ dsF, dsF.block = .node W C ∧ NodeFacts σ Γ l dsF
  | .var x, W, C, h => by
      have h' : Γ.blockAt x = some (.node W C) := h
      rcases hσ.get_shape x with ⟨_, _, _, _, _, hb⟩ | ⟨Tel, ds, e, _, hb⟩
      · rw [hb] at h'; cases h'
      · rw [hb] at h'
        injection h' with h''
        exact ⟨_, h'', hσ.nodeFacts_var e⟩
  | .sel l a, W, C, h => by
      have h' : (Γ.nodeAt l).bind (·.child a) = some (.node W C) := h
      cases hl : Γ.nodeAt l with
      | none => rw [hl] at h'; cases h'
      | some B =>
          rw [hl] at h'
          cases B with
          | fwd _ => cases h'
          | clo => cases h'
          | node W₀ C₀ =>
              obtain ⟨dsF, hb, hF⟩ := Store.Typed.nodeFacts hσ l hl
              have hk : dsF.kids.get a = some (.node W C) := by
                have e : Block.node dsF.tyDefs dsF.kids = .node W₀ C₀ := hb
                injection e with _ e2
                rw [e2]
                exact h'
              obtain ⟨rhs, hr, hc⟩ := Defs.getFld_of_kids_get dsF a _ hk
              cases rhs with
              | path P => cases hc
              | fn v => cases hc
              | nest Tel' ds' => exact ⟨ds', hc, hF.nest hr⟩

/-- A forwarding child is one lookup step from its path to its target. -/
theorem Store.Typed.fwd_step {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {l q : Path s} {W : TyDefs s}
    {C : Kids s} {a : Label} (hl : Γ.nodeAt l = some (.node W C)) (ha : C.get a = some (.fwd q)) :
    PDot.Runtime.LStep σ.erase (.defp (.sel l a)) (.defp q) := by
  obtain ⟨dsF, hb, hF⟩ := hσ.nodeFacts l hl
  have hk : dsF.kids.get a = some (.fwd q) := by
    have e : Block.node dsF.tyDefs dsF.kids = .node W C := hb
    injection e with _ e2
    rw [e2]
    exact ha
  obtain ⟨rhs, hr, hc⟩ := Defs.getFld_of_kids_get dsF a _ hk
  cases rhs with
  | path P =>
      have hq : P.path = q := by
        have e : Block.fwd P.path = .fwd q := hc
        injection e
      have h2 := hF.fld a _ hr
      rw [← hq]
      exact h2
  | fn v => cases hc
  | nest _ _ => cases hc

/-- No variable of a typed store's context holds a forward. -/
theorem Store.Typed.blockAt_ne_fwd {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) (x : BVar s .var)
    (q : Path s) : Γ.blockAt x ≠ some (.fwd q) := by
  intro h
  rcases hσ.get_shape x with ⟨_, _, _, _, _, hb⟩ | ⟨_, _, _, _, hb⟩
  · rw [hb] at h; cases h
  · rw [hb] at h; cases h

/-! ## Where the walk lands, and how it gets there -/

/-- A landing with a block is the node of the context at its path. -/
theorem canonFuel_nodeAt (Γ : Ctx s) : ∀ (n : Nat) (p c : Path s) (B : Block s),
    canonFuel Γ n p = some (c, some B) → Γ.nodeAt c = some B := by
  intro n
  induction n with
  | zero => intro p c B h; cases h
  | succ n ihn =>
    intro p
    induction p with
    | var x =>
        intro c B h
        have h' : canonPass Γ (canonFuel Γ n) (.var x) = some (c, some B) := h
        simp only [canonPass] at h'
        cases hx : Γ.blockAt x with
        | none => rw [hx] at h'; cases h'
        | some B₀ =>
            rw [hx] at h'
            cases B₀ with
            | node W C => cases h'; exact hx
            | clo => cases h'; exact hx
            | fwd q => exact ihn q c B h'
    | sel p a ihp =>
        intro c B h
        have h' : canonPass Γ (canonFuel Γ n) (.sel p a) = some (c, some B) := h
        simp only [canonPass] at h'
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rw [hp] at h'; cases h'
        | some l =>
            obtain ⟨c', b'⟩ := l
            rw [hp] at h'
            cases b' with
            | none => cases h'
            | some B' =>
                cases B' with
                | clo => cases h'
                | fwd r => cases h'
                | node W C =>
                    have hc' : Γ.nodeAt c' = some (.node W C) := ihp c' (.node W C) hp
                    simp only at h'
                    cases ha : C.get a with
                    | none => rw [ha] at h'; cases h'
                    | some B'' =>
                        rw [ha] at h'
                        cases B'' with
                        | node W' C' =>
                            cases h'
                            show (Γ.nodeAt c').bind (·.child a) = _
                            rw [hc']
                            exact ha
                        | clo =>
                            cases h'
                            show (Γ.nodeAt c').bind (·.child a) = _
                            rw [hc']
                            exact ha
                        | fwd q => exact ihn q c B h'

/-- The walk at any fuel follows lookup in the erased store. -/
theorem canonFuel_lookups {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) : ∀ (n : Nat) (p c : Path s)
    (b : Option (Block s)), canonFuel Γ n p = some (c, b) → PDot.Runtime.Lookups σ.erase (.defp p) (.defp c) := by
  intro n
  induction n with
  | zero => intro p c b h; cases h
  | succ n ihn =>
    intro p
    induction p with
    | var x =>
        intro c b h
        have h' : canonPass Γ (canonFuel Γ n) (.var x) = some (c, b) := h
        simp only [canonPass] at h'
        cases hx : Γ.blockAt x with
        | none => rw [hx] at h'; cases h'; exact .refl
        | some B₀ =>
            rw [hx] at h'
            cases B₀ with
            | node W C => cases h'; exact .refl
            | clo => cases h'; exact .refl
            | fwd q => exact absurd hx (hσ.blockAt_ne_fwd x q)
    | sel p a ihp =>
        intro c b h
        have h' : canonPass Γ (canonFuel Γ n) (.sel p a) = some (c, b) := h
        simp only [canonPass] at h'
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rw [hp] at h'; cases h'
        | some l =>
            obtain ⟨c', b'⟩ := l
            rw [hp] at h'
            have hl : PDot.Runtime.Lookups σ.erase (.defp p) (.defp c') := ihp c' b' hp
            cases b' with
            | none => cases h'; exact PDot.Runtime.Lookups.sel_path a hl
            | some B' =>
                cases B' with
                | clo => cases h'; exact PDot.Runtime.Lookups.sel_path a hl
                | fwd r => cases h'; exact PDot.Runtime.Lookups.sel_path a hl
                | node W C =>
                    have hc' : Γ.nodeAt c' = some (.node W C) := canonFuel_nodeAt Γ (n+1) p c' (.node W C) hp
                    simp only at h'
                    cases ha : C.get a with
                    | none => rw [ha] at h'; cases h'; exact PDot.Runtime.Lookups.sel_path a hl
                    | some B'' =>
                        rw [ha] at h'
                        cases B'' with
                        | node W' C' => cases h'; exact PDot.Runtime.Lookups.sel_path a hl
                        | clo => cases h'; exact PDot.Runtime.Lookups.sel_path a hl
                        | fwd q =>
                            exact (PDot.Runtime.Lookups.sel_path a hl).trans
                              (.step (hσ.fwd_step hc' ha) (ihn q c b h'))

/-- `canon_lookup`: the name of a path is reached from it by lookup. -/
theorem canon_lookup {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {p c : Path s} (h : Γ.canon p = some c) :
    PDot.Runtime.Lookups σ.erase (.defp p) (.defp c) := by
  unfold Ctx.canon at h
  cases hw : Γ.canonWalk p with
  | none => rw [hw] at h; cases h
  | some l =>
      obtain ⟨c', b⟩ := l
      rw [hw] at h
      cases h
      exact canonFuel_lookups hσ _ p c' b hw

/-- A walk that lands away from its path starts with a lookup step to a path of the same name. -/
theorem canonFuel_first {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) : ∀ (n : Nat) (p c : Path s)
    (b : Option (Block s)), canonFuel Γ n p = some (c, b) →
      p = c ∨ ∃ p₁, PDot.Runtime.LStep σ.erase (.defp p) (.defp p₁) ∧ Γ.canon p₁ = Γ.canon p := by
  intro n
  induction n with
  | zero => intro p c b h; cases h
  | succ n ihn =>
    intro p
    induction p with
    | var x =>
        intro c b h
        have h' : canonPass Γ (canonFuel Γ n) (.var x) = some (c, b) := h
        simp only [canonPass] at h'
        cases hx : Γ.blockAt x with
        | none => rw [hx] at h'; cases h'; exact .inl rfl
        | some B₀ =>
            rw [hx] at h'
            cases B₀ with
            | node W C => cases h'; exact .inl rfl
            | clo => cases h'; exact .inl rfl
            | fwd q => exact absurd hx (hσ.blockAt_ne_fwd x q)
    | sel p a ihp =>
        intro c b h
        have h' : canonPass Γ (canonFuel Γ n) (.sel p a) = some (c, b) := h
        simp only [canonPass] at h'
        cases hp : canonPass Γ (canonFuel Γ n) p with
        | none => rw [hp] at h'; cases h'
        | some l =>
            obtain ⟨c', b'⟩ := l
            rw [hp] at h'
            rcases ihp c' b' hp with rfl | ⟨p₁, hs, he⟩
            · cases b' with
              | none => cases h'; exact .inl rfl
              | some B' =>
                  cases B' with
                  | clo => cases h'; exact .inl rfl
                  | fwd r => cases h'; exact .inl rfl
                  | node W C =>
                      have hc' : Γ.nodeAt p = some (.node W C) := canonFuel_nodeAt Γ (n+1) p p (.node W C) hp
                      simp only at h'
                      cases ha : C.get a with
                      | none => rw [ha] at h'; cases h'; exact .inl rfl
                      | some B'' =>
                          rw [ha] at h'
                          cases B'' with
                          | node W' C' => cases h'; exact .inl rfl
                          | clo => cases h'; exact .inl rfl
                          | fwd q => exact .inr ⟨q, hσ.fwd_step hc' ha, (canon_fwd Γ hc' ha).symm⟩
            · exact .inr ⟨p₁.sel a, .selP hs, canon_sel_congr Γ he a⟩

/-- A path named `none` takes a lookup step to a path named `none`. -/
theorem canon_none_step {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    ∀ (p : Path s), Γ.canon p = none → ∃ p', PDot.Runtime.LStep σ.erase (.defp p) (.defp p') ∧ Γ.canon p' = none
  | .var x, h => by
      exfalso
      rcases hσ.get_shape x with ⟨_, _, _, _, _, hb⟩ | ⟨_, _, _, _, hb⟩
      · rw [canon_opaque Γ hb] at h; cases h
      · rw [canon_node Γ (p := .var x) hb] at h; cases h
  | .sel p a, h => by
      have h0 := h
      rw [canon_sel] at h
      cases hc : Γ.canon p with
      | none =>
          obtain ⟨p', hs, hn⟩ := canon_none_step hσ p hc
          refine ⟨p'.sel a, .selP hs, ?_⟩
          rw [canon_sel, hn]
          rfl
      | some c =>
          rw [hc] at h
          have hc' := hc
          unfold Ctx.canon at hc'
          cases hw : Γ.canonWalk p with
          | none => rw [hw] at hc'; cases hc'
          | some l =>
              obtain ⟨c', b⟩ := l
              rw [hw] at hc'
              cases hc'
              rcases canonFuel_first hσ _ p c' b hw with rfl | ⟨p₁, hs, he⟩
              · have h1 : canonPass Γ (canonFuel Γ Γ.fwds.length) p = some (p, b) := hw
                have h2 : Γ.canon (.sel p a) = (canonPass Γ (canonFuel Γ Γ.fwds.length) (.sel p a)).map Prod.fst := rfl
                rw [h0] at h2
                simp only [canonPass, h1] at h2
                cases b with
                | none => cases h2
                | some B =>
                    cases B with
                    | clo => cases h2
                    | fwd r => cases h2
                    | node W C =>
                        have hn : Γ.nodeAt p = some (.node W C) := canonFuel_nodeAt Γ _ p p (.node W C) hw
                        simp only at h2
                        cases ha : C.get a with
                        | none => rw [ha] at h2; cases h2
                        | some B' =>
                            rw [ha] at h2
                            cases B' with
                            | node W' C' => cases h2
                            | clo => cases h2
                            | fwd q =>
                                refine ⟨q, hσ.fwd_step hn ha, ?_⟩
                                rw [← canon_fwd Γ hn ha]
                                exact h0
              · exact ⟨p₁.sel a, .selP hs, (canon_sel_congr Γ he a).trans h0⟩

/-- Lookup computed is lookup: the converse of `PDot.Runtime.LStep.of_lookPath`, in its equation form. -/
theorem lookPath_complete_of_eq {γ : PDot.Runtime.Store s} {r k : PDot.Runtime.Rhs s} (h : PDot.Runtime.LStep γ r k) :
    ∀ {p : Path s}, r = .defp p → PDot.Runtime.lookPath γ p = some k := by
  induction h with
  | var =>
      intro p e
      cases e
      rfl
  | @selP p₀ q₀ a₀ _ ih =>
      intro p e
      cases e
      simp only [PDot.Runtime.lookPath, ih rfl]
  | @selV p₀ ds₀ a₀ r₀ _ hg ih =>
      intro p e
      cases e
      simp only [PDot.Runtime.lookPath, ih rfl, hg]
      rfl
  | @selN p₀ ds₀ a₀ r₀ _ hg ih =>
      intro p e
      cases e
      simp only [PDot.Runtime.lookPath, ih rfl, hg]

theorem lookPath_complete {γ : PDot.Runtime.Store s} {p : Path s} {k : PDot.Runtime.Rhs s} (h : PDot.Runtime.LStep γ (.defp p) k) :
    PDot.Runtime.lookPath γ p = some k :=
  lookPath_complete_of_eq h rfl

/-- The lookup sequence from `p`, one computed step at a time. -/
def lookSeq (γ : PDot.Runtime.Store s) (p : Path s) : Nat → PDot.Runtime.Rhs s
  | 0 => .defp p
  | n+1 =>
      match lookSeq γ p n with
      | .defp q => (PDot.Runtime.lookPath γ q).getD (.defp q)
      | .defv v => .defv v
      | .nest ds => .nest ds

theorem lookSeq_succ_of_step {γ : PDot.Runtime.Store s} {p q q' : Path s} {n : Nat} (hq : lookSeq γ p n = .defp q)
    (hs : PDot.Runtime.LStep γ (.defp q) (.defp q')) : lookSeq γ p (n+1) = .defp q' := by
  show (match lookSeq γ p n with
    | .defp q => (PDot.Runtime.lookPath γ q).getD (.defp q)
    | .defv v => .defv v
    | .nest ds => .nest ds) = _
  rw [hq]
  simp only [lookPath_complete hs]
  rfl

/-- `canon_cyclic`: a path named `none` has an infinite lookup. -/
theorem canon_cyclic {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {p : Path s} (h : Γ.canon p = none) :
    PDot.Runtime.CyclicPath σ.erase p := by
  have inv : ∀ n, ∃ q, lookSeq σ.erase p n = .defp q ∧ Γ.canon q = none := by
    intro n
    induction n with
    | zero => exact ⟨p, rfl, h⟩
    | succ n ih =>
        obtain ⟨q, hq, hn⟩ := ih
        obtain ⟨q', hs, hn'⟩ := canon_none_step hσ q hn
        exact ⟨q', lookSeq_succ_of_step hq hs, hn'⟩
  refine ⟨lookSeq σ.erase p, rfl, fun n => ?_⟩
  obtain ⟨q, hq, hn⟩ := inv n
  obtain ⟨q', hs, _⟩ := canon_none_step hσ q hn
  rw [hq, lookSeq_succ_of_step hq hs]
  exact hs

end Nominal.FCn
