import Coercions.Separation.FCdot.Names
import Coercions.Separation.FCdot.Levels

namespace Separation

/-!
# Kills and names across a map of contexts

Plan V-D, S0.8, the kill half.  A renaming, a substitution or a refinement
carries every typing judgment from one context to another.  The term rules
of the separation line read four things that the older fields of those maps
do not carry: the flavour, the bit, the owners and the claims of a capture
binder, and the full names of a set.  This module states both as properties
of a map of capture atoms, so that renamings, substitutions and refinements
share them.

`Ctx.KillMap` is the evidence half.  It says that the map sends a consumable
binder to a consumable binder with a live bit when the source bit is live, and
that the map masks nothing that was live and unmasked.  It is a field of every
map record, and `ELeCo.packF` reads it.

`Ctx.NamesMap` is the term half.  It says that the full names of an image are
covered by the images of the full names, and it adds what a lift through a
binder needs to keep it: the innermost root goes to the innermost root, roots
are reflected, every binder a root of the target opens is the image of a
binder its source root opens, and claims are reflected.  It is a hypothesis of
the term lemmas and of no evidence lemma.

A kill changes bits and nothing else.  So names, claims and owners read the
same in a context and in any of its killed forms, and the maps between killed
contexts are built from the maps between the contexts they kill.
-/

namespace FCdot

/-! ## Lookups of capture binders -/

@[simp] theorem Ctx.lookupCap_here (Γ : Ctx s) (b : CapBound s) :
    (Ctx.consC Γ b).lookupCap .here = b↑ := rfl

@[simp] theorem Ctx.lookupCap_there (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Ctx.cons Γ b).lookupCap (.there κ) = (Γ.lookupCap κ)↑ := rfl

@[simp] theorem Ctx.lookupCap_thereC (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Ctx.consC Γ b).lookupCap (.there κ) = (Γ.lookupCap κ)↑ := rfl

/-! ## Ownership under weakening -/

theorem CapBound.ownsB_weaken (b : CapBound s) (κ : BVar s .cap) :
    (CapBound.weaken (k := k) b).ownsB (.there κ) = b.ownsB κ := by
  cases b <;> try rfl
  case own k₀ W =>
    show (CaptureSet.weaken (k := k) W).elem (CapAtom.weaken (k := k) (.cvar κ)) =
      W.elem (.cvar κ)
    rw [Bool.eq_iff_iff, CaptureSet.elem_iff, CaptureSet.elem_iff,
      CaptureSet.weaken_mem_weaken]

theorem CapBound.ownsB_weaken_here (b : CapBound s) :
    (CapBound.weaken (k := .cap) b).ownsB .here = false := by
  cases b <;> try rfl
  case own k₀ W =>
    show (CaptureSet.weaken (k := .cap) W).elem (.cvar .here) = false
    rw [Bool.eq_false_iff]
    intro h
    rw [CaptureSet.elem_iff, CaptureSet.mem_weaken] at h
    obtain ⟨y, -, hy⟩ := h
    exact CapAtom.cvar_here_ne_weaken y hy

theorem CapBound.ownsB_weaken_inv {b : CapBound s} {κ : BVar (s,,k) .cap}
    (h : (CapBound.weaken (k := k) b).ownsB κ = true) :
    ∃ κ₀, κ = .there κ₀ ∧ b.ownsB κ₀ = true := by
  cases b <;> simp [CapBound.weaken, CapBound.rename, CapBound.ownsB] at h
  case own k₀ W =>
    have h' : CapAtom.cvar κ ∈ CaptureSet.weaken (k := k) W :=
      (CaptureSet.elem_iff _).mp h
    obtain ⟨κ₀, rfl, hκ₀⟩ := CaptureSet.cvar_mem_weaken h'
    exact ⟨κ₀, rfl, (CaptureSet.elem_iff _).mpr hκ₀⟩

theorem CapBound.ownsB_eq_true {b : CapBound s} {κ : BVar s .cap} :
    b.ownsB κ = true ↔ ∃ k W, b = .own k W ∧ CapAtom.cvar κ ∈ W := by
  cases b
  case own k W =>
    constructor
    · intro h; exact ⟨k, W, rfl, (CaptureSet.elem_iff _).mp h⟩
    · rintro ⟨k', W', he, h⟩
      cases he
      exact (CaptureSet.elem_iff _).mpr h
  all_goals simp [CapBound.ownsB]

theorem Ctx.ownsB_cons_there (Γ : Ctx s) (b : Binding s) (h κ : BVar s .cap) :
    (Γ.cons b).ownsB (.there h) (.there κ) = Γ.ownsB h κ :=
  CapBound.ownsB_weaken (Γ.lookupCap h) κ

theorem Ctx.ownsB_consC_there (Γ : Ctx s) (b : CapBound s) (h κ : BVar s .cap) :
    (Γ.consC b).ownsB (.there h) (.there κ) = Γ.ownsB h κ :=
  CapBound.ownsB_weaken (Γ.lookupCap h) κ

theorem Ctx.ownsB_consC_here_there (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Γ.consC b).ownsB .here (.there κ) = b.ownsB κ :=
  CapBound.ownsB_weaken b κ

/-- Nobody owns the newest capture binder. -/
theorem Ctx.ownsB_consC_right_here (Γ : Ctx s) (b : CapBound s) (h : BVar (s,c) .cap) :
    (Γ.consC b).ownsB h .here = false := by
  cases h with
  | here => exact CapBound.ownsB_weaken_here b
  | there h₀ => exact CapBound.ownsB_weaken_here (Γ.lookupCap h₀)

/-- Ownership after a capture binder: the binder itself, or an old pair. -/
theorem Ctx.ownsB_consC_cases {Γ : Ctx s} {b : CapBound s} {h κ : BVar (s,c) .cap}
    (ho : (Γ.consC b).ownsB h κ = true) :
    (h = .here ∧ ∃ κ₀, κ = .there κ₀ ∧ b.ownsB κ₀ = true) ∨
      (∃ h₀ κ₀, h = .there h₀ ∧ κ = .there κ₀ ∧ Γ.ownsB h₀ κ₀ = true) := by
  cases κ with
  | here => rw [Ctx.ownsB_consC_right_here] at ho; cases ho
  | there κ₀ =>
      cases h with
      | here => exact Or.inl ⟨rfl, κ₀, rfl, by rwa [Ctx.ownsB_consC_here_there] at ho⟩
      | there h₀ => exact Or.inr ⟨h₀, κ₀, rfl, rfl, by rwa [Ctx.ownsB_consC_there] at ho⟩

/-- Ownership after a term binder: an old pair. -/
theorem Ctx.ownsB_cons_cases {Γ : Ctx s} {b : Binding s} {h κ : BVar (s,x) .cap}
    (ho : (Γ.cons b).ownsB h κ = true) :
    ∃ h₀ κ₀, h = .there h₀ ∧ κ = .there κ₀ ∧ Γ.ownsB h₀ κ₀ = true := by
  cases h with
  | there h₀ =>
      cases κ with
      | there κ₀ => exact ⟨h₀, κ₀, rfl, rfl, by rwa [Ctx.ownsB_cons_there] at ho⟩

/-- What an old binder owns after a capture binder is an old binder. -/
theorem Ctx.ownsB_consC_old {Γ : Ctx s} {b : CapBound s} {h₀ : BVar s .cap}
    {κ : BVar (s,c) .cap} (ho : (Γ.consC b).ownsB (.there h₀) κ = true) :
    ∃ κ₀, κ = .there κ₀ ∧ Γ.ownsB h₀ κ₀ = true := by
  rcases Ctx.ownsB_consC_cases ho with ⟨he, -⟩ | ⟨h₁, κ₀, he, rfl, ho₀⟩
  · cases he
  · cases he; exact ⟨κ₀, rfl, ho₀⟩

/-- A capture binder that is no heir owns nothing. -/
theorem CapBound.ownsB_of_not_own {b : CapBound s} (hb : ∀ k W, b ≠ .own k W)
    (κ : BVar s .cap) : b.ownsB κ = false := by
  cases b with
  | own k W => exact absurd rfl (hb k W)
  | _ => rfl

theorem Ctx.masked_iff {Γ : Ctx s} {κ : BVar s .cap} :
    Γ.Masked κ ↔ ∃ h, Γ.ownsB h κ = true := by
  unfold Ctx.Masked
  rw [List.any_eq_true]
  constructor
  · rintro ⟨h, -, hh⟩; exact ⟨h, hh⟩
  · rintro ⟨h, hh⟩; exact ⟨h, Γ.mem_capBinders h, hh⟩

theorem Ctx.masked_cons_iff (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Γ.cons b).Masked (.there κ) ↔ Γ.Masked κ := by
  rw [Ctx.masked_iff, Ctx.masked_iff]
  constructor
  · rintro ⟨h, hh⟩
    cases h with
    | there h₀ => exact ⟨h₀, by rwa [Ctx.ownsB_cons_there] at hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨.there h, by rw [Ctx.ownsB_cons_there]; exact hh⟩

theorem Ctx.masked_consC_iff (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Γ.consC b).Masked (.there κ) ↔ Γ.Masked κ ∨ b.ownsB κ = true := by
  rw [Ctx.masked_iff, Ctx.masked_iff]
  constructor
  · rintro ⟨h, hh⟩
    cases h with
    | here => exact Or.inr (by rwa [Ctx.ownsB_consC_here_there] at hh)
    | there h₀ => exact Or.inl ⟨h₀, by rwa [Ctx.ownsB_consC_there] at hh⟩
  · rintro (⟨h, hh⟩ | hb)
    · exact ⟨.there h, by rw [Ctx.ownsB_consC_there]; exact hh⟩
    · exact ⟨.here, by rw [Ctx.ownsB_consC_here_there]; exact hb⟩

theorem Ctx.not_masked_consC_here (Γ : Ctx s) (b : CapBound s) :
    ¬ (Γ.consC b).Masked .here := by
  rw [Ctx.masked_iff]
  rintro ⟨h, hh⟩
  rw [Ctx.ownsB_consC_right_here] at hh
  exact Bool.false_ne_true hh

/-! ## A kill changes the bit and nothing else -/

@[simp] theorem CapBound.consumable_kill (b : CapBound s) : b.kill.consumable = b.consumable := by
  cases b <;> rfl

@[simp] theorem CapBound.isRoot_kill (b : CapBound s) : b.kill.isRoot = b.isRoot := by
  cases b <;> rfl

@[simp] theorem CapBound.instSet?_kill (b : CapBound s) : b.kill.instSet? = b.instSet? := by
  cases b <;> rfl

@[simp] theorem CapBound.ownSet?_kill (b : CapBound s) : b.kill.ownSet? = b.ownSet? := by
  cases b <;> rfl

@[simp] theorem CapBound.ownsB_kill (b : CapBound s) (κ : BVar s .cap) :
    b.kill.ownsB κ = b.ownsB κ := by
  cases b <;> rfl

@[simp] theorem CapBound.kill_kill (b : CapBound s) : b.kill.kill = b.kill := by
  cases b <;> rfl

/-- A kill makes a consumable bound dead and leaves every other bound live. -/
theorem CapBound.live_kill (b : CapBound s) : b.kill.live = !b.consumable := by
  cases b <;> rfl

/-- A bound that is not consumable is live. -/
theorem CapBound.live_of_not_consumable {b : CapBound s} (h : b.consumable = false) :
    b.live = true := by
  cases b <;> simp_all [CapBound.consumable, CapBound.live]

/-- A bound that is not consumable is its own kill. -/
theorem CapBound.kill_of_not_consumable {b : CapBound s} (h : b.consumable = false) :
    b.kill = b := by
  cases b <;> simp_all [CapBound.consumable, CapBound.kill]

theorem CapBound.kill_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.kill).rename ρ = (b.rename ρ).kill := by
  cases b <;> rfl

/-- The claims of a bound, read as a function of the bound. -/
theorem Ctx.claimsB_eq (Γ : Ctx s) (h κ : BVar s .cap) :
    Γ.claimsB h κ =
      (match Γ.lookupCap h with
        | .own _ W => W.elem (.cvar κ)
        | .loc _ C => C.elem (.cvar κ)
        | .param _ => decide (h.depth < κ.depth)
        | _ => false) := rfl

/-- The bound of a binder after one kill. -/
theorem Ctx.lookupCap_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ κ₁ : BVar s .cap),
    (Γ.killAt κ).lookupCap κ₁ = if κ₁ = κ then (Γ.lookupCap κ₁).kill else Γ.lookupCap κ₁
  | _, .consC Γ b, .here, .here => by
      simp [Ctx.killAt, CapBound.weaken, CapBound.kill_rename]
  | _, .consC Γ b, .here, .there κ₁ => by
      simp [Ctx.killAt]
  | _, .consC Γ b, .there κ, .here => by
      simp [Ctx.killAt]
  | _, .consC Γ b, .there κ, .there κ₁ => by
      show ((Γ.killAt κ).lookupCap κ₁)↑ = _
      rw [Ctx.lookupCap_killAt Γ κ κ₁]
      by_cases h : κ₁ = κ
      · subst h; simp [CapBound.weaken, CapBound.kill_rename]
      · have h' : (BVar.there κ₁ : BVar (_,c) .cap) ≠ .there κ := fun e => h (BVar.there.inj e)
        simp [h, h']
  | _, .cons Γ b, .there κ, .there κ₁ => by
      show ((Γ.killAt κ).lookupCap κ₁)↑ = _
      rw [Ctx.lookupCap_killAt Γ κ κ₁]
      by_cases h : κ₁ = κ
      · subst h; simp [CapBound.weaken, CapBound.kill_rename]
      · have h' : (BVar.there κ₁ : BVar (_,x) .cap) ≠ .there κ := fun e => h (BVar.there.inj e)
        simp [h, h']

/-- The bound of a binder after a list of kills. -/
theorem Ctx.lookupCap_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (κ₁ : BVar s .cap) :
    (Γ.killNames D).lookupCap κ₁ = if κ₁ ∈ D then (Γ.lookupCap κ₁).kill else Γ.lookupCap κ₁ := by
  induction D generalizing Γ with
  | nil => simp [Ctx.killNames]
  | cons κ D ih =>
      show ((Γ.killAt κ).killNames D).lookupCap κ₁ = _
      rw [ih, Ctx.lookupCap_killAt]
      by_cases h₁ : κ₁ = κ
      · subst h₁; by_cases h₂ : κ₁ ∈ D <;> simp [h₂]
      · by_cases h₂ : κ₁ ∈ D <;> simp [h₁, h₂]

/-- Every flavour but the bit reads the same after a kill. -/
theorem Ctx.lookupCap_killNames_consumable (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    ((Γ.killNames D).lookupCap κ).consumable = (Γ.lookupCap κ).consumable := by
  rw [Ctx.lookupCap_killNames]; split <;> simp

theorem Ctx.lookupCap_killNames_isRoot (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    ((Γ.killNames D).lookupCap κ).isRoot = (Γ.lookupCap κ).isRoot := by
  rw [Ctx.lookupCap_killNames]; split <;> simp

theorem Ctx.lookupCap_killNames_instSet? (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    ((Γ.killNames D).lookupCap κ).instSet? = (Γ.lookupCap κ).instSet? := by
  rw [Ctx.lookupCap_killNames]; split <;> simp

theorem Ctx.lookupCap_killNames_ownSet? (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    ((Γ.killNames D).lookupCap κ).ownSet? = (Γ.lookupCap κ).ownSet? := by
  rw [Ctx.lookupCap_killNames]; split <;> simp

theorem Ctx.ownsB_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (h κ : BVar s .cap) :
    (Γ.killNames D).ownsB h κ = Γ.ownsB h κ := by
  unfold Ctx.ownsB
  rw [Ctx.lookupCap_killNames]; split <;> simp

theorem Ctx.claimsB_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (h κ : BVar s .cap) :
    (Γ.killNames D).claimsB h κ = Γ.claimsB h κ := by
  rw [Ctx.claimsB_eq, Ctx.claimsB_eq, Ctx.lookupCap_killNames]
  by_cases hD : h ∈ D
  · rw [if_pos hD]; cases Γ.lookupCap h <;> rfl
  · rw [if_neg hD]

/-- A binder is live after a kill exactly when it was live and is not a
consumable binder the kill lists. -/
theorem Ctx.bitLive_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    (Γ.killNames D).BitLive κ ↔
      Γ.BitLive κ ∧ ((Γ.lookupCap κ).consumable = true → κ ∉ D) := by
  unfold Ctx.BitLive
  rw [Ctx.lookupCap_killNames]
  by_cases hD : κ ∈ D
  · simp only [hD, if_true, CapBound.live_kill, not_true_eq_false, imp_false]
    cases hc : (Γ.lookupCap κ).consumable
    · simp [CapBound.live_of_not_consumable hc]
    · simp
  · simp [hD]

theorem Ctx.BitLive.of_killNames {Γ : Ctx s} {D : List (BVar s .cap)} {κ : BVar s .cap}
    (h : (Γ.killNames D).BitLive κ) : Γ.BitLive κ :=
  ((Γ.bitLive_killNames D κ).mp h).1

theorem Ctx.masked_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (κ : BVar s .cap) :
    (Γ.killNames D).Masked κ ↔ Γ.Masked κ := by
  rw [Ctx.masked_iff, Ctx.masked_iff]
  simp only [Ctx.ownsB_killNames]

/-! ### Effective liveness under kills and weakenings (plan-5h decision 39) -/

/-- An owner is an heir, a consumable binder. -/
theorem Ctx.consumable_of_ownsB {Γ : Ctx s} {h κ : BVar s .cap} (ho : Γ.ownsB h κ = true) :
    (Γ.lookupCap h).consumable = true := by
  unfold Ctx.ownsB at ho
  obtain ⟨k, W, hb, -⟩ := CapBound.ownsB_eq_true.mp ho
  rw [hb]; rfl

/-- Fewer kills keep effective liveness. -/
theorem Ctx.EffLive.revive {Γ : Ctx s} {D : List (BVar s .cap)} {κ : BVar s .cap}
    (h : (Γ.killNames D).EffLive κ) : Γ.EffLive κ := by
  induction h with
  | live hl => exact .live hl.of_killNames
  | owned ho _ ih => exact .owned (by rw [Ctx.ownsB_killNames] at ho; exact ho) ih

/-- Ownership reads no bit. -/
theorem Ctx.Owns.killNames {Γ : Ctx s} {D : List (BVar s .cap)} {h κ : BVar s .cap}
    (ho : Γ.Owns h κ) : (Γ.killNames D).Owns h κ := by
  induction ho with
  | direct hd => exact .direct (by rw [Ctx.ownsB_killNames]; exact hd)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Ctx.Owns.of_killNames {Γ : Ctx s} {D : List (BVar s .cap)} {h κ : BVar s .cap}
    (ho : (Γ.killNames D).Owns h κ) : Γ.Owns h κ := by
  induction ho with
  | direct hd => exact .direct (by rw [Ctx.ownsB_killNames] at hd; exact hd)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- A binder that is not consumable is live under every kill. -/
theorem Ctx.effLive_of_not_consumable {Γ : Ctx s} {D : List (BVar s .cap)} {κ : BVar s .cap}
    (hl : ∀ κ, (Γ.lookupCap κ).live = true) (hc : (Γ.lookupCap κ).consumable = false) :
    (Γ.killNames D).EffLive κ := by
  refine .live ((Γ.bitLive_killNames D κ).mpr ⟨hl κ, fun h => ?_⟩)
  rw [hc] at h; cases h

theorem Ctx.EffLive.weakenC {Γ : Ctx s} {κ : BVar s .cap} (h : Γ.EffLive κ) (b : CapBound s) :
    (Γ.consC b).EffLive (.there κ) := by
  induction h with
  | live hl =>
      refine .live ?_
      unfold Ctx.BitLive at hl ⊢
      rw [Ctx.lookupCap_thereC, CapBound.live_weaken]; exact hl
  | owned ho _ ih => exact .owned (by rw [Ctx.ownsB_consC_there]; exact ho) ih

theorem Ctx.EffLive.weaken {Γ : Ctx s} {κ : BVar s .cap} (h : Γ.EffLive κ) (b : Binding s) :
    (Γ.cons b).EffLive (.there κ) := by
  induction h with
  | live hl =>
      refine .live ?_
      unfold Ctx.BitLive at hl ⊢
      rw [Ctx.lookupCap_there, CapBound.live_weaken]; exact hl
  | owned ho _ ih => exact .owned (by rw [Ctx.ownsB_cons_there]; exact ho) ih

/-- An heir appended live makes every name it owns effectively live: the
unpack step revives the witness for access, while its bit stays killed for
consumption. -/
theorem Ctx.EffLive.of_heir {Γ : Ctx s} {W : CaptureSet s} {κ : BVar s .cap}
    (hW : CapAtom.cvar κ ∈ W) : (Γ.consC (.own true W)).EffLive (.there κ) := by
  refine .owned (h := .here) ?_ (.live rfl)
  rw [Ctx.ownsB_consC_here_there]
  show (CapBound.own true W).ownsB κ = true
  simp only [CapBound.ownsB]
  exact (CaptureSet.elem_iff _).mpr hW

/-! ### The spine of a killed context

A kill touches no term binder, no root and no instance, so every lookup of the
spine reads the same. -/

theorem Ctx.killAt_cons (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Γ.cons b).killAt (.there κ) = (Γ.killAt κ).cons b := rfl

theorem Ctx.killAt_consC (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Γ.consC b).killAt (.there κ) = (Γ.killAt κ).consC b := rfl

/-- Killing the weakened list in an extended context is killing in the prefix. -/
theorem Ctx.killNames_cons (Γ : Ctx s) (b : Binding s) (D : List (BVar s .cap)) :
    (Γ.cons b).killNames (D.map .there) = (Γ.killNames D).cons b := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.cons b).killAt (.there κ)).killNames (D.map .there) = _
      rw [Ctx.killAt_cons, ih]
      rfl

theorem Ctx.killNames_consC (Γ : Ctx s) (b : CapBound s) (D : List (BVar s .cap)) :
    (Γ.consC b).killNames (D.map .there) = (Γ.killNames D).consC b := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.consC b).killAt (.there κ)).killNames (D.map .there) = _
      rw [Ctx.killAt_consC, ih]
      rfl

theorem Ctx.killNames_append (Γ : Ctx s) (D D' : List (BVar s .cap)) :
    Γ.killNames (D ++ D') = (Γ.killNames D).killNames D' := by
  simp [Ctx.killNames, List.foldl_append]

/-- A property of contexts that one kill keeps is kept by a list of kills. -/
theorem Ctx.killNames_induct {P : Ctx s → Prop} (hP : ∀ Δ κ, P Δ → P (Δ.killAt κ)) :
    ∀ (Γ : Ctx s) (D : List (BVar s .cap)), P Γ → P (Γ.killNames D)
  | _, [], h => h
  | Γ, κ :: D, h => Ctx.killNames_induct hP (Γ.killAt κ) D (hP Γ κ h)

theorem Ctx.lookupTy_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) (x : BVar s .var),
    (Γ.killAt κ).lookupTy x = Γ.lookupTy x
  | _, .consC Γ b, .here, .there x => rfl
  | _, .consC Γ b, .there κ, .there x => by
      show ((Γ.killAt κ).lookupTy x)↑ = (Γ.lookupTy x)↑
      rw [Ctx.lookupTy_killAt Γ κ x]
  | _, .cons Γ b, .there κ, .here => rfl
  | _, .cons Γ b, .there κ, .there x => by
      show ((Γ.killAt κ).lookupTy x)↑ = (Γ.lookupTy x)↑
      rw [Ctx.lookupTy_killAt Γ κ x]

theorem Ctx.lookupDef_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) (x : BVar s .var)
    (l : Label), (Γ.killAt κ).lookupDef x l = Γ.lookupDef x l
  | _, .consC Γ b, .here, .there x, l => rfl
  | _, .consC Γ b, .there κ, .there x, l => by
      show ((Γ.killAt κ).lookupDef x l).map Shape.weaken = (Γ.lookupDef x l).map Shape.weaken
      rw [Ctx.lookupDef_killAt Γ κ x l]
  | _, .cons Γ b, .there κ, .here, l => by cases b <;> rfl
  | _, .cons Γ b, .there κ, .there x, l => by
      cases b <;>
      · show ((Γ.killAt κ).lookupDef x l).map Shape.weaken = (Γ.lookupDef x l).map Shape.weaken
        rw [Ctx.lookupDef_killAt Γ κ x l]

theorem Ctx.lookupDefC_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) (x : BVar s .var)
    (l : Label), (Γ.killAt κ).lookupDefC x l = Γ.lookupDefC x l
  | _, .consC Γ b, .here, .there x, l => rfl
  | _, .consC Γ b, .there κ, .there x, l => by
      show ((Γ.killAt κ).lookupDefC x l).map CaptureSet.weaken =
        (Γ.lookupDefC x l).map CaptureSet.weaken
      rw [Ctx.lookupDefC_killAt Γ κ x l]
  | _, .cons Γ b, .there κ, .here, l => by cases b <;> rfl
  | _, .cons Γ b, .there κ, .there x, l => by
      cases b <;>
      · show ((Γ.killAt κ).lookupDefC x l).map CaptureSet.weaken =
          (Γ.lookupDefC x l).map CaptureSet.weaken
        rw [Ctx.lookupDefC_killAt Γ κ x l]

theorem Ctx.lookupFields_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) (x : BVar s .var),
    (Γ.killAt κ).lookupFields x = Γ.lookupFields x
  | _, .consC Γ b, .here, .there x => rfl
  | _, .consC Γ b, .there κ, .there x => by
      show (Γ.killAt κ).lookupFields x = Γ.lookupFields x
      rw [Ctx.lookupFields_killAt Γ κ x]
  | _, .cons Γ b, .there κ, .here => by cases b <;> rfl
  | _, .cons Γ b, .there κ, .there x => by
      cases b <;>
      · show (Γ.killAt κ).lookupFields x = Γ.lookupFields x
        rw [Ctx.lookupFields_killAt Γ κ x]

theorem Ctx.root?_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.killAt κ).root? = Γ.root?
  | _, .consC Γ b, .here => by cases b <;> rfl
  | _, .consC Γ b, .there κ => by
      cases b <;> simp only [Ctx.killAt, Ctx.root?, Ctx.root?_killAt Γ κ]
  | _, .cons Γ b, .there κ => by
      simp only [Ctx.killAt, Ctx.root?, Ctx.root?_killAt Γ κ]

theorem Ctx.lvl_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) {k : Kind} (y : BVar s k),
    (Γ.killAt κ).lvl y = Γ.lvl y
  | _, .consC Γ b, .here, _, .here => by cases b <;> rfl
  | _, .consC Γ b, .here, _, .there y => by cases b <;> rfl
  | _, .consC Γ b, .there κ, _, .here => by
      cases b <;> simp only [Ctx.killAt, Ctx.lvl, Ctx.root?_killAt Γ κ]
  | _, .consC Γ b, .there κ, _, .there y => by
      cases b <;> simp only [Ctx.killAt, Ctx.lvl, Ctx.lvl_killAt Γ κ y]
  | _, .cons Γ b, .there κ, _, .here => by
      simp only [Ctx.killAt, Ctx.lvl, Ctx.root?_killAt Γ κ]
  | _, .cons Γ b, .there κ, _, .there y => by
      simp only [Ctx.killAt, Ctx.lvl, Ctx.lvl_killAt Γ κ y]

theorem Ctx.capBinders_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.killAt κ).capBinders = Γ.capBinders
  | _, .consC Γ b, .here => rfl
  | _, .consC Γ b, .there κ => by
      simp only [Ctx.killAt, Ctx.capBinders, Ctx.capBinders_killAt Γ κ]
  | _, .cons Γ b, .there κ => by
      simp only [Ctx.killAt, Ctx.capBinders, Ctx.capBinders_killAt Γ κ]

theorem Ctx.formalFree_killAt : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.killAt κ).formalFree = Γ.formalFree
  | _, .consC Γ b, .here => rfl
  | _, .consC Γ b, .there κ => by
      simp only [Ctx.killAt, Ctx.formalFree, Ctx.formalFree_killAt Γ κ]
  | _, .cons Γ b, .there κ => by
      simp only [Ctx.killAt, Ctx.formalFree, Ctx.formalFree_killAt Γ κ]

theorem Ctx.lookupTy_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (x : BVar s .var) :
    (Γ.killNames D).lookupTy x = Γ.lookupTy x := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih => show ((Γ.killAt κ).killNames D).lookupTy x = _; rw [ih, Ctx.lookupTy_killAt]

theorem Ctx.lookupDef_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (x : BVar s .var)
    (l : Label) : (Γ.killNames D).lookupDef x l = Γ.lookupDef x l := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih => show ((Γ.killAt κ).killNames D).lookupDef x l = _; rw [ih, Ctx.lookupDef_killAt]

theorem Ctx.lookupDefC_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (x : BVar s .var)
    (l : Label) : (Γ.killNames D).lookupDefC x l = Γ.lookupDefC x l := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.killAt κ).killNames D).lookupDefC x l = _; rw [ih, Ctx.lookupDefC_killAt]

theorem Ctx.lookupFields_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (x : BVar s .var) :
    (Γ.killNames D).lookupFields x = Γ.lookupFields x := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.killAt κ).killNames D).lookupFields x = _; rw [ih, Ctx.lookupFields_killAt]

theorem Ctx.root?_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).root? = Γ.root? := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih => show ((Γ.killAt κ).killNames D).root? = _; rw [ih, Ctx.root?_killAt]

theorem Ctx.lvl_killNames (Γ : Ctx s) (D : List (BVar s .cap)) {k : Kind} (y : BVar s k) :
    (Γ.killNames D).lvl y = Γ.lvl y := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih => show ((Γ.killAt κ).killNames D).lvl y = _; rw [ih, Ctx.lvl_killAt]

theorem Ctx.capBinders_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).capBinders = Γ.capBinders := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih => show ((Γ.killAt κ).killNames D).capBinders = _; rw [ih, Ctx.capBinders_killAt]

theorem Ctx.formalFree_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).formalFree = Γ.formalFree := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.killAt κ).killNames D).formalFree = _; rw [ih, Ctx.formalFree_killAt]

theorem Ctx.rootAtom_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).rootAtom = Γ.rootAtom := by
  unfold Ctx.rootAtom; rw [Ctx.root?_killNames]

theorem Ctx.lvlAtom_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s) :
    (Γ.killNames D).lvlAtom a = Γ.lvlAtom a := by
  induction a <;> simp_all [Ctx.lvlAtom, Ctx.lvl_killNames]

theorem Ctx.lvlLeB_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (e r : CapAtom s) :
    (Γ.killNames D).lvlLeB e r = Γ.lvlLeB e r := by
  unfold Ctx.lvlLeB; rw [Ctx.lvlAtom_killNames]

theorem Ctx.isRootB_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s) :
    (Γ.killNames D).isRootB a = Γ.isRootB a := by
  cases a <;> simp [Ctx.isRootB, Ctx.lookupCap_killNames_isRoot]

theorem Ctx.instSet?_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s) :
    (Γ.killNames D).instSet? a = Γ.instSet? a := by
  cases a <;> simp [Ctx.instSet?, Ctx.lookupCap_killNames_instSet?]

theorem Ctx.ownSet?_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s) :
    (Γ.killNames D).ownSet? a = Γ.ownSet? a := by
  cases a <;> simp [Ctx.ownSet?, Ctx.lookupCap_killNames_ownSet?]

/-- A location stays a location with some bit. -/
theorem Ctx.locBit?_killNames_isSome (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s) :
    ((Γ.killNames D).locBit? a).isSome = (Γ.locBit? a).isSome := by
  cases a <;> simp only [Ctx.locBit?]
  rename_i κ
  rw [Ctx.lookupCap_killNames]
  split
  · cases h : Γ.lookupCap κ with
    | loc k C => cases C <;> rfl
    | _ => rfl
  · rfl

theorem Ctx.rootAtom_killAt (Γ : Ctx s) (κ : BVar s .cap) :
    (Γ.killAt κ).rootAtom = Γ.rootAtom := by
  unfold Ctx.rootAtom; rw [Ctx.root?_killAt]

/-! ### Names read no bit -/

theorem Ctx.namesCapsP_killAt (p : Bool) : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.killAt κ).namesCapsP p = Γ.namesCapsP p
  | _, .consC Γ b, .here => by
      funext a
      show (Γ.consC b.kill).namesCapsP p a = (Γ.consC b).namesCapsP p a
      cases b <;>
        rcases a with ⟨_ | y⟩ | ⟨_ | κ₀⟩ | ⟨_ | y, l⟩ | _ | ⟨m, a⟩ <;> rfl
  | _, .consC Γ b, .there κ => by
      have ih := Ctx.namesCapsP_killAt p Γ κ
      funext a
      show ((Γ.killAt κ).consC b).namesCapsP p a = (Γ.consC b).namesCapsP p a
      cases b <;>
        rcases a with ⟨_ | y⟩ | ⟨_ | κ₀⟩ | ⟨_ | y, l⟩ | _ | ⟨m, a⟩ <;>
          simp only [Ctx.namesCapsP, ih]
  | _, .cons Γ b, .there κ => by
      have ih := Ctx.namesCapsP_killAt p Γ κ
      have hr := Ctx.rootAtom_killAt Γ κ
      funext a
      show ((Γ.killAt κ).cons b).namesCapsP p a = (Γ.cons b).namesCapsP p a
      cases b <;>
        rcases a with ⟨_ | y⟩ | ⟨_ | κ₀⟩ | ⟨_ | y, l⟩ | _ | ⟨m, a⟩ <;>
          simp only [Ctx.namesCapsP, ih, hr]

theorem Ctx.namesCapsP_killNames (p : Bool) (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).namesCapsP p = Γ.namesCapsP p := by
  induction D generalizing Γ with
  | nil => rfl
  | cons κ D ih =>
      show ((Γ.killAt κ).killNames D).namesCapsP p = _
      rw [ih, Ctx.namesCapsP_killAt]

theorem Ctx.expandNames_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).expandNames = Γ.expandNames := by
  funext a
  unfold Ctx.expandNames
  simp only [Ctx.isRootB_killNames, Ctx.capBinders_killNames, Ctx.lookupCap_killNames_isRoot]

theorem Ctx.namesAtom_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).namesAtom = Γ.namesAtom := by
  funext a
  unfold Ctx.namesAtom
  simp only [Ctx.namesCaps, Ctx.namesCapsP_killNames, Ctx.expandNames_killNames]

theorem Ctx.names_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).names C = Γ.names C := by
  unfold Ctx.names
  rw [Ctx.namesAtom_killNames]

/-! ### Accessibility over effective liveness (plan-5h decision 39) -/

/-- With no heir accessibility reads the bit. -/
theorem Ctx.accessible_iff_of_noHeir {Γ : Ctx s} (hn : ∀ h κ, Γ.ownsB h κ = false)
    {C : CaptureSet s} :
    Γ.Accessible C ↔ ∀ a ∈ Γ.names C, ∀ κ, a.base = .cvar κ → Γ.BitLive κ := by
  constructor
  · intro h a ha κ hκ; exact (Ctx.effLive_iff_of_noHeir hn).mp (h a ha κ hκ)
  · intro h a ha κ hκ; exact .live (h a ha κ hκ)

/-- Fewer kills keep accessibility. -/
theorem Ctx.Accessible.revive {Γ : Ctx s} {D : List (BVar s .cap)} {C : CaptureSet s}
    (h : (Γ.killNames D).Accessible C) : Γ.Accessible C := by
  intro a ha κ hκ
  rw [← Γ.names_killNames D] at ha
  exact (h a ha κ hκ).revive

/-- **The typing-time half of no use after consume** (plan-5h T0.10 (f)): over
a context with no heir, which every context of a checked program is, a
killed consumable binder is no name of an accessed set. -/
theorem Ctx.accessible_killed {Γ : Ctx s} {D : List (BVar s .cap)} {C : CaptureSet s}
    {κ : BVar s .cap} (hn : ∀ h κ, Γ.ownsB h κ = false)
    (h : (Γ.killNames D).Accessible C) (hκ : (Γ.lookupCap κ).consumable = true)
    (hD : κ ∈ D) : ∀ a ∈ Γ.names C, a.base ≠ .cvar κ := by
  intro a ha hb
  rw [← Γ.names_killNames D] at ha
  have hl := h a ha κ hb
  have hn' : ∀ h κ, (Γ.killNames D).ownsB h κ = false := fun h κ => by
    rw [Ctx.ownsB_killNames]; exact hn h κ
  rw [Ctx.effLive_iff_of_noHeir hn', Ctx.bitLive_killNames] at hl
  exact hl.2 hκ hD

theorem Ctx.consumedNames_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).consumedNames C = Γ.consumedNames C := by
  unfold Ctx.consumedNames
  rw [Ctx.names_killNames]

theorem Ctx.ownClosure_killNames (Γ : Ctx s) (D L : List (BVar s .cap)) :
    (Γ.killNames D).ownClosure L = Γ.ownClosure L := by
  unfold Ctx.ownClosure
  have hs : (Γ.killNames D).ownStep = Γ.ownStep := by
    funext L
    unfold Ctx.ownStep
    simp only [Ctx.capBinders_killNames, Ctx.claimsB_killNames]
  rw [hs, Ctx.capBinders_killNames]

theorem Ctx.modeCaps_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).modeCaps = Γ.modeCaps :=
  Ctx.namesCapsP_killNames true Γ D

theorem Ctx.namesCaps_killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    (Γ.killNames D).namesCaps = Γ.namesCaps :=
  Ctx.namesCapsP_killNames false Γ D

/-- **The kill of a let step.**  A head read under a kill context kills its
own consumed names on top of it, and names, consumed names and claims read no
bit. -/
theorem Ctx.killFor_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).killFor C = Γ.killNames (D ++ Γ.ownClosure (Γ.consumedNames C)) := by
  unfold Ctx.killFor
  rw [Ctx.consumedNames_killNames, Ctx.ownClosure_killNames, Ctx.killNames_append]

theorem Ctx.claimsFor_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).claimsFor C = Γ.claimsFor C := by
  unfold Ctx.claimsFor
  rw [Ctx.consumedNames_killNames, Ctx.ownClosure_killNames]

/-- The mode bounds read no bit. -/
theorem Ctx.modeBound_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (a : CapAtom s)
    (m : EMode) : (Γ.killNames D).ModeBound a m ↔ Γ.ModeBound a m := by
  unfold Ctx.ModeBound
  rw [Ctx.modeCaps_killNames]

theorem Ctx.ModeMap.killNames {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap f Γ') (D : List (BVar s1 .cap)) (D' : List (BVar s2 .cap)) :
    (Γ.killNames D).ModeMap f (Γ'.killNames D') := fun a m ha =>
  (Ctx.modeBound_killNames Γ' D' (f a) m).mpr (h a m ((Ctx.modeBound_killNames Γ D a m).mp ha))

theorem Ctx.accessOnly_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).AccessOnly C ↔ Γ.AccessOnly C := by
  unfold Ctx.AccessOnly Ctx.SetBound
  simp only [Ctx.modeBound_killNames]

/-! ## The evidence half: flavours, bits and owners -/

/-- A map injective on the members of a list without repeats makes a list
without repeats. -/
theorem CaptureSet.nodup_map_of_injOn {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hi, hd => by
      rw [List.nodup_cons] at hd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, CaptureSet.nodup_map_of_injOn
        (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hd.2⟩
      intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have hba := hi b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) he
      exact hd.1 (hba ▸ hb)

/-- A map of atoms keeps the flavour and the bit of every consumable binder,
sends it to a capture binder, is injective on consumable binders, and keeps
direct ownership between images.  Every renaming and substitution the tree
builds proves it by one weakening commutation, and `ELeCo.packF` reads it.
No judgment reads a mask (plan-5h decision 38), and effective liveness reads
ownership (decision 39). -/
structure Ctx.KillMap (Γ : Ctx s1) (f : CapAtom s1 → CapAtom s2) (Γ' : Ctx s2) : Prop where
  cvar : ∀ κ, (Γ.lookupCap κ).consumable = true → ∃ κ', f (.cvar κ) = .cvar κ'
  inj : ∀ κ₁ κ₂ κ', (Γ.lookupCap κ₁).consumable = true →
      f (.cvar κ₁) = .cvar κ' → f (.cvar κ₂) = .cvar κ' → κ₁ = κ₂
  cons : ∀ κ κ', (Γ.lookupCap κ).consumable = true → f (.cvar κ) = .cvar κ' →
      (Γ'.lookupCap κ').consumable = true
  live : ∀ κ κ', (Γ.lookupCap κ).consumable = true → f (.cvar κ) = .cvar κ' →
      Γ.BitLive κ → Γ'.BitLive κ'
  owns : ∀ h κ h' κ', f (.cvar h) = .cvar h' → f (.cvar κ) = .cvar κ' →
      Γ.ownsB h κ = true → Γ'.ownsB h' κ' = true

namespace Ctx.KillMap

variable {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}

/-- Two maps that agree on atoms agree as kill maps. -/
theorem congr (h : Γ.KillMap f Γ') {g : CapAtom s1 → CapAtom s2} (hg : ∀ a, g a = f a) :
    Γ.KillMap g Γ' := by
  have : g = f := funext hg
  subst this; exact h

/-- A consumable name goes to a consumable name. -/
theorem consumable (h : Γ.KillMap f Γ') {κ : BVar s1 .cap} {κ' : BVar s2 .cap}
    (hκ : Γ.Consumable κ) (hf : f (.cvar κ) = .cvar κ') : Γ'.Consumable κ' :=
  ⟨h.cons κ κ' hκ.1 hf, h.live κ κ' hκ.1 hf hκ.2⟩

/-- **The witness of a fresh pack under a map**: it stays a list of distinct
consumable names. -/
theorem packF (h : Γ.KillMap f Γ') {W : CaptureSet s1} (hN : W.IsNames) (hD : W.Nodup)
    (hc : ∀ κ : BVar s1 .cap, CapAtom.cvar κ ∈ W → Γ.Consumable κ) :
    CaptureSet.IsNames (W.map f) ∧ (W.map f).Nodup ∧
      ∀ κ' : BVar s2 .cap, CapAtom.cvar κ' ∈ W.map f → Γ'.Consumable κ' := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨κ, rfl⟩ := hN a₀ ha₀
    obtain ⟨κ', hκ'⟩ := h.cvar κ (hc κ ha₀).1
    exact ⟨κ', hκ'⟩
  · refine CaptureSet.nodup_map_of_injOn ?_ hD
    intro a₁ h₁ a₂ h₂ he
    obtain ⟨κ₁, rfl⟩ := hN a₁ h₁
    obtain ⟨κ₂, rfl⟩ := hN a₂ h₂
    obtain ⟨κ', hκ'⟩ := h.cvar κ₁ (hc κ₁ h₁).1
    rw [h.inj κ₁ κ₂ κ' (hc κ₁ h₁).1 hκ' (he ▸ hκ')]
  · intro κ' hκ'
    obtain ⟨a₀, ha₀, he⟩ := List.mem_map.mp hκ'
    obtain ⟨κ, rfl⟩ := hN a₀ ha₀
    exact h.consumable (hc κ ha₀) he

/-- Between killed contexts: a map keeps its evidence half when every target
kill is the image of a source kill, and the map is injective. -/
theorem killNames (h : Γ.KillMap f Γ') {D : List (BVar s1 .cap)} {D' : List (BVar s2 .cap)}
    (hinj : ∀ κ₁ κ₂ κ', f (.cvar κ₁) = .cvar κ' → f (.cvar κ₂) = .cvar κ' → κ₁ = κ₂)
    (hD : ∀ κ' ∈ D', ∃ κ ∈ D, f (.cvar κ) = .cvar κ') :
    (Γ.killNames D).KillMap f (Γ'.killNames D') where
  cvar κ hc := h.cvar κ (by rwa [Ctx.lookupCap_killNames_consumable] at hc)
  inj κ₁ κ₂ κ' h₁ := h.inj κ₁ κ₂ κ' (by rwa [Ctx.lookupCap_killNames_consumable] at h₁)
  cons κ κ' hc hf := by
    rw [Ctx.lookupCap_killNames_consumable] at hc ⊢
    exact h.cons κ κ' hc hf
  live κ κ' hc hf hl := by
    rw [Ctx.lookupCap_killNames_consumable] at hc
    rw [Ctx.bitLive_killNames] at hl ⊢
    refine ⟨h.live κ κ' hc hf hl.1, fun _ hmem => ?_⟩
    obtain ⟨κ₀, hκ₀, hf₀⟩ := hD κ' hmem
    rw [hinj κ₀ κ κ' hf₀ hf] at hκ₀
    exact hl.2 hc hκ₀
  owns h₀ κ h' κ' hh hk ho := by
    rw [Ctx.ownsB_killNames] at ho ⊢
    exact h.owns h₀ κ h' κ' hh hk ho

/-- **Effective liveness along a kill map**, given that the map keeps the
flavour of every capture binder it sends to a capture binder. -/
theorem effLive (h : Γ.KillMap f Γ')
    (hcons : ∀ κ κ', f (.cvar κ) = .cvar κ' →
      (Γ'.lookupCap κ').consumable = (Γ.lookupCap κ).consumable)
    {κ : BVar s1 .cap} (hl : Γ.EffLive κ) : ∀ κ', f (.cvar κ) = .cvar κ' → Γ'.EffLive κ' := by
  induction hl with
  | @live κ hb =>
      intro κ' hf
      cases hc : (Γ.lookupCap κ).consumable with
      | true => exact .live (h.live κ κ' hc hf hb)
      | false =>
          have hc' := hcons κ κ' hf
          rw [hc] at hc'
          exact .live (CapBound.live_of_not_consumable hc')
  | @owned h₀ κ ho _ ih =>
      intro κ' hf
      obtain ⟨h', hh'⟩ := h.cvar h₀ (Ctx.consumable_of_ownsB ho)
      exact .owned (h.owns h₀ κ h' κ' hh' hf ho) (ih h' hh')

end Ctx.KillMap

/-! ## The term half: full names -/

/-- A root is no consumable binder. -/
theorem CapBound.consumable_of_isRoot {b : CapBound s} (h : b.isRoot = true) :
    b.consumable = false := by
  cases b <;> simp_all [CapBound.isRoot, CapBound.consumable]

/-- A name whose base is a root is consumed by no set that passes the kill
premise, since a root is no consumable capture binder. -/
theorem Ctx.KillOk.not_root {Γ : Ctx s} {C : CaptureSet s} (hk : Γ.KillOk C)
    {y : CapAtom s} (hy : y ∈ Γ.names C) (hr : Γ.isRootB y.base = true)
    (hm : y.effMode = .consume) : False := by
  obtain ⟨κ, hb, hc⟩ := hk y hy hm
  rw [hb] at hr
  have : (Γ.lookupCap κ).isRoot = true := hr
  rw [CapBound.consumable_of_isRoot this] at hc
  cases hc

/-- A consumed name of a kill-ok set is a consumable binder. -/
theorem Ctx.KillOk.consumable_of_mem {Γ : Ctx s} {C : CaptureSet s} (hk : Γ.KillOk C)
    {l : BVar s .cap} (hl : l ∈ Γ.consumedNames C) : (Γ.lookupCap l).consumable = true := by
  obtain ⟨z, hz, hsel⟩ := List.mem_filterMap.mp hl
  obtain ⟨hm, hb⟩ := Ctx.leafFn_eq_some.mp hsel
  obtain ⟨κ, hκ, hc⟩ := hk z hz hm
  rw [hb] at hκ
  cases hκ
  exact hc

/-- A consumed name is in the closure of the consumed names. -/
theorem Ctx.mem_ownClosure_self {Γ : Ctx s} {L : List (BVar s .cap)} {l : BVar s .cap}
    (hl : l ∈ L) : l ∈ Γ.ownClosure L :=
  Ctx.mem_ownClosure.mpr (Or.inl hl)

/-- **A root among the names of a set opens every capture binder that is no
root** (plan-5h decision 38). -/
theorem Ctx.names_root_opens {Γ : Ctx s} {B : CaptureSet s} {y : CapAtom s}
    (hy : y ∈ Γ.names B) (hr : Γ.isRootB y.base = true) {κ : BVar s .cap}
    (hκ : (Γ.lookupCap κ).isRoot = false) : ∃ z ∈ Γ.names B, z.base = .cvar κ := by
  obtain ⟨c, hc, hyc⟩ := List.mem_flatMap.mp hy
  obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.mp hyc
  have hxr : Γ.isRootB x.base = true := by
    unfold Ctx.expandNames at hyx
    split at hyx
    · assumption
    · rw [List.mem_singleton.mp hyx] at hr; exact hr
  refine ⟨x.reapply (.cvar κ), List.mem_flatMap.mpr ⟨c, hc, List.mem_flatMap.mpr ⟨x, hx, ?_⟩⟩,
    by rw [CapAtom.base_reapply]; rfl⟩
  unfold Ctx.expandNames
  rw [if_pos hxr]
  refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨κ, List.mem_filter.mpr
    ⟨Γ.mem_capBinders κ, ?_⟩, rfl⟩)
  rw [hκ]; rfl

/-- A set whose names hold a root separates from a kill-ok set only if that
set consumes nothing. -/
theorem Ctx.ArgSep.not_consumed_of_root {Γ : Ctx s} {B C : CaptureSet s} (hS : Γ.ArgSep B C)
    (hk : Γ.KillOk C) {y : CapAtom s} (hy : y ∈ Γ.names B) (hr : Γ.isRootB y.base = true)
    {l : BVar s .cap} (hl : l ∈ Γ.consumedNames C) : False := by
  have hnr : (Γ.lookupCap l).isRoot = false := by
    cases h : (Γ.lookupCap l).isRoot with
    | false => rfl
    | true =>
        have := CapBound.consumable_of_isRoot h
        rw [hk.consumable_of_mem hl] at this; cases this
  obtain ⟨z, hz, hzb⟩ := Ctx.names_root_opens hy hr hnr
  exact (hS z hz l hzb).1 (Ctx.mem_ownClosure_self hl)

/-- A binder of the target that the map does not reach: no root, a live bit,
and no image.  A capture weakening appends one, and a root of the target
opens it.  No image claims it (`Ctx.NamesMap.fresh_not_claimed`). -/
def Ctx.NamesMap.Fresh (_Γ : Ctx s1) (f : CapAtom s1 → CapAtom s2) (Γ' : Ctx s2)
    (κ' : BVar s2 .cap) : Prop :=
  (Γ'.lookupCap κ').isRoot = false ∧ Γ'.BitLive κ' ∧ ∀ κ, f (.cvar κ) ≠ .cvar κ'

/-- **`Ctx.NamesMap Γ f Γ'`**: the full names of an image are covered by the
images of the full names (phase one field by field, phase two by opening
roots), with a mode at most the source's, up to fresh binders.  The other
fields are what a lift through a binder needs to keep it and what the kills
read: the innermost root goes to the innermost root, roots are reflected and
kept, every target capture binder is an image or fresh, the map is injective
and keeps flavours on capture binders, and claims of an image are images of
claims.  No field reads a level, since a root opens every binder that is no
root (plan-5h decision 38). -/
structure Ctx.NamesMap (Γ : Ctx s1) (f : CapAtom s1 → CapAtom s2) (Γ' : Ctx s2) : Prop where
  names : ∀ a z', z' ∈ Γ'.namesCaps (f a) →
      ∃ z ∈ Γ.namesCaps a, z'.base = f z.base ∧ z'.effMode ≤ z.effMode
  rootAtom : Γ'.rootAtom = f Γ.rootAtom
  rootRefl : ∀ x, Γ'.isRootB (f x) = true → Γ.isRootB x = true
  rootMap : ∀ x, Γ.isRootB x = true → Γ'.isRootB (f x) = true
  surj : ∀ κ', (∃ κ, f (.cvar κ) = .cvar κ') ∨ Ctx.NamesMap.Fresh Γ f Γ' κ'
  inj : ∀ κ₁ κ₂ κ', f (.cvar κ₁) = .cvar κ' → f (.cvar κ₂) = .cvar κ' → κ₁ = κ₂
  consEq : ∀ κ κ', f (.cvar κ) = .cvar κ' →
      (Γ'.lookupCap κ').consumable = (Γ.lookupCap κ).consumable
  claims : ∀ h h' κ', f (.cvar h) = .cvar h' → Γ'.claimsB h' κ' = true →
      ∃ κ, f (.cvar κ) = .cvar κ' ∧ Γ.claimsB h κ = true

/-- What the transports ask of the map of atoms itself: it commutes with the
base, keeps effective modes, never raises the use mode (a substitution may
send a capture binder to a term binder, plan-5h decision 39), and sends an
atom to a capture binder only from a capture binder.  Renamings and
substitutions whose capture images carry no mode satisfy it. -/
structure CapAtom.NameMapFn (f : CapAtom s1 → CapAtom s2) : Prop where
  base : ∀ a, (f a).base = f a.base
  effMode : ∀ a, (f a).effMode = a.effMode
  useMode : ∀ a, (f a).useMode ≤ a.useMode
  cvar : ∀ x κ', f x = .cvar κ' → ∃ κ, x = .cvar κ

namespace Ctx.NamesMap

variable {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}

/-- Two maps that agree on atoms agree as names maps. -/
theorem congr (h : Γ.NamesMap f Γ') {g : CapAtom s1 → CapAtom s2} (hg : ∀ a, g a = f a) :
    Γ.NamesMap g Γ' := by
  have : g = f := funext hg
  subst this; exact h

/-- No image claims a fresh binder. -/
theorem fresh_not_claimed (h : Γ.NamesMap f Γ') {κ' : BVar s2 .cap} (hκ' : Fresh Γ f Γ' κ')
    {h₀ : BVar s1 .cap} {h' : BVar s2 .cap} (hf : f (.cvar h₀) = .cvar h') :
    Γ'.claimsB h' κ' = false := by
  cases hc : Γ'.claimsB h' κ' with
  | false => rfl
  | true =>
      obtain ⟨κ, hκ, -⟩ := h.claims h₀ h' κ' hf hc
      exact absurd hκ (hκ'.2.2 κ)

/-- **The full names of an image are covered by the images of the full
names**, or are a fresh binder under a root of the source's names, at that
root's mode. -/
theorem namesAtom (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) :
    ∀ a z', z' ∈ Γ'.namesAtom (f a) →
      (∃ z ∈ Γ.namesAtom a, z'.base = f z.base ∧ z'.effMode ≤ z.effMode) ∨
      (∃ κ', z'.base = .cvar κ' ∧ Fresh Γ f Γ' κ' ∧
        ∃ y ∈ Γ.namesAtom a, Γ.isRootB y.base = true ∧ z'.effMode ≤ y.effMode) := by
  intro a z' hz'
  unfold Ctx.namesAtom at hz'
  obtain ⟨y', hy', hz'y⟩ := List.mem_flatMap.mp hz'
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy'
  rw [hf.base] at hx'
  obtain ⟨x, hx, hxb, hxe⟩ := h.names a.base x' hx'
  have hyb : ((f a).useApply x').base = f (a.useApply x).base := by
    rw [CapAtom.base_useApply, CapAtom.base_useApply, hxb]
  have hye : ((f a).useApply x').effMode ≤ (a.useApply x).effMode := by
    rw [CapAtom.effMode_useApply, CapAtom.effMode_useApply]
    exact EMode.le_trans (EMode.comb_mono_left (hf.useMode a) _) (EMode.comb_mono _ hxe)
  have hy : a.useApply x ∈ (Γ.namesCaps a.base).map a.useApply := List.mem_map_of_mem hx
  have hyN : a.useApply x ∈ Γ.namesAtom a :=
    List.mem_flatMap.mpr ⟨_, hy, Γ.mem_expandNames_self _⟩
  unfold Ctx.expandNames at hz'y
  split at hz'y
  · rename_i hroot
    rcases List.mem_cons.mp hz'y with rfl | hz'y
    · exact Or.inl ⟨a.useApply x, hyN, hyb, hye⟩
    · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hz'y
      obtain ⟨-, hκ'f⟩ := List.mem_filter.mp hκ'
      rw [Bool.not_eq_true'] at hκ'f
      rw [hyb] at hroot
      have hr := h.rootRefl _ hroot
      have hzb : (((f a).useApply x').reapply (CapAtom.cvar κ')).base = .cvar κ' := by
        simp only [CapAtom.reapply_eq, CapAtom.base_applyEMode, CapAtom.base]
      have hze : (((f a).useApply x').reapply (CapAtom.cvar κ')).effMode ≤
          (a.useApply x).effMode := by
        have hye' := hye
        simp only [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, CapAtom.effMode,
          EMode.comb_eps] at hye' ⊢
        exact hye'
      rcases h.surj κ' with ⟨κ, hκ⟩ | hfr
      · have hnr : (Γ.lookupCap κ).isRoot = false := by
          cases hr' : (Γ.lookupCap κ).isRoot with
          | false => rfl
          | true =>
              have := h.rootMap (.cvar κ) hr'
              rw [hκ] at this
              have h' : (Γ'.lookupCap κ').isRoot = true := this
              rw [hκ'f] at h'
              cases h'
        refine Or.inl ⟨(a.useApply x).reapply (.cvar κ), List.mem_flatMap.mpr ⟨_, hy, ?_⟩, ?_, ?_⟩
        · unfold Ctx.expandNames
          rw [if_pos hr]
          refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨κ, List.mem_filter.mpr
            ⟨Γ.mem_capBinders κ, ?_⟩, rfl⟩)
          rw [hnr]; rfl
        · rw [hzb]
          simp only [CapAtom.reapply_eq, CapAtom.base_applyEMode, CapAtom.base]
          exact hκ.symm
        · have hye' := hye
          simp only [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, CapAtom.effMode,
            EMode.comb_eps] at hye' ⊢
          exact hye'
      · exact Or.inr ⟨κ', hzb, hfr, a.useApply x, hyN, hr, hze⟩
  · rw [List.mem_singleton.mp hz'y]
    exact Or.inl ⟨a.useApply x, hyN, hyb, hye⟩

/-- The same for a set. -/
theorem names_cover (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) (C : CaptureSet s1) :
    ∀ z' ∈ Γ'.names (C.map f),
      (∃ z ∈ Γ.names C, z'.base = f z.base ∧ z'.effMode ≤ z.effMode) ∨
      (∃ κ', z'.base = .cvar κ' ∧ Fresh Γ f Γ' κ' ∧
        ∃ y ∈ Γ.names C, Γ.isRootB y.base = true ∧ z'.effMode ≤ y.effMode) := by
  intro z' hz'
  obtain ⟨c', hc', hz'c⟩ := List.mem_flatMap.mp hz'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  rcases h.namesAtom hf c z' hz'c with ⟨z, hz, hb, he⟩ | ⟨κ', hb, hfr, y, hy, hr, he⟩
  · exact Or.inl ⟨z, List.mem_flatMap.mpr ⟨c, hc, hz⟩, hb, he⟩
  · exact Or.inr ⟨κ', hb, hfr, y, List.mem_flatMap.mpr ⟨c, hc, hy⟩, hr, he⟩

theorem EMode.eq_consume_of_le {m : EMode} (h : EMode.consume ≤ m) : m = .consume := by
  revert h; cases m <;> decide

/-- A consuming name of an image of a kill-ok set is an image. -/
theorem names_cover_consume (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hk : Γ.KillOk C) {z' : CapAtom s2} (hz' : z' ∈ Γ'.names (C.map f))
    (hm : z'.effMode = .consume) :
    ∃ z ∈ Γ.names C, z'.base = f z.base ∧ z.effMode = .consume := by
  rcases h.names_cover hf C z' hz' with ⟨z, hz, hb, he⟩ | ⟨κ', -, -, y, hy, hr, he⟩
  · rw [hm] at he
    exact ⟨z, hz, hb, EMode.eq_consume_of_le he⟩
  · rw [hm] at he
    exact (hk.not_root hy hr (EMode.eq_consume_of_le he)).elim

/-- **Accessibility under a map.** -/
theorem accessible (h : Γ.NamesMap f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hA : Γ.Accessible C) : Γ'.Accessible (C.map f) := by
  intro z' hz' κ' hκ'
  rcases h.names_cover hf C z' hz' with ⟨z, hz, hb, -⟩ | ⟨κ'', hb, hfr, -⟩
  · rw [hκ'] at hb
    obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
    have hl := hA z hz κ hzκ
    rw [hzκ] at hb
    exact hk.effLive h.consEq hl κ' hb.symm
  · rw [hκ'] at hb
    cases hb
    exact .live hfr.2.1

/-- **Consumability under a map.** -/
theorem consumeOk (h : Γ.NamesMap f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.ConsumeOk C) : Γ'.ConsumeOk (C.map f) := by
  intro z' hz' hm
  obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf (Ctx.KillOk.of_consumeOk hK) hz' hm
  obtain ⟨κ, hzκ, hcons⟩ := hK z hz hzm
  obtain ⟨κ', hκ'⟩ := hk.cvar κ hcons.1
  refine ⟨κ', ?_, hk.consumable hcons hκ'⟩
  rw [hb, hzκ, hκ']

/-- **The kill premise under a map.** -/
theorem killOk (h : Γ.NamesMap f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.KillOk C) : Γ'.KillOk (C.map f) := by
  intro z' hz' hm
  obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf hK hz' hm
  obtain ⟨κ, hzκ, hcons⟩ := hK z hz hzm
  rw [hzκ] at hb
  obtain ⟨κ', hκ'⟩ := hk.cvar κ hcons
  exact ⟨κ', by rw [hb, hκ'], hk.cons κ κ' hcons hκ'⟩

/-- The consumed names of an image of a kill-ok set are images of consumed
names. -/
theorem consumedNames (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) {C : CaptureSet s1}
    (hk : Γ.KillOk C) :
    ∀ κ' ∈ Γ'.consumedNames (C.map f), ∃ κ ∈ Γ.consumedNames C, f (.cvar κ) = .cvar κ' := by
  intro κ' hκ'
  obtain ⟨z', hz', hsel⟩ := List.mem_filterMap.mp hκ'
  split at hsel
  · rename_i hm
    obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf hk hz' hm
    have hz'b : z'.base = .cvar κ' := by
      cases hzb : z'.base <;> rw [hzb] at hsel <;> simp [CapAtom.cvar?] at hsel
      rw [hsel]
    rw [hz'b] at hb
    obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
    refine ⟨κ, List.mem_filterMap.mpr ⟨z, hz, ?_⟩, by rw [← hzκ]; exact hb.symm⟩
    rw [if_pos hzm, hzκ]; rfl
  · cases hsel

/-- Possible ownership from an image lands in images. -/
theorem mayOwn (h : Γ.NamesMap f Γ') {h' κ' : BVar s2 .cap} (hm : Γ'.MayOwn h' κ') :
    ∀ h₀, f (.cvar h₀) = .cvar h' → ∃ κ, f (.cvar κ) = .cvar κ' ∧ Γ.MayOwn h₀ κ := by
  induction hm with
  | direct hd =>
      intro h₀ hf₀
      obtain ⟨κ, hκ, hcl⟩ := h.claims h₀ _ _ hf₀ hd
      exact ⟨κ, hκ, .direct hcl⟩
  | trans _ _ ih₁ ih₂ =>
      intro h₀ hf₀
      obtain ⟨c, hc, hm₁⟩ := ih₁ h₀ hf₀
      obtain ⟨κ, hκ, hm₂⟩ := ih₂ c hc
      exact ⟨κ, hκ, .trans hm₁ hm₂⟩

/-- The closure of images is the image of the closure. -/
theorem ownClosure (h : Γ.NamesMap f Γ') {L : List (BVar s1 .cap)} {L' : List (BVar s2 .cap)}
    (hL : ∀ κ' ∈ L', ∃ κ ∈ L, f (.cvar κ) = .cvar κ') :
    ∀ κ' ∈ Γ'.ownClosure L', ∃ κ ∈ Γ.ownClosure L, f (.cvar κ) = .cvar κ' := by
  intro κ' hκ'
  rcases Ctx.mem_ownClosure.mp hκ' with hmem | ⟨h', hh', hm⟩
  · obtain ⟨κ, hκ, hf⟩ := hL κ' hmem
    exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inl hκ), hf⟩
  · obtain ⟨h₀, hh₀, hf₀⟩ := hL h' hh'
    obtain ⟨κ, hκ, hm₀⟩ := h.mayOwn hm h₀ hf₀
    exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inr ⟨h₀, hh₀, hm₀⟩), hκ⟩

/-- The kill of an image of a kill-ok set is the image of the kill. -/
theorem killSet (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) {C : CaptureSet s1}
    (hk : Γ.KillOk C) :
    ∀ κ' ∈ Γ'.ownClosure (Γ'.consumedNames (C.map f)),
      ∃ κ ∈ Γ.ownClosure (Γ.consumedNames C), f (.cvar κ) = .cvar κ' :=
  h.ownClosure (h.consumedNames hf hk)

/-- **Argument separation under a map**, when the consumed side passes the
kill premise. -/
theorem argSep (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) {B C : CaptureSet s1}
    (hS : Γ.ArgSep B C) (hk : Γ.KillOk C) : Γ'.ArgSep (B.map f) (C.map f) := by
  intro z' hz' κ' hκ'
  rcases h.names_cover hf B z' hz' with ⟨z, hz, hb, -⟩ | ⟨κ'', hb, hfr, y, hy, hr, -⟩
  · rw [hκ'] at hb
    obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
    rw [hzκ] at hb
    obtain ⟨hS₁, hS₂⟩ := hS z hz κ hzκ
    refine ⟨fun hmem => ?_, fun l' hl' hm => ?_⟩
    · obtain ⟨κ₀, hκ₀, hf₀⟩ := h.killSet hf hk κ' hmem
      rw [h.inj κ₀ κ κ' hf₀ hb.symm] at hκ₀
      exact hS₁ hκ₀
    · obtain ⟨l, hl, hfl⟩ := h.consumedNames hf hk l' hl'
      obtain ⟨l₂, hl₂, hm₂⟩ := h.mayOwn hm κ hb.symm
      rw [h.inj l₂ l l' hl₂ hfl] at hm₂
      exact hS₂ l hl hm₂
  · rw [hκ'] at hb
    cases hb
    refine ⟨fun hmem => ?_, fun l' hl' _ => ?_⟩
    · obtain ⟨κ₀, -, hf₀⟩ := h.killSet hf hk κ' hmem
      exact hfr.2.2 κ₀ hf₀
    · obtain ⟨l, hl, -⟩ := h.consumedNames hf hk l' hl'
      exact hS.not_consumed_of_root hk hy hr hl

/-- Between killed contexts: kills read no name, no root, no flavour and no
claim, and a fresh binder stays live when every target kill is an image. -/
theorem killNames (h : Γ.NamesMap f Γ') (D : List (BVar s1 .cap)) (D' : List (BVar s2 .cap))
    (hD : ∀ κ' ∈ D', ∃ κ, f (.cvar κ) = .cvar κ') :
    (Γ.killNames D).NamesMap f (Γ'.killNames D') where
  names a z' hz' := by
    rw [Ctx.namesCaps_killNames] at hz' ⊢
    exact h.names a z' hz'
  rootAtom := by rw [Ctx.rootAtom_killNames, Ctx.rootAtom_killNames]; exact h.rootAtom
  rootRefl x hx := by
    rw [Ctx.isRootB_killNames] at hx ⊢
    exact h.rootRefl x hx
  rootMap x hx := by
    rw [Ctx.isRootB_killNames] at hx ⊢
    exact h.rootMap x hx
  surj κ' := by
    rcases h.surj κ' with hi | ⟨hr, hl, hni⟩
    · exact Or.inl hi
    · refine Or.inr ⟨by rw [Ctx.lookupCap_killNames_isRoot]; exact hr, ?_, hni⟩
      rw [Ctx.bitLive_killNames]
      refine ⟨hl, fun _ hmem => ?_⟩
      obtain ⟨κ, hκ⟩ := hD κ' hmem
      exact hni κ hκ
  inj := h.inj
  consEq κ κ' hf := by
    rw [Ctx.lookupCap_killNames_consumable, Ctx.lookupCap_killNames_consumable]
    exact h.consEq κ κ' hf
  claims h₀ h' κ' hf hc := by
    rw [Ctx.claimsB_killNames] at hc
    obtain ⟨κ, hκ, hcl⟩ := h.claims h₀ h' κ' hf hc
    exact ⟨κ, hκ, by rw [Ctx.claimsB_killNames]; exact hcl⟩

/-- The evidence half between the kills a head causes on both sides. -/
theorem killMap_killFor (h : Γ.NamesMap f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.KillOk C) : (Γ.killFor C).KillMap f (Γ'.killFor (C.map f)) :=
  hk.killNames h.inj (h.killSet hf hK)

/-- The term half between the kills a head causes on both sides. -/
theorem killFor (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) {C : CaptureSet s1}
    (hK : Γ.KillOk C) : (Γ.killFor C).NamesMap f (Γ'.killFor (C.map f)) :=
  h.killNames _ _ (fun κ' hκ' => by
    obtain ⟨κ, -, hκ⟩ := h.killSet hf hK κ' hκ'
    exact ⟨κ, hκ⟩)

end Ctx.NamesMap

/-! ## Names up to ownership (plan-5h decision 39)

In a store the names of a closed atom's root are covered by the names of its
type exactly at `consume` and up to ownership below it (`Ctx.NamesLe`).  A
names map up to ownership records that cover.  An exact names map is one
(`Ctx.NamesMap.toO`).  The owned disjunct is read on a term binder only, and
names an owned binder that is no root: the substitutions of the machine
instantiate a term binder at a store binder, and in a store an heir owns
consumable names only. -/

/-- `Ctx.NamesMapO Γ f Γ'`: `Ctx.NamesMap` with the owned disjunct, effective
liveness along the map, and linear ownership in the target. -/
structure Ctx.NamesMapO (Γ : Ctx s1) (f : CapAtom s1 → CapAtom s2) (Γ' : Ctx s2) : Prop where
  names : ∀ a z', z' ∈ Γ'.namesCaps (f a) → ∃ z ∈ Γ.namesCaps a, z'.effMode ≤ z.effMode ∧
      (z'.base = f z.base ∨ (a.isTermB = true ∧ z'.effMode ≠ .consume ∧
        ∃ κ κ', f z.base = .cvar κ ∧ z'.base = .cvar κ' ∧ Γ'.Owns κ κ' ∧
          (Γ'.lookupCap κ').isRoot = false))
  rootAtom : Γ'.rootAtom = f Γ.rootAtom
  rootRefl : ∀ x, Γ'.isRootB (f x) = true → Γ.isRootB x = true
  rootMap : ∀ x, Γ.isRootB x = true → Γ'.isRootB (f x) = true
  surj : ∀ κ', (∃ κ, f (.cvar κ) = .cvar κ') ∨ Ctx.NamesMap.Fresh Γ f Γ' κ'
  inj : ∀ κ₁ κ₂ κ', f (.cvar κ₁) = .cvar κ' → f (.cvar κ₂) = .cvar κ' → κ₁ = κ₂
  consEq : ∀ κ κ', f (.cvar κ) = .cvar κ' →
      (Γ'.lookupCap κ').consumable = (Γ.lookupCap κ).consumable
  claims : ∀ h h' κ', f (.cvar h) = .cvar h' → Γ'.claimsB h' κ' = true →
      ∃ κ, f (.cvar κ) = .cvar κ' ∧ Γ.claimsB h κ = true
  /-- Effective liveness moves along the map. -/
  effLive : ∀ κ κ', f (.cvar κ) = .cvar κ' → Γ.EffLive κ → Γ'.EffLive κ'
  /-- Ownership in the target is linear, as in a store. -/
  linear : ∀ h₁ h₂ κ, Γ'.ownsB h₁ κ = true → Γ'.ownsB h₂ κ = true → h₁ = h₂

/-- **An exact names map is a names map up to ownership**, given the evidence
half and linear ownership in the target. -/
theorem Ctx.NamesMap.toO {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}
    (h : Γ.NamesMap f Γ') (hk : Γ.KillMap f Γ')
    (hl : ∀ h₁ h₂ κ, Γ'.ownsB h₁ κ = true → Γ'.ownsB h₂ κ = true → h₁ = h₂) :
    Γ.NamesMapO f Γ' where
  names a z' hz' := by
    obtain ⟨z, hz, hb, he⟩ := h.names a z' hz'
    exact ⟨z, hz, he, Or.inl hb⟩
  rootAtom := h.rootAtom
  rootRefl := h.rootRefl
  rootMap := h.rootMap
  surj := h.surj
  inj := h.inj
  consEq := h.consEq
  claims := h.claims
  effLive κ κ' hf hl' := hk.effLive h.consEq hl' κ' hf
  linear := hl

theorem EMode.comb_ne_consume {m e : EMode} (hm : m ≠ .consume) (he : e ≠ .consume) :
    m.comb e ≠ .consume := by
  revert hm he; cases m <;> cases e <;> decide

theorem EMode.ne_consume_of_le {m m' : EMode} (h : m ≤ m') (hm' : m' ≠ .consume) :
    m ≠ .consume := by
  revert h hm'; cases m <;> cases m' <;> decide

namespace Ctx.NamesMapO

variable {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}

/-- A name of the target reached from a name of the source: at a mode at
most the source's, its image, or below `consume` a name its image owns. -/
def Reach (Γ' : Ctx s2) (f : CapAtom s1 → CapAtom s2) (z : CapAtom s1) (z' : CapAtom s2) :
    Prop :=
  z'.effMode ≤ z.effMode ∧ (z'.base = f z.base ∨ (z'.effMode ≠ .consume ∧
    ∃ κ κ', f z.base = .cvar κ ∧ z'.base = .cvar κ' ∧ Γ'.Owns κ κ'))

/-- **The full names of an image**, up to ownership. -/
theorem namesAtom (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f) :
    ∀ a z', z' ∈ Γ'.namesAtom (f a) →
      (∃ z ∈ Γ.namesAtom a, Reach Γ' f z z') ∨
      (∃ κ', z'.base = .cvar κ' ∧ NamesMap.Fresh Γ f Γ' κ' ∧
        ∃ y ∈ Γ.namesAtom a, Γ.isRootB y.base = true ∧ z'.effMode ≤ y.effMode) := by
  intro a z' hz'
  unfold Ctx.namesAtom at hz'
  obtain ⟨y', hy', hz'y⟩ := List.mem_flatMap.mp hz'
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy'
  rw [hf.base] at hx'
  obtain ⟨x, hx, hxe, hxb⟩ := h.names a.base x' hx'
  have hye : ((f a).useApply x').effMode ≤ (a.useApply x).effMode := by
    rw [CapAtom.effMode_useApply, CapAtom.effMode_useApply]
    exact EMode.le_trans (EMode.comb_mono_left (hf.useMode a) _) (EMode.comb_mono _ hxe)
  have hy : a.useApply x ∈ (Γ.namesCaps a.base).map a.useApply := List.mem_map_of_mem hx
  have hyN : a.useApply x ∈ Γ.namesAtom a :=
    List.mem_flatMap.mpr ⟨_, hy, Γ.mem_expandNames_self _⟩
  rcases hxb with hxb | ⟨ht, hne, κ, κ', hfz, hx'b, ho, hnr⟩
  · have hyb : ((f a).useApply x').base = f (a.useApply x).base := by
      rw [CapAtom.base_useApply, CapAtom.base_useApply, hxb]
    unfold Ctx.expandNames at hz'y
    split at hz'y
    · rename_i hroot
      rcases List.mem_cons.mp hz'y with rfl | hz'y
      · exact Or.inl ⟨a.useApply x, hyN, hye, Or.inl hyb⟩
      · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hz'y
        obtain ⟨-, hκ'f⟩ := List.mem_filter.mp hκ'
        rw [Bool.not_eq_true'] at hκ'f
        rw [hyb] at hroot
        have hr := h.rootRefl _ hroot
        have hzb : (((f a).useApply x').reapply (CapAtom.cvar κ')).base = .cvar κ' := by
          simp only [CapAtom.reapply_eq, CapAtom.base_applyEMode, CapAtom.base]
        have hze : (((f a).useApply x').reapply (CapAtom.cvar κ')).effMode ≤
            (a.useApply x).effMode := by
          have hye' := hye
          simp only [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, CapAtom.effMode,
            EMode.comb_eps] at hye' ⊢
          exact hye'
        rcases h.surj κ' with ⟨κ, hκ⟩ | hfr
        · have hnr : (Γ.lookupCap κ).isRoot = false := by
            cases hr' : (Γ.lookupCap κ).isRoot with
            | false => rfl
            | true =>
                have := h.rootMap (.cvar κ) hr'
                rw [hκ] at this
                have h' : (Γ'.lookupCap κ').isRoot = true := this
                rw [hκ'f] at h'
                cases h'
          refine Or.inl ⟨(a.useApply x).reapply (.cvar κ),
            List.mem_flatMap.mpr ⟨_, hy, ?_⟩, ?_, Or.inl ?_⟩
          · unfold Ctx.expandNames
            rw [if_pos hr]
            refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨κ, List.mem_filter.mpr
              ⟨Γ.mem_capBinders κ, ?_⟩, rfl⟩)
            rw [hnr]; rfl
          · have hye' := hye
            simp only [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, CapAtom.effMode,
              EMode.comb_eps] at hye' ⊢
            exact hye'
          · rw [hzb]
            simp only [CapAtom.reapply_eq, CapAtom.base_applyEMode, CapAtom.base]
            exact hκ.symm
        · exact Or.inr ⟨κ', hzb, hfr, a.useApply x, hyN, hr, hze⟩
    · rw [List.mem_singleton.mp hz'y]
      exact Or.inl ⟨a.useApply x, hyN, hye, Or.inl hyb⟩
  · have hyb' : ((f a).useApply x').base = .cvar κ' := by rw [CapAtom.base_useApply, hx'b]
    have hnroot : Γ'.isRootB ((f a).useApply x').base = false := by rw [hyb']; exact hnr
    unfold Ctx.expandNames at hz'y
    rw [if_neg (by rw [hnroot]; decide)] at hz'y
    rw [List.mem_singleton.mp hz'y]
    refine Or.inl ⟨a.useApply x, hyN, hye, Or.inr ⟨?_, κ, κ', ?_, hyb', ho⟩⟩
    · rw [CapAtom.effMode_useApply]
      refine EMode.comb_ne_consume ?_ hne
      exact EMode.ne_consume_of_le (hf.useMode a) (CapAtom.useMode_ne_consume ht)
    · rw [CapAtom.base_useApply]; exact hfz

/-- The same for a set. -/
theorem names_cover (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f) (C : CaptureSet s1) :
    ∀ z' ∈ Γ'.names (C.map f),
      (∃ z ∈ Γ.names C, Reach Γ' f z z') ∨
      (∃ κ', z'.base = .cvar κ' ∧ NamesMap.Fresh Γ f Γ' κ' ∧
        ∃ y ∈ Γ.names C, Γ.isRootB y.base = true ∧ z'.effMode ≤ y.effMode) := by
  intro z' hz'
  obtain ⟨c', hc', hz'c⟩ := List.mem_flatMap.mp hz'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  rcases h.namesAtom hf c z' hz'c with ⟨z, hz, hr⟩ | ⟨κ', hb, hfr, y, hy, hr, he⟩
  · exact Or.inl ⟨z, List.mem_flatMap.mpr ⟨c, hc, hz⟩, hr⟩
  · exact Or.inr ⟨κ', hb, hfr, y, List.mem_flatMap.mpr ⟨c, hc, hy⟩, hr, he⟩

/-- **Exact at `consume`**: a consuming name of an image of a kill-ok set is
an image. -/
theorem names_cover_consume (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hk : Γ.KillOk C) {z' : CapAtom s2} (hz' : z' ∈ Γ'.names (C.map f))
    (hm : z'.effMode = .consume) :
    ∃ z ∈ Γ.names C, z'.base = f z.base ∧ z.effMode = .consume := by
  rcases h.names_cover hf C z' hz' with ⟨z, hz, he, hb⟩ | ⟨κ', -, -, y, hy, hr, he⟩
  · rw [hm] at he
    rcases hb with hb | ⟨hne, -⟩
    · exact ⟨z, hz, hb, NamesMap.EMode.eq_consume_of_le he⟩
    · exact absurd hm hne
  · rw [hm] at he
    exact (hk.not_root hy hr (NamesMap.EMode.eq_consume_of_le he)).elim

/-- **Accessibility under a names map up to ownership**: an owned name of the
target is effectively live when its owner is. -/
theorem accessible (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hA : Γ.Accessible C) : Γ'.Accessible (C.map f) := by
  intro z' hz' κ' hκ'
  rcases h.names_cover hf C z' hz' with ⟨z, hz, -, hb⟩ | ⟨κ'', hb, hfr, -⟩
  · rcases hb with hb | ⟨-, κ₀, κ₁, hfz, hz'b, ho⟩
    · rw [hκ'] at hb
      obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
      rw [hzκ] at hb
      exact h.effLive κ κ' hb.symm (hA z hz κ hzκ)
    · rw [hκ'] at hz'b
      cases hz'b
      obtain ⟨κ, hzκ⟩ := hf.cvar _ κ₀ hfz
      rw [hzκ] at hfz
      exact (h.effLive κ κ₀ hfz (hA z hz κ hzκ)).owns ho
  · rw [hκ'] at hb
    cases hb
    exact .live hfr.2.1

/-- **Consumability under a names map up to ownership.** -/
theorem consumeOk (h : Γ.NamesMapO f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.ConsumeOk C) : Γ'.ConsumeOk (C.map f) := by
  intro z' hz' hm
  obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf (Ctx.KillOk.of_consumeOk hK) hz' hm
  obtain ⟨κ, hzκ, hcons⟩ := hK z hz hzm
  obtain ⟨κ', hκ'⟩ := hk.cvar κ hcons.1
  refine ⟨κ', ?_, hk.consumable hcons hκ'⟩
  rw [hb, hzκ, hκ']

/-- **The kill premise under a names map up to ownership.** -/
theorem killOk (h : Γ.NamesMapO f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.KillOk C) : Γ'.KillOk (C.map f) := by
  intro z' hz' hm
  obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf hK hz' hm
  obtain ⟨κ, hzκ, hcons⟩ := hK z hz hzm
  rw [hzκ] at hb
  obtain ⟨κ', hκ'⟩ := hk.cvar κ hcons
  exact ⟨κ', by rw [hb, hκ'], hk.cons κ κ' hcons hκ'⟩

/-- The consumed names of an image of a kill-ok set are images of consumed
names. -/
theorem consumedNames (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f) {C : CaptureSet s1}
    (hk : Γ.KillOk C) :
    ∀ κ' ∈ Γ'.consumedNames (C.map f), ∃ κ ∈ Γ.consumedNames C, f (.cvar κ) = .cvar κ' := by
  intro κ' hκ'
  obtain ⟨z', hz', hsel⟩ := List.mem_filterMap.mp hκ'
  split at hsel
  · rename_i hm
    obtain ⟨z, hz, hb, hzm⟩ := h.names_cover_consume hf hk hz' hm
    have hz'b : z'.base = .cvar κ' := by
      cases hzb : z'.base <;> rw [hzb] at hsel <;> simp [CapAtom.cvar?] at hsel
      rw [hsel]
    rw [hz'b] at hb
    obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
    refine ⟨κ, List.mem_filterMap.mpr ⟨z, hz, ?_⟩, by rw [← hzκ]; exact hb.symm⟩
    rw [if_pos hzm, hzκ]; rfl
  · cases hsel

/-- Possible ownership from an image lands in images. -/
theorem mayOwn (h : Γ.NamesMapO f Γ') {h' κ' : BVar s2 .cap} (hm : Γ'.MayOwn h' κ') :
    ∀ h₀, f (.cvar h₀) = .cvar h' → ∃ κ, f (.cvar κ) = .cvar κ' ∧ Γ.MayOwn h₀ κ := by
  induction hm with
  | direct hd =>
      intro h₀ hf₀
      obtain ⟨κ, hκ, hcl⟩ := h.claims h₀ _ _ hf₀ hd
      exact ⟨κ, hκ, .direct hcl⟩
  | trans _ _ ih₁ ih₂ =>
      intro h₀ hf₀
      obtain ⟨c, hc, hm₁⟩ := ih₁ h₀ hf₀
      obtain ⟨κ, hκ, hm₂⟩ := ih₂ c hc
      exact ⟨κ, hκ, .trans hm₁ hm₂⟩

/-- The closure of images is the image of the closure. -/
theorem ownClosure (h : Γ.NamesMapO f Γ') {L : List (BVar s1 .cap)} {L' : List (BVar s2 .cap)}
    (hL : ∀ κ' ∈ L', ∃ κ ∈ L, f (.cvar κ) = .cvar κ') :
    ∀ κ' ∈ Γ'.ownClosure L', ∃ κ ∈ Γ.ownClosure L, f (.cvar κ) = .cvar κ' := by
  intro κ' hκ'
  rcases Ctx.mem_ownClosure.mp hκ' with hmem | ⟨h', hh', hm⟩
  · obtain ⟨κ, hκ, hf⟩ := hL κ' hmem
    exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inl hκ), hf⟩
  · obtain ⟨h₀, hh₀, hf₀⟩ := hL h' hh'
    obtain ⟨κ, hκ, hm₀⟩ := h.mayOwn hm h₀ hf₀
    exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inr ⟨h₀, hh₀, hm₀⟩), hκ⟩

/-- The kill of an image of a kill-ok set is inside the image of the kill. -/
theorem killSet (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f) {C : CaptureSet s1}
    (hk : Γ.KillOk C) :
    ∀ κ' ∈ Γ'.ownClosure (Γ'.consumedNames (C.map f)),
      ∃ κ ∈ Γ.ownClosure (Γ.consumedNames C), f (.cvar κ) = .cvar κ' :=
  h.ownClosure (h.consumedNames hf hk)

/-- **Argument separation under a names map up to ownership**, given that
in the target a name that may own an owned name is comparable with its owner.
In a store that is the linearity of ownership (`ownsR_comparable`,
`Retyping.lean`).  Past a typing-time claim it fails: an opened name that
claims a name an heir owns is unrelated to the heir
(`s0-g6s-counterexample.lean`). -/
theorem argSep (h : Γ.NamesMapO f Γ') (hf : CapAtom.NameMapFn f) {B C : CaptureSet s1}
    (hcmp : ∀ l κ₀ κ', Γ'.MayOwn l κ' → Γ'.Owns κ₀ κ' →
      l = κ₀ ∨ Γ'.MayOwn l κ₀ ∨ Γ'.MayOwn κ₀ l)
    (hS : Γ.ArgSep B C) (hk : Γ.KillOk C) : Γ'.ArgSep (B.map f) (C.map f) := by
  intro z' hz' κ' hκ'
  rcases h.names_cover hf B z' hz' with ⟨z, hz, -, hb⟩ | ⟨κ'', hb, hfr, y, hy, hr, -⟩
  · rcases hb with hb | ⟨-, κ₀, κ₁, hfz, hz'b, ho⟩
    · rw [hκ'] at hb
      obtain ⟨κ, hzκ⟩ := hf.cvar _ κ' hb.symm
      rw [hzκ] at hb
      obtain ⟨hS₁, hS₂⟩ := hS z hz κ hzκ
      refine ⟨fun hmem => ?_, fun l' hl' hm => ?_⟩
      · obtain ⟨κ₂, hκ₂, hf₂⟩ := h.killSet hf hk κ' hmem
        rw [h.inj κ₂ κ κ' hf₂ hb.symm] at hκ₂
        exact hS₁ hκ₂
      · obtain ⟨l, hl, hfl⟩ := h.consumedNames hf hk l' hl'
        obtain ⟨l₂, hl₂, hm₂⟩ := h.mayOwn hm κ hb.symm
        rw [h.inj l₂ l l' hl₂ hfl] at hm₂
        exact hS₂ l hl hm₂
    · rw [hκ'] at hz'b
      cases hz'b
      obtain ⟨κ, hzκ⟩ := hf.cvar _ κ₀ hfz
      rw [hzκ] at hfz
      obtain ⟨hS₁, hS₂⟩ := hS z hz κ hzκ
      have hno : ∀ l' ∈ Γ'.consumedNames (C.map f), ¬ Γ'.MayOwn κ₀ l' := by
        intro l' hl' hm
        obtain ⟨l, hl, hfl⟩ := h.consumedNames hf hk l' hl'
        obtain ⟨l₂, hl₂, hm₂⟩ := h.mayOwn hm κ hfz
        rw [h.inj l₂ l l' hl₂ hfl] at hm₂
        exact hS₂ l hl hm₂
      refine ⟨fun hmem => ?_, fun l' hl' hm => hno l' hl' (.trans (.of_owns ho) hm)⟩
      rcases Ctx.mem_ownClosure.mp hmem with hmem | ⟨l', hl', hm⟩
      · exact hno κ' hmem (.of_owns ho)
      · rcases hcmp l' κ₀ κ' hm ho with rfl | hm' | hm'
        · obtain ⟨κ₂, hκ₂, hf₂⟩ := h.killSet hf hk l'
            (Ctx.mem_ownClosure.mpr (Or.inl hl'))
          rw [h.inj κ₂ κ l' hf₂ hfz] at hκ₂
          exact hS₁ hκ₂
        · obtain ⟨κ₂, hκ₂, hf₂⟩ := h.killSet hf hk κ₀
            (Ctx.mem_ownClosure.mpr (Or.inr ⟨l', hl', hm'⟩))
          rw [h.inj κ₂ κ κ₀ hf₂ hfz] at hκ₂
          exact hS₁ hκ₂
        · exact hno l' hl' hm'
  · rw [hκ'] at hb
    cases hb
    refine ⟨fun hmem => ?_, fun l' hl' _ => ?_⟩
    · obtain ⟨κ₀, -, hf₀⟩ := h.killSet hf hk κ' hmem
      exact hfr.2.2 κ₀ hf₀
    · obtain ⟨l, hl, -⟩ := h.consumedNames hf hk l' hl'
      exact hS.not_consumed_of_root hk hy hr hl

/-- Between killed contexts, when every target kill is the image of a source
kill: effective liveness moves by the evidence half. -/
theorem killNames (h : Γ.NamesMapO f Γ') (hk : Γ.KillMap f Γ') (D : List (BVar s1 .cap))
    (D' : List (BVar s2 .cap)) (hD : ∀ κ' ∈ D', ∃ κ ∈ D, f (.cvar κ) = .cvar κ') :
    (Γ.killNames D).NamesMapO f (Γ'.killNames D') where
  names a z' hz' := by
    rw [Ctx.namesCaps_killNames] at hz' ⊢
    obtain ⟨z, hz, he, hb⟩ := h.names a z' hz'
    refine ⟨z, hz, he, ?_⟩
    rcases hb with hb | ⟨ht, hne, κ, κ', hfz, hz'b, ho, hnr⟩
    · exact Or.inl hb
    · exact Or.inr ⟨ht, hne, κ, κ', hfz, hz'b, ho.killNames,
        by rw [Ctx.lookupCap_killNames_isRoot]; exact hnr⟩
  rootAtom := by rw [Ctx.rootAtom_killNames, Ctx.rootAtom_killNames]; exact h.rootAtom
  rootRefl x hx := by
    rw [Ctx.isRootB_killNames] at hx ⊢
    exact h.rootRefl x hx
  rootMap x hx := by
    rw [Ctx.isRootB_killNames] at hx ⊢
    exact h.rootMap x hx
  surj κ' := by
    rcases h.surj κ' with hi | ⟨hr, hl, hni⟩
    · exact Or.inl hi
    · refine Or.inr ⟨by rw [Ctx.lookupCap_killNames_isRoot]; exact hr, ?_, hni⟩
      rw [Ctx.bitLive_killNames]
      refine ⟨hl, fun _ hmem => ?_⟩
      obtain ⟨κ, -, hκ⟩ := hD κ' hmem
      exact hni κ hκ
  inj := h.inj
  consEq κ κ' hf := by
    rw [Ctx.lookupCap_killNames_consumable, Ctx.lookupCap_killNames_consumable]
    exact h.consEq κ κ' hf
  claims h₀ h' κ' hf hc := by
    rw [Ctx.claimsB_killNames] at hc
    obtain ⟨κ, hκ, hcl⟩ := h.claims h₀ h' κ' hf hc
    exact ⟨κ, hκ, by rw [Ctx.claimsB_killNames]; exact hcl⟩
  effLive κ κ' hf hl := by
    refine (hk.killNames h.inj hD).effLive ?_ hl κ' hf
    intro κ₁ κ₁' hf₁
    rw [Ctx.lookupCap_killNames_consumable, Ctx.lookupCap_killNames_consumable]
    exact h.consEq κ₁ κ₁' hf₁
  linear h₁ h₂ κ o₁ o₂ := by
    rw [Ctx.ownsB_killNames] at o₁ o₂
    exact h.linear h₁ h₂ κ o₁ o₂

/-- The evidence half between the kills a head causes on both sides. -/
theorem killMap_killFor (h : Γ.NamesMapO f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.KillOk C) : (Γ.killFor C).KillMap f (Γ'.killFor (C.map f)) :=
  hk.killNames h.inj (h.killSet hf hK)

/-- The term half between the kills a head causes on both sides: the target
kills inside the image of the source's kill. -/
theorem killFor (h : Γ.NamesMapO f Γ') (hk : Γ.KillMap f Γ') (hf : CapAtom.NameMapFn f)
    {C : CaptureSet s1} (hK : Γ.KillOk C) : (Γ.killFor C).NamesMapO f (Γ'.killFor (C.map f)) :=
  h.killNames hk _ _ (h.killSet hf hK)

end Ctx.NamesMapO

/-! ## Lifting the term half through a binder

The atoms of an extended signature are the new binder, a capture name on it,
an older atom weakened, or a moded atom. -/

/-- An atom of a term-extended signature is the new binder, a field name on
it, or an older atom weakened. -/
theorem CapAtom.cons_cases (e : CapAtom (s,x)) :
    e = .var .here ∨ (∃ l, e = .name .here l) ∨ (∃ e₀ : CapAtom s, e = e₀.weaken) ∨
      ∃ (m : Mode) (e₀ : CapAtom (s,x)), e = .mode m e₀ := by
  cases e with
  | top => exact Or.inr (Or.inr (Or.inl ⟨.top, rfl⟩))
  | var x => cases x with
      | here => exact Or.inl rfl
      | there x0 => exact Or.inr (Or.inr (Or.inl ⟨.var x0, rfl⟩))
  | name x l => cases x with
      | here => exact Or.inr (Or.inl ⟨l, rfl⟩)
      | there x0 => exact Or.inr (Or.inr (Or.inl ⟨.name x0 l, rfl⟩))
  | cvar k => cases k with
      | there k0 => exact Or.inr (Or.inr (Or.inl ⟨.cvar k0, rfl⟩))
  | mode m e₀ => exact Or.inr (Or.inr (Or.inr ⟨m, e₀, rfl⟩))

/-- And of a capture-extended signature: the new binder, or an older atom
weakened. -/
theorem CapAtom.consC_cases (e : CapAtom (s,c)) :
    e = .cvar .here ∨ (∃ e₀ : CapAtom s, e = e₀.weaken) ∨
      ∃ (m : Mode) (e₀ : CapAtom (s,c)), e = .mode m e₀ := by
  cases e with
  | top => exact Or.inr (Or.inl ⟨.top, rfl⟩)
  | var x => cases x with
      | there x0 => exact Or.inr (Or.inl ⟨.var x0, rfl⟩)
  | name x l => cases x with
      | there x0 => exact Or.inr (Or.inl ⟨.name x0 l, rfl⟩)
  | cvar k => cases k with
      | here => exact Or.inl rfl
      | there k0 => exact Or.inr (Or.inl ⟨.cvar k0, rfl⟩)
  | mode m e₀ => exact Or.inr (Or.inr ⟨m, e₀, rfl⟩)

/-- A weakened atom is a capture binder exactly when the atom is. -/
theorem CapAtom.weaken_eq_cvar {a : CapAtom s} {κ' : BVar (s,,k) .cap}
    (h : CapAtom.weaken (k := k) a = .cvar κ') : ∃ κ₀, κ' = .there κ₀ ∧ a = .cvar κ₀ := by
  cases a with
  | cvar κ₀ =>
      simp only [CapAtom.weaken, CapAtom.rename, Rename.succ_var, CapAtom.cvar.injEq] at h
      exact ⟨κ₀, h.symm, rfl⟩
  | var _ => simp [CapAtom.weaken, CapAtom.rename] at h
  | name _ _ => simp [CapAtom.weaken, CapAtom.rename] at h
  | top => simp [CapAtom.weaken, CapAtom.rename] at h
  | mode _ _ => simp [CapAtom.weaken, CapAtom.rename] at h

theorem BVar.eq_of_depth : ∀ {s : Sig} {k : Kind} (a b : BVar s k), a.depth = b.depth → a = b
  | _, _, .here, .here, _ => rfl
  | _, _, .there a, .there b, h => by
      have h' : a.depth = b.depth := Nat.succ.inj h
      rw [BVar.eq_of_depth a b h']
  | _, _, .here, .there b, h => absurd h.symm (Nat.succ_ne_zero _)
  | _, _, .there a, .here, h => absurd h (Nat.succ_ne_zero _)

/-- A moded atom has no names of its own. -/
theorem Ctx.namesCapsP_mode (p : Bool) (Γ : Ctx s) (m : Mode) (a : CapAtom s) :
    Γ.namesCapsP p (.mode m a) = [] := by
  cases Γ <;> rfl

/-- In a root-free context the only root is the universal one. -/
theorem Ctx.eq_top_of_rootFree {Γ : Ctx s} (hΓ : Γ.root? = none) {r : CapAtom s}
    (hr : Γ.isRootB r = true) : r = .top := by
  cases r with
  | top => rfl
  | cvar κ =>
      have := Γ.root?_none_isRoot hΓ κ
      simp [Ctx.isRootB, this] at hr
  | var _ => simp [Ctx.isRootB] at hr
  | name _ _ => simp [Ctx.isRootB] at hr
  | mode _ _ => simp [Ctx.isRootB] at hr

/-- **The binder a capture binding appends is opened by exactly the innermost
root.** -/
theorem Ctx.lvlLeB_here_weakenC_iff (Γ : Ctx s) {b : CapBound s} (hb : b.isRoot = false)
    {r : CapAtom s} (hr : Γ.isRootB r = true) :
    (Γ.consC b).lvlLeB (.cvar .here) (CapAtom.weaken (k := .cap) r) = true ↔ r = Γ.rootAtom := by
  have hl : (Γ.consC b).lvlAtom (.cvar .here) = Γ.root?.map .there :=
    Ctx.lvl_consC_here_of_not_root Γ b hb
  unfold Ctx.lvlLeB
  rw [hl, Ctx.rootDepth?_weaken]
  cases hρ : Γ.root? with
  | none =>
      have hrt : r = .top := Ctx.eq_top_of_rootFree hρ hr
      simp [Ctx.rootAtom, hρ, hrt]
  | some ρ₀ =>
      have hra : Γ.rootAtom = .cvar ρ₀ := by simp [Ctx.rootAtom, hρ]
      rw [hra]
      cases r with
      | top => simp [depthGe]
      | cvar κ =>
          have hκ : (Γ.lookupCap κ).isRoot = true := hr
          have hmin := Γ.root?_min hρ hκ
          simp only [Option.map_some, Ctx.rootDepth?_cvar, BVar.depth_there, depthGe,
            decide_eq_true_eq, CapAtom.cvar.injEq]
          constructor
          · intro h
            exact BVar.eq_of_depth κ ρ₀ (by omega)
          · rintro rfl; omega
      | var _ => simp [Ctx.isRootB] at hr
      | name _ _ => simp [Ctx.isRootB] at hr
      | mode _ _ => simp [Ctx.isRootB] at hr

/-- The root of a fresh scope opens every older binder. -/
theorem Ctx.lvlLeB_there_consC_root (Γ : Ctx s) (κ : BVar s .cap) :
    (Γ.consC .root).lvlLeB (.cvar (.there κ)) (.cvar .here) = true :=
  Ctx.lvlLeB_depth_zero _ _ _ rfl

namespace Ctx.NamesMap

variable {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}

/-- Phase one of a set, covered atom by atom. -/
theorem cover_flat (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f) (C : CaptureSet s1) :
    ∀ z' ∈ (C.map f).flatMap (fun (c : CapAtom s2) => (Γ'.namesCaps c.base).map c.useApply),
      ∃ z ∈ C.flatMap (fun (c : CapAtom s1) => (Γ.namesCaps c.base).map c.useApply),
        z'.base = f z.base ∧ z'.effMode ≤ z.effMode := by
  intro z' hz'
  obtain ⟨c', hc', hz'c⟩ := List.mem_flatMap.mp hz'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hz'c
  rw [hf.base] at hx'
  obtain ⟨x, hx, hxb, hxe⟩ := h.names c.base x' hx'
  refine ⟨c.useApply x, List.mem_flatMap.mpr ⟨c, hc, List.mem_map_of_mem hx⟩, ?_, ?_⟩
  · rw [CapAtom.base_useApply, CapAtom.base_useApply, hxb]
  · rw [CapAtom.effMode_useApply, CapAtom.effMode_useApply]
    exact EMode.le_trans (EMode.comb_mono_left (hf.useMode c) _) (EMode.comb_mono _ hxe)

/-- A cover survives a weakening on both sides. -/
theorem cover_weaken {L : CaptureSet s1} {L' : CaptureSet s2}
    {f₁ : CapAtom (s1,,k) → CapAtom (s2,,k)}
    (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    (hL : ∀ z' ∈ L', ∃ z ∈ L, z'.base = f z.base ∧ z'.effMode ≤ z.effMode) :
    ∀ z' ∈ CaptureSet.weaken (k := k) L',
      ∃ z ∈ CaptureSet.weaken (k := k) L, z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode := by
  intro z' hz'
  obtain ⟨w', hw', rfl⟩ := CaptureSet.mem_weaken.mp hz'
  obtain ⟨w, hw₀, hb, he⟩ := hL w' hw'
  refine ⟨CapAtom.weaken w, CaptureSet.weaken_mem_weaken.mpr hw₀, ?_, ?_⟩
  · have e1 : (CapAtom.weaken (k := k) w').base = CapAtom.weaken w'.base :=
      CapAtom.base_rename w' _
    have e2 : (CapAtom.weaken (k := k) w).base = CapAtom.weaken w.base :=
      CapAtom.base_rename w _
    rw [e1, e2, hw, hb]
  · have e1 : (CapAtom.weaken (k := k) w').effMode = w'.effMode := CapAtom.effMode_rename w' _
    have e2 : (CapAtom.weaken (k := k) w).effMode = w.effMode := CapAtom.effMode_rename w _
    rw [e1, e2]
    exact he

/-- **Lifting through a term binder.** -/
theorem lift_cons (h : Γ.NamesMap f Γ') {f₁ : CapAtom (s1,x) → CapAtom (s2,x)}
    (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    (hhere : f₁ (.var .here) = .var .here)
    (hname : ∀ ℓ, f₁ (.name .here ℓ) = .name .here ℓ)
    (hmode : ∀ m a, ∃ a', f₁ (.mode m a) = .mode m a')
    {b : Binding s1} {b' : Binding s2}
    (hvar : ∀ z', z' ∈ (Γ'.cons b').namesCaps (.var .here) →
      ∃ z ∈ (Γ.cons b).namesCaps (.var .here), z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode)
    (hnm : ∀ ℓ z', z' ∈ (Γ'.cons b').namesCaps (.name .here ℓ) →
      ∃ z ∈ (Γ.cons b).namesCaps (.name .here ℓ), z'.base = f₁ z.base ∧
        z'.effMode ≤ z.effMode) :
    (Γ.cons b).NamesMap f₁ (Γ'.cons b') where
  names a z' hz' := by
    rcases CapAtom.cons_cases a with rfl | ⟨l, rfl⟩ | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rw [hhere] at hz'; exact hvar z' hz'
    · rw [hname] at hz'; exact hnm l z' hz'
    · rw [hw, Ctx.namesCaps_weaken] at hz'
      obtain ⟨z, hz, hb, he⟩ := cover_weaken hw (h.names a₀) z' hz'
      exact ⟨z, by rw [Ctx.namesCaps_weaken]; exact hz, hb, he⟩
    · obtain ⟨a', ha'⟩ := hmode m a₁
      rw [ha', Ctx.namesCaps, Ctx.namesCapsP_mode] at hz'
      cases hz'
  rootAtom := by
    rw [Ctx.rootAtom_cons, Ctx.rootAtom_cons, hw, h.rootAtom]
  rootRefl x hx := by
    rcases CapAtom.cons_cases x with rfl | ⟨l, rfl⟩ | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rw [hhere] at hx; simp [Ctx.isRootB] at hx
    · rw [hname] at hx; simp [Ctx.isRootB] at hx
    · rw [hw, Ctx.isRootB_weaken] at hx
      rw [Ctx.isRootB_weaken]
      exact h.rootRefl a₀ hx
    · obtain ⟨a', ha'⟩ := hmode m a₁
      rw [ha'] at hx; simp [Ctx.isRootB] at hx
  rootMap x hx := by
    rcases CapAtom.cons_cases x with rfl | ⟨l, rfl⟩ | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · simp [Ctx.isRootB] at hx
    · simp [Ctx.isRootB] at hx
    · rw [Ctx.isRootB_weaken] at hx
      rw [hw, Ctx.isRootB_weaken]
      exact h.rootMap a₀ hx
    · simp [Ctx.isRootB] at hx
  surj κ' := by
    cases κ' with
    | there κ'' =>
        rcases h.surj κ'' with ⟨κ₀, hf₀⟩ | ⟨hr, hl, hni⟩
        · refine Or.inl ⟨.there κ₀, ?_⟩
          rw [CapAtom.cvar_there, hw, hf₀]; rfl
        · refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [Ctx.lookupCap_there, CapBound.isRoot_weaken]; exact hr
          · show ((Γ'.cons b').lookupCap (.there κ'')).live = true
            rw [Ctx.lookupCap_there, CapBound.live_weaken]; exact hl
          · intro κ he
            cases κ with
            | there κ₀ =>
                rw [CapAtom.cvar_there, hw] at he
                obtain ⟨κ₁, he₁, he₂⟩ := CapAtom.weaken_eq_cvar he
                cases BVar.there.inj he₁
                exact hni κ₀ he₂
  inj κ₁ κ₂ κ' h₁ h₂ := by
    cases κ₁ with
    | there κ₁₀ =>
    cases κ₂ with
    | there κ₂₀ =>
        rw [CapAtom.cvar_there, hw] at h₁ h₂
        obtain ⟨κ'', rfl, h₁'⟩ := CapAtom.weaken_eq_cvar h₁
        obtain ⟨κ''', he, h₂'⟩ := CapAtom.weaken_eq_cvar h₂
        cases BVar.there.inj he
        rw [h.inj κ₁₀ κ₂₀ κ'' h₁' h₂']
  consEq κ κ' hf' := by
    cases κ with
    | there κ₀ =>
        rw [CapAtom.cvar_there, hw] at hf'
        obtain ⟨κ'', rfl, hf₀⟩ := CapAtom.weaken_eq_cvar hf'
        rw [Ctx.lookupCap_there, Ctx.lookupCap_there, CapBound.consumable_weaken,
          CapBound.consumable_weaken]
        exact h.consEq κ₀ κ'' hf₀
  claims h₀ h' κ' hf' hc := by
    cases h₀ with
    | there h₀₀ =>
        rw [CapAtom.cvar_there, hw] at hf'
        obtain ⟨h'', rfl, hf₀⟩ := CapAtom.weaken_eq_cvar hf'
        cases κ' with
        | there κ'' =>
            rw [Ctx.claimsB_cons_there] at hc
            obtain ⟨κ₀, hκ₀, hcl⟩ := h.claims h₀₀ h'' κ'' hf₀ hc
            refine ⟨.there κ₀, ?_, by rw [Ctx.claimsB_cons_there]; exact hcl⟩
            rw [CapAtom.cvar_there, hw, hκ₀]; rfl

/-- **Lifting through a capture binder.**  The two bounds are roots together,
consumable together, their names are covered, and the claims of the new
target binder are images of claims of the new source binder. -/
theorem lift_consC (h : Γ.NamesMap f Γ') {f₁ : CapAtom (s1,c) → CapAtom (s2,c)}
    (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    (hhere : f₁ (.cvar .here) = .cvar .here)
    (hmode : ∀ m a, ∃ a', f₁ (.mode m a) = .mode m a')
    {b : CapBound s1} {b' : CapBound s2}
    (hroot : b'.isRoot = b.isRoot) (hcons : b'.consumable = b.consumable)
    (hcv : ∀ z', z' ∈ (Γ'.consC b').namesCaps (.cvar .here) →
      ∃ z ∈ (Γ.consC b).namesCaps (.cvar .here), z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode)
    (hcl : ∀ κ', (Γ'.consC b').claimsB .here κ' = true →
      ∃ κ, f₁ (.cvar κ) = .cvar κ' ∧ (Γ.consC b).claimsB .here κ = true) :
    (Γ.consC b).NamesMap f₁ (Γ'.consC b') where
  names a z' hz' := by
    rcases CapAtom.consC_cases a with rfl | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rw [hhere] at hz'; exact hcv z' hz'
    · rw [hw, Ctx.namesCaps_weakenC] at hz'
      obtain ⟨z, hz, hb, he⟩ := cover_weaken hw (h.names a₀) z' hz'
      exact ⟨z, by rw [Ctx.namesCaps_weakenC]; exact hz, hb, he⟩
    · obtain ⟨a', ha'⟩ := hmode m a₁
      rw [ha', Ctx.namesCaps, Ctx.namesCapsP_mode] at hz'
      cases hz'
  rootAtom := by
    cases hb : b.isRoot with
    | false =>
        rw [hb] at hroot
        rw [Ctx.rootAtom_consC _ _ hb, Ctx.rootAtom_consC _ _ hroot, hw, h.rootAtom]
    | true =>
        rw [hb] at hroot
        have h1 : (Γ.consC b).rootAtom = .cvar .here := by
          cases b <;> simp_all [CapBound.isRoot] <;> rfl
        have h2 : (Γ'.consC b').rootAtom = .cvar .here := by
          cases b' <;> simp_all [CapBound.isRoot] <;> rfl
        rw [h1, h2, hhere]
  rootRefl x hx := by
    rcases CapAtom.consC_cases x with rfl | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rw [hhere] at hx
      have : ((Γ'.consC b').lookupCap .here).isRoot = true := hx
      show ((Γ.consC b).lookupCap .here).isRoot = true
      rw [Ctx.lookupCap_here, CapBound.isRoot_weaken, ← hroot]
      rwa [Ctx.lookupCap_here, CapBound.isRoot_weaken] at this
    · rw [hw, Ctx.isRootB_weakenC] at hx
      rw [Ctx.isRootB_weakenC]
      exact h.rootRefl a₀ hx
    · obtain ⟨a', ha'⟩ := hmode m a₁
      rw [ha'] at hx; simp [Ctx.isRootB] at hx
  rootMap x hx := by
    rcases CapAtom.consC_cases x with rfl | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rw [hhere]
      have : ((Γ.consC b).lookupCap .here).isRoot = true := hx
      show ((Γ'.consC b').lookupCap .here).isRoot = true
      rw [Ctx.lookupCap_here, CapBound.isRoot_weaken, hroot]
      rwa [Ctx.lookupCap_here, CapBound.isRoot_weaken] at this
    · rw [Ctx.isRootB_weakenC] at hx
      rw [hw, Ctx.isRootB_weakenC]
      exact h.rootMap a₀ hx
    · simp [Ctx.isRootB] at hx
  surj κ' := by
    cases κ' with
    | here => exact Or.inl ⟨.here, hhere⟩
    | there κ'' =>
        rcases h.surj κ'' with ⟨κ₀, hf₀⟩ | ⟨hr, hl, hni⟩
        · refine Or.inl ⟨.there κ₀, ?_⟩
          rw [CapAtom.cvar_there, hw, hf₀]; rfl
        · refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [Ctx.lookupCap_thereC, CapBound.isRoot_weaken]; exact hr
          · show ((Γ'.consC b').lookupCap (.there κ'')).live = true
            rw [Ctx.lookupCap_thereC, CapBound.live_weaken]; exact hl
          · intro κ he
            cases κ with
            | here =>
                rw [hhere] at he
                cases he
            | there κ₀ =>
                rw [CapAtom.cvar_there, hw] at he
                obtain ⟨κ₁, he₁, he₂⟩ := CapAtom.weaken_eq_cvar he
                cases BVar.there.inj he₁
                exact hni κ₀ he₂
  inj κ₁ κ₂ κ' h₁ h₂ := by
    cases κ₁ with
    | here =>
        rw [hhere] at h₁
        cases κ₂ with
        | here => rfl
        | there κ₂₀ =>
            rw [CapAtom.cvar_there, hw, ← h₁] at h₂
            exact absurd h₂.symm (CapAtom.cvar_here_ne_weaken _)
    | there κ₁₀ =>
        cases κ₂ with
        | here =>
            rw [hhere] at h₂
            rw [CapAtom.cvar_there, hw, ← h₂] at h₁
            exact absurd h₁.symm (CapAtom.cvar_here_ne_weaken _)
        | there κ₂₀ =>
            rw [CapAtom.cvar_there, hw] at h₁ h₂
            obtain ⟨κ'', rfl, h₁'⟩ := CapAtom.weaken_eq_cvar h₁
            obtain ⟨κ''', he, h₂'⟩ := CapAtom.weaken_eq_cvar h₂
            cases BVar.there.inj he
            rw [h.inj κ₁₀ κ₂₀ κ'' h₁' h₂']
  consEq κ κ' hf' := by
    cases κ with
    | here =>
        rw [hhere] at hf'
        cases hf'
        rw [Ctx.lookupCap_here, Ctx.lookupCap_here, CapBound.consumable_weaken,
          CapBound.consumable_weaken]
        exact hcons
    | there κ₀ =>
        rw [CapAtom.cvar_there, hw] at hf'
        obtain ⟨κ'', rfl, hf₀⟩ := CapAtom.weaken_eq_cvar hf'
        rw [Ctx.lookupCap_thereC, Ctx.lookupCap_thereC, CapBound.consumable_weaken,
          CapBound.consumable_weaken]
        exact h.consEq κ₀ κ'' hf₀
  claims h₀ h' κ' hf' hc := by
    cases h₀ with
    | here =>
        rw [hhere] at hf'
        cases hf'
        exact hcl κ' hc
    | there h₀₀ =>
        rw [CapAtom.cvar_there, hw] at hf'
        obtain ⟨h'', rfl, hf₀⟩ := CapAtom.weaken_eq_cvar hf'
        cases κ' with
        | here =>
            rw [Ctx.claimsB_right_here] at hc
            cases hc
        | there κ'' =>
            rw [Ctx.claimsB_consC_there] at hc
            obtain ⟨κ₀, hκ₀, hcl'⟩ := h.claims h₀₀ h'' κ'' hf₀ hc
            refine ⟨.there κ₀, ?_, by rw [Ctx.claimsB_consC_there]; exact hcl'⟩
            rw [CapAtom.cvar_there, hw, hκ₀]; rfl

end Ctx.NamesMap

/-! ## The maps of atoms the tree uses -/

theorem CapAtom.nameMapFn_rename (ρ : Rename s1 s2) :
    CapAtom.NameMapFn (fun a : CapAtom s1 => a.rename ρ) where
  base a := CapAtom.base_rename a ρ
  effMode a := CapAtom.effMode_rename a ρ
  useMode a := by rw [CapAtom.useMode_rename]; exact EMode.le_refl _
  cvar x κ' h := by
    cases x with
    | cvar κ => exact ⟨κ, rfl⟩
    | var _ => simp [CapAtom.rename] at h
    | name _ _ => simp [CapAtom.rename] at h
    | top => simp [CapAtom.rename] at h
    | mode _ _ => simp [CapAtom.rename] at h

theorem CapAtom.nameMapFn_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ) :
    CapAtom.NameMapFn (fun a : CapAtom s1 => a.subst σ) where
  base a := CapAtom.base_subst hσ a
  effMode a := CapAtom.effMode_subst hσ a
  useMode a := CapAtom.useMode_subst_le hσ a
  cvar x κ' h := by
    cases x with
    | cvar κ => exact ⟨κ, rfl⟩
    | var _ => simp [CapAtom.subst] at h
    | name _ _ => simp [CapAtom.subst] at h
    | top => simp [CapAtom.subst] at h
    | mode _ _ => simp [CapAtom.subst] at h

theorem CapAtom.nameMapFn_id : CapAtom.NameMapFn (fun a : CapAtom s => a) where
  base _ := rfl
  effMode _ := rfl
  useMode _ := EMode.le_refl _
  cvar _ κ' h := ⟨κ', h⟩

/-! ## The names of the newest binder -/

/-- A term binder's names are the names of its declared set, one binder out. -/
theorem Ctx.namesCaps_var_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).namesCaps (.var .here) =
      CaptureSet.weaken (b.ty.captureSet.flatMap
        fun (a : CapAtom s) => (Γ.namesCaps a.base).map a.useApply) := by
  simp [Ctx.namesCaps, Ctx.namesCapsP]

/-- A capture name of an opaque binder or a parameter stands for the level root
of the binder. -/
theorem Ctx.namesCaps_name_here_leaf (Γ : Ctx s) {b : Binding s}
    (hb : ∀ T W Wc Fs, b ≠ .transparent T W Wc Fs) (ℓ : Label) :
    (Γ.cons b).namesCaps (.name .here ℓ) = [CapAtom.weaken Γ.rootAtom] := by
  cases b with
  | «opaque» T => rfl
  | formal T => rfl
  | transparent T W Wc Fs => exact absurd rfl (hb T W Wc Fs)

theorem Ctx.namesCaps_name_here_transparent (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) (ℓ : Label) :
    (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ) =
      CaptureSet.weaken ((Wc.reach ℓ).flatMap
        (Ctx.namesSelfWith (fun a => Γ.namesCaps a) T)) := rfl

theorem Ctx.namesCaps_cvar_here_upper (Γ : Ctx s) (C : CaptureSet s) :
    (Γ.consC (.upper C)).namesCaps (.cvar .here) =
      CaptureSet.weaken (C.flatMap fun (a : CapAtom s) => (Γ.namesCaps a.base).map a.useApply) :=
  rfl

theorem Ctx.namesCaps_cvar_here_inst (Γ : Ctx s) (C : CaptureSet s) :
    (Γ.consC (.inst C)).namesCaps (.cvar .here) =
      CaptureSet.weaken (C.flatMap fun (a : CapAtom s) => (Γ.namesCaps a.base).map a.useApply) :=
  rfl

/-- A base atom of the witness scope, one binder out, stands for its names. -/
theorem Ctx.selfInner_weaken_base (g : CapAtom s → CaptureSet s) (hg : g .top = [.top])
    (T : Ty s) : ∀ c : CapAtom s, c.base = c →
      Ctx.selfInner g T (CapAtom.weaken (k := .var) c) = g c
  | .var _, _ => rfl
  | .cvar _, _ => rfl
  | .name _ _, _ => rfl
  | .top, _ => hg.symm
  | .mode m c, h => absurd h (CapAtom.base_ne_mode c m c)

theorem Ctx.namesCaps_top (Γ : Ctx s) : Γ.namesCaps .top = [.top] := by
  cases Γ <;> rfl

/-- An atom whose weakening is its own base is its own base. -/
theorem CapAtom.base_of_weaken' {s : Sig} {k : Kind} {a : CapAtom s}
    (h : (CapAtom.weaken (k := k) a).base = a.weaken) : a.base = a := by
  rw [CapAtom.weaken, CapAtom.base_rename] at h
  exact CapAtom.rename_inj _ _ _ Rename.succ_injective h

namespace Ctx.NamesMap

variable {Γ : Ctx s1} {f : CapAtom s1 → CapAtom s2} {Γ' : Ctx s2}

theorem cover_var_here (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f)
    {f₁ : CapAtom (s1,x) → CapAtom (s2,x)} (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    {b : Binding s1} {b' : Binding s2} (hty : b'.ty.captureSet = b.ty.captureSet.map f) :
    ∀ z', z' ∈ (Γ'.cons b').namesCaps (.var .here) →
      ∃ z ∈ (Γ.cons b).namesCaps (.var .here), z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode := by
  rw [Ctx.namesCaps_var_here, Ctx.namesCaps_var_here, hty]
  exact cover_weaken hw (h.cover_flat hf _)

theorem cover_cvar_here_set (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f)
    {f₁ : CapAtom (s1,c) → CapAtom (s2,c)} (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    {C : CaptureSet s1} {b : CapBound s1} {b' : CapBound s2}
    (hb : (b = .upper C ∧ b' = .upper (C.map f)) ∨ (b = .inst C ∧ b' = .inst (C.map f))) :
    ∀ z', z' ∈ (Γ'.consC b').namesCaps (.cvar .here) →
      ∃ z ∈ (Γ.consC b).namesCaps (.cvar .here), z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode := by
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Ctx.namesCaps_cvar_here_upper, Ctx.namesCaps_cvar_here_upper]
    exact cover_weaken hw (h.cover_flat hf _)
  · rw [Ctx.namesCaps_cvar_here_inst, Ctx.namesCaps_cvar_here_inst]
    exact cover_weaken hw (h.cover_flat hf _)

theorem cover_cvar_here_leaf {f₁ : CapAtom (s1,c) → CapAtom (s2,c)}
    (hhere : f₁ (.cvar .here) = .cvar .here) {b : CapBound s1} {b' : CapBound s2}
    (hu : ∀ C, b ≠ .upper C) (hi : ∀ C, b ≠ .inst C)
    (hu' : ∀ C, b' ≠ .upper C) (hi' : ∀ C, b' ≠ .inst C) :
    ∀ z', z' ∈ (Γ'.consC b').namesCaps (.cvar .here) →
      ∃ z ∈ (Γ.consC b).namesCaps (.cvar .here), z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode := by
  intro z' hz'
  rw [Ctx.namesCaps_consC_leaf _ hu' hi'] at hz'
  rw [List.mem_singleton.mp hz']
  refine ⟨.cvar .here, by rw [Ctx.namesCaps_consC_leaf _ hu hi]; exact List.mem_singleton_self _,
    ?_, EMode.le_refl _⟩
  exact hhere.symm

theorem cover_name_leaf (h : Γ.NamesMap f Γ')
    {f₁ : CapAtom (s1,x) → CapAtom (s2,x)} (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    {b : Binding s1} {b' : Binding s2}
    (hb : ∀ T W Wc Fs, b ≠ .transparent T W Wc Fs) (hb' : ∀ T W Wc Fs, b' ≠ .transparent T W Wc Fs)
    (ℓ : Label) :
    ∀ z', z' ∈ (Γ'.cons b').namesCaps (.name .here ℓ) →
      ∃ z ∈ (Γ.cons b).namesCaps (.name .here ℓ), z'.base = f₁ z.base ∧
        z'.effMode ≤ z.effMode := by
  intro z' hz'
  rw [Ctx.namesCaps_name_here_leaf _ hb'] at hz'
  rw [List.mem_singleton.mp hz']
  have hmem : CapAtom.weaken Γ.rootAtom ∈ (Γ.cons b).namesCaps (.name .here ℓ) := by
    rw [Ctx.namesCaps_name_here_leaf _ hb]; exact List.mem_singleton_self _
  refine ⟨CapAtom.weaken Γ.rootAtom, hmem, ?_, ?_⟩
  · have hr : ∀ (Δ : Ctx s2), (CapAtom.weaken (k := .var) Δ.rootAtom).base =
        CapAtom.weaken Δ.rootAtom := by
      intro Δ; unfold Ctx.rootAtom; cases Δ.root? <;> rfl
    have hr₀ : (CapAtom.weaken (k := .var) Γ.rootAtom).base = CapAtom.weaken Γ.rootAtom := by
      unfold Ctx.rootAtom; cases Γ.root? <;> rfl
    rw [hr, hr₀, hw, h.rootAtom]
  · have hr : ∀ {s : Sig} (Δ : Ctx s), (CapAtom.weaken (k := .var) Δ.rootAtom).effMode = .eps := by
      intro s Δ; unfold Ctx.rootAtom; cases Δ.root? <;> rfl
    rw [hr, hr]; exact EMode.le_refl _

/-- The names a witness atom stands for, under a map lifted through the self. -/
theorem cover_selfInner (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f)
    {f₁ : CapAtom (s1,x) → CapAtom (s2,x)} (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    (hhere : f₁ (.var .here) = .var .here) (hname : ∀ ℓ, f₁ (.name .here ℓ) = .name .here ℓ)
    {T : Ty s1} {T' : Ty s2} (hT : T'.captureSet = T.captureSet.map f) :
    ∀ c : CapAtom (s1,x), c.base = c →
      ∀ v' ∈ Ctx.selfInner (fun a => Γ'.namesCaps a) T' (f₁ c),
        ∃ v ∈ Ctx.selfInner (fun a => Γ.namesCaps a) T c,
          v'.base = f v.base ∧ v'.effMode ≤ v.effMode := by
  intro c hc
  rcases CapAtom.cons_cases c with rfl | ⟨l, rfl⟩ | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
  · rw [hhere]
    show ∀ v' ∈ T'.captureSet.flatMap _, _
    rw [hT]
    exact h.cover_flat hf _
  · rw [hname]; intro v' hv'; cases hv'
  · have ha₀ : a₀.base = a₀ := CapAtom.base_of_weaken' hc
    have hfa : (f a₀).base = f a₀ := by rw [hf.base, ha₀]
    rw [hw, Ctx.selfInner_weaken_base _ (Ctx.namesCaps_top Γ') _ _ hfa,
      Ctx.selfInner_weaken_base _ (Ctx.namesCaps_top Γ) _ _ ha₀]
    exact h.names a₀
  · exact absurd hc (CapAtom.base_ne_mode _ m a₁)

theorem cover_name_transparent (h : Γ.NamesMap f Γ') (hf : CapAtom.NameMapFn f)
    {f₁ : CapAtom (s1,x) → CapAtom (s2,x)} (hf₁ : CapAtom.NameMapFn f₁)
    (hw : ∀ a, f₁ (CapAtom.weaken a) = CapAtom.weaken (f a))
    (hhere : f₁ (.var .here) = .var .here) (hname : ∀ ℓ, f₁ (.name .here ℓ) = .name .here ℓ)
    {T : Ty s1} {T' : Ty s2} {W : Witnesses (s1,x)} {W' : Witnesses (s2,x)}
    {Wc : CapWitnesses (s1,x)} {Wc' : CapWitnesses (s2,x)} {Fs Fs' : List Label}
    (hT : T'.captureSet = T.captureSet.map f)
    (hreach : ∀ ℓ, Wc'.reach ℓ = (Wc.reach ℓ).map f₁) (ℓ : Label) :
    ∀ z', z' ∈ (Γ'.cons (.transparent T' W' Wc' Fs')).namesCaps (.name .here ℓ) →
      ∃ z ∈ (Γ.cons (.transparent T W Wc Fs)).namesCaps (.name .here ℓ),
        z'.base = f₁ z.base ∧ z'.effMode ≤ z.effMode := by
  rw [Ctx.namesCaps_name_here_transparent, Ctx.namesCaps_name_here_transparent]
  refine cover_weaken hw ?_
  intro w' hw'
  obtain ⟨c', hc', hw'c⟩ := List.mem_flatMap.mp hw'
  rw [hreach] at hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  unfold Ctx.namesSelfWith at hw'c
  obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hw'c
  rw [hf₁.base] at hv'
  obtain ⟨v, hv, hvb, hve⟩ := h.cover_selfInner hf hw hhere hname hT c.base
    (CapAtom.base_base c) v' hv'
  refine ⟨v.applyEMode c.useMode, List.mem_flatMap.mpr ⟨c, hc, ?_⟩, ?_, ?_⟩
  · unfold Ctx.namesSelfWith
    exact List.mem_map_of_mem hv
  · rw [CapAtom.base_applyEMode, CapAtom.base_applyEMode, hvb]
  · rw [CapAtom.effMode_applyEMode, CapAtom.effMode_applyEMode]
    exact EMode.le_trans (EMode.comb_mono_left (hf₁.useMode c) _) (EMode.comb_mono _ hve)

/-- The identity keeps names. -/
theorem refl (Γ : Ctx s) : Γ.NamesMap (fun a => a) Γ where
  names a z' hz' := ⟨z', hz', rfl, EMode.le_refl _⟩
  rootAtom := rfl
  rootRefl _ h := h
  rootMap _ h := h
  surj κ' := Or.inl ⟨κ', rfl⟩
  inj κ₁ κ₂ κ' h₁ h₂ := by
    cases h₁; cases h₂; rfl
  consEq κ κ' hf := by cases hf; rfl
  claims h h' κ' hf hc := by cases hf; exact ⟨κ', rfl, hc⟩

/-- Weakening under a term binder keeps names: the capture spine is untouched. -/
theorem weaken (Γ : Ctx s) (b : Binding s) :
    Γ.NamesMap (CapAtom.weaken (k := .var)) (Γ.cons b) where
  names a z' hz' := by
    rw [Ctx.namesCaps_weaken] at hz'
    obtain ⟨z, hz, rfl⟩ := CaptureSet.mem_weaken.mp hz'
    refine ⟨z, hz, CapAtom.base_rename z _, ?_⟩
    rw [show (CapAtom.weaken (k := .var) z).effMode = z.effMode from CapAtom.effMode_rename z _]
    exact EMode.le_refl _
  rootAtom := Ctx.rootAtom_cons Γ b
  rootRefl x hx := by rwa [Ctx.isRootB_weaken] at hx
  rootMap x hx := by rwa [Ctx.isRootB_weaken]
  surj κ' := by
    cases κ' with
    | there κ'' => exact Or.inl ⟨κ'', rfl⟩
  inj κ₁ κ₂ κ' h₁ h₂ := by
    have := h₁.trans h₂.symm
    exact CapAtom.cvar.inj (CapAtom.weaken_inj this)
  consEq κ κ' hf := by
    obtain ⟨κ₀, rfl, he⟩ := CapAtom.weaken_eq_cvar hf
    cases he
    rw [Ctx.lookupCap_there, CapBound.consumable_weaken]
  claims h h' κ' hf hc := by
    obtain ⟨h₀, rfl, he⟩ := CapAtom.weaken_eq_cvar hf
    cases he
    cases κ' with
    | there κ'' =>
        rw [Ctx.claimsB_cons_there] at hc
        exact ⟨κ'', rfl, hc⟩

end Ctx.NamesMap

/-! ## Capture weakening under a binder that is no root

Plan-5h decision 38.  A root opens every capture binder that is no root, so
the names of a weakened set are the weakened names, and the new binder under
a root of the old set at that root's mode.  A kill-ok set never consumes the
new binder, so the kill of a weakened set is the weakened kill, and a names
map of the weakening has the new binder as its one fresh binder. -/

theorem CaptureSet.weaken_eq_map {k : Kind} (C : CaptureSet s) :
    CaptureSet.weaken (k := k) C = C.map (CapAtom.weaken (k := k)) := rfl

namespace Ctx.NamesMap

/-- **Weakening under a capture binder that is no root and is live keeps
names**, with the new binder fresh. -/
theorem weakenC (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) (hl : b.live = true) :
    Γ.NamesMap (CapAtom.weaken (k := .cap)) (Γ.consC b) where
  names a z' hz' := by
    rw [Ctx.namesCaps_weakenC] at hz'
    obtain ⟨z, hz, rfl⟩ := CaptureSet.mem_weaken.mp hz'
    refine ⟨z, hz, CapAtom.base_rename z _, ?_⟩
    rw [show (CapAtom.weaken (k := .cap) z).effMode = z.effMode from CapAtom.effMode_rename z _]
    exact EMode.le_refl _
  rootAtom := Ctx.rootAtom_consC Γ b hb
  rootRefl x hx := by rwa [Ctx.isRootB_weakenC] at hx
  rootMap x hx := by rwa [Ctx.isRootB_weakenC]
  surj κ' := by
    cases κ' with
    | here =>
        refine Or.inr ⟨?_, ?_, ?_⟩
        · rw [Ctx.lookupCap_here, CapBound.isRoot_weaken]; exact hb
        · show ((Γ.consC b).lookupCap .here).live = true
          rw [Ctx.lookupCap_here, CapBound.live_weaken]; exact hl
        · intro κ he
          exact CapAtom.cvar_here_ne_weaken (CapAtom.cvar κ) he.symm
    | there κ'' => exact Or.inl ⟨κ'', rfl⟩
  inj κ₁ κ₂ κ' h₁ h₂ := by
    have := h₁.trans h₂.symm
    exact CapAtom.cvar.inj (CapAtom.weaken_inj this)
  consEq κ κ' hf := by
    obtain ⟨κ₀, rfl, he⟩ := CapAtom.weaken_eq_cvar hf
    cases he
    rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]
  claims h h' κ' hf hc := by
    obtain ⟨h₀, rfl, he⟩ := CapAtom.weaken_eq_cvar hf
    cases he
    cases κ' with
    | here => rw [Ctx.claimsB_right_here] at hc; cases hc
    | there κ'' =>
        rw [Ctx.claimsB_consC_there] at hc
        exact ⟨κ'', rfl, hc⟩

end Ctx.NamesMap

/-! ### The names of a weakened set -/

/-- Phase one of a weakened atom is the weakened phase one. -/
theorem Ctx.phase1_weakenC (Γ : Ctx s) (b : CapBound s) (c : CapAtom s) :
    ((Γ.consC b).namesCaps (CapAtom.weaken (k := .cap) c).base).map
        (CapAtom.weaken (k := .cap) c).useApply
      = ((Γ.namesCaps c.base).map c.useApply).map (CapAtom.weaken (k := .cap)) := by
  rw [CapAtom.weaken_base', Ctx.namesCaps_weakenC]
  simp only [CaptureSet.weaken, CaptureSet.rename, List.map_map]
  apply List.map_congr_left
  intro x _
  exact CapAtom.weaken_useApply c x

/-- **Phase two of a weakened atom**: a weakened name of the old expansion,
or the new binder under an old root, at the root's mode. -/
theorem Ctx.mem_expandNames_weakenC (Γ : Ctx s) (b : CapBound s) (y : CapAtom s)
    {z' : CapAtom (s,c)} (h : z' ∈ (Γ.consC b).expandNames (CapAtom.weaken (k := .cap) y)) :
    (∃ z ∈ Γ.expandNames y, z' = CapAtom.weaken (k := .cap) z) ∨
      (z'.base = .cvar .here ∧ z'.effMode = y.effMode ∧ Γ.isRootB y.base = true) := by
  unfold Ctx.expandNames at h
  rw [CapAtom.weaken_base', Ctx.isRootB_weakenC] at h
  by_cases hr : Γ.isRootB y.base = true
  · rw [if_pos hr] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl ⟨y, Γ.mem_expandNames_self y, rfl⟩
    · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp h
      obtain ⟨hκ'm, hκ'f⟩ := List.mem_filter.mp hκ'
      rw [Ctx.capBinders_consC] at hκ'm
      rcases List.mem_cons.mp hκ'm with rfl | hκ'm
      · refine Or.inr ⟨?_, ?_, hr⟩
        · rw [CapAtom.reapply_eq, CapAtom.base_applyEMode]; rfl
        · rw [CapAtom.reapply_eq, CapAtom.effMode_applyEMode, CapAtom.weaken_effMode']
          exact EMode.comb_eps _
      · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hκ'm
        rw [Ctx.lookupCap_thereC, CapBound.isRoot_weaken] at hκ'f
        refine Or.inl ⟨y.reapply (.cvar κ), ?_, ?_⟩
        · unfold Ctx.expandNames
          rw [if_pos hr]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨κ, List.mem_filter.mpr ⟨hκ, hκ'f⟩, rfl⟩)
        · rw [CapAtom.cvar_there, CapAtom.weaken_reapply]
  · rw [if_neg hr] at h
    rw [List.mem_singleton.mp h]
    exact Or.inl ⟨y, Γ.mem_expandNames_self y, rfl⟩

/-- The converse of the old half. -/
theorem Ctx.weaken_mem_expandNames (Γ : Ctx s) (b : CapBound s) (y : CapAtom s)
    {z : CapAtom s} (h : z ∈ Γ.expandNames y) :
    CapAtom.weaken (k := .cap) z ∈ (Γ.consC b).expandNames (CapAtom.weaken (k := .cap) y) := by
  unfold Ctx.expandNames at h ⊢
  rw [CapAtom.weaken_base', Ctx.isRootB_weakenC]
  by_cases hr : Γ.isRootB y.base = true
  · rw [if_pos hr] at h ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
      obtain ⟨hκm, hκf⟩ := List.mem_filter.mp hκ
      refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨.there κ, ?_, ?_⟩)
      · refine List.mem_filter.mpr ⟨?_, ?_⟩
        · rw [Ctx.capBinders_consC]
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem hκm)
        · rw [Ctx.lookupCap_thereC, CapBound.isRoot_weaken]; exact hκf
      · rw [CapAtom.cvar_there, CapAtom.weaken_reapply]
  · rw [if_neg hr] at h ⊢
    rw [List.mem_singleton.mp h]
    exact List.mem_singleton_self _

/-- **The names of a weakened set**: a weakened name, or the new binder under
a root of the old set, at that root's mode. -/
theorem Ctx.mem_names_weakenC (Γ : Ctx s) (b : CapBound s) (C : CaptureSet s)
    {z' : CapAtom (s,c)} (h : z' ∈ (Γ.consC b).names (CaptureSet.weaken (k := .cap) C)) :
    (∃ z ∈ Γ.names C, z' = CapAtom.weaken (k := .cap) z) ∨
      (z'.base = .cvar .here ∧ ∃ y ∈ Γ.names C, Γ.isRootB y.base = true ∧
        z'.effMode = y.effMode) := by
  rw [CaptureSet.weaken_eq_map] at h
  obtain ⟨c', hc', hz'⟩ := List.mem_flatMap.mp h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  unfold Ctx.namesAtom at hz'
  rw [Ctx.phase1_weakenC] at hz'
  obtain ⟨y', hy', hz'y⟩ := List.mem_flatMap.mp hz'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
  have hyN : ∀ {z}, z ∈ Γ.expandNames y → z ∈ Γ.names C := fun hz =>
    List.mem_flatMap.mpr ⟨c, hc, List.mem_flatMap.mpr ⟨y, hy, hz⟩⟩
  rcases Γ.mem_expandNames_weakenC b y hz'y with ⟨z, hz, rfl⟩ | ⟨hb, he, hr⟩
  · exact Or.inl ⟨z, hyN hz, rfl⟩
  · exact Or.inr ⟨hb, y, hyN (Γ.mem_expandNames_self y), hr, he⟩

/-- Every old name, weakened, is a name of the weakened set. -/
theorem Ctx.weaken_mem_names (Γ : Ctx s) (b : CapBound s) (C : CaptureSet s)
    {z : CapAtom s} (h : z ∈ Γ.names C) :
    CapAtom.weaken (k := .cap) z ∈ (Γ.consC b).names (CaptureSet.weaken (k := .cap) C) := by
  rw [CaptureSet.weaken_eq_map]
  obtain ⟨c, hc, hz⟩ := List.mem_flatMap.mp h
  unfold Ctx.namesAtom at hz
  obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz
  refine List.mem_flatMap.mpr ⟨CapAtom.weaken (k := .cap) c, List.mem_map_of_mem hc, ?_⟩
  unfold Ctx.namesAtom
  rw [Ctx.phase1_weakenC]
  exact List.mem_flatMap.mpr ⟨CapAtom.weaken (k := .cap) y, List.mem_map_of_mem hy,
    Γ.weaken_mem_expandNames b y hzy⟩

/-! ### The kill premises under a capture weakening -/

/-- The kill premise survives a capture weakening. -/
theorem Ctx.KillOk.weakenC {Γ : Ctx s} {C : CaptureSet s} (h : Γ.KillOk C) (b : CapBound s) :
    (Γ.consC b).KillOk (CaptureSet.weaken (k := .cap) C) := by
  intro z' hz' hm
  rcases Γ.mem_names_weakenC b C hz' with ⟨z, hz, rfl⟩ | ⟨_, y, hy, hr, he⟩
  · rw [CapAtom.weaken_effMode'] at hm
    obtain ⟨κ, hb, hc⟩ := h z hz hm
    refine ⟨.there κ, by rw [CapAtom.weaken_base', hb]; rfl, ?_⟩
    rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]; exact hc
  · rw [he] at hm
    exact (h.not_root hy hr hm).elim

/-- **The consumed names of a weakened kill-ok set are the weakened consumed
names.** -/
theorem Ctx.consumedNames_weakenC {Γ : Ctx s} {C : CaptureSet s} (hk : Γ.KillOk C)
    (b : CapBound s) (κ' : BVar (s,c) .cap) :
    κ' ∈ (Γ.consC b).consumedNames (CaptureSet.weaken (k := .cap) C) ↔
      ∃ κ ∈ Γ.consumedNames C, κ' = .there κ := by
  constructor
  · intro h
    obtain ⟨z', hz', hsel⟩ := List.mem_filterMap.mp h
    split at hsel
    · rename_i hm
      have hz'b : z'.base = .cvar κ' := by
        cases hzb : z'.base <;> rw [hzb] at hsel <;> simp [CapAtom.cvar?] at hsel
        rw [hsel]
      rcases Γ.mem_names_weakenC b C hz' with ⟨z, hz, rfl⟩ | ⟨_, y, hy, hr, he⟩
      · rw [CapAtom.weaken_effMode'] at hm
        rw [CapAtom.weaken_base'] at hz'b
        obtain ⟨κ, rfl, hzκ⟩ := CapAtom.weaken_eq_cvar hz'b
        refine ⟨κ, List.mem_filterMap.mpr ⟨z, hz, ?_⟩, rfl⟩
        rw [if_pos hm, hzκ]; rfl
      · rw [he] at hm
        exact (hk.not_root hy hr hm).elim
    · cases hsel
  · rintro ⟨κ, hκ, rfl⟩
    obtain ⟨z, hz, hsel⟩ := List.mem_filterMap.mp hκ
    split at hsel
    · rename_i hm
      have hzb : z.base = .cvar κ := by
        cases hzb : z.base <;> rw [hzb] at hsel <;> simp [CapAtom.cvar?] at hsel
        rw [hsel]
      refine List.mem_filterMap.mpr ⟨CapAtom.weaken (k := .cap) z, Γ.weaken_mem_names b C hz, ?_⟩
      rw [if_pos (by rw [CapAtom.weaken_effMode']; exact hm), CapAtom.weaken_base', hzb]; rfl
    · cases hsel

/-- Possible ownership from an old binder stays among old binders. -/
theorem Ctx.MayOwn.of_weakenC {Γ : Ctx s} {b : CapBound s} {h' κ' : BVar (s,c) .cap}
    (hm : (Γ.consC b).MayOwn h' κ') :
    ∀ h₀, h' = .there h₀ → ∃ κ, κ' = .there κ ∧ Γ.MayOwn h₀ κ := by
  induction hm with
  | @direct h₁ κ₁ hd =>
      intro h₀ he
      subst he
      cases κ₁ with
      | here => rw [Ctx.claimsB_right_here] at hd; cases hd
      | there κ =>
          rw [Ctx.claimsB_consC_there] at hd
          exact ⟨κ, rfl, .direct hd⟩
  | trans _ _ ih₁ ih₂ =>
      intro h₀ hh
      obtain ⟨c₁, rfl, hm₁⟩ := ih₁ h₀ hh
      obtain ⟨κ, rfl, hm₂⟩ := ih₂ c₁ rfl
      exact ⟨κ, rfl, .trans hm₁ hm₂⟩

theorem Ctx.MayOwn.weakenC {Γ : Ctx s} {h κ : BVar s .cap} (hm : Γ.MayOwn h κ)
    (b : CapBound s) : (Γ.consC b).MayOwn h.there κ.there := by
  induction hm with
  | direct hd => exact .direct (by rw [Ctx.claimsB_consC_there]; exact hd)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The closure of a weakened list is the weakened closure. -/
theorem Ctx.ownClosure_weakenC (Γ : Ctx s) (b : CapBound s) (L : List (BVar s .cap))
    (L' : List (BVar (s,c) .cap)) (hL : ∀ κ', κ' ∈ L' ↔ ∃ κ ∈ L, κ' = .there κ)
    (κ' : BVar (s,c) .cap) :
    κ' ∈ (Γ.consC b).ownClosure L' ↔ ∃ κ ∈ Γ.ownClosure L, κ' = .there κ := by
  rw [Ctx.mem_ownClosure]
  constructor
  · rintro (hm | ⟨h', hh', hm⟩)
    · obtain ⟨κ, hκ, rfl⟩ := (hL κ').mp hm
      exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inl hκ), rfl⟩
    · obtain ⟨h₀, hh₀, rfl⟩ := (hL h').mp hh'
      obtain ⟨κ, rfl, hm₀⟩ := hm.of_weakenC h₀ rfl
      exact ⟨κ, Ctx.mem_ownClosure.mpr (Or.inr ⟨h₀, hh₀, hm₀⟩), rfl⟩
  · rintro ⟨κ, hκ, rfl⟩
    rcases Ctx.mem_ownClosure.mp hκ with hm | ⟨h₀, hh₀, hm⟩
    · exact Or.inl ((hL _).mpr ⟨κ, hm, rfl⟩)
    · exact Or.inr ⟨.there h₀, (hL _).mpr ⟨h₀, hh₀, rfl⟩, hm.weakenC b⟩

/-! ### A kill reads its list as a set -/

/-- Kill every capture binder a predicate selects, in place. -/
def Ctx.killBy : {s : Sig} → Ctx s → (BVar s .cap → Bool) → Ctx s
  | _, .nil, _ => .nil
  | _, .cons Γ b, p => .cons (Γ.killBy (fun κ => p (.there κ))) b
  | _, .consC Γ b, p => .consC (Γ.killBy (fun κ => p (.there κ))) (if p .here then b.kill else b)

theorem Ctx.killBy_false : ∀ {s : Sig} (Γ : Ctx s), Γ.killBy (fun _ => false) = Γ
  | _, .nil => rfl
  | _, .cons Γ b => by
      show Ctx.cons (Γ.killBy (fun _ => false)) b = _
      rw [Ctx.killBy_false Γ]
  | _, .consC Γ b => by
      show Ctx.consC (Γ.killBy (fun _ => false)) (if false = true then b.kill else b) = _
      rw [Ctx.killBy_false Γ]; rfl

theorem Ctx.killBy_congr {Γ : Ctx s} {p q : BVar s .cap → Bool} (h : ∀ κ, p κ = q κ) :
    Γ.killBy p = Γ.killBy q := by
  have : p = q := funext h
  rw [this]

theorem Ctx.killAt_killBy : ∀ {s : Sig} (Γ : Ctx s) (p : BVar s .cap → Bool) (κ : BVar s .cap),
    (Γ.killBy p).killAt κ = Γ.killBy (fun k => p k || decide (k = κ))
  | _, .nil, _, κ => by cases κ
  | _, .cons Γ b, p, .there κ => by
      show Ctx.cons ((Γ.killBy (fun k => p (.there k))).killAt κ) b = _
      rw [Ctx.killAt_killBy Γ _ κ]
      show _ = Ctx.cons (Γ.killBy (fun k => p (.there k) || decide (BVar.there k = .there κ))) b
      congr 1
      apply Ctx.killBy_congr
      intro k
      by_cases hk : k = κ
      · subst hk; simp
      · have : (BVar.there k : BVar (_,x) .cap) ≠ .there κ := fun e => hk (BVar.there.inj e)
        simp [hk, this]
  | _, .consC Γ b, p, .here => by
      simp only [Ctx.killBy, Ctx.killAt]
      congr 1
      · apply Ctx.killBy_congr
        intro k
        simp
      · cases p .here <;> simp [CapBound.kill_kill]
  | _, .consC Γ b, p, .there κ => by
      show Ctx.consC ((Γ.killBy (fun k => p (.there k))).killAt κ)
          (if p .here = true then b.kill else b) = _
      rw [Ctx.killAt_killBy Γ _ κ]
      show _ = Ctx.consC (Γ.killBy (fun k => p (.there k) || decide (BVar.there k = .there κ)))
          (if (p .here || decide ((BVar.here : BVar (_,c) .cap) = .there κ)) = true
            then b.kill else b)
      have hh : decide ((BVar.here : BVar (_,c) .cap) = .there κ) = false := by simp
      rw [hh, Bool.or_false]
      congr 1
      apply Ctx.killBy_congr
      intro k
      by_cases hk : k = κ
      · subst hk; simp
      · have : (BVar.there k : BVar (_,c) .cap) ≠ .there κ := fun e => hk (BVar.there.inj e)
        simp [hk, this]

theorem Ctx.killBy_killNames (Γ : Ctx s) (p : BVar s .cap → Bool) (D : List (BVar s .cap)) :
    (Γ.killBy p).killNames D = Γ.killBy (fun k => p k || decide (k ∈ D)) := by
  induction D generalizing p with
  | nil => simp [Ctx.killNames]
  | cons κ D ih =>
      show ((Γ.killBy p).killAt κ).killNames D = _
      rw [Ctx.killAt_killBy, ih]
      apply Ctx.killBy_congr
      intro k
      simp [Bool.or_assoc]

/-- A kill is a kill by membership. -/
theorem Ctx.killNames_eq_killBy (Γ : Ctx s) (D : List (BVar s .cap)) :
    Γ.killNames D = Γ.killBy (fun k => decide (k ∈ D)) := by
  have := Ctx.killBy_killNames Γ (fun _ => false) D
  rw [Ctx.killBy_false] at this
  rw [this]
  apply Ctx.killBy_congr
  intro k; simp

/-- **A kill reads its list as a set.** -/
theorem Ctx.killNames_congr (Γ : Ctx s) {D D' : List (BVar s .cap)}
    (h : ∀ κ, κ ∈ D ↔ κ ∈ D') : Γ.killNames D = Γ.killNames D' := by
  rw [Ctx.killNames_eq_killBy, Ctx.killNames_eq_killBy]
  apply Ctx.killBy_congr
  intro k
  simp [h k]

/-- **The kill of a weakened kill-ok set is the weakened kill**, as contexts.
So a body or an evidence read under the kill is weakened under the new
binder, and the new binder stays as it was appended. -/
theorem Ctx.killFor_weakenC {Γ : Ctx s} {C : CaptureSet s} (hk : Γ.KillOk C) (b : CapBound s) :
    (Γ.consC b).killFor (CaptureSet.weaken (k := .cap) C) = (Γ.killFor C).consC b := by
  unfold Ctx.killFor
  rw [← Ctx.killNames_consC]
  apply Ctx.killNames_congr
  intro κ'
  rw [Ctx.ownClosure_weakenC Γ b (Γ.consumedNames C) _ (Ctx.consumedNames_weakenC hk b) κ']
  constructor
  · rintro ⟨κ, hκ, rfl⟩; exact List.mem_map_of_mem hκ
  · intro h
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
    exact ⟨κ, hκ, rfl⟩

/-- The claims of a weakened kill-ok set are the weakened claims, up to
order and repetition, which `claimsB` does not read. -/
theorem Ctx.claimsFor_weakenC {Γ : Ctx s} {C : CaptureSet s} (hk : Γ.KillOk C) (b : CapBound s)
    (a : CapAtom (s,c)) :
    a ∈ (Γ.consC b).claimsFor (CaptureSet.weaken (k := .cap) C) ↔
      a ∈ CaptureSet.weaken (k := .cap) (Γ.claimsFor C) := by
  unfold Ctx.claimsFor
  simp only [CaptureSet.weaken_eq_map, List.mem_map]
  constructor
  · rintro ⟨κ', hκ', rfl⟩
    obtain ⟨κ, hκ, rfl⟩ :=
      (Ctx.ownClosure_weakenC Γ b _ _ (Ctx.consumedNames_weakenC hk b) κ').mp hκ'
    exact ⟨.cvar κ, ⟨κ, hκ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩
    exact ⟨.there κ,
      (Ctx.ownClosure_weakenC Γ b _ _ (Ctx.consumedNames_weakenC hk b) _).mpr ⟨κ, hκ, rfl⟩, rfl⟩

/-! ### The read premises under a capture weakening -/

/-- Accessibility survives appending a live binder. -/
theorem Ctx.Accessible.weakenC {Γ : Ctx s} {C : CaptureSet s} (h : Γ.Accessible C)
    {b : CapBound s} (hb : b.live = true) :
    (Γ.consC b).Accessible (CaptureSet.weaken (k := .cap) C) := by
  intro z' hz' κ' hκ'
  rcases Γ.mem_names_weakenC b C hz' with ⟨z, hz, rfl⟩ | ⟨hb', _⟩
  · rw [CapAtom.weaken_base'] at hκ'
    obtain ⟨κ, rfl, hzκ⟩ := CapAtom.weaken_eq_cvar hκ'
    exact (h z hz κ hzκ).weakenC b
  · rw [hb'] at hκ'
    cases hκ'
    refine .live ?_
    unfold Ctx.BitLive
    rw [Ctx.lookupCap_here, CapBound.live_weaken]; exact hb

/-- Argument separation survives, when the consumed side is kill-ok: a name
of the new binder comes from a root, and a set whose names hold a root
separates only from a set that consumes nothing (plan-5h decision 39,
`ArgSepO.weakenC` of the ownership round). -/
theorem Ctx.ArgSep.weakenC {Γ : Ctx s} {B C : CaptureSet s} (h : Γ.ArgSep B C)
    (hk : Γ.KillOk C) (b : CapBound s) :
    (Γ.consC b).ArgSep (CaptureSet.weaken (k := .cap) B) (CaptureSet.weaken (k := .cap) C) := by
  intro z' hz' κ' hκ'
  have hcn := Ctx.consumedNames_weakenC hk b
  rcases Γ.mem_names_weakenC b B hz' with ⟨z, hz, rfl⟩ | ⟨hb', y, hy, hr, -⟩
  · rw [CapAtom.weaken_base'] at hκ'
    obtain ⟨κ, hκe, hzκ⟩ := CapAtom.weaken_eq_cvar hκ'
    cases hκe
    obtain ⟨h₁, h₂⟩ := h z hz κ hzκ
    refine ⟨fun hmem => ?_, fun l' hl' hm => ?_⟩
    · obtain ⟨κ₀, hκ₀, he⟩ :=
        (Ctx.ownClosure_weakenC Γ b _ _ hcn (.there κ)).mp hmem
      cases he
      exact h₁ hκ₀
    · obtain ⟨l, hl, rfl⟩ := (hcn l').mp hl'
      obtain ⟨l₀, he, hm₀⟩ := hm.of_weakenC κ rfl
      cases he
      exact h₂ l hl hm₀
  · rw [hb'] at hκ'
    cases hκ'
    refine ⟨fun hmem => ?_, fun l' hl' _ => ?_⟩
    · obtain ⟨κ₀, -, he⟩ := (Ctx.ownClosure_weakenC Γ b _ _ hcn .here).mp hmem
      cases he
    · obtain ⟨l, hl, -⟩ := (hcn l').mp hl'
      exact h.not_consumed_of_root hk hy hr hl

/-- Consumability survives appending any binder, an heir included, since it
reads no mask. -/
theorem Ctx.ConsumeOk.weakenC {Γ : Ctx s} {C : CaptureSet s} (h : Γ.ConsumeOk C)
    (b : CapBound s) : (Γ.consC b).ConsumeOk (CaptureSet.weaken (k := .cap) C) := by
  intro z' hz' hm
  rcases Γ.mem_names_weakenC b C hz' with ⟨z, hz, rfl⟩ | ⟨_, y, hy, hr, he⟩
  · rw [CapAtom.weaken_effMode'] at hm
    obtain ⟨κ, hb, hc, hl⟩ := h z hz hm
    refine ⟨.there κ, by rw [CapAtom.weaken_base', hb]; rfl, ?_, ?_⟩
    · rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]; exact hc
    · unfold Ctx.BitLive at hl ⊢
      rw [Ctx.lookupCap_thereC, CapBound.live_weaken]; exact hl
  · rw [he] at hm
    exact ((Ctx.KillOk.of_consumeOk h).not_root hy hr hm).elim

/-- What an appended heir masks: the old masks and its own names. -/
theorem Ctx.masked_consC_own_iff (Γ : Ctx s) (bit : Bool) (W : CaptureSet s)
    (κ : BVar s .cap) :
    (Γ.consC (.own bit W)).Masked (.there κ) ↔ Γ.Masked κ ∨ CapAtom.cvar κ ∈ W := by
  rw [Ctx.masked_consC_iff]
  show _ ∨ W.elem (.cvar κ) = true ↔ _
  rw [CaptureSet.elem_iff]

end FCdot

end Separation
