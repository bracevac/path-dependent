import Coercions.Separation.FCdot.Machine
import Coercions.Separation.FCdot.TypingSubst
import Coercions.Separation.FCdot.Transparency
import Coercions.Separation.FCdot.ModeBounds

namespace Separation

/-!
# Retyping for the FCdot store machine

The lemmas preservation reads at each step: store lookups, continuation
weakening, the substitution instances the machine uses, the answer sort, and
the typed result of each step.  They are split off `Preservation.lean` so that
they build before the steps of the machine (plan-5h S0.13, group g6r).
-/

namespace FCdot

/-! ## Renaming algebra for stores -/

theorem Rename.succ_lift_comp_subst_here {s : Sig} {k : Kind} :
    (Rename.succ (s := s) (k := k)).lift.comp
        (Rename.subst (BVar.here : BVar (s,,k) k)) = Rename.id := by
  apply Rename.funext'
  intro k' x
  cases x <;> rfl

theorem Rename.succ_lift_comp_subst_there {s : Sig} {k k0 : Kind} (y : BVar s k) :
    (Rename.succ (s := s) (k := k0)).lift.comp
        (Rename.subst (BVar.there y : BVar (s,,k0) k))
      = (Rename.subst y).comp (Rename.succ (k := k0)) := by
  apply Rename.funext'
  intro k' x
  cases x <;> rfl

/-! ## Values under renaming -/

theorem Value.witnesses_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2),
      (v.rename ρ).witnesses = v.witnesses.rename ρ.lift
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.witnesses]
  | .box _, _ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .cell _ _, _ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .reader _, _ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .cast v _, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]
  | .pack _ _ _ v, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]
  | .packF _ _ v, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]

theorem Value.fieldLabels_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).fieldLabels = v.fieldLabels
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .box _, _ => by simp [Value.rename, Value.fieldLabels]
  | .cell _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .reader _, _ => by simp [Value.rename, Value.fieldLabels]
  | .cast v _, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]
  | .pack _ _ _ v, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]
  | .packF _ _ v, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]

/-- Capture witnesses commute with renaming, as block witnesses do. -/
theorem Value.capWitnesses_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2),
      (v.rename ρ).capWitnesses = v.capWitnesses.rename ρ.lift
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.capWitnesses]
  | .box _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .cell _ _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .reader _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .cast v _, ρ => by
      simp [Value.rename, Value.capWitnesses, Value.capWitnesses_rename v ρ]
  | .pack _ _ _ v, ρ => by
      simp [Value.rename, Value.capWitnesses, Value.capWitnesses_rename v ρ]
  | .packF _ _ v, ρ => by
      simp [Value.rename, Value.capWitnesses, Value.capWitnesses_rename v ρ]

theorem Value.core_witnesses {s : Sig} :
    ∀ v : Value s, v.core.witnesses = v.witnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cell _ _ => rfl
  | .reader _ => rfl
  | .cast v _ => by simp [Value.core, Value.witnesses, Value.core_witnesses v]
  | .pack _ _ _ _ => rfl
  | .packF _ _ _ => rfl

theorem Value.core_capWitnesses {s : Sig} :
    ∀ v : Value s, v.core.capWitnesses = v.capWitnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cell _ _ => rfl
  | .reader _ => rfl
  | .cast v _ => by simp [Value.core, Value.capWitnesses, Value.core_capWitnesses v]
  | .pack _ _ _ _ => rfl
  | .packF _ _ _ => rfl

theorem Value.core_fieldLabels {s : Sig} :
    ∀ v : Value s, v.core.fieldLabels = v.fieldLabels
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cell _ _ => rfl
  | .reader _ => rfl
  | .cast v _ => by simp [Value.core, Value.fieldLabels, Value.core_fieldLabels v]
  | .pack _ _ _ _ => rfl
  | .packF _ _ _ => rfl

theorem Value.core_isLiteral {s : Sig} : ∀ v : Value s, v.core.IsLiteral
  | .lam _ _ _ _ => trivial
  | .obj _ _ _ _ => trivial
  | .box _ => trivial
  | .cell _ _ => trivial
  | .reader _ => trivial
  | .cast v _ => by simpa [Value.core] using Value.core_isLiteral v
  -- `Value.IsLiteral` gains no clause, so a pack falls into its catch-all and
  -- `core` is the identity on it.  A packed value is kept out of a store by
  -- `Store.Typed.cons`, which premises `Value.HasType`, and that has no pack rule.
  | .pack _ _ _ _ => trivial
  | .packF _ _ _ => trivial

/-! ## Composites of cast wrappers -/

theorem LeCo.composite_append {s : Sig} :
    ∀ (e : LeCo s) (l1 l2 : List (LeCo s)),
      LeCo.composite e (l1 ++ l2) = LeCo.composite (LeCo.composite e l1) l2
  | _, [], _ => rfl
  | e, f :: fs, l2 => by
      simp [LeCo.composite, LeCo.composite_append (.trans e f) fs l2]

theorem LeCo.composite_snoc {s : Sig} (e f : LeCo s) (l : List (LeCo s)) :
    LeCo.composite e (l ++ [f]) = .trans (LeCo.composite e l) f := by
  rw [LeCo.composite_append]
  rfl

/-- Stripping the cast wrappers of a well-typed value: the literal underneath
is well typed, and the composite of the wrappers coerces its type to the
value's type. -/
theorem Value.HasType.coreDecomp {s : Sig} {Γ : Ctx s} :
    ∀ (v : Value s) (T : Ty s), Γ ⊢ᵥ v : T →
      ∃ S₀, Γ ⊢ᵥ v.core : S₀ ∧ v.core.IsLiteral ∧
        ((v.composite? = none ∧ S₀ = T) ∨
          ∃ E, v.composite? = some E ∧ Γ ⊢ E : S₀ ≤ T)
  | .lam _ _ _ _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .obj _ _ _ _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .box _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .cell _ _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .reader _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .cast v e, T, h => by
      cases h with
      | cast hv he =>
          obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v _ hv
          refine ⟨S₀, by simpa [Value.core] using hcore,
            by simpa [Value.core] using hlit, Or.inr ?_⟩
          cases hc : v.coercions with
          | nil =>
              rcases hd with ⟨_, rfl⟩ | ⟨E, hE?, _⟩
              · exact ⟨e, by simp [Value.composite?, Value.coercions, hc, LeCo.composite], he⟩
              · simp [Value.composite?, hc] at hE?
          | cons f fs =>
              rcases hd with ⟨hn, _⟩ | ⟨E, hE?, hE⟩
              · simp [Value.composite?, hc] at hn
              · obtain rfl : LeCo.composite f fs = E := by
                  simpa [Value.composite?, hc] using hE?
                exact ⟨.trans (LeCo.composite f fs) e,
                  by simp [Value.composite?, Value.coercions, hc, LeCo.composite_snoc],
                  .trans hE he⟩
  -- `Value.HasType` has no `pack` rule, so a packed value has no plain type.
  | .pack _ _ _ _, _, h => nomatch h

/-! ## Store typing -/

theorem Store.Typed.lookup {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ x : BVar s .var, Γ ⊢ᵥ (σ.lookup x) : (Γ.lookupTy x) := by
  induction h with
  | nil => intro x; cases x
  | cons _ _ hv ih =>
      intro x
      cases x with
      | here => simpa [Store.lookup, Binding.ty] using hv.weaken _
      | there y => simpa [Store.lookup] using (ih y).weaken _
  | consC _ hb hl ih =>
      intro x
      cases x with
      | there y => simpa [Store.lookup] using (ih y).weakenC _ hb hl
  | write _ _ _ ih => exact ih

theorem Store.Typed.lookupFields {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : ⊢ σ : Γ) :
    ∀ x : BVar s .var, Γ.lookupFields x = some (σ.lookup x).fieldLabels := by
  induction h with
  | nil => intro x; cases x
  | cons _ _ _ ih =>
      intro x
      cases x with
      | here =>
          simp [Store.lookup, Value.weaken, Value.fieldLabels_rename]
      | there y =>
          simp only [Ctx.lookupFields_there, ih y, Store.lookup, Value.weaken,
            Value.fieldLabels_rename]
  | consC _ _ _ ih =>
      intro x
      cases x with
      | there y =>
          simp only [Ctx.lookupFields_thereC, ih y, Store.lookup, Value.weaken,
            Value.fieldLabels_rename]
  | write _ _ _ ih => exact ih

theorem Store.Typed.isTransparent {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : ⊢ σ : Γ) (x : BVar s .var) : Γ.IsTransparent x :=
  Ctx.IsTransparent.of_lookup (h.lookupFields x)

theorem Store.Typed.lookupDef {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ (x : BVar s .var) (l : Label),
      Γ.lookupDef x l = some (((σ.lookup x).witnesses.get l)⟦x⟧) := by
  induction h with
  | nil => intro x l; cases x
  | cons _ _ _ ih =>
      intro x l
      cases x with
      | here =>
          simp only [Ctx.lookupDef, Store.lookup, Value.weaken, Value.witnesses_rename,
            Witnesses.get_rename, Shape.substVar, Shape.rename_comp,
            Rename.succ_lift_comp_subst_here, Shape.rename_id]
      | there y =>
          simp only [Ctx.lookupDef_there, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.witnesses_rename, Witnesses.get_rename, Shape.substVar,
            Shape.weaken, Shape.rename_comp, Rename.succ_lift_comp_subst_there]
  | consC _ _ _ ih =>
      intro x l
      cases x with
      | there y =>
          simp only [Ctx.lookupDef_thereC, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.witnesses_rename, Witnesses.get_rename, Shape.substVar,
            Shape.weaken, Shape.rename_comp, Rename.succ_lift_comp_subst_there]
  | write _ _ _ ih => exact ih

/-- The capture definition a typed store records at a variable is the
value's capture witness, read at the binder -- the capture-sort twin of
`Store.Typed.lookupDef`. -/
theorem Store.Typed.lookupDefC {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ (x : BVar s .var) (l : Label),
      Γ.lookupDefC x l = some (((σ.lookup x).capWitnesses.get l)⟦x⟧) := by
  induction h with
  | nil => intro x l; cases x
  | cons _ _ _ ih =>
      intro x l
      cases x with
      | here =>
          simp only [Ctx.lookupDefC, Store.lookup, Value.weaken, Value.capWitnesses_rename,
            CapWitnesses.get_rename, CaptureSet.substVar, CaptureSet.rename_comp,
            Rename.succ_lift_comp_subst_here, CaptureSet.rename_id]
      | there y =>
          simp only [Ctx.lookupDefC_there, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.capWitnesses_rename, CapWitnesses.get_rename,
            CaptureSet.substVar, CaptureSet.weaken, CaptureSet.rename_comp,
            Rename.succ_lift_comp_subst_there]
  | consC _ _ _ ih =>
      intro x l
      cases x with
      | there y =>
          simp only [Ctx.lookupDefC_thereC, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.capWitnesses_rename, CapWitnesses.get_rename,
            CaptureSet.substVar, CaptureSet.weaken, CaptureSet.rename_comp,
            Rename.succ_lift_comp_subst_there]
  | write _ _ _ ih => exact ih

/-- The closure stored at a variable is typed at the variable's type. -/
theorem Store.Typed.lam_of_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    (h : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) :
    Γ ⊢ᵥ .lam A S₀ t₀ g : Γ.lookupTy x :=
  hx ▸ h.lookup x

/-- The box stored at a variable is typed at the variable's type. -/
theorem Store.Typed.box_of_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {b : Atom s} (h : ⊢ σ : Γ) (hx : σ.lookup x = .box b) :
    Γ ⊢ᵥ .box b : Γ.lookupTy x :=
  hx ▸ h.lookup x

/-! ## The frame clause under weakening

A frame reads the consumed leaves of its declared set, which do not grow when
a binder is appended (`Ctx.consumedLeaves_weakenC`), and the masks, which an
appended heir extends by names consumed above the frame (plan-5h S0.5,
decision 38). -/

/-- Leaves read no bit. -/
theorem Ctx.consumedLeaves_killNames (Γ : Ctx s) (D : List (BVar s .cap)) (C : CaptureSet s) :
    (Γ.killNames D).consumedLeaves C = Γ.consumedLeaves C := by
  unfold Ctx.consumedLeaves
  rw [Ctx.namesCaps_killNames]

/-- A frame keeps its clause at a smaller index. -/
theorem Ctx.FrameKilled.mono {Γ : Ctx s} {A A' D : List (BVar s .cap)} {V : CaptureSet s}
    (h : Γ.FrameKilled A D V) (hA : ∀ κ ∈ A', κ ∈ A) : Γ.FrameKilled A' D V :=
  fun κ hκ hor => h κ hκ (hor.imp id (hA κ))

/-- A frame keeps its clause when an heir of names consumed above it is
appended: the new masks are names of `A`, and the new index adds at most the
heir. -/
theorem Ctx.FrameKilled.heir {Γ : Ctx s} {A D : List (BVar s .cap)} {V W : CaptureSet s}
    (bit : Bool) (h : Γ.FrameKilled A D V) (hW : ∀ κ, CapAtom.cvar κ ∈ W → κ ∈ A)
    {A' : List (BVar (s,c) .cap)} (hA' : ∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) :
    (Γ.consC (.own bit W)).FrameKilled A' (D.map BVar.there)
      (CaptureSet.weaken (k := .cap) V) := by
  intro κ' hκ' hor
  rw [Ctx.consumedLeaves_weakenC] at hκ'
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hκ'
  refine List.mem_map_of_mem (h κ hκ ?_)
  rcases hor with hm | hA
  · rcases (Ctx.masked_consC_own_iff Γ bit W κ).mp hm with hm | hw
    · exact Or.inl hm
    · exact Or.inr (hW κ hw)
  · rcases hA' _ hA with he | ⟨κ₀, hκ₀, he⟩
    · cases he
    · cases he; exact Or.inr hκ₀

/-- A frame keeps its clause under any capture binder that owns nothing. -/
theorem Ctx.FrameKilled.weakenC {Γ : Ctx s} {A D : List (BVar s .cap)} {V : CaptureSet s}
    (b : CapBound s) (hb : ∀ κ, b.ownsB κ = false) (h : Γ.FrameKilled A D V)
    {A' : List (BVar (s,c) .cap)} (hA' : ∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) :
    (Γ.consC b).FrameKilled A' (D.map BVar.there) (CaptureSet.weaken (k := .cap) V) := by
  intro κ' hκ' hor
  rw [Ctx.consumedLeaves_weakenC] at hκ'
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hκ'
  refine List.mem_map_of_mem (h κ hκ ?_)
  rcases hor with hm | hA
  · rcases (Ctx.masked_consC_iff Γ b κ).mp hm with hm | hw
    · exact Or.inl hm
    · rw [hb κ] at hw; cases hw
  · rcases hA' _ hA with he | ⟨κ₀, hκ₀, he⟩
    · cases he
    · cases he; exact Or.inr hκ₀

/-- A frame keeps its clause under a term binder. -/
theorem Ctx.FrameKilled.weaken {Γ : Ctx s} {A D : List (BVar s .cap)} {V : CaptureSet s}
    (b : Binding s) (h : Γ.FrameKilled A D V)
    {A' : List (BVar (s,x) .cap)} (hA' : ∀ κ' ∈ A', ∃ κ ∈ A, κ' = .there κ) :
    (Γ.cons b).FrameKilled A' (D.map BVar.there) (CaptureSet.weaken (k := .var) V) := by
  intro κ' hκ' hor
  rw [Ctx.consumedLeaves_weaken] at hκ'
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hκ'
  refine List.mem_map_of_mem (h κ hκ ?_)
  rcases hor with hm | hA
  · exact Or.inl ((Ctx.masked_cons_iff Γ b κ).mp hm)
  · obtain ⟨κ₀, hκ₀, he⟩ := hA' _ hA
    cases he; exact Or.inr hκ₀

/-- A frame keeps its clause when the bits of its context are revived, with
the ghost of the revived frame the two ghosts together. -/
theorem Ctx.FrameKilled.revive {Γ : Ctx s} {A D D' : List (BVar s .cap)} {V : CaptureSet s}
    (h : (Γ.killNames D).FrameKilled A D' V) : Γ.FrameKilled A (D ++ D') V := by
  intro κ hκ hor
  rw [← Ctx.consumedLeaves_killNames Γ D] at hκ
  have hor' : (Γ.killNames D).Masked κ ∨ κ ∈ A := by
    rcases hor with hm | hA
    · exact Or.inl ((Ctx.masked_killNames Γ D κ).mpr hm)
    · exact Or.inr hA
  exact List.mem_append_right D (h κ hκ hor')

/-- **The `hlive` of `Ctx.SepInv.heir`**: a leaf the running term consumes,
whose bit is live in the running context, is unmasked. -/
theorem Ctx.MaskKilled.unmasked {Γ : Ctx s} {D : List (BVar s .cap)} {C : CaptureSet s}
    {κ : BVar s .cap} (h : Γ.MaskKilled D C) (hκ : κ ∈ Γ.consumedLeaves C)
    (hc : (Γ.lookupCap κ).consumable = true) (hl : (Γ.killNames D).BitLive κ) :
    ¬ Γ.Masked κ := by
  intro hm
  exact ((Ctx.bitLive_killNames Γ D κ).mp hl).2 hc (h κ hκ hm)

/-! ## Continuation weakening

A frame is typed in its context with the kills of its activation, the ghost
list `D` of the frame.  Weakening moves the ghost list up by one binder:
`Ctx.killNames_cons` says that killing the moved list in the extended
context is extending the killed context.  The names of every body stay the
images of names by `Ctx.NamesMap.renameSucc`, `Ctx.NamesMap.weakenC` and
their lifts, and the index of leaves consumed above a frame moves with the
binder. -/

/-- **A continuation keeps its typing at a smaller index.** -/
theorem Cont.Typed.mono {s : Sig} {Γ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} (h : Γ ⊢ₖ[A] K : E ⇒ U) :
    ∀ {A' : List (BVar s .cap)}, (∀ κ ∈ A', κ ∈ A) → Γ ⊢ₖ[A'] K : E ⇒ U := by
  induction h with
  | nil => intro _ _; exact .nil
  | «let» hu hf hk _ ih =>
      intro A' hA
      refine Cont.Typed.let hu hf (hk.mono hA) (ih ?_)
      intro κ hκ
      rcases List.mem_append.mp hκ with h | h
      · exact List.mem_append_left _ (hA κ h)
      · exact List.mem_append_right _ h
  | cast he _ ih =>
      intro A' hA
      exact Cont.Typed.cast he (ih hA)
  | castE hg hk _ ih =>
      intro A' hA
      refine Cont.Typed.castE hg (hk.mono hA) (ih ?_)
      intro κ hκ
      rcases List.mem_append.mp hκ with h | h
      · exact List.mem_append_left _ (hA κ h)
      · exact List.mem_append_right _ h
  | letex hh hkU hsep hbA hu hf hk _ ih =>
      intro A' hA
      refine Cont.Typed.letex hh hkU hsep hbA hu hf (hk.mono hA) (ih ?_)
      intro κ hκ
      rcases List.mem_append.mp hκ with h | h
      · exact List.mem_append_left _ (hA κ h)
      · exact List.mem_append_right _ h
  | letexF hu hf hk _ ih =>
      intro A' hA
      refine Cont.Typed.letexF hu hf (hk.mono hA) (ih ?_)
      intro κ hκ
      rcases List.mem_append.mp hκ with h | h
      · exact List.mem_append_left _ (hA κ h)
      · exact List.mem_append_right _ h

/-- The index relation across a capture binder, extended by a set of leaves. -/
theorem Cont.index_appendC {A : List (BVar s .cap)} {A' : List (BVar (s,c) .cap)}
    (hA' : ∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) (L : List (BVar s .cap)) :
    ∀ κ' ∈ A' ++ L.map BVar.there, κ' = .here ∨ ∃ κ ∈ A ++ L, κ' = .there κ := by
  intro κ' hκ'
  rcases List.mem_append.mp hκ' with h | h
  · rcases hA' κ' h with he | ⟨κ, hκ, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨κ, List.mem_append_left _ hκ, he⟩
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨κ, List.mem_append_right _ hκ, rfl⟩

/-- The index relation across a term binder, extended by a set of leaves. -/
theorem Cont.index_append {A : List (BVar s .cap)} {A' : List (BVar (s,x) .cap)}
    (hA' : ∀ κ' ∈ A', ∃ κ ∈ A, κ' = .there κ) (L : List (BVar s .cap)) :
    ∀ κ' ∈ A' ++ L.map BVar.there, ∃ κ ∈ A ++ L, κ' = .there κ := by
  intro κ' hκ'
  rcases List.mem_append.mp hκ' with h | h
  · obtain ⟨κ, hκ, he⟩ := hA' κ' h
    exact ⟨κ, List.mem_append_left _ hκ, he⟩
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
    exact ⟨κ, List.mem_append_right _ hκ, rfl⟩

theorem Cont.Typed.weaken {s : Sig} {Γ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} (h : Γ ⊢ₖ[A] K : E ⇒ U) (b : Binding s) :
    ∀ {A' : List (BVar (s,x) .cap)}, (∀ κ' ∈ A', ∃ κ ∈ A, κ' = .there κ) →
      (Γ.cons b) ⊢ₖ[A'] K↑ : E↑ ⇒ U↑ := by
  induction h with
  | nil => intro _ _; exact .nil
  | @«let» u E f U' Γ A T K V D hu hf hk _ ih =>
      intro A' hA'
      have hρ := (Ctx.Ren.succ (Γ := Γ.killNames D) b).lift (.opaque T)
      have hN := (Ctx.NamesMap.renameSucc (Γ.killNames D) b).renameLift (.opaque T)
      refine Cont.Typed.let (D := D.map .there) (E := ETy.weaken E) ?_ ?_ (hk.weaken b hA') ?_
      · rw [Ctx.killNames_cons]
        have := hu.rename hρ hN
        simpa [ETy.weaken_rename] using this
      · rw [Ctx.killNames_cons]
        have := hf.rename hρ
        rwa [CaptureSet.weaken_rename, ← Tm.uses_rename] at this
      · refine ih ?_
        have := Cont.index_append hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weaken Γ b U'] at this
  | cast he _ ih =>
      intro A' hA'
      exact Cont.Typed.cast (LeCo.HasType.weaken he b) (ih hA')
  | @castE g E E' Γ A K V D hg hk _ ih =>
      intro A' hA'
      refine Cont.Typed.castE (D := D.map .there) (E' := E'.rename Rename.succ) ?_ ?_ ?_
      · rw [Ctx.killNames_cons]
        exact ELeCo.HasType.rename (Ctx.Ren.succ b) hg
      · rw [ELeCo.charge_rename]; exact hk.weaken b hA'
      · rw [ELeCo.charge_rename]
        refine ih ?_
        have := Cont.index_append hA' (Γ.consumedLeaves g.charge)
        rwa [← Ctx.consumedLeaves_weaken Γ b g.charge] at this
  | @letex h u f Γ A K V D T C₀ U' E hh hkU hsep hbA hu hf hk _ ih =>
      intro A' hA'
      have hρ := ((Ctx.Ren.succ (Γ := Γ.killNames D) b).liftC CapBound.star).lift (.opaque T)
      have hN0 := Ctx.NamesMap.renameSucc (Γ.killNames D) b
      have hN := (hN0.renameLiftC CapBound.star
        (Or.inl (fun _ he => by cases he))).renameLift (.opaque T)
      refine Cont.Typed.letex (D := D.map .there) (E := ETy.weaken E) ?_ ?_ ?_ ?_ ?_ ?_
        (hk.weaken b hA') ?_
      · rw [Ctx.killNames_cons]; exact CapCo.HasType.weaken hh b
      · rw [Ctx.killNames_cons]
        exact hN0.killOk_rename (Ctx.Ren.succ b).kill hkU
      · rw [Ctx.killNames_cons]
        exact hN0.argSep (CapAtom.nameMapFn_rename Rename.succ) hsep hkU
      · rw [Ctx.killNames_cons]
        exact hN0.accessible (Ctx.Ren.succ b).kill (CapAtom.nameMapFn_rename Rename.succ) hbA
      · rw [Ctx.killNames_cons]
        have hu' := hu.rename hρ hN
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · rw [Ctx.killNames_cons]
        have hf' := CapCo.HasType.rename hρ hf
        rw [CaptureSet.letexCharge_rename] at hf'
        simpa only [Tm.uses_rename] using hf'
      · refine ih ?_
        have := Cont.index_append hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weaken Γ b U'] at this
  | @letexF u f Γ A K V D Cl T E U' hu hf hk _ ih =>
      intro A' hA'
      have hρ := ((Ctx.Ren.succ (Γ := Γ.killNames D) b).liftC (.loc true Cl)).lift (.opaque T)
      have hN := ((Ctx.NamesMap.renameSucc (Γ.killNames D) b).renameLiftC
        (.loc true Cl) (Or.inl (fun _ he => by cases he))).renameLift (.opaque T)
      refine Cont.Typed.letexF (D := D.map .there) (Cl := Cl.rename Rename.succ)
        (E := ETy.weaken E) ?_ ?_ (hk.weaken b hA') ?_
      · rw [Ctx.killNames_cons]
        have hu' := hu.rename hρ hN
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · rw [Ctx.killNames_cons]
        have hf' := CapCo.HasType.rename hρ hf
        rw [CaptureSet.freshCharge_rename] at hf'
        rw [Tm.uses_rename]; exact hf'
      · refine ih ?_
        have := Cont.index_append hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weaken Γ b U'] at this

/-- The capture-kind twin of `Cont.Typed.weaken`, for a live bound that is no
root, with the frame clause carried by a transport `hfk` that holds of every
index `P` admits.  `Cont.Typed.weakenC` and `Cont.Typed.heir` are its two
instances. -/
theorem Cont.Typed.weakenCGen {s : Sig} {Γ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} (h : Γ ⊢ₖ[A] K : E ⇒ U) (b : CapBound s) (hb : b.isRoot = false)
    (hl : b.live = true) (P : List (BVar s .cap) → Prop)
    (hPmono : ∀ A L, P A → P (A ++ L))
    (hfk : ∀ {A D : List (BVar s .cap)} {V : CaptureSet s}, P A → Γ.FrameKilled A D V →
      ∀ {A' : List (BVar (s,c) .cap)}, (∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) →
        (Γ.consC b).FrameKilled A' (D.map BVar.there) (CaptureSet.weaken (k := .cap) V)) :
    P A → ∀ {A' : List (BVar (s,c) .cap)},
      (∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) →
      (Γ.consC b) ⊢ₖ[A'] K.weakenC : ETy.weaken (k := .cap) E ⇒ Ty.weaken (k := .cap) U := by
  revert hfk
  induction h with
  | nil => intro _ _ _ _; exact .nil
  | @«let» u E f U' Γ A T K V D hu hf hk _ ih =>
      intro hfk hP A' hA'
      have hρ := (Ctx.Ren.succC (Γ := Γ.killNames D) b hb).lift (.opaque T)
      have hN := ((Ctx.NamesMap.weakenC (Γ.killNames D) b hb hl).congr
        (fun _ => rfl)).renameLift (.opaque T)
      refine Cont.Typed.let (D := D.map .there) (E := ETy.weaken (k := .cap) E) ?_ ?_
        (hfk hP hk hA') ?_
      · rw [Ctx.killNames_consC]
        have := hu.rename hρ hN
        simpa [ETy.weaken_rename] using this
      · rw [Ctx.killNames_consC]
        have := hf.rename hρ
        rwa [CaptureSet.weaken_rename, ← Tm.uses_rename] at this
      · refine ih hfk (hPmono _ _ hP) ?_
        have := Cont.index_appendC hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weakenC Γ b U'] at this
  | cast he _ ih =>
      intro hfk hP A' hA'
      exact Cont.Typed.cast (LeCo.HasType.weakenC he b hb) (ih hfk hP hA')
  | @castE g E E' Γ A K V D hg hk _ ih =>
      intro hfk hP A' hA'
      refine Cont.Typed.castE (D := D.map .there) (E' := E'.rename Rename.succ) ?_ ?_ ?_
      · rw [Ctx.killNames_consC]
        exact ELeCo.HasType.rename (Ctx.Ren.succC b hb) hg
      · rw [ELeCo.charge_rename]; exact hfk hP hk hA'
      · rw [ELeCo.charge_rename]
        refine ih hfk (hPmono _ _ hP) ?_
        have := Cont.index_appendC hA' (Γ.consumedLeaves g.charge)
        rwa [← Ctx.consumedLeaves_weakenC Γ b g.charge] at this
  | @letex h u f Γ A K V D T C₀ U' E hh hkU hsep hbA hu hf hk _ ih =>
      intro hfk hP A' hA'
      have hρ := ((Ctx.Ren.succC (Γ := Γ.killNames D) b hb).liftC CapBound.star).lift
        (.opaque T)
      have hN0 : (Γ.killNames D).NamesMap (·.rename Rename.succ) ((Γ.killNames D).consC b) :=
        (Ctx.NamesMap.weakenC (Γ.killNames D) b hb hl).congr (fun _ => rfl)
      have hN := (hN0.renameLiftC CapBound.star
        (Or.inl (fun _ he => by cases he))).renameLift (.opaque T)
      refine Cont.Typed.letex (D := D.map .there) (E := ETy.weaken (k := .cap) E) ?_ ?_ ?_
        ?_ ?_ ?_ (hfk hP hk hA') ?_
      · rw [Ctx.killNames_consC]; exact CapCo.HasType.weakenC hh b hb
      · rw [Ctx.killNames_consC]
        exact hN0.killOk_rename (Ctx.Ren.succC b hb).kill hkU
      · rw [Ctx.killNames_consC]
        exact hN0.argSep (CapAtom.nameMapFn_rename Rename.succ) hsep hkU
      · rw [Ctx.killNames_consC]
        exact hN0.accessible (Ctx.Ren.succC b hb).kill (CapAtom.nameMapFn_rename Rename.succ) hbA
      · rw [Ctx.killNames_consC]
        have hu' := hu.rename hρ hN
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · rw [Ctx.killNames_consC]
        have hf' := CapCo.HasType.rename hρ hf
        rw [CaptureSet.letexCharge_rename] at hf'
        simpa only [Tm.uses_rename] using hf'
      · refine ih hfk (hPmono _ _ hP) ?_
        have := Cont.index_appendC hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weakenC Γ b U'] at this
  | @letexF u f Γ A K V D Cl T E U' hu hf hk _ ih =>
      intro hfk hP A' hA'
      have hρ := ((Ctx.Ren.succC (Γ := Γ.killNames D) b hb).liftC (.loc true Cl)).lift
        (.opaque T)
      have hN0 : (Γ.killNames D).NamesMap (·.rename Rename.succ) ((Γ.killNames D).consC b) :=
        (Ctx.NamesMap.weakenC (Γ.killNames D) b hb hl).congr (fun _ => rfl)
      have hN := (hN0.renameLiftC (.loc true Cl)
        (Or.inl (fun _ he => by cases he))).renameLift (.opaque T)
      refine Cont.Typed.letexF (D := D.map .there) (Cl := Cl.rename Rename.succ)
        (E := ETy.weaken (k := .cap) E) ?_ ?_ (hfk hP hk hA') ?_
      · rw [Ctx.killNames_consC]
        have hu' := hu.rename hρ hN
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · rw [Ctx.killNames_consC]
        have hf' := CapCo.HasType.rename hρ hf
        rw [CaptureSet.freshCharge_rename] at hf'
        rw [Tm.uses_rename]; exact hf'
      · refine ih hfk (hPmono _ _ hP) ?_
        have := Cont.index_appendC hA' (Γ.consumedLeaves U')
        rwa [← Ctx.consumedLeaves_weakenC Γ b U'] at this

/-- **Capture weakening of a continuation**, under a live binder that is no
root and owns nothing (plan-5h S0.8, decision 38). -/
theorem Cont.Typed.weakenC {s : Sig} {Γ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} (h : Γ ⊢ₖ[A] K : E ⇒ U) (b : CapBound s) (hb : b.isRoot = false)
    (hl : b.live = true) (ho : ∀ κ, b.ownsB κ = false) {A' : List (BVar (s,c) .cap)}
    (hA' : ∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) :
    (Γ.consC b) ⊢ₖ[A'] K.weakenC : ETy.weaken (k := .cap) E ⇒ Ty.weaken (k := .cap) U :=
  h.weakenCGen b hb hl (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hk _ hA'' => hk.weakenC b ho hA'') trivial hA'

/-- **A continuation under an heir of names consumed above it** (plan-5h
S0.8, decision 38): the frame clause survives by `Ctx.FrameKilled.heir`. -/
theorem Cont.Typed.heir {s : Sig} {Γ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} {W : CaptureSet s} (h : Γ ⊢ₖ[A] K : E ⇒ U)
    (hW : ∀ κ, CapAtom.cvar κ ∈ W → κ ∈ A) {A' : List (BVar (s,c) .cap)}
    (hA' : ∀ κ' ∈ A', κ' = .here ∨ ∃ κ ∈ A, κ' = .there κ) :
    (Γ.consC (.own true W)) ⊢ₖ[A'] K.weakenC :
      ETy.weaken (k := .cap) E ⇒ Ty.weaken (k := .cap) U :=
  h.weakenCGen (.own true W) rfl rfl (fun A => ∀ κ, CapAtom.cvar κ ∈ W → κ ∈ A)
    (fun _ _ hP κ hκ => List.mem_append_left _ (hP κ hκ))
    (fun hP hk _ hA'' => hk.heir true hP hA'') hW hA'

/-- Reviving the bits of the context a continuation is typed in.  A frame
typed under the ghost `D'` of the killed context is typed under the ghost
`D ++ D'` of the revived one (`Ctx.killNames_append`). -/
theorem Cont.Typed.reviveAux {s : Sig} {Δ : Ctx s} {A : List (BVar s .cap)} {K : Cont s}
    {E : ETy s} {U : Ty s} (h : Δ ⊢ₖ[A] K : E ⇒ U) :
    ∀ (Γ : Ctx s) (D : List (BVar s .cap)), Δ = Γ.killNames D → Γ ⊢ₖ[A] K : E ⇒ U := by
  induction h with
  | nil => intro _ _ _; exact .nil
  | «let» hu hf hk _ ih =>
      intro Γ D hΔ
      subst hΔ
      rw [← Ctx.killNames_append] at hu hf
      refine Cont.Typed.let hu hf hk.revive ?_
      have := ih Γ D rfl
      rwa [Ctx.consumedLeaves_killNames] at this
  | cast he _ ih =>
      intro Γ D hΔ
      subst hΔ
      exact Cont.Typed.cast he.revive (ih Γ D rfl)
  | castE hg hk _ ih =>
      intro Γ D hΔ
      subst hΔ
      rw [← Ctx.killNames_append] at hg
      refine Cont.Typed.castE hg hk.revive ?_
      have := ih Γ D rfl
      rwa [Ctx.consumedLeaves_killNames] at this
  | letex hh hkU hsep hbA hu hf hk _ ih =>
      intro Γ D hΔ
      subst hΔ
      rw [← Ctx.killNames_append] at hh hkU hsep hbA hu hf
      refine Cont.Typed.letex hh hkU hsep hbA hu hf hk.revive ?_
      have := ih Γ D rfl
      rwa [Ctx.consumedLeaves_killNames] at this
  | letexF hu hf hk _ ih =>
      intro Γ D hΔ
      subst hΔ
      rw [← Ctx.killNames_append] at hu hf
      refine Cont.Typed.letexF hu hf hk.revive ?_
      have := ih Γ D rfl
      rwa [Ctx.consumedLeaves_killNames] at this

/-- **Continuation typing is monotone in bits.** -/
theorem Cont.Typed.revive {s : Sig} {Γ : Ctx s} {D : List (BVar s .cap)}
    {A : List (BVar s .cap)} {K : Cont s} {E : ETy s} {U : Ty s}
    (h : Γ.killNames D ⊢ₖ[A] K : E ⇒ U) : Γ ⊢ₖ[A] K : E ⇒ U :=
  h.reviveAux Γ D rfl

/-! ## Inversions -/

theorem Atom.HasType.var_inv {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Γ ⊢ₐ .var x : T) : T = Γ.lookupTy x := by
  cases h with
  | var => rfl

/-- Inversion of a closure.  The type is the arrow at the closure's own
annotation `A`, the body is typed under the parameter, and the closing
evidence puts the body's use set below `A` weakened united with the
parameter.  The last conjunct is the premise the `lam` rule of A2.2 carries;
`step_uses` reads it at the application steps. -/
theorem Value.HasType.lam_inv {s : Sig} {Γ : Ctx s} {A : CaptureSet s} {S₀ : Dom s}
    {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)} {T : Ty s} (h : Γ ⊢ᵥ .lam A S₀ t₀ g : T) :
    ∃ T₀ : Cod s, T = (Π(S₀) T₀) ^ A ∧ (Γ.body S₀) ⊢ t₀ :ᵉ T₀.underRoot ∧
      (Γ.body S₀) ⊢ᶜ g : t₀.uses ⊑ (A↑↑↑ ∪ [CapAtom.var .here]) := by
  cases h with
  | lam ht hg => exact ⟨_, rfl, ht, hg⟩

/-- Inversion of a boxed value: a box has the box shape of the boxed atom's
type, with the empty capture set. -/
theorem Value.HasType.box_inv {s : Sig} {Γ : Ctx s} {b : Atom s} {T : Ty s}
    (h : Γ ⊢ᵥ .box b : T) : ∃ X, T = (□ X) ^ [] ∧ Γ ⊢ₐ b : X := by
  cases h with
  | box hb => exact ⟨_, rfl, hb⟩

/-- Inversion of a cell: the cell shape of its content type, at its location,
which claims nothing. -/
theorem Value.HasType.cell_inv {s : Sig} {Γ : Ctx s} {c : CapAtom s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ᵥ .cell c a : T) :
    ∃ X, T = (Shape.cell X) ^ [c] ∧ (∃ b, Γ.LocOf c b) ∧
      Γ ⊢ₐ a : X ∧ X.captureSet = [] := by
  cases h with
  | cell hℓ ha hT => exact ⟨_, rfl, ⟨_, hℓ⟩, ha, hT⟩

/-- A stored literal declares a cell only at a location: the premise
`Binding.CellAtLoc` that `Ctx.SepInv.cons` reads when a literal is stored
(plan-5h T0.2).  Only the cell rule gives a literal the cell shape. -/
theorem Value.HasType.cellAtLoc {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (hv : Γ ⊢ᵥ v : T) (hlit : v.IsLiteral) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
    (Fs : List Label) : (Binding.transparent T W Wc Fs).CellAtLoc Γ := by
  intro X C hT
  simp only [Binding.ty] at hT
  cases hv with
  | cell hL _ _ =>
      obtain ⟨κ, rfl, hk⟩ := hL.cvar
      simp only [Ty.capt.injEq] at hT
      exact ⟨κ, hT.1.symm, _, hk⟩
  | lam _ _ => simp at hT
  | obj _ _ => simp at hT
  | box _ => simp at hT
  | reader _ _ => simp at hT
  | cast _ _ => exact absurd hlit (by simp [Value.IsLiteral])

/-- **A cell at a fresh location is no old cell** (plan-5h S0.6 and S0.7).
Along a growth an old cell keeps its value (`Store.Grow.lookup`), so it sits at
the image of its old location, and a cell whose location is no image is one the
run appended.  The design's claim that distinct cells have distinct locations
is false for an initial store (plan-5h, Refutations), and this is the form the
theorems use: a write at a fresh location leaves every old cell alone. -/
theorem Store.Grow.cell_fresh {s s' : Sig} {σ : Store s} {σ' : Store s'} {ρ : Rename s s'}
    {Γ : Ctx s} (h : Store.Grow σ σ' ρ) (hσ : ⊢ σ : Γ) {r : BVar s .var} {c : CapAtom s}
    {a₀ : Atom s} (hr : σ.lookup r = .cell c a₀) {x : BVar s' .var} {c' : CapAtom s'}
    {a' : Atom s'} (hx : σ'.lookup x = .cell c' a') (hfresh : ∀ κ, c'.base ≠ .cvar (ρ.var κ)) :
    x ≠ ρ.var r := by
  rintro rfl
  have hv := hσ.lookup r
  rw [hr] at hv
  obtain ⟨_, _, ⟨_, hL⟩, _⟩ := hv.cell_inv
  obtain ⟨ℓ, rfl, _⟩ := hL.cvar
  rw [h.lookup, hr] at hx
  simp only [Value.rename, Value.cell.injEq] at hx
  exact hfresh ℓ (by rw [← hx.1]; rfl)

/-- Inversion of a reader: the reader shape of the content type of the cell
at its transparent binder. -/
theorem Value.HasType.reader_inv {s : Sig} {Γ : Ctx s} {r : BVar s .var} {T : Ty s}
    (h : Γ ⊢ᵥ .reader r : T) :
    ∃ X, T = (Shape.reader X) ^ [CapAtom.mode .ro (CapAtom.var r)] ∧ Γ.IsTransparent r ∧
      ∃ C, Γ.lookupTy r = (Shape.cell X) ^ C := by
  cases h with
  | reader htr hty => exact ⟨_, rfl, htr, _, hty⟩

/-- Inversion of an object literal.  The type is the precise object type at
the literal's own annotation `A`, and the fields are typed against that same
`A`, which is the index of the fields judgement of A2.2. -/
theorem Value.HasType.obj_inv {s : Sig} {Γ : Ctx s} {A : CaptureSet s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields ((s,c),x)} {T : Ty s}
    (h : Γ ⊢ᵥ .obj A W Wc F : T) :
    T = (μ (Telescope.ofLiteral W Wc F.labels)) ^ A ∧
      Fields.HasType
        (Γ.objBody ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc F.labels)
        A↑ F := by
  cases h with
  | obj hF _ => exact ⟨rfl, hF⟩

/-- Inversion of a field list at a label: the field's body has the field's
result type, the capture name of its own label at the self, and its closing
evidence puts its use set below the literal's assigned set weakened united
with the self.  The second conjunct is the premise the `fields` rule of A2.2
carries; `step_uses` reads it at the projection step. -/
theorem Fields.HasType.getFull {s : Sig} {Γ : Ctx (s,x)} {A : CaptureSet s} :
    ∀ (F : Fields (s,x)), Γ ⊢ᶠ[A] F → ∀ (l : Label) (t : Tm (s,x)),
      F.get? l = some t →
      (Γ ⊢ t : (.here ∙ l) ^ [CapAtom.name .here l]) ∧
        ∃ g, Γ ⊢ᶜ g : t.uses ⊑ (A↑ ∪ [CapAtom.var .here])
  | .nil, _, l, t, hg => by simp [Fields.get?] at hg
  | .cons F l' t' g', h, l, t, hg => by
      cases h with
      | cons hF ht hg' =>
          by_cases hl : l = l'
          · subst hl
            obtain rfl : t' = t := by simpa [Fields.get?] using hg
            exact ⟨ht, ⟨_, hg'⟩⟩
          · rw [show Fields.get? (.cons F l' t' g') l = F.get? l by
                simp [Fields.get?, hl]] at hg
            exact Fields.HasType.getFull F hF l t hg

theorem Fields.HasType.get {s : Sig} {Γ : Ctx (s,x)} {A : CaptureSet s}
    (F : Fields (s,x)) (h : Γ ⊢ᶠ[A] F) (l : Label) (t : Tm (s,x))
    (hg : F.get? l = some t) : Γ ⊢ t : (.here ∙ l) ^ [CapAtom.name .here l] :=
  (Fields.HasType.getFull F h l t hg).1

/-! ## Mode bounds in a store and across the let-like steps (plan-5h S0.8)

A let binder, an unpack payload and a store binder keep their declared sets,
and each is instantiated by a closed atom of a store.  Their mode maps read
`Ctx.ModeSound`, which closed evidence has in a store (`Ctx.modeSound_store`,
`CanonicalForms.lean`), and the access-only capture names of the atom's root,
which the literal premise gives (`Store.Typed.names_accessOnly`). -/

/-- **A let binder.**  `Subst.single a` keeps every mode bound when the
context is sound and the capture names of the root are access-only. -/
theorem Ctx.modeMap_single {s : Sig} {Γ : Ctx s} (hms : Γ.ModeSound) {a : Atom s} {T : Ty s}
    (ha : Γ ⊢ₐ a : T) (hn : ∀ ℓ, Γ.AccessOnly [CapAtom.name a.root ℓ]) :
    (Γ.cons (.opaque T)).ModeMap (·.subst (Subst.single a)) Γ := by
  intro c m h
  match c with
  | .var .here =>
      show Γ.ModeBound (.var a.root) m
      rw [Ctx.modeBound_cons_here Γ (b := .opaque T) rfl] at h
      exact hms.atom ha m h
  | .var (.there y) =>
      show Γ.ModeBound (.var y) m
      exact (Γ.modeBound_weaken_iff _ (.var y) m).mp h
  | .cvar (.there κ) =>
      show Γ.ModeBound (.cvar κ) m
      exact (Γ.modeBound_weaken_iff _ (.cvar κ) m).mp h
  | .name .here ℓ =>
      show Γ.ModeBound (.name a.root ℓ) m
      have hm := (Γ.modeBound_cons_name_opaque T ℓ m).mp h
      exact (Ctx.accessOnly_singleton.mp (hn ℓ)).mono hm
  | .name (.there y) ℓ =>
      show Γ.ModeBound (.name y ℓ) m
      exact (Γ.modeBound_weaken_iff _ (.name y ℓ) m).mp h
  | .top =>
      show Γ.ModeBound .top m
      exact (Γ.modeBound_top m).mpr (((Γ.cons (.opaque T)).modeBound_top m).mp h)
  | .mode md c => exact Γ.modeBound_mode md _ m

/-- **Storing a value at a let binder** (`Tm.adjust`, `Subst.Typed.selfCast`).
The binder is retyped along closed evidence and gains its literal's capture
witnesses, whose names are access-only by the literal premise. -/
theorem Ctx.modeMap_adjust {s : Sig} {Γ : Ctx s} (hms : Γ.ModeSound) {S₀ T : Ty s} {E : LeCo s}
    (hE : Γ ⊢ E : S₀ ≤ T) {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label}
    (hWc : ∀ ℓ, (Γ.cons (.transparent S₀ W Wc Fs)).AccessOnly [CapAtom.name .here ℓ]) :
    (Γ.cons (.opaque T)).ModeMap (·.subst (Subst.selfCast (LeCo.weaken (k := .var) E)))
      (Γ.cons (.transparent S₀ W Wc Fs)) := by
  intro c m h
  simp only [CapAtom.subst_selfCast]
  match c with
  | .var .here =>
      rw [Ctx.modeBound_cons_here Γ (b := .opaque T) rfl] at h
      rw [Ctx.modeBound_cons_here Γ (b := .transparent S₀ W Wc Fs) rfl]
      cases hE with
      | capt _ hf => exact hms _ _ _ hf m h
  | .var (.there y) =>
      exact (Γ.modeBound_weaken_iff _ (.var y) m).mpr ((Γ.modeBound_weaken_iff _ (.var y) m).mp h)
  | .cvar (.there κ) =>
      exact (Γ.modeBound_weaken_iff _ (.cvar κ) m).mpr
        ((Γ.modeBound_weaken_iff _ (.cvar κ) m).mp h)
  | .name .here ℓ =>
      have hm := (Γ.modeBound_cons_name_opaque T ℓ m).mp h
      exact (Ctx.accessOnly_singleton.mp (hWc ℓ)).mono hm
  | .name (.there y) ℓ =>
      exact (Γ.modeBound_weaken_iff _ (.name y ℓ) m).mpr
        ((Γ.modeBound_weaken_iff _ (.name y ℓ) m).mp h)
  | .top =>
      exact ((Γ.cons _).modeBound_top m).mpr (((Γ.cons (.opaque T)).modeBound_top m).mp h)
  | .mode md c => exact (Γ.cons _).modeBound_mode md _ m

/-- A label with no witness of its own reaches no atom. -/
theorem CapWitnesses.not_mem_reach_of_get {s : Sig} {Wc : CapWitnesses (s,x)} {ℓ : Label}
    (h : Wc.get ℓ = []) (r : CapAtom (s,x)) (hr : r ∈ Wc.reach ℓ) : False := by
  unfold CapWitnesses.reach at hr
  obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨c, hc, -⟩ := List.mem_map.mp hr
  obtain ⟨hc, -⟩ := List.mem_filter.mp hc
  rcases CapWitnesses.reachPairs_decomp hp with rfl | ⟨c', hc', -⟩
  · rw [h] at hc; cases hc
  · rw [h] at hc'; cases hc'

/-- So its capture name has every mode bound. -/
theorem Ctx.modeBound_name_here_of_get {s : Sig} (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (Fs : List Label) {ℓ : Label} (h : Wc.get ℓ = []) (m : EMode) :
    (Γ.cons (.transparent T W Wc Fs)).ModeBound (.name .here ℓ) m :=
  (Γ.modeBound_cons_name_transparent T W Wc Fs ℓ m).mpr
    (fun r hr => (CapWitnesses.not_mem_reach_of_get h r hr).elim)

/-- **A literal's capture names are access-only** in the context
`Store.Typed.cons` builds: an object by its literal premise (plan-5h S0.5),
a closure and a box by their empty witnesses. -/
theorem Value.HasType.obj_names_accessOnly {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (hv : Γ ⊢ᵥ v : T) (hlit : v.IsLiteral) (ℓ : Label) :
    (Γ.cons (.transparent T v.witnesses v.capWitnesses v.fieldLabels)).AccessOnly
      [CapAtom.name .here ℓ] := by
  match hv, hlit with
  | .lam _ _, _ =>
      rw [Ctx.accessOnly_singleton]
      exact Ctx.modeBound_name_here_of_get _ _ _ _ _ rfl _
  | @Value.HasType.obj _ _ _ _ _ Wc _ hW, _ =>
      cases hℓ : decide (ℓ ∈ Wc.labels) with
      | true => exact hW ℓ (of_decide_eq_true hℓ)
      | false =>
          rw [Ctx.accessOnly_singleton]
          exact Ctx.modeBound_name_here_of_get _ _ _ _ _
            (CapWitnesses.get_of_not_mem_labels Wc (of_decide_eq_false hℓ)) _
  | .box _, _ =>
      rw [Ctx.accessOnly_singleton]
      exact Ctx.modeBound_name_here_of_get _ _ _ _ _ rfl _
  | .cell _ _ _, _ =>
      rw [Ctx.accessOnly_singleton]
      exact Ctx.modeBound_name_here_of_get _ _ _ _ _ rfl _
  | .reader _ _, _ =>
      rw [Ctx.accessOnly_singleton]
      exact Ctx.modeBound_name_here_of_get _ _ _ _ _ rfl _
  | .cast _ _, h => exact absurd h (by simp [Value.IsLiteral])

/-- A store context binds no parameter. -/
theorem Store.Typed.formalFree {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    Γ.formalFree = true := by
  induction hσ with
  | nil => rfl
  | cons _ _ _ ih => simp [Ctx.formalFree, Binding.isFormal, ih]
  | consC _ _ _ ih => exact ih
  | write _ _ _ ih => exact ih

/-- **In a store every capture name is access-only**: the literal premise
(plan-5h S0.5), carried by store typing. -/
theorem Store.Typed.names_accessOnly {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    ∀ (x : BVar s .var) (ℓ : Label), Γ.AccessOnly [CapAtom.name x ℓ] := by
  induction hσ with
  | nil => intro x; cases x
  | cons _ hlit hv ih =>
      intro x ℓ
      cases x with
      | here => exact hv.obj_names_accessOnly hlit ℓ
      | there y =>
          have h := Ctx.accessOnly_singleton.mp (ih y ℓ)
          exact Ctx.accessOnly_singleton.mpr ((Ctx.modeBound_weaken_iff _ _ (.name y ℓ) _).mpr h)
  | consC _ _ _ ih =>
      intro x ℓ
      cases x with
      | there y =>
          have h := Ctx.accessOnly_singleton.mp (ih y ℓ)
          exact Ctx.accessOnly_singleton.mpr ((Ctx.modeBound_weakenC_iff _ _ (.name y ℓ) _).mpr h)
  | write _ _ _ ih => exact ih

/-! ### The capture names of a store binder

The capture names of `y` in a store context are the capture names of a copy
of `y`'s binder pushed on top of the context: weakening past a binder keeps
the names a witness atom stands for, one binder at a time. -/

theorem Ctx.selfInner_weaken_iff {s : Sig} (Γ : Ctx s) (b : Binding s) (T : Ty s) (m : EMode) :
    ∀ r : CapAtom (s,x),
      (∀ z ∈ Ctx.selfInner (fun a => (Γ.cons b).modeCaps a) (T.rename Rename.succ)
          (r.rename Rename.succ.lift), z.effMode ≤ m) ↔
        (∀ z ∈ Ctx.selfInner (fun a => Γ.modeCaps a) T r, z.effMode ≤ m)
  | .var .here => by
      have h1 := Ctx.setBound_iff (Γ := Γ.cons b) (C := (T.rename Rename.succ).captureSet) (m := m)
      have h2 := Ctx.setBound_iff (Γ := Γ) (C := T.captureSet) (m := m)
      have h3 : (Γ.cons b).SetBound (T.rename Rename.succ).captureSet m ↔
          Γ.SetBound T.captureSet m := by
        rw [Ty.captureSet_renameSucc]; exact Γ.setBound_weaken_iff b _ m
      exact h1.symm.trans (h3.trans h2)
  | .var (.there y) => CaptureSet.forall_weaken_effMode
  | .cvar (.there κ) => CaptureSet.forall_weaken_effMode
  | .name (.there y) ℓ => CaptureSet.forall_weaken_effMode
  | .name .here ℓ => ⟨fun _ z hz => (by cases hz), fun _ z hz => (by cases hz)⟩
  | .top => by
      constructor
      · intro h z hz
        have hz' : z = CapAtom.top := List.mem_singleton.mp hz
        subst hz'
        exact h CapAtom.top (List.mem_singleton_self _)
      · intro h z hz
        have hz' : z = CapAtom.top := List.mem_singleton.mp hz
        subst hz'
        exact h CapAtom.top (List.mem_singleton_self _)
  | .mode _ _ => ⟨fun _ z hz => (by cases hz), fun _ z hz => (by cases hz)⟩

theorem Ctx.selfInner_weakenC_iff {s : Sig} (Γ : Ctx s) (b : CapBound s) (T : Ty s) (m : EMode) :
    ∀ r : CapAtom (s,x),
      (∀ z ∈ Ctx.selfInner (fun a => (Γ.consC b).modeCaps a) (T.rename Rename.succ)
          (r.rename Rename.succ.lift), z.effMode ≤ m) ↔
        (∀ z ∈ Ctx.selfInner (fun a => Γ.modeCaps a) T r, z.effMode ≤ m)
  | .var .here => by
      have h1 := Ctx.setBound_iff (Γ := Γ.consC b) (C := (T.rename Rename.succ).captureSet)
        (m := m)
      have h2 := Ctx.setBound_iff (Γ := Γ) (C := T.captureSet) (m := m)
      have h3 : (Γ.consC b).SetBound (T.rename Rename.succ).captureSet m ↔
          Γ.SetBound T.captureSet m := by
        rw [Ty.captureSet_renameSucc]; exact Γ.setBound_weakenC_iff b _ m
      exact h1.symm.trans (h3.trans h2)
  | .var (.there y) => CaptureSet.forall_weaken_effMode
  | .cvar (.there κ) => CaptureSet.forall_weaken_effMode
  | .name (.there y) ℓ => CaptureSet.forall_weaken_effMode
  | .name .here ℓ => ⟨fun _ z hz => (by cases hz), fun _ z hz => (by cases hz)⟩
  | .top => by
      constructor
      · intro h z hz
        have hz' : z = CapAtom.top := List.mem_singleton.mp hz
        subst hz'
        exact h CapAtom.top (List.mem_singleton_self _)
      · intro h z hz
        have hz' : z = CapAtom.top := List.mem_singleton.mp hz
        subst hz'
        exact h CapAtom.top (List.mem_singleton_self _)
  | .mode _ _ => ⟨fun _ z hz => (by cases hz), fun _ z hz => (by cases hz)⟩

/-- The capture names of a transparent binder pushed on top keep their bounds
when a binder is added below it. -/
theorem Ctx.modeBound_name_weaken_iff {s : Sig} (Γ : Ctx s) (b : Binding s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (ℓ : Label) (m : EMode) :
    ((Γ.cons b).cons (.transparent (T.rename Rename.succ) (W.rename Rename.succ.lift)
        (Wc.rename Rename.succ.lift) Fs)).ModeBound (.name .here ℓ) m ↔
      (Γ.cons (.transparent T W Wc Fs)).ModeBound (.name .here ℓ) m := by
  rw [Ctx.modeBound_cons_name_transparent, Ctx.modeBound_cons_name_transparent,
    CapWitnesses.reach_rename_lift]
  constructor
  · intro h r hr
    have := h (r.rename Rename.succ.lift) (List.mem_map_of_mem hr)
    rw [CapAtom.base_rename, CapAtom.useMode_rename] at this
    exact (Γ.selfInner_weaken_iff b T _ r.base).mp this
  · intro h r hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    rw [CapAtom.base_rename, CapAtom.useMode_rename]
    exact (Γ.selfInner_weaken_iff b T _ r₀.base).mpr (h r₀ hr₀)

theorem Ctx.modeBound_name_weakenC_iff {s : Sig} (Γ : Ctx s) (b : CapBound s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (ℓ : Label) (m : EMode) :
    ((Γ.consC b).cons (.transparent (T.rename Rename.succ) (W.rename Rename.succ.lift)
        (Wc.rename Rename.succ.lift) Fs)).ModeBound (.name .here ℓ) m ↔
      (Γ.cons (.transparent T W Wc Fs)).ModeBound (.name .here ℓ) m := by
  rw [Ctx.modeBound_cons_name_transparent, Ctx.modeBound_cons_name_transparent,
    CapWitnesses.reach_rename_lift]
  constructor
  · intro h r hr
    have := h (r.rename Rename.succ.lift) (List.mem_map_of_mem hr)
    rw [CapAtom.base_rename, CapAtom.useMode_rename] at this
    exact (Γ.selfInner_weakenC_iff b T _ r.base).mp this
  · intro h r hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    rw [CapAtom.base_rename, CapAtom.useMode_rename]
    exact (Γ.selfInner_weakenC_iff b T _ r₀.base).mpr (h r₀ hr₀)

/-- **The capture names of a store binder** have the bounds of the capture
names of a copy of its binder pushed on top of the context.  This is the
transport the entering substitution of a projection reads. -/
theorem Store.Typed.modeBound_name {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    ∀ (y : BVar s .var) (ℓ : Label) (m : EMode),
      Γ.ModeBound (.name y ℓ) m ↔
        (Γ.cons (.transparent (Γ.lookupTy y) (σ.lookup y).witnesses (σ.lookup y).capWitnesses
          (σ.lookup y).fieldLabels)).ModeBound (.name .here ℓ) m := by
  induction hσ with
  | nil => intro y; cases y
  | @cons s' σ' Γ' v T _ _ _ ih =>
      intro y ℓ m
      cases y with
      | here =>
          show _ ↔ ((Γ'.cons (.transparent T v.witnesses v.capWitnesses v.fieldLabels)).cons
            (.transparent (T.rename Rename.succ) (v.rename Rename.succ).witnesses
              (v.rename Rename.succ).capWitnesses (v.rename Rename.succ).fieldLabels)).ModeBound
              (.name .here ℓ) m
          rw [Value.witnesses_rename, Value.capWitnesses_rename, Value.fieldLabels_rename,
            Ctx.modeBound_name_weaken_iff]
      | there z =>
          show (Γ'.cons _).ModeBound (CapAtom.weaken (.name z ℓ)) m ↔
            ((Γ'.cons (.transparent T v.witnesses v.capWitnesses v.fieldLabels)).cons
              (.transparent ((Γ'.lookupTy z).rename Rename.succ)
                ((σ'.lookup z).rename Rename.succ).witnesses
                ((σ'.lookup z).rename Rename.succ).capWitnesses
                ((σ'.lookup z).rename Rename.succ).fieldLabels)).ModeBound (.name .here ℓ) m
          rw [Ctx.modeBound_weaken_iff, Value.witnesses_rename, Value.capWitnesses_rename,
            Value.fieldLabels_rename, Ctx.modeBound_name_weaken_iff]
          exact ih z ℓ m
  | @consC s' σ' Γ' b _ _ _ ih =>
      intro y ℓ m
      cases y with
      | there z =>
          show (Γ'.consC b).ModeBound (CapAtom.weaken (.name z ℓ)) m ↔
            ((Γ'.consC b).cons
              (.transparent ((Γ'.lookupTy z).rename Rename.succ)
                ((σ'.lookup z).rename Rename.succ).witnesses
                ((σ'.lookup z).rename Rename.succ).capWitnesses
                ((σ'.lookup z).rename Rename.succ).fieldLabels)).ModeBound (.name .here ℓ) m
          rw [Ctx.modeBound_weakenC_iff, Value.witnesses_rename, Value.capWitnesses_rename,
            Value.fieldLabels_rename, Ctx.modeBound_name_weakenC_iff]
          exact ih z ℓ m
  | write _ _ _ ih => exact ih

/-- **Entering an object body** at the store binder the literal lives at.
The self goes to the receiver, whose declared set is the literal's, and the
self's capture names go to the receiver's, whose bounds are those of a copy of
the receiver's binder (`hname`, from `Store.Typed.modeBound_name` in a
store). -/
theorem Ctx.modeMap_enterObj {s : Sig} {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)}
    {Wc : CapWitnesses (s,x)} {ls : List Label} {y : BVar s .var}
    (hy : Γ.lookupTy y = T) (hfields : Γ.lookupFields y = some ls)
    (hname : ∀ ℓ m, (Γ.cons (.transparent T W Wc ls)).ModeBound (.name .here ℓ) m →
      Γ.ModeBound (.name y ℓ) m) :
    (Γ.objBody T W Wc ls).ModeMap (·.subst (Subst.enterObj y)) Γ := by
  have hfy := Ctx.isFormalVar_of_lookupFields hfields
  intro a m h
  match a with
  | .var .here =>
      show Γ.ModeBound (.var y) m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (.var .here) m := h
      rw [Ctx.modeBound_cons_here _ rfl] at h1
      change (Γ.consC .root).SetBound (T.rename Rename.succ).captureSet m at h1
      rw [Ty.captureSet_renameSucc, Ctx.setBound_weakenC_iff] at h1
      rw [Ctx.modeBound_var Γ y hfy, hy]
      exact h1
  | .var (.there (.there z)) =>
      show Γ.ModeBound (.var z) m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (CapAtom.weaken (CapAtom.weaken (.var z))) m := h
      rw [Ctx.modeBound_weaken_iff, Ctx.modeBound_weakenC_iff] at h1
      exact h1
  | .cvar (.there .here) =>
      show Γ.ModeBound .top m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (CapAtom.weaken (.cvar .here)) m := h
      rw [Ctx.modeBound_weaken_iff] at h1
      have hm := (Ctx.modeBound_consC_leaf Γ (b := .root) (by simp) (by simp) m).mp h1
      exact (Γ.modeBound_top m).mpr hm
  | .cvar (.there (.there κ)) =>
      show Γ.ModeBound (.cvar κ) m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (CapAtom.weaken (CapAtom.weaken (.cvar κ))) m := h
      rw [Ctx.modeBound_weaken_iff, Ctx.modeBound_weakenC_iff] at h1
      exact h1
  | .name .here ℓ =>
      show Γ.ModeBound (.name y ℓ) m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (.name .here ℓ) m := h
      exact hname ℓ m ((Γ.modeBound_name_weakenC_iff .root T W Wc ls ℓ m).mp h1)
  | .name (.there (.there z)) ℓ =>
      show Γ.ModeBound (.name z ℓ) m
      have h1 : ((Γ.consC .root).cons (.transparent (T.rename Rename.succ)
          (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)).ModeBound
          (CapAtom.weaken (CapAtom.weaken (.name z ℓ))) m := h
      rw [Ctx.modeBound_weaken_iff, Ctx.modeBound_weakenC_iff] at h1
      exact h1
  | .top =>
      show Γ.ModeBound .top m
      exact (Γ.modeBound_top m).mpr (((Γ.objBody T W Wc ls).modeBound_top m).mp h)
  | .mode md a => exact Γ.modeBound_mode md _ m

/-! ## The two substitution instances the machine uses

The equations of `Subst.selfCast` and the facts that say a term binding is
invisible to the capture spine moved to `TypingSubst.lean`, so that
`FormAlgebra.lean`, which reads them and nothing else of the machine, can
import `TypingSubst` rather than this module. -/

theorem Subst.Typed.selfCast {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label} (hE : Γ ⊢ E : S₀ ≤ T)
    (hms : Γ.ModeSound)
    (hWc : ∀ ℓ, (Γ.cons (.transparent S₀ W Wc Fs)).AccessOnly [CapAtom.name .here ℓ]) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E↑)
      (Γ.cons (.transparent S₀ W Wc Fs)) where
  var := by
    intro y
    cases y with
    | here =>
        show (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .cast (.var .here) E↑ :
          ((Γ.cons (.opaque T)).lookupTy .here).subst (Subst.selfCast E↑)
        have hE' : (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ E↑ : S₀↑ ≤ T↑ :=
          hE.weaken _
        have hvar : (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .var .here : S₀↑ := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Wc Fs)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .var (.there z) :
          ((Γ.cons (.opaque T)).lookupTy (.there z)).subst (Subst.selfCast E↑)
        simpa using Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Wc Fs)) (x := .there z)
  ty := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simp
  transparent := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simpa using (Ctx.isTransparent_there Γ _ z).mp ht
  def_ := by
    intro y l W' hW'
    cases y with
    | here => simp at hW'
    | there z =>
        rw [Ctx.lookupDef_there] at hW'
        simpa using hW'
  defC := by
    intro y l C' hC'
    cases y with
    | here => simp at hC'
    | there z =>
        rw [Ctx.lookupDefC_there] at hC'
        simpa using hC'
  fields := by
    intro y Fs' hFs'
    cases y with
    | here => simp at hFs'
    | there z =>
        rw [Ctx.lookupFields_there] at hFs'
        simpa using hFs'
  capRoot := by
    intro r hr
    simp only [CapAtom.subst_selfCast]
    unfold Ctx.IsRoot
    rw [← Ctx.isRootB_cons_eq Γ (Binding.opaque T) (.transparent S₀ W Wc Fs) r]
    exact hr
  capLvl := by
    intro e r _ hl
    simp only [CapAtom.subst_selfCast]
    unfold Ctx.LvlLe
    rw [← Ctx.lvlLeB_cons_eq Γ (Binding.opaque T) (.transparent S₀ W Wc Fs) e r]
    exact hl
  capInner := by
    simp only [CapAtom.subst_selfCast]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)
  capModeFree := by
    intro κ
    cases κ with
    | there κ0 => rfl
  capInst := by
    intro a C h
    simp only [CapAtom.subst_selfCast, CaptureSet.subst_selfCast]
    exact (Ctx.instOf_cons_eq Γ (.opaque T) (.transparent S₀ W Wc Fs) a C).mp h
  modeBound := Ctx.modeMap_adjust hms hE hWc
  capOwn := by
    intro a W' h
    simp only [CapAtom.subst_selfCast, CaptureSet.subst_selfCast]
    exact (Ctx.ownOf_cons_eq Γ (.opaque T) (.transparent S₀ W Wc Fs) a W').mp h
  capLoc := by
    intro a k h
    simp only [CapAtom.subst_selfCast]
    exact ⟨k, (Ctx.locOf_cons_eq Γ (.opaque T) (.transparent S₀ W Wc Fs) a k).mp h⟩
  kill := Ctx.KillMap.selfCast Γ (.opaque T) (.transparent S₀ W Wc Fs) E↑

/-- The self binder of a stored object literal may be replaced by the
variable it is stored at. -/
theorem Ctx.Ren.selfObj {s : Sig} {Γ : Ctx s} {Tel : Telescope (s,x)} {C : CaptureSet s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label} {y : BVar s .var}
    (hty : Γ.lookupTy y = (μ Tel) ^ C)
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧))
    (hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧))
    (hfields : Γ.lookupFields y = some Fs)
    (hname : ∀ ℓ m, (Γ.cons (.transparent ((μ Tel) ^ C) W Wc Fs)).ModeBound (.name .here ℓ) m →
      Γ.ModeBound (.name y ℓ) m) :
    Ctx.Ren (Γ.cons (.transparent ((μ Tel) ^ C) W Wc Fs)) (Rename.subst y) Γ where
  ty := by
    intro z
    cases z with
    | here =>
        have h : ((Γ.cons (Binding.transparent ((μ Tel) ^ C) W Wc Fs)).lookupTy BVar.here).rename
            (Rename.subst y) = (μ Tel) ^ C := Ty.rename_subst_weaken _ _
        exact hty.trans h.symm
    | there w => simp
  def_ := by
    intro z l W' hW'
    cases z with
    | here =>
        obtain rfl : W.get l = W' := by simpa using hW'
        simpa [Shape.substVar] using hdef l
    | there w =>
        rw [Ctx.lookupDef_there] at hW'
        obtain ⟨W0, hd, rfl⟩ := Option.map_eq_some_iff.mp hW'
        simpa using hd
  defC := by
    intro z l C' hC'
    cases z with
    | here =>
        obtain rfl : Wc.get l = C' := by simpa using hC'
        simpa [CaptureSet.substVar] using hdefC l
    | there w =>
        rw [Ctx.lookupDefC_there] at hC'
        obtain ⟨C0, hd, rfl⟩ := Option.map_eq_some_iff.mp hC'
        show Γ.lookupDefC w l = some ((C0↑)⟦y⟧)
        rw [CaptureSet.rename_subst_weaken]
        exact hd
  fields := by
    intro z Fs' hFs'
    cases z with
    | here =>
        obtain rfl : Fs = Fs' := by simpa using hFs'
        simpa using hfields
    | there w =>
        rw [Ctx.lookupFields_there] at hFs'
        simpa using hFs'
  capRoot := by
    intro r hr
    obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
    rw [CapAtom.rename_subst_weaken]
    exact hr₀
  capLvl := by
    intro e r hr hl
    obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
    rw [CapAtom.rename_subst_weaken]
    -- the level fact about the self binder is L0 in `Γ`, at the variable it
    -- is stored at
    have hhere : ∀ x0 : BVar s .var,
        (Γ.cons (Binding.transparent ((μ Tel) ^ C) W Wc Fs)).LvlLe (CapAtom.var .here)
          (CapAtom.weaken (k := .var) r₀) → Γ.LvlLe (CapAtom.var x0) r₀ := by
      intro x0 hh
      have h1 : (Γ.cons (Binding.transparent ((μ Tel) ^ C) W Wc Fs)).LvlLe
          (CapAtom.weaken (k := .var) Γ.rootAtom) (CapAtom.weaken (k := .var) r₀) := by
        unfold Ctx.LvlLe
        rw [Ctx.lvlLeB_congr_left (Γ.cons (Binding.transparent ((μ Tel) ^ C) W Wc Fs))
          (CapAtom.weaken (k := .var) Γ.rootAtom) (CapAtom.var .here) _
          (Ctx.lvlAtom_cons_here_eq Γ (Binding.transparent ((μ Tel) ^ C) W Wc Fs)).symm]
        exact hh
      rw [Ctx.lvlLe_weaken_iff] at h1
      exact Ctx.LvlLe.trans (Ctx.rootAtom_isRoot Γ) (Γ.lvl_le_rootAtom_var x0) h1
    revert hl
    refine Ctx.lvlLe_rename_of_base ?_ e
    clear e
    intro e hbase hl
    cases e with
    | mode m e₀ => exact absurd hbase (CapAtom.base_ne_mode e₀ m e₀)
    | top => exact Ctx.top_lvlLe _ _
    | cvar k =>
        cases k with
        | there k0 =>
            exact (Ctx.lvlLe_weaken_iff Γ _ (CapAtom.cvar k0) r₀).mp hl
    | var x =>
        cases x with
        | here => exact hhere y hl
        | there x0 =>
            exact (Ctx.lvlLe_weaken_iff Γ _ (CapAtom.var x0) r₀).mp hl
    | name x l =>
        cases x with
        | here => exact hhere y hl
        | there x0 =>
            exact (Ctx.lvlLe_weaken_iff Γ _ (CapAtom.name x0 l) r₀).mp hl
  capInner := by
    rw [Ctx.rootAtom_cons Γ (Binding.transparent ((μ Tel) ^ C) W Wc Fs),
      CapAtom.rename_subst_weaken]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)
  capInst := by
    intro a C' hI
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.instOf_cons_cases hI
    rw [CapAtom.rename_subst_weaken, CaptureSet.rename_subst_weaken']
    exact h₀
  modeBound := by
    intro a m h
    match a with
    | .var .here =>
        show Γ.ModeBound (.var y) m
        rw [Ctx.modeBound_cons_here Γ (b := .transparent ((μ Tel) ^ C) W Wc Fs) rfl] at h
        rw [Ctx.modeBound_var Γ y (Ctx.isFormalVar_of_lookupFields hfields), hty]
        exact h
    | .var (.there z) =>
        show Γ.ModeBound (.var z) m
        exact (Γ.modeBound_weaken_iff _ (.var z) m).mp h
    | .cvar (.there κ) =>
        show Γ.ModeBound (.cvar κ) m
        exact (Γ.modeBound_weaken_iff _ (.cvar κ) m).mp h
    | .name .here ℓ =>
        show Γ.ModeBound (.name y ℓ) m
        exact hname ℓ m h
    | .name (.there z) ℓ =>
        show Γ.ModeBound (.name z ℓ) m
        exact (Γ.modeBound_weaken_iff _ (.name z ℓ) m).mp h
    | .top =>
        show Γ.ModeBound .top m
        exact (Γ.modeBound_top m).mpr ((Ctx.modeBound_top _ m).mp h)
    | .mode md a => exact Γ.modeBound_mode md _ m
  capOwn := by
    intro a W' hO
    obtain ⟨a₀, W₀, rfl, rfl, h₀⟩ := Ctx.ownOf_cons_cases hO
    rw [CapAtom.rename_subst_weaken, CaptureSet.rename_subst_weaken']
    exact h₀
  capLoc := by
    intro a k hL
    obtain ⟨a₀, rfl, h₀⟩ := Ctx.locOf_cons_cases hL
    rw [CapAtom.rename_subst_weaken]
    exact ⟨k, h₀⟩
  kill := Ctx.KillMap.ofEmbed (Δ := Γ.cons (.transparent ((μ Tel) ^ C) W Wc Fs)) (Γ' := Γ)
    BVar.there (fun _ => rfl)
    (fun κ _ => by cases κ with | there κ₀ => exact ⟨κ₀, rfl⟩)
    (fun κ' => by rw [Ctx.lookupCap_there, CapBound.consumable_weaken])
    (fun κ' => by rw [Ctx.lookupCap_there, CapBound.live_weaken])
    (fun κ _ _ _ => by cases κ with | there κ₀ => exact ⟨κ₀, rfl⟩)
    (fun _ _ ho => by
      obtain ⟨_, κ₀, -, rfl, -⟩ := Ctx.ownsB_cons_cases ho
      exact ⟨κ₀, rfl⟩)
    (fun _ _ ho => by rwa [Ctx.ownsB_cons_there] at ho)

/-! ## The answer sort: isolation, canonical forms, and applying a coercion

**T8, isolation.**  Store free, no fuel, no context predicate.  An existential
answer cannot be widened to a plain one, which is the target's form of "a
result `fresh` cannot flow into a local `any`". -/

/-- Whether an answer is an existential, bounded or fresh. -/
def ETy.isEx : ETy s → Bool
  | .ex _ _ => true
  | .fresh _ => true
  | .ty _ => false

@[simp] theorem ETy.isEx_ty (T : Ty s) : (ETy.ty T).isEx = false := rfl
@[simp] theorem ETy.isEx_ex (C : CaptureSet s) (T : Ty (s,c)) : (ETy.ex C T).isEx = true := rfl
@[simp] theorem ETy.isEx_fresh (T : Ty (s,c)) : (ETy.fresh T).isEx = true := rfl

/-- **T8.**  An existential stays an existential along answer inclusion. -/
theorem ex_stays_ex {s : Sig} {Γ : Ctx s} :
    ∀ (g : ELeCo s) {E₁ E₂ : ETy s}, Γ ⊢ᵉ g : E₁ ≤ E₂ → E₁.isEx = true → E₂.isEx = true
  | .plain _, _, _, h => by cases h with | plain _ => intro he; exact absurd he (by simp)
  | .pack _ _ _, _, _, h => by cases h with | pack _ _ => intro _; rfl
  | .cong _ _, _, _, h => by cases h with | cong _ _ => intro _; rfl
  | .trans g₁ g₂, _, _, h => by
      cases h with
      | trans h₁ h₂ => intro he; exact ex_stays_ex g₂ h₂ (ex_stays_ex g₁ h₁ he)
  | .packF _ _, _, _, h => by cases h with | packF _ _ _ _ => intro _; rfl
  | .congF _, _, _, h => by cases h with | congF _ => intro _; rfl

/-- **T8, the corollary.**  No evidence takes an existential answer to a
plain one. -/
theorem no_ex_le_ty {s : Sig} {Γ : Ctx s} {g : ELeCo s} {C₀ : CaptureSet s}
    {T₁ : Ty (s,c)} {T₂ : Ty s} (h : Γ ⊢ᵉ g : ∃ᶜ[C₀] T₁ ≤ .ty T₂) : False := by
  have := ex_stays_ex g h rfl
  simp at this

/-! ### Canonical forms at an existential answer

**T9.**  Both are one inversion on the wrapper: no normalisation, no fuel,
no store.  They are what the two unpack steps read. -/

/-- **T9.**  A packed atom at an existential answer is a `pack`. -/
theorem pack_canon {s : Sig} {Γ : Ctx s} {p : PAtom s} {C₀ : CaptureSet s} {T : Dom s}
    (h : Γ ⊢ₚ p : ∃ᶜ[C₀] T) :
    ∃ (C : CaptureSet s) (h₀ : CapCo s) (e : LeCo (Sig.scope s)) (a : Atom s) (S : Ty s),
      p = .pack C h₀ e a ∧ Γ ⊢ₐ a : S ∧ Γ ⊢ᶜ h₀ : C ⊑ C₀ ∧
        Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot := by
  cases h with
  | pack ha hb he => exact ⟨_, _, _, _, _, rfl, ha, hb, he⟩

/-- **T9, the value twin.** -/
theorem pack_canon_val {s : Sig} {Γ : Ctx s} {v : Value s} {C₀ : CaptureSet s} {T : Dom s}
    (h : Γ ⊢ᵥᵉ v : ∃ᶜ[C₀] T) :
    ∃ (C : CaptureSet s) (h₀ : CapCo s) (e : LeCo (Sig.scope s)) (v₀ : Value s) (S : Ty s),
      v = .pack C h₀ e v₀ ∧ Γ ⊢ᵥ v₀ : S ∧ Γ ⊢ᶜ h₀ : C ⊑ C₀ ∧
        Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot := by
  cases h with
  | pack hv hb he => exact ⟨_, _, _, _, _, rfl, hv, hb, he⟩

/-- A packed atom has no plain answer, so a wrapper at `.ty T` is plain. -/
theorem PAtom.HasType.ty_inv {s : Sig} {Γ : Ctx s} {p : PAtom s} {T : Ty s}
    (h : Γ ⊢ₚ p : .ty T) : ∃ a : Atom s, p = .plain a ∧ Γ ⊢ₐ a : T := by
  cases h with
  | plain ha => exact ⟨_, rfl, ha⟩

/-- A packed value has no plain answer, so a value at `.ty T` is typed by the
plain rule.  `Value.HasType` has no `pack` rule, which is why this holds. -/
theorem Value.HasTypeE.ty_inv {s : Sig} {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥᵉ v : .ty T) : Γ ⊢ᵥ v : T := by
  cases h with
  | plain hv => exact hv

/-! ### T-B2.3, coercions apply

`Value.applyE` and `PAtom.applyE` are total and structural on the coercion.
The clauses that hand back their input are the typed-impossible combinations,
and each is closed here by inverting the two typings, not by an appeal to
reachability. -/

/-- The residual of a congruence, read at the wrapper's instance scope.  It is
`Ctx.Ren.instC` at the identity renaming, which is T-B2.1. -/
theorem LeCo.HasType.atScopeInst {s : Sig} {Γ : Ctx s} {C : CaptureSet s}
    {f : LeCo (Sig.scope s)} {X Y : Ty (Sig.scope s)} (hC : Γ.AccessOnly C)
    (h : Γ.scope ⊢ f : X ≤ Y) : Γ.scopeInst C ⊢ f : X ≤ Y := by
  have hC' : (Γ.consC .root).AccessOnly (CaptureSet.weaken (k := .cap) C) :=
    (Γ.setBound_weakenC_iff .root C .eps).mpr hC
  have := h.rename (Ctx.Ren.instC (Γ := Γ.consC .root) (C := CaptureSet.weaken (k := .cap) C) hC')
  rwa [LeCo.rename_id, Ty.rename_id, Ty.rename_id] at this

/-- The residual of a congruence of `∃ᶠ` is read in the scope of a fresh
pack: a location and an heir are leaves that no evidence rule tells apart. -/
theorem Ctx.RenH.locOwn (Δ : Ctx s) (k k' : Bool) (Cl W : CaptureSet s) :
    Ctx.RenH (Δ.consC (.loc k Cl)) Rename.id (Δ.consC (.own k' W)) where
  ty := fun x => by cases x with | there y => simp
  def_ := fun x l W₀ hd => by cases x with | there y => simpa using hd
  defC := fun x l C₀ hd => by cases x with | there y => simpa using hd
  fields := fun x Fs hf => by cases x with | there y => simpa using hf
  capRoot := fun r hr => by
    rw [CapAtom.rename_id]
    unfold Ctx.IsRoot at hr ⊢
    rw [Ctx.isRootB_consC_congr Δ (b₁ := .own k' W) (b₂ := .loc k Cl) rfl]
    exact hr
  capLvl := fun e r _ hl => by
    rw [CapAtom.rename_id, CapAtom.rename_id]
    unfold Ctx.LvlLe at hl ⊢
    rw [Ctx.lvlLeB_consC_congr Δ (b₁ := .own k' W) (b₂ := .loc k Cl) rfl]
    exact hl
  capInst := fun a C₀ hI => by
    rw [CapAtom.rename_id, CaptureSet.rename_id]
    rcases Ctx.instOf_consC_cases hI with ⟨C₁, rfl, rfl, hb⟩ | ⟨a₀, C₁, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hb
    · exact h₀.weakenC _
  modeBound := fun a m ha => by
    show (Δ.consC (CapBound.own k' W)).ModeBound (a.rename Rename.id) m
    rw [CapAtom.rename_id]
    cases a with
    | cvar κ =>
        cases κ with
        | here =>
            rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha ⊢
            exact ha
        | there κ₀ =>
            exact (Δ.modeBound_weakenC_iff _ (.cvar κ₀) m).mpr
              ((Δ.modeBound_weakenC_iff _ (.cvar κ₀) m).mp ha)
    | var y =>
        cases y with
        | there y₀ =>
            exact (Δ.modeBound_weakenC_iff _ (.var y₀) m).mpr
              ((Δ.modeBound_weakenC_iff _ (.var y₀) m).mp ha)
    | name y l =>
        cases y with
        | there y₀ =>
            exact (Δ.modeBound_weakenC_iff _ (.name y₀ l) m).mpr
              ((Δ.modeBound_weakenC_iff _ (.name y₀ l) m).mp ha)
    | top => exact (Ctx.modeBound_top _ m).mpr ((Ctx.modeBound_top _ m).mp ha)
    | mode md a => exact Ctx.modeBound_mode _ md a m
  capOwn := fun a W₀ hO => by
    rw [CapAtom.rename_id, CaptureSet.rename_id]
    rcases Ctx.ownOf_consC_cases hO with ⟨W₁, rfl, rfl, hb⟩ | ⟨a₀, W₁, rfl, rfl, h₀⟩
    · simp [CapBound.ownSet?] at hb
    · exact h₀.weakenC _

/-- The residual of a congruence of `∃ᶠ`, read in the scope of a fresh pack. -/
theorem LeCo.HasType.atScopeOwn {s : Sig} {Γ : Ctx s} {W : CaptureSet s}
    {f : LeCo (Sig.scope s)} {X Y : Ty (Sig.scope s)}
    (h : ((Γ.consC .root).consC (.loc true [])) ⊢ f : X ≤ Y) : Γ.scopeOwn W ⊢ f : X ≤ Y := by
  have := h.renameH (Ctx.RenH.locOwn (Γ.consC .root) true true [] (CaptureSet.weaken (k := .cap) W))
  rwa [LeCo.rename_id, Ty.rename_id, Ty.rename_id] at this

/-- **T-B2.3.**  A typed answer coercion applies to a typed value wrapper. -/
theorem Value.HasTypeE.applyE {s : Sig} {Γ : Ctx s} :
    ∀ (g : ELeCo s) {v : Value s} {E E' : ETy s},
      Γ ⊢ᵥᵉ v : E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ᵥᵉ v.applyE g : E'
  | .plain _, _, _, _, hv, hg => by
      cases hg with | plain he => exact .plain ((hv.ty_inv).cast he)
  | .pack _ _ _, _, _, _, hv, hg => by
      cases hg with | pack hh he hA => exact .pack hv.ty_inv hh he hA
  | .cong _ _, _, _, _, hv, hg => by
      cases hg with
      | cong hh hf =>
          cases hv with
          | pack hv₀ hb he hA =>
              exact .pack hv₀ (.trans hb hh) (he.trans (LeCo.HasType.atScopeInst hA hf)) hA
  | .trans g₁ g₂, _, _, _, hv, hg => by
      cases hg with
      | trans h₁ h₂ =>
          exact Value.HasTypeE.applyE g₂ (Value.HasTypeE.applyE g₁ hv h₁) h₂
  | .packF _ _, _, _, _, hv, hg => by
      cases hg with | packF hN hD hc he => exact .packF hv.ty_inv hN hD hc he
  | .congF _, _, _, _, hv, hg => by
      cases hg with
      | congF hf =>
          cases hv with
          | packF hv₀ hN hD hc he =>
              exact .packF hv₀ hN hD hc (he.trans (LeCo.HasType.atScopeOwn hf))

/-- **T-B2.3, the atom twin.** -/
theorem PAtom.HasType.applyE {s : Sig} {Γ : Ctx s} :
    ∀ (g : ELeCo s) {p : PAtom s} {E E' : ETy s},
      Γ ⊢ₚ p : E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ₚ p.applyE g : E'
  | .plain _, _, _, _, hp, hg => by
      cases hg with
      | plain he =>
          obtain ⟨a, rfl, ha⟩ := hp.ty_inv
          exact .plain (ha.cast he)
  | .pack _ _ _, _, _, _, hp, hg => by
      cases hg with
      | pack hh he hA =>
          obtain ⟨a, rfl, ha⟩ := hp.ty_inv
          exact .pack ha hh he hA
  | .cong _ _, _, _, _, hp, hg => by
      cases hg with
      | cong hh hf =>
          cases hp with
          | pack ha hb he hA =>
              exact .pack ha (.trans hb hh) (he.trans (LeCo.HasType.atScopeInst hA hf)) hA
  | .trans g₁ g₂, p, _, _, hp, hg => by
      cases hg with
      | trans h₁ h₂ =>
          rw [PAtom.applyE_trans]
          exact PAtom.HasType.applyE g₂ (PAtom.HasType.applyE g₁ hp h₁) h₂
  | .packF _ _, _, _, _, hp, hg => by
      cases hg with
      | packF hN hD hc he =>
          obtain ⟨a, rfl, ha⟩ := hp.ty_inv
          exact .packF ha hN hD hc he
  | .congF _, _, _, _, hp, hg => by
      cases hg with
      | congF hf =>
          cases hp with
          | packF ha hN hD hc he =>
              exact .packF ha hN hD hc (he.trans (LeCo.HasType.atScopeOwn hf))

/-! ## Preservation -/

/-- Every consumable name of `C` is reached through a name of `D`: itself at
`consume`, itself or an owner below it (plan-5h T0.4, decision 39). -/
def Ctx.NamesLe (Γ : Ctx s) (C D : CaptureSet s) : Prop :=
  ∀ a ∈ Γ.names C, ∀ κ, a.base = .cvar κ → (Γ.lookupCap κ).consumable = true →
    ∃ b ∈ Γ.names D, ∃ κ', b.base = .cvar κ' ∧ a.effMode ≤ b.effMode ∧
      (κ' = κ ∨ (a.effMode ≠ .consume ∧ Γ.MayOwn κ' κ))

/-! ### Access and separation across a cover up to ownership (plan-5h S0.3) -/

/-- **The access half of every substitution over a typed store**: a set whose
names are covered, up to ownership, by an accessible set is accessible, under
the same ghost.  A killed name owned by a live heir is effectively live. -/
theorem Ctx.Accessible.of_namesLe {Γ : Ctx s} (hs : Γ.SepInv) {D : List (BVar s .cap)}
    {C C' : CaptureSet s} (hle : Γ.NamesLe C' C) (h : (Γ.killNames D).Accessible C) :
    (Γ.killNames D).Accessible C' := by
  intro a ha κ hκ
  rw [Ctx.names_killNames] at ha
  cases hc : (Γ.lookupCap κ).consumable with
  | false => exact Ctx.effLive_of_not_consumable hs.allLive hc
  | true =>
      obtain ⟨b, hb, κ', hκ', -, hrel⟩ := hle a ha κ hκ hc
      have hl := h b (by rw [Ctx.names_killNames]; exact hb) κ' hκ'
      rcases hrel with rfl | ⟨-, hm⟩
      · exact hl
      · exact hl.owns ((hs.mayOwn_iff_owns).mp hm).killNames

/-- Reflexive ownership. -/
def Ctx.OwnsR (Γ : Ctx s) (a x : BVar s .cap) : Prop := a = x ∨ Γ.Owns a x

/-- The last step of an ownership chain. -/
theorem Ctx.Owns.last {Γ : Ctx s} {l κ : BVar s .cap} (h : Γ.Owns l κ) :
    ∃ c, Γ.ownsB c κ = true ∧ (c = l ∨ Γ.Owns l c) := by
  induction h with
  | direct hd => exact ⟨_, hd, Or.inl rfl⟩
  | trans h₁ _ _ ih₂ =>
      obtain ⟨c, hc, hcm⟩ := ih₂
      rcases hcm with rfl | hcm
      · exact ⟨_, hc, Or.inr h₁⟩
      · exact ⟨c, hc, Or.inr (.trans h₁ hcm)⟩

/-- **In a store two owners of one name are comparable**, by linearity. -/
theorem Ctx.ownsR_comparable {Γ : Ctx s} (hs : Γ.SepInv) : ∀ (n : Nat) (x : BVar s .cap),
    x.depth ≤ n → ∀ a b, Γ.OwnsR a x → Γ.OwnsR b x → Γ.OwnsR a b ∨ Γ.OwnsR b a
  | n, x, hn, a, b, ha, hb => by
      rcases ha with rfl | ha
      · exact Or.inr hb
      rcases hb with rfl | hb
      · exact Or.inl (Or.inr ha)
      obtain ⟨ca, hca, hac⟩ := ha.last
      obtain ⟨cb, hcb, hbc⟩ := hb.last
      have he : ca = cb := hs.linear ca cb x hca hcb
      subst he
      have hd := Ctx.depth_lt_of_ownsB hca
      cases n with
      | zero => exact absurd (Nat.lt_of_lt_of_le hd hn) (Nat.not_lt_zero _)
      | succ n =>
          have hac' : Γ.OwnsR a ca := by
            rcases hac with rfl | h
            · exact Or.inl rfl
            · exact Or.inr h
          have hbc' : Γ.OwnsR b ca := by
            rcases hbc with rfl | h
            · exact Or.inl rfl
            · exact Or.inr h
          exact Ctx.ownsR_comparable hs n ca
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hd hn)) a b hac' hbc'

/-- **In a store a name that may own an owned name is comparable with its
owner**: the hypothesis of `Ctx.NamesMapO.argSep`, which a store context
meets and a typing context past a claim does not
(`s0-g6s-counterexample.lean`). -/
theorem Ctx.SepInv.mayOwn_comparable {Γ : Ctx s} (hs : Γ.SepInv) (l κ₀ κ' : BVar s .cap)
    (hm : Γ.MayOwn l κ') (ho : Γ.Owns κ₀ κ') :
    l = κ₀ ∨ Γ.MayOwn l κ₀ ∨ Γ.MayOwn κ₀ l := by
  rcases Ctx.ownsR_comparable hs κ'.depth κ' (Nat.le_refl _) l κ₀
      (Or.inr ((hs.mayOwn_iff_owns).mp hm)) (Or.inr ho) with h | h
  · rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Ctx.MayOwn.of_owns h))
  · rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Ctx.MayOwn.of_owns h))

/-- **The separation half of every substitution over a typed store**: a cover
up to ownership of the argument side keeps `ArgSep`, by linearity. -/
theorem Ctx.ArgSep.of_cover {Γ : Ctx s} (hs : Γ.SepInv) {B B' C : CaptureSet s}
    (hcov : ∀ a' ∈ Γ.names B', ∀ κ', a'.base = .cvar κ' →
      ∃ a ∈ Γ.names B, ∃ κ, a.base = .cvar κ ∧ (κ = κ' ∨ Γ.Owns κ κ'))
    (h : Γ.ArgSep B C) : Γ.ArgSep B' C := by
  intro a' ha' κ' hκ'
  obtain ⟨a, ha, κ, hκ, hr⟩ := hcov a' ha' κ' hκ'
  obtain ⟨h₁, h₂⟩ := h a ha κ hκ
  rcases hr with rfl | hr
  · exact ⟨h₁, h₂⟩
  refine ⟨fun hm => ?_, fun l hl hm => h₂ l hl (Ctx.MayOwn.of_owns (.trans hr
    ((hs.mayOwn_iff_owns).mp hm)))⟩
  rcases Ctx.mem_ownClosure.mp hm with hm | ⟨l, hl, hlm⟩
  · exact h₂ κ' hm (Ctx.MayOwn.of_owns hr)
  · have hlo := (hs.mayOwn_iff_owns).mp hlm
    rcases Ctx.ownsR_comparable hs κ'.depth κ' (Nat.le_refl _) l κ (Or.inr hlo) (Or.inr hr) with
      hc | hc
    · rcases hc with rfl | hc
      · exact h₁ (Ctx.mem_ownClosure.mpr (Or.inl hl))
      · exact h₁ (Ctx.mem_ownClosure.mpr (Or.inr ⟨l, hl, Ctx.MayOwn.of_owns hc⟩))
    · rcases hc with rfl | hc
      · exact h₁ (Ctx.mem_ownClosure.mpr (Or.inl hl))
      · exact h₂ l hl (Ctx.MayOwn.of_owns hc)

/-- Typedness of the head form used by the application and unboxing steps:
whenever the head form of a function atom's casts is `pi d c`, `d` and `c`
are typed between the atom's function type and its closure's type; whenever
it is the identity form, the two function types coincide; and the same two
sentences for a box atom, whose head form is `boxed d` or the identity.
Discharged by the canonical-forms theorem (`CanonicalForms.lean`). -/
structure FormsTyped (σ : Store s) (Γ : Ctx s) : Prop where
  pi : ∀ {a : Atom s} {S : Dom s} {T : Cod s} {C : CaptureSet s} {n : Nat} {a' : Atom s}
    {d : LeCo (Sig.scope s)} {c : ELeCo (Sig.body s)} {S₀ : Dom s} {T₀ : Cod s},
    Γ ⊢ₐ a : (Π(S) T) ^ C → σ ⊢ a ⇓ᶜ[n] (a', .pi d c) →
    (Γ.lookupTy a.root).shape = Π(S₀) T₀ →
    Γ.scope ⊢ d : S.underRoot ≤ S₀.underRoot ∧
      (Γ.body S) ⊢ᵉ c : T₀.underRoot ≤ T.underRoot
  refl : ∀ {a : Atom s} {S : Dom s} {T : Cod s} {C : CaptureSet s} {n : Nat} {a' : Atom s}
    {F : Form s},
    Γ ⊢ₐ a : (Π(S) T) ^ C → σ ⊢ a ⇓ᶜ[n] (a', F) →
    (F = .id ∨ ∃ φ, F = .eqv φ) →
    (Γ.lookupTy a.root).shape = Π(S) T
  boxed : ∀ {a : Atom s} {X T : Ty s} {D : CaptureSet s} {n : Nat} {a' : Atom s}
    {d : LeCo s},
    Γ ⊢ₐ a : (□ T) ^ D → σ ⊢ a ⇓ᶜ[n] (a', .boxed d) →
    (Γ.lookupTy a.root).shape = □ X →
    Γ ⊢ d : X ≤ T
  boxRefl : ∀ {a : Atom s} {T : Ty s} {D : CaptureSet s} {n : Nat} {a' : Atom s}
    {F : Form s},
    Γ ⊢ₐ a : (□ T) ^ D → σ ⊢ a ⇓ᶜ[n] (a', F) →
    (F = .id ∨ ∃ φ, F = .eqv φ) →
    (Γ.lookupTy a.root).shape = □ T
  /-- Closed capture evidence keeps every mode bound (plan-5h T0.4). -/
  modeSound : Γ.ModeSound
  /-- The same one capture slot further, where an unpack reads its payload. -/
  modeSoundC : ∀ b : CapBound s, b.isRoot = false → (Γ.consC b).ModeSound
  /-- Closed evidence covers names (plan-5h T0.4, `namesLe_closed`). -/
  namesLe : ∀ (f : CapCo s) (C D : CaptureSet s), Γ ⊢ᶜ f : C ⊑ D → Γ.NamesLe C D
  /-- Closed evidence keeps consumed leaves (`Ctx.consumedLeaves_closed`). -/
  leavesLe : ∀ (f : CapCo s) (C D : CaptureSet s), Γ ⊢ᶜ f : C ⊑ D →
    ∀ κ ∈ Γ.consumedLeaves C, κ ∈ Γ.consumedLeaves D
  /-- Closed evidence reflects the kill premise (`Ctx.killOk_closed`). -/
  killOkLe : ∀ (f : CapCo s) (C D : CaptureSet s), Γ ⊢ᶜ f : C ⊑ D → Γ.KillOk D → Γ.KillOk C
  /-- The three one capture slot further. -/
  namesLeC : ∀ b : CapBound s, b.isRoot = false →
    ∀ (f : CapCo (s,c)) (C D : CaptureSet (s,c)), (Γ.consC b) ⊢ᶜ f : C ⊑ D →
      (Γ.consC b).NamesLe C D
  leavesLeC : ∀ b : CapBound s, b.isRoot = false →
    ∀ (f : CapCo (s,c)) (C D : CaptureSet (s,c)), (Γ.consC b) ⊢ᶜ f : C ⊑ D →
      ∀ κ ∈ (Γ.consC b).consumedLeaves C, κ ∈ (Γ.consC b).consumedLeaves D
  killOkLeC : ∀ b : CapBound s, b.isRoot = false →
    ∀ (f : CapCo (s,c)) (C D : CaptureSet (s,c)), (Γ.consC b) ⊢ᶜ f : C ⊑ D →
      (Γ.consC b).KillOk D → (Γ.consC b).KillOk C

/-- A step that does not allocate keeps the signature: the result type is
transported along the identity renaming. -/
theorem State.Typed.exists_rename_id {s : Sig} {st : State s} {U : Ty s}
    (h : State.Typed st U) : ∃ ρ : Rename s s, State.Typed st (U.rename ρ) :=
  ⟨Rename.id, by simpa using h⟩

/-- The avoidance evidence of a let, transported into the transparent context
of the freshly allocated literal by the very substitution that `Tm.adjust`
applies to the body.  The value carried casts, whose composite is `E`.  The
use set on the left is that of the adjusted body, so `cap_canon` reads this
as `CapLe` between the adjusted body's use set and the declared set.  This is
what `step_uses` needs at `alloc`. -/
theorem CapCo.HasType.adjust {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s} {v : Value s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)}
    (hE? : v.composite? = some E) (hE : Γ ⊢ E : S₀ ≤ T) (hms : Γ.ModeSound)
    (hWc : ∀ ℓ, (Γ.cons (.transparent S₀ W Wc Fs)).AccessOnly [CapAtom.name .here ℓ])
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑) :
    (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ᶜ f.subst (Subst.selfCast E↑)
      : (u.adjust v).uses ⊑ U'↑ := by
  rw [show u.adjust v = u.subst (Subst.selfCast E↑) by simp [Tm.adjust, hE?]]
  simpa [Tm.uses_subst] using
    hf.subst (Subst.Typed.selfCast (W := W) (Wc := Wc) (Fs := Fs) hE hms hWc)

/-- The same when the value carried no cast: `Tm.adjust` is the identity and
only the context is refined. -/
theorem CapCo.HasType.adjust_none {s : Sig} {Γ : Ctx s} {T : Ty s} {v : Value s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)}
    (hn : v.composite? = none)
    (hWc : ∀ ℓ, (Γ.cons (.transparent T W Wc Fs)).AccessOnly [CapAtom.name .here ℓ])
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑) :
    (Γ.cons (.transparent T W Wc Fs)) ⊢ᶜ f : (u.adjust v).uses ⊑ U'↑ := by
  rw [show u.adjust v = u by simp [Tm.adjust, hn]]
  exact hf.refine (Ctx.Refines.transparent hWc)

/-- The type sort of a substitution reads an argument only through its root,
so two arguments with one root give one substitution on types. -/
theorem Subst.arg_core_congr {s : Sig} {a a' : Atom s} (h : a.root = a'.root) :
    (Subst.arg a).core = (Subst.arg a').core := by
  apply Subst.funext'
  · intro y
    cases y with
    | here => show Atom.var a.root = Atom.var a'.root; rw [h]
    | there y => cases y with | there y => rfl
  · intro κ
    cases κ with
    | there κ =>
        cases κ with
        | here => show CapAtom.var a.root = CapAtom.var a'.root; rw [h]
        | there κ => rfl

/-- The same at the answer sort, which is where a codomain lives.  It is the
`Ty` lemma one sort up, through `ETy.subst_core`. -/
theorem Ty.arg_congr {s : Sig} (T : Cod s) {a a' : Atom s} (h : a.root = a'.root) :
    T.subst (Subst.arg a) = T.subst (Subst.arg a') := by
  rw [ETy.subst_core T (Subst.arg a), ETy.subst_core T (Subst.arg a'),
    Subst.arg_core_congr h]

/-- The body and the closing evidence of a stored closure, read in the
current context at the parameter binder.  This is the ingredient `step_uses`
needs at `appVar`, `appCastRefl` and `appCast`: substituting the argument
into `g` bounds the use set of the body by the closure's annotation united
with the argument. -/
theorem Store.Typed.lam_closing {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) :
    ∃ T₀ : Cod s, Γ.lookupTy x = (Π(S₀) T₀) ^ A ∧ (Γ.body S₀) ⊢ t₀ :ᵉ T₀.underRoot ∧
      (Γ.body S₀) ⊢ᶜ g : t₀.uses ⊑ (A↑↑↑ ∪ [CapAtom.var .here]) :=
  Value.HasType.lam_inv (hσ.lam_of_lookup hx)

/-- The domain evidence of a `pi` form, instantiated at the argument's root:
this is the cast the `appCast` step applies to the argument, and the reason
the step is typed.  The form's evidence lives in a scope, so the
instantiation sends the arrow's capture binder to the argument's root and the
body root to the universal root. -/
theorem Atom.HasType.castDom {s : Sig} {Γ : Ctx s} {S₀ S : Dom s}
    {d : LeCo (Sig.scope s)} {b : Atom s} (hΓ : Γ.root? = none)
    (hdom : Γ.scope ⊢ d : S.underRoot ≤ S₀.underRoot)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root)))
    (hacc : Γ.AccessOnly [CapAtom.var b.root]) :
    Γ ⊢ₐ .cast b (d.subst (Subst.enterC b))
      : S₀.subst (Subst.singleC (.var (Atom.cast b (d.subst (Subst.enterC b))).root)) := by
  have hdom' := hdom.subst (Subst.Typed.enterC (b := b) hΓ hacc)
  rw [Dom.underRoot_enterC, Dom.underRoot_enterC] at hdom'
  exact Atom.HasType.cast hb hdom'

/-- The content of a stored box: its type is the box of the boxed atom's
type, so the atom is typed at the boxed type of the variable's shape. -/
theorem Store.Typed.boxContent {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {b : Atom s} (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .box b) :
    ∃ X, (Γ.lookupTy x).shape = □ X ∧ Γ ⊢ₐ b : X := by
  obtain ⟨X, hE, hb⟩ := Value.HasType.box_inv (hσ.box_of_lookup hx)
  exact ⟨X, by rw [hE]; rfl, hb⟩

/-! ## The result of each step, typed

`step_uses` of the next group needs the type of the term a step produces,
which the statement of `preservation` does not expose.  Each lemma below is
the typing of one step's result, read off the premises of the step and the
typing of the term it fires on.  The application and projection steps already
have theirs above (`Store.Typed.beta`, `Tm.HasType.betaCast`,
`Tm.HasType.projField`), and `alloc` has `preservation_alloc`. -/

/-- `let`: the head of a let is typed at the type the let frame accepts. -/
theorem Tm.HasType.let_inv {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)}
    {U' : CaptureSet s} {f : CapCo (s,x)} {U : Ty s} (h : Γ ⊢ .let t u U' f : U) :
    ∃ T, Γ ⊢ t : T ∧ (Γ.cons (.opaque T)) ⊢ u : U↑ ∧
      (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑ := by
  cases h with
  | «let» ht _ hu hf =>
      refine ⟨_, ht, ?_, ?_⟩
      · unfold Ctx.killFor at hu
        rw [← Ctx.killNames_cons] at hu
        exact hu.revive
      · unfold Ctx.killFor at hf
        rw [← Ctx.killNames_cons] at hf
        exact hf.revive

/-- `castPush`: the body of a cast is typed at the type the cast frame
accepts. -/
theorem Tm.HasType.cast_inv {s : Sig} {Γ : Ctx s} {t : Tm s} {e : LeCo s} {U : Ty s}
    (h : Γ ⊢ .cast t e : U) : ∃ T, Γ ⊢ t : T ∧ Γ ⊢ e : T ≤ U := by
  cases h with
  | cast ht he => exact ⟨_, ht, he⟩

/-! ### Instantiating a binder at the answer sort

A let body and a `letex` body may have an answer, so the two steps that
substitute an atom into a body read it against an answer.  Each lemma below is
the plain one of `TypingSubst.lean` one sort up, proven the same way. -/

/-- `Subst.single` on an answer is `substVar` at the atom's root: the answer
sort reads an atom only through its root, as a type does. -/
@[simp] theorem ETy.subst_single {s : Sig} (E : ETy (s,x)) (a : Atom s) :
    E.subst (Subst.single a) = E⟦a.root⟧ := by
  rw [ETy.subst_core, Subst.single_core, ETy.subst_ofRename]
  rfl

/-- A weakened answer is unchanged by the instantiation of the binder it
avoids.  This is the avoidance the `let` and `letex` rules write into their
body premises. -/
@[simp] theorem ETy.weaken_substVar {s : Sig} {k : Kind} (E : ETy s) (r : BVar s k) :
    (E.weaken (k := k))⟦r⟧ = E := by
  simp only [ETy.weaken, ETy.substVar, ETy.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k <;> rfl)]
  exact ETy.rename_id E

/-- `unboxRefl`: the boxed atom is typed at the type the unboxing announces.
The stored box holds an atom of the shape's boxed type, and the head form of
the wrapper chain being the identity identifies that type with the announced
one. -/
theorem Store.Typed.unboxRefl_result {s : Sig} {σ : Store s} {Γ : Ctx s}
    {a b a' : Atom s} {S : Shape s} {C D : CaptureSet s} {n : Nat} {F : Form s}
    (hσ : ⊢ σ : Γ) (hFT : FormsTyped σ Γ) (hx : σ.lookup a.root = .box b)
    (ha : Γ ⊢ₐ a : (□ (S ^ C)) ^ D) (hcf : σ ⊢ a ⇓ᶜ[n] (a', F))
    (hid : F = .id ∨ ∃ φ, F = .eqv φ) : Γ ⊢ₐ b : S ^ C := by
  obtain ⟨X, hshape, hb⟩ := hσ.boxContent hx
  obtain rfl : X = _ := Shape.box.inj (hshape.symm.trans (hFT.boxRefl ha hcf hid))
  exact hb

/-- `unboxCast`: the boxed atom under the box coercion of the head form is
typed at the type the unboxing announces. -/
theorem Store.Typed.unboxCast_result {s : Sig} {σ : Store s} {Γ : Ctx s}
    {a b a' : Atom s} {S : Shape s} {C D : CaptureSet s} {n : Nat} {d : LeCo s}
    (hσ : ⊢ σ : Γ) (hFT : FormsTyped σ Γ) (hx : σ.lookup a.root = .box b)
    (ha : Γ ⊢ₐ a : (□ (S ^ C)) ^ D) (hcf : σ ⊢ a ⇓ᶜ[n] (a', .boxed d)) :
    Γ ⊢ₐ .cast b d : S ^ C := by
  obtain ⟨X, hshape, hb⟩ := hσ.boxContent hx
  exact hb.cast (hFT.boxed ha hcf hshape)

/-! ## The two unpack steps

The eight steps of B2.12, packaged as two lemmas.  Both extend the store by
the witness as an instance binder, read the wrapper's payload in the extended
scope under the residual coercion collapsed by `Subst.instRoot`, transport the
frame's body along `Ctx.Ren.instC`, and weaken the continuation by
`Cont.Typed.weakenC`.  Neither reads a form and neither takes fuel. -/

/-- The frame's avoidance evidence, read in the store's `.inst C` context. -/
theorem CapCo.HasType.letexCharge_instC {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T : Dom s}
    {u : Tm ((s,c),x)} {f : CapCo ((s,c),x)} {U' : CaptureSet s} (hC : Γ.AccessOnly C)
    (hf : ((Γ.consC .star).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)])) :
    ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)]) := by
  have h := CapCo.HasType.rename ((Ctx.Ren.instC (Γ := Γ) (C := C) hC).lift (.opaque T)) hf
  simpa [Binding.rename, Rename.lift_id, Tm.uses_rename] using h

/-- The payload of a wrapper, read in the store's `.inst C` context: the
carried atom weakened past the instance binder, under the residual coercion
with the pack's own root collapsed by `Subst.instRoot`.  The two cancellations
are `Ty.weakenC_two_instRoot` and `Dom.underRoot_instRoot`. -/
theorem Atom.HasType.unpackPayload {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {S : Ty s}
    {T : Dom s} {e : LeCo (Sig.scope s)} {a : Atom s} (hΓ : Γ.root? = none)
    (ha : Γ ⊢ₐ a : S)
    (he : Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S))
      ≤ T.underRoot) :
    (Γ.consC (.inst C)) ⊢ₐ .cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot) : T := by
  have he' := he.subst (Subst.Typed.instRoot hΓ C)
  rw [Ty.weakenC_two_instRoot, Dom.underRoot_instRoot] at he'
  exact (ha.weakenC (.inst C) rfl).cast he'

/-- The value twin of `Atom.HasType.unpackPayload`. -/
theorem Value.HasType.unpackPayload {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {S : Ty s}
    {T : Dom s} {e : LeCo (Sig.scope s)} {v : Value s} (hΓ : Γ.root? = none)
    (hv : Γ ⊢ᵥ v : S)
    (he : Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S))
      ≤ T.underRoot) :
    (Γ.consC (.inst C)) ⊢ᵥ .cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot) : T := by
  have he' := he.subst (Subst.Typed.instRoot hΓ C)
  rw [Ty.weakenC_two_instRoot, Dom.underRoot_instRoot] at he'
  exact (hv.weakenC (.inst C) rfl rfl).cast he'

end FCdot

end Separation
