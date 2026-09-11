import Coercions.Classifiers.FCdot.CanonicalForms

namespace Classifiers

/-!
# Consistency of typed stores (Plan III §8.3, the target side of M5)

Over a typed store, closed inclusion evidence relates types of compatible
shapes only; in particular there is no closed `⊤ ≤ ⊥`, no closed inclusion
of an object type *without bounds* into a function type, no closed inclusion
of a function type into an object type with a proposition that is not a
bound, and every block name of a store binder is defined by the stored
literal's witness.  Bad bounds remain expressible under a lambda; they never
reach the store.  Along a run of the machine the store stays typed
(`Steps.typed`), so these hold at every reachable state.

With self-bound propositions a coercion may also go *through* a bound of the
source object type, or *into* an object type whose propositions are proven
without consulting the source's view; `closed_le_shapes` has one disjunct
for each.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Telescopes of bounds only -/

/-- A telescope all of whose propositions are bounds. -/
def Telescope.BndsOnly (Tel : Telescope (s,x)) : Prop :=
  ∀ (i : Nat) (P : Proposition (s,x)), Tel ∋ (i ↦ P) → ∃ X : Shape (s,x), P = Proposition.bnd X

theorem Telescope.BndsOnly.nil : (Telescope.nil (s := (s,x))).BndsOnly := by
  intro i P h; cases h

/-- An entry over a bounds-only telescope proves a bound. -/
theorem EntryTyped.bnd_of_bndsOnly {ρ : Option (BVar s .var)} {TelM : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} (hb : TelM.BndsOnly)
    (hE : EntryTyped Γ ρ TelM E P) : ∃ X : Shape (s,x), P = Proposition.bnd X := by
  cases hE with
  | le hh _ _ =>
      cases hh with
      | le hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eq hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eqSym hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eq hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eqSym hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | has hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | bnd _ => exact ⟨_, rfl⟩
  | bndId _ => exact ⟨_, rfl⟩
  -- The capture slots: their hole names a capture proposition of the source,
  -- and a bounds-only telescope has none.
  | leC hh _ _ =>
      cases hh with
      | leC hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eqC hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eqSymC hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eqC hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eqSymC hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)

mutual

/-- View-free entries out of a source that is neither `⊥` nor an object type
can only prove bounds. -/
theorem BndsTyped.bndsOnly {ρ : Option (BVar s .var)} {S : Shape s} {Es : Entries s}
    {Tel : Telescope (s,x)} (hb : Γ.resolveAt? ρ S ≠ ⊥)
    (ho : ∀ Tel₁ : Telescope (s,x), Γ.resolveAt? ρ S ≠ μ Tel₁)
    (h : BndsTyped Γ ρ S Es Tel) : Tel.BndsOnly := by
  match h with
  | .nil => intro i P hP; cases hP
  | .cons h' _ =>
      intro i P hP
      cases hP with
      | here => exact ⟨_, rfl⟩
      | there hP' => exact BndsTyped.bndsOnly hb ho h' _ _ hP'
  | .thru h' hH hM hE =>
      intro i P hP
      cases hP with
      | here => exact EntryTyped.bnd_of_bndsOnly (FormTyped.bndsOnly_target hb ho hH hM) hE
      | there hP' => exact BndsTyped.bndsOnly hb ho h' _ _ hP'

/-- A form out of a source that is neither `⊥` nor an object type reaches
only object types with bounds only. -/
theorem FormTyped.bndsOnly_target {ρ : Option (BVar s .var)} {S M : Shape s} {H : Form s}
    {TelM : Telescope (s,x)} (hb : Γ.resolveAt? ρ S ≠ ⊥)
    (ho : ∀ Tel₁ : Telescope (s,x), Γ.resolveAt? ρ S ≠ μ Tel₁)
    (hH : FormTyped Γ ρ H S M) (hM : Γ.resolveAt? ρ M = μ TelM) : TelM.BndsOnly := by
  match hH with
  | .bot hS => exact absurd hS hb
  | .top hT =>
      rw [hM] at hT
      obtain rfl := Shape.obj.inj (by simpa using hT : (μ TelM : Shape s) = μ .nil)
      exact Telescope.BndsOnly.nil
  | .id hres => exact absurd (hres.trans hM) (ho TelM)
  | .eqv hres => exact absurd (hres.trans hM) (ho TelM)
  | .pi _ hT _ _ => rw [hM] at hT; exact absurd hT (by simp)
  | .obj hS _ _ => exact absurd hS (ho _)
  | .boxed _ hT _ => rw [hM] at hT; exact absurd hT (by simp)
  | .bnd hS _ _ => exact absurd hS (ho _)
  | .into hT hB =>
      rw [hM] at hT
      obtain rfl := Shape.obj.inj hT
      exact BndsTyped.bndsOnly hb ho hB

end

/-- Closed inclusion evidence relates types of compatible shapes: the source
resolves to `⊥`, or the target to `⊤`, or both resolve equally, or both are
function types, or both are object types, or the target resolves to a box
shape, or the source resolves to an object type with a bound whose type is
below the target, or the target resolves to an object type that is
bounds-only unless the source is an object type too.  Shapes are what
resolution reads, so every disjunct is about the shape of an endpoint; the
box disjunct is the one the box former adds. -/
theorem closed_le_shapes (hσ : ⊢ σ : Γ) {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    Γ.resolve S.shape = ⊥ ∨ Γ.resolve T.shape = ⊤ ∨ Γ.resolve S.shape = Γ.resolve T.shape ∨
    (∃ S₁ T₁ S₂ T₂, Γ.resolve S.shape = Π(S₁) T₁ ∧ Γ.resolve T.shape = Π(S₂) T₂) ∨
    (∃ Tel₁ Tel₂, Γ.resolve S.shape = μ Tel₁ ∧ Γ.resolve T.shape = μ Tel₂) ∨
    (∃ Y : Ty s, Γ.resolve T.shape = □ Y) ∨
    (∃ (Tel₁ : Telescope (s,x)) (i : Nat) (T' : Shape s) (F : Form s),
      Γ.resolve S.shape = μ Tel₁ ∧ Tel₁ ∋ (i ↦ ⊑ T'↑) ∧ Γ ⊨ F : T' ≤ T.shape) ∨
    (∃ Tel₂ : Telescope (s,x), Γ.resolve T.shape = μ Tel₂ ∧
      ((∃ Tel₁ : Telescope (s,x), Γ.resolve S.shape = μ Tel₁) ∨ Tel₂.BndsOnly)) := by
  obtain ⟨_, F, _, hF⟩ := le_canon hσ h
  cases hF with
  | bot hS => exact Or.inl hS
  | top hT => exact Or.inr (Or.inl hT)
  | id hres => exact Or.inr (Or.inr (Or.inl hres))
  | eqv hres => exact Or.inr (Or.inr (Or.inl hres))
  | pi hS hT _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hS, hT⟩)))
  | obj hS hT _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, hS, hT⟩))))
  | boxed _ hT _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hT⟩)))))
  | bnd hS hAt hF' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨_, _, _, _, hS, hAt, hF'⟩))))))
  | into hT hB =>
      cases hres : Γ.resolve S.shape with
      | bot => exact Or.inl rfl
      | obj Tel₁ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨_, hT, Or.inl ⟨Tel₁, rfl⟩⟩))))))
      | sel y ℓ =>
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inr ?_⟩))))))
          exact BndsTyped.bndsOnly (ρ := none) (by rw [Ctx.resolveAt?_none, hres]; simp)
            (fun Tel₁ h' => by rw [Ctx.resolveAt?_none, hres] at h'; simp at h') hB
      | pi S₀ T₀ =>
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inr ?_⟩))))))
          exact BndsTyped.bndsOnly (ρ := none) (by rw [Ctx.resolveAt?_none, hres]; simp)
            (fun Tel₁ h' => by rw [Ctx.resolveAt?_none, hres] at h'; simp at h') hB
      | box X =>
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inr ?_⟩))))))
          exact BndsTyped.bndsOnly (ρ := none) (by rw [Ctx.resolveAt?_none, hres]; simp)
            (fun Tel₁ h' => by rw [Ctx.resolveAt?_none, hres] at h'; simp at h') hB

/-- No closed evidence for `⊤ ≤ ⊥`. -/
theorem Store.Typed.no_top_le_bot (hσ : ⊢ σ : Γ) :
    ¬ ∃ (e : LeCo s) (C C' : CaptureSet s), Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C' := by
  rintro ⟨e, C, C', h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ |
      ⟨Tel₁, i, T', F, hS, hAt, _⟩ | ⟨_, h, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · obtain rfl := Shape.obj.inj (by simpa using hS : (μ .nil : Shape s) = μ Tel₁)
    cases hAt
  · simp at h

/-- No closed evidence from an object type without bounds into a function
type. -/
theorem Store.Typed.no_obj_le_pi (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Dom s}
    {T : Cod s} (hnb : ∀ (i : Nat) (T' : Shape s), ¬ Tel ∋ (i ↦ ⊑ T'↑)) :
    ¬ ∃ (e : LeCo s) (C C' : CaptureSet s), Γ ⊢ e : (μ Tel) ^ C ≤ (Π(S) T) ^ C' := by
  rintro ⟨e, C, C', h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ |
      ⟨Tel₁, i, T', F, hS, hAt, _⟩ | ⟨_, h, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [Ty.shape_capt, Ctx.resolve_obj] at hS
    obtain rfl := Shape.obj.inj hS
    exact hnb i T' hAt
  · simp at h

/-- No closed evidence from a function type into an object type with a
proposition that is not a bound. -/
theorem Store.Typed.no_pi_le_obj (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Dom s}
    {T : Cod s} {i : Nat} {P : Proposition (s,x)} (hAt : Tel ∋ (i ↦ P))
    (hP : ∀ X : Shape (s,x), P ≠ Proposition.bnd X) :
    ¬ ∃ (e : LeCo s) (C C' : CaptureSet s), Γ ⊢ e : (Π(S) T) ^ C ≤ (μ Tel) ^ C' := by
  rintro ⟨e, C, C', h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h, _⟩ | ⟨_, h⟩ |
      ⟨_, _, _, _, h, _⟩ | ⟨Tel₂, hT, hd⟩
  · simp at h
  · rw [Ty.shape_capt, Ctx.resolve_obj] at h
    obtain rfl := Shape.obj.inj (by simpa using h : (μ Tel : Shape s) = μ .nil)
    cases hAt
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [Ty.shape_capt, Ctx.resolve_obj] at hT
    obtain rfl := Shape.obj.inj hT
    rcases hd with ⟨Tel₁, h₁⟩ | hbo
    · simp at h₁
    · obtain ⟨X, hX⟩ := hbo _ _ hAt
      exact hP X hX

/-! ## Consistency in the capture sort -/

/-- A rigid capture binder -- a root, or the platform's `∗` -- is its own
root: `caps` stops there at every fuel. -/
theorem Ctx.Root_cvar_rigid {Γ : Ctx s} {κ : BVar s .cap}
    (h : Γ.lookupCap κ = .root ∨ Γ.lookupCap κ = .star) :
    Γ.Root (.cvar κ) [CapAtom.cvar κ] := by
  refine ⟨0, ?_⟩
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_cons, Ctx.caps_nil, List.append_nil,
    Ctx.capsAtom_cvar]
  have hc : Γ.capsBound 0 κ (Γ.lookupCap κ) = [CapAtom.cvar κ] := by
    rcases h with h | h <;> rw [h] <;> simp [Ctx.capsBound]
  rw [hc]
  exact Ctx.mem_expand.mpr
    ⟨.cvar κ, List.mem_cons_self .., Γ.mem_expandAtom_self _ (Cls.Kind.contains_top _)⟩

/-- Consistency in the capture sort, at a platform binder `κ ⊑ᶜ ∗`: no closed
capture evidence puts `{κ}` below a set whose roots miss `κ`.  Bad capture
bounds stay expressible under a lambda (example C3); over a typed store they
prove nothing. -/
theorem Store.Typed.no_cap_escape (hσ : ⊢ σ : Γ) {κ : BVar s .cap}
    (hκ : Γ.lookupCap κ = .star) {D : CaptureSet s} (hD : ¬ Γ.Root (.cvar κ) D) :
    ¬ ∃ f : CapCo s, Γ ⊢ᶜ f : [CapAtom.cvar κ] ⊑ D := by
  rintro ⟨f, hf⟩
  exact hD (cap_canon hσ hf _ (Ctx.Root_cvar_rigid (Or.inr hκ)))

/-- In particular the platform's capability never sinks to the empty set. -/
theorem Store.Typed.no_cap_star_le_nil (hσ : ⊢ σ : Γ) {κ : BVar s .cap}
    (hκ : Γ.lookupCap κ = .star) :
    ¬ ∃ f : CapCo s, Γ ⊢ᶜ f : [CapAtom.cvar κ] ⊑ [] :=
  hσ.no_cap_escape hκ (by rintro ⟨n, hn⟩; simp at hn)

/-! ## Levels over a typed store

A store binds capabilities, never scopes, so a store context has no root
binder and every binder of it is at the outermost level.  On top of that the
level rule is sound in the strong sense: closed evidence never lowers the
level of what a capture set resolves to. -/

/-- A capture bound that is opaque resolves to its own binder at every
fuel. -/
theorem Ctx.caps_of_opaque {Γ : Ctx s} {κ : BVar s .cap}
    (hκ : (Γ.lookupCap κ).opaque = true) (n : Nat) :
    Γ.caps n [CapAtom.cvar κ] = [CapAtom.cvar κ] := by
  rw [Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_cvar]
  cases h : Γ.lookupCap κ with
  | root => rfl
  | star => rfl
  | upper C => rw [h] at hκ; simp [CapBound.opaque] at hκ
  | inst C => rw [h] at hκ; simp [CapBound.opaque] at hκ
  | cls c => rfl

/-! **T-B0.7**, `Store.Typed.rootFree`, is proved in `FCdot/Store.lean`,
beside the judgement it inducts on, because the four entering steps of the
machine consume it and `FCdot/Preservation.lean` comes before this file. -/

/-- **T13, consistency at the top.**  At run time every capability is at the
outermost level.  This is L0 read at `rootAtom = ⊤ᶜ`, which is what a
root-free context has.  `h` is not needed for the proof: on a root-free
context `⊤ᶜ` bounds every atom, `⊤ᶜ` included.  It is kept because it is the
form the statement was specified in. -/
theorem Store.Typed.confined (hσ : ⊢ σ : Γ) (C : CaptureSet s)
    (h : CapAtom.top ∉ C) : Γ.Confined C ⊤ᶜ := by
  have hr : Γ.rootAtom = ⊤ᶜ := by
    unfold Ctx.rootAtom
    rw [hσ.rootFree]
    rfl
  rw [← hr]
  exact Γ.confined_rootAtom C

/-- **T10, `lvl_canon`.**  Closed capture evidence never lowers the level: if
every resolution of the target is at or outside `r`, so is every resolution
of the source.  A corollary of item 6 over a typed store, not an induction on
the evidence: as an induction on `f` alone the `capvar` case is false, since
bad capture bounds are derivable under a lambda (example C3). -/
theorem lvl_canon (hσ : ⊢ σ : Γ) {f : CapCo s} {C₁ C₂ : CaptureSet s} {r : CapAtom s}
    (h : Γ ⊢ᶜ f : C₁ ⊑ C₂) (n : Nat)
    (h₂ : ∀ m, Γ.Confined (Γ.roots m C₂) r) : Γ.Confined (Γ.roots n C₁) r := by
  intro a ha
  obtain ⟨m, hm⟩ := cap_canon hσ h a ⟨n, ha⟩
  exact h₂ m a hm

/-- **T11, `rigid_canon`.**  A rigid binder is a root of every set closed
evidence puts it below. -/
theorem rigid_canon (hσ : ⊢ σ : Γ) {κ : BVar s .cap} {f : CapCo s} {C : CaptureSet s}
    (hκ : Γ.lookupCap κ = .star) (h : Γ ⊢ᶜ f : [CapAtom.cvar κ] ⊑ C) :
    Γ.Root (.cvar κ) C :=
  cap_canon hσ h _ (Ctx.Root_cvar_rigid (Or.inr hκ))

/-- **T11', `rigid_target`.**  Nothing else resolves below a rigid binder. -/
theorem rigid_target (hσ : ⊢ σ : Γ) {κ : BVar s .cap} {f : CapCo s} {C : CaptureSet s}
    (hκ : Γ.lookupCap κ = .star) (h : Γ ⊢ᶜ f : C ⊑ [CapAtom.cvar κ]) (n : Nat) :
    (Γ.roots n C).Subset [CapAtom.cvar κ] := by
  intro a ha
  obtain ⟨m, hm⟩ := cap_canon hσ h a ⟨n, ha⟩
  rw [Ctx.roots_eq_expand_caps,
    Ctx.caps_of_opaque (by rw [hκ]; rfl), Ctx.expand_cons, Ctx.expand_nil,
    List.append_nil, Ctx.expandAtom_of_not_root (by rw [Ctx.isRootB, hκ]; rfl) rfl] at hm
  exact hm

/-- **T12, scope safety.**  What closed evidence puts below a scope root
resolves to capabilities at or outside that root. -/
theorem lvl_safety (hσ : ⊢ σ : Γ) {r : CapAtom s} {f : CapCo s} {C : CaptureSet s}
    (hr : Γ.IsRoot r) (h : Γ ⊢ᶜ f : C ⊑ [r]) (n : Nat) :
    Γ.Confined (Γ.roots n C) r :=
  lvl_canon hσ h n (fun m => by
    rw [Ctx.roots_of_isRoot hr]
    intro c hc
    rcases Ctx.mem_expandAtom_root hr hc with rfl | ⟨κ, rfl, _, hκ⟩
    · exact Ctx.top_lvlLe _ _
    · exact hκ)

/-- **T12, the escape form.**  No closed derivation puts a capability
introduced strictly inside a scope below that scope's root.  The conclusion
is about what `C` resolves to and not about its syntactic atoms: a pure inner
binder is below every set by `capvar` and `elem`, so the syntactic reading is
false and the resolved reading is what holds. -/
theorem no_inner_escape (hσ : ⊢ σ : Γ) {r : CapAtom s} {κ : BVar s .cap}
    (hr : Γ.IsRoot r) (hκ : (Γ.lookupCap κ).opaque = true)
    (hout : ¬ Γ.LvlLe (.cvar κ) r) : ¬ ∃ f : CapCo s, Γ ⊢ᶜ f : [CapAtom.cvar κ] ⊑ [r] := by
  rintro ⟨f, hf⟩
  refine hout (lvl_safety hσ hr hf 0 (.cvar κ) ?_)
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_of_opaque hκ, Ctx.expand_cons, Ctx.expand_nil,
    List.append_nil]
  exact Ctx.mem_expandAtom_self_of_not_proj rfl

/-- Every block name of a store binder is defined by the stored literal's
witness, and the definition is closed equality evidence. -/
theorem Store.Typed.realized (hσ : ⊢ σ : Γ) (x : BVar s .var) (ℓ : Label) :
    ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W :=
  ⟨_, hσ.lookupDef x ℓ, .def (hσ.lookupDef x ℓ)⟩

end

/-- Along a run, states stay typed (at a renamed result type). -/
theorem Steps.typed {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (run : st ⟶* st') : ∃ U', State.Typed st' U' := by
  induction run with
  | refl => exact ⟨U, hT⟩
  | tail _ step ih =>
      obtain ⟨U', hT'⟩ := ih hT
      obtain ⟨ρ, hT''⟩ := preservation' hT' step
      exact ⟨_, hT''⟩

/-- Every store reachable from a typed state is typed, hence consistent: no
closed `⊤ ≤ ⊥` in its context, and every block name is defined. -/
theorem reachable_consistent {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (run : st ⟶* st') :
    ∃ Γ : Ctx s', ⊢ st'.σ : Γ ∧
      (¬ ∃ (e : LeCo s') (C C' : CaptureSet s'), Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C') ∧
      ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W := by
  obtain ⟨U', Γ, T, hσ, _, _⟩ := Steps.typed hT run
  exact ⟨Γ, hσ, hσ.no_top_le_bot, hσ.realized⟩

end FCdot

end Classifiers
