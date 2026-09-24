import Coercions.Captures.FCdot.Machine
import Coercions.Captures.FCdot.TypingSubst
import Coercions.Captures.FCdot.Transparency

namespace Captures

/-!
# Preservation for the FCdot store machine

Every step of a well-typed state yields a well-typed state; allocation
extends the signature, and the result type is transported along the
signature embedding (`Rename.succ` for `alloc`, the identity otherwise).
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
  | .cast v _, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]

theorem Value.fieldLabels_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).fieldLabels = v.fieldLabels
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .box _, _ => by simp [Value.rename, Value.fieldLabels]
  | .cast v _, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]

/-- Capture witnesses commute with renaming, as block witnesses do. -/
theorem Value.capWitnesses_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2),
      (v.rename ρ).capWitnesses = v.capWitnesses.rename ρ.lift
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.capWitnesses]
  | .box _, _ => by simp [Value.rename, Value.capWitnesses, CapWitnesses.rename]
  | .cast v _, ρ => by
      simp [Value.rename, Value.capWitnesses, Value.capWitnesses_rename v ρ]

theorem Value.core_witnesses {s : Sig} :
    ∀ v : Value s, v.core.witnesses = v.witnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.witnesses, Value.core_witnesses v]

theorem Value.core_capWitnesses {s : Sig} :
    ∀ v : Value s, v.core.capWitnesses = v.capWitnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.capWitnesses, Value.core_capWitnesses v]

theorem Value.core_fieldLabels {s : Sig} :
    ∀ v : Value s, v.core.fieldLabels = v.fieldLabels
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.fieldLabels, Value.core_fieldLabels v]

theorem Value.core_isLiteral {s : Sig} : ∀ v : Value s, v.core.IsLiteral
  | .lam _ _ _ _ => trivial
  | .obj _ _ _ _ => trivial
  | .box _ => trivial
  | .cast v _ => by simpa [Value.core] using Value.core_isLiteral v

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
  | consC _ ih =>
      intro x
      cases x with
      | there y => simpa [Store.lookup] using (ih y).weakenC _

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
  | consC _ ih =>
      intro x
      cases x with
      | there y =>
          simp only [Ctx.lookupFields_thereC, ih y, Store.lookup, Value.weaken,
            Value.fieldLabels_rename]

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
  | consC _ ih =>
      intro x l
      cases x with
      | there y =>
          simp only [Ctx.lookupDef_thereC, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.witnesses_rename, Witnesses.get_rename, Shape.substVar,
            Shape.weaken, Shape.rename_comp, Rename.succ_lift_comp_subst_there]

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
  | consC _ ih =>
      intro x l
      cases x with
      | there y =>
          simp only [Ctx.lookupDefC_thereC, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.capWitnesses_rename, CapWitnesses.get_rename,
            CaptureSet.substVar, CaptureSet.weaken, CaptureSet.rename_comp,
            Rename.succ_lift_comp_subst_there]

/-- The closure stored at a variable is typed at the variable's type. -/
theorem Store.Typed.lam_of_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)}
    (h : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) :
    Γ ⊢ᵥ .lam A S₀ t₀ g : Γ.lookupTy x :=
  hx ▸ h.lookup x

/-- The box stored at a variable is typed at the variable's type. -/
theorem Store.Typed.box_of_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {b : Atom s} (h : ⊢ σ : Γ) (hx : σ.lookup x = .box b) :
    Γ ⊢ᵥ .box b : Γ.lookupTy x :=
  hx ▸ h.lookup x

/-! ## Continuation weakening -/

theorem Cont.Typed.weaken {s : Sig} {Γ : Ctx s} {K : Cont s} {T U : Ty s}
    (h : Γ ⊢ₖ K : T ⇒ U) (b : Binding s) :
    (Γ.cons b) ⊢ₖ K↑ : T↑ ⇒ U↑ := by
  induction h with
  | nil => exact .nil
  | «let» hu hf _ ih =>
      refine Cont.Typed.let ?_ ?_ ih
      · have := hu.rename ((Ctx.Ren.succ b).lift (.opaque _))
        simpa [Ty.weaken_rename] using this
      · have := hf.rename ((Ctx.Ren.succ b).lift (.opaque _))
        rwa [CaptureSet.weaken_rename, ← Tm.uses_rename] at this
  | cast he _ ih =>
      exact Cont.Typed.cast (LeCo.HasType.weaken he b) ih

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
theorem Value.HasType.lam_inv {s : Sig} {Γ : Ctx s} {A : CaptureSet s} {S₀ : Ty s}
    {t₀ : Tm (s,x)} {g : CapCo (s,x)} {T : Ty s} (h : Γ ⊢ᵥ .lam A S₀ t₀ g : T) :
    ∃ T₀, T = (Π(S₀) T₀) ^ A ∧ (Γ.cons (.opaque S₀)) ⊢ t₀ : T₀ ∧
      (Γ.cons (.opaque S₀)) ⊢ᶜ g : t₀.uses ⊑ (A↑ ∪ [CapAtom.var .here]) := by
  cases h with
  | lam ht hg => exact ⟨_, rfl, ht, hg⟩

/-- Inversion of a boxed value: a box has the box shape of the boxed atom's
type, with the empty capture set. -/
theorem Value.HasType.box_inv {s : Sig} {Γ : Ctx s} {b : Atom s} {T : Ty s}
    (h : Γ ⊢ᵥ .box b : T) : ∃ X, T = (□ X) ^ [] ∧ Γ ⊢ₐ b : X := by
  cases h with
  | box hb => exact ⟨_, rfl, hb⟩

/-- Inversion of an object literal.  The type is the precise object type at
the literal's own annotation `A`, and the fields are typed against that same
`A`, which is the index of the fields judgement of A2.2. -/
theorem Value.HasType.obj_inv {s : Sig} {Γ : Ctx s} {A : CaptureSet s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields (s,x)} {T : Ty s}
    (h : Γ ⊢ᵥ .obj A W Wc F : T) :
    T = (μ (Telescope.ofLiteral W Wc F.labels)) ^ A ∧
      Fields.HasType
        (Γ.cons (.transparent ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc F.labels))
        A F := by
  cases h with
  | obj hF => exact ⟨rfl, hF⟩

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

/-! ## The two substitution instances the machine uses -/

@[simp] theorem Subst.selfCast_root {s : Sig} (E : LeCo (s,x)) :
    (Subst.selfCast E).root = Rename.id := by
  apply Rename.funext'
  intro k x
  cases k <;> cases x <;> rfl

theorem Subst.Typed.selfCast {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label} (hE : Γ ⊢ E : S₀ ≤ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E↑)
      (Γ.cons (.transparent S₀ W Wc Fs)) where
  var := by
    intro y
    cases y with
    | here =>
        show (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .cast (.var .here) E↑ :
          ((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E↑).root
        have hE' : (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ E↑ : S₀↑ ≤ T↑ :=
          hE.weaken _
        have hvar : (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .var .here : S₀↑ := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Wc Fs)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ₐ .var (.there z) :
          ((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E↑).root
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

/-- The self binder of a stored object literal may be replaced by the
variable it is stored at. -/
theorem Ctx.Ren.selfObj {s : Sig} {Γ : Ctx s} {Tel : Telescope (s,x)} {C : CaptureSet s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label} {y : BVar s .var}
    (hty : Γ.lookupTy y = (μ Tel) ^ C)
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧))
    (hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧))
    (hfields : Γ.lookupFields y = some Fs) :
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

/-! ## Preservation -/

/-- Typedness of the head form used by the application and unboxing steps:
whenever the head form of a function atom's casts is `pi d c`, `d` and `c`
are typed between the atom's function type and its closure's type; whenever
it is the identity form, the two function types coincide; and the same two
sentences for a box atom, whose head form is `boxed d` or the identity.
Discharged by the canonical-forms theorem (`CanonicalForms.lean`). -/
structure FormsTyped (σ : Store s) (Γ : Ctx s) : Prop where
  pi : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {C : CaptureSet s} {n : Nat} {a' : Atom s}
    {d : LeCo s} {c : LeCo (s,x)} {S₀ : Ty s} {T₀ : Ty (s,x)},
    Γ ⊢ₐ a : (Π(S) T) ^ C → σ ⊢ a ⇓ᶜ[n] (a', .pi d c) →
    (Γ.lookupTy a.root).shape = Π(S₀) T₀ →
    Γ ⊢ d : S ≤ S₀ ∧ (Γ.cons (.opaque S)) ⊢ c : T₀ ≤ T
  refl : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {C : CaptureSet s} {n : Nat} {a' : Atom s}
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

/-- A step that does not allocate keeps the signature: the result type is
transported along the identity renaming. -/
theorem State.Typed.exists_rename_id {s : Sig} {st : State s} {U : Ty s}
    (h : State.Typed st U) : ∃ ρ : Rename s s, State.Typed st (U.rename ρ) :=
  ⟨Rename.id, by simpa using h⟩

/-- `alloc`: the stripped literal is stored at its own type, and the
continuation body is adjusted to use the new variable under the composite of
the stripped casts. -/
theorem preservation_alloc {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)} {v : Value s} {T U : Ty s}
    (hσ : ⊢ σ : Γ) (hv : Γ ⊢ᵥ v : T) (hK : Γ ⊢ₖ K ▹ .let u U' f : T ⇒ U) :
    State.Typed ⟨.cons σ v.core, K↑, u.adjust v⟩ U↑ := by
  cases hK with
  | «let» hu _ hK' =>
      obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v T hv
      refine ⟨_, _, Store.Typed.cons hσ hlit hcore, ?_, Cont.Typed.weaken hK' _⟩
      rcases hd with ⟨hn, rfl⟩ | ⟨E, hE?, hE⟩
      · rw [show u.adjust v = u by simp [Tm.adjust, hn]]
        exact hu.refine Ctx.Refines.transparent
      · rw [show u.adjust v = u.subst (Subst.selfCast E↑) by simp [Tm.adjust, hE?]]
        simpa using hu.subst (Subst.Typed.selfCast (W := v.core.witnesses)
          (Fs := v.core.fieldLabels) hE)

/-- The avoidance evidence of a let, transported into the transparent context
of the freshly allocated literal by the very substitution that `Tm.adjust`
applies to the body.  The value carried casts, whose composite is `E`.  The
use set on the left is that of the adjusted body, so `cap_canon` reads this
as `CapLe` between the adjusted body's use set and the declared set.  This is
what `step_uses` needs at `alloc`. -/
theorem CapCo.HasType.adjust {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s} {v : Value s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)}
    (hE? : v.composite? = some E) (hE : Γ ⊢ E : S₀ ≤ T)
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑) :
    (Γ.cons (.transparent S₀ W Wc Fs)) ⊢ᶜ f.subst (Subst.selfCast E↑)
      : (u.adjust v).uses ⊑ U'↑ := by
  rw [show u.adjust v = u.subst (Subst.selfCast E↑) by simp [Tm.adjust, hE?]]
  simpa [Tm.uses_subst] using
    hf.subst (Subst.Typed.selfCast (W := W) (Wc := Wc) (Fs := Fs) hE)

/-- The same when the value carried no cast: `Tm.adjust` is the identity and
only the context is refined. -/
theorem CapCo.HasType.adjust_none {s : Sig} {Γ : Ctx s} {T : Ty s} {v : Value s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label}
    {u : Tm (s,x)} {U' : CaptureSet s} {f : CapCo (s,x)}
    (hn : v.composite? = none)
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑) :
    (Γ.cons (.transparent T W Wc Fs)) ⊢ᶜ f : (u.adjust v).uses ⊑ U'↑ := by
  rw [show u.adjust v = u by simp [Tm.adjust, hn]]
  exact hf.refine Ctx.Refines.transparent

/-- β: a closure applied at its own function type. -/
theorem Value.HasType.beta {s : Sig} {Γ : Ctx s} {A : CaptureSet s} {S₀ S : Ty s}
    {t₀ : Tm (s,x)} {g : CapCo (s,x)} {T : Ty (s,x)} {C : CaptureSet s} {b : Atom s}
    (hlam : Γ ⊢ᵥ .lam A S₀ t₀ g : (Π(S) T) ^ C) (hb : Γ ⊢ₐ b : S) :
    Γ ⊢ t₀.substAtom b : T⟦b.root⟧ := by
  obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv hlam
  obtain ⟨-, rfl, rfl⟩ : C = A ∧ S = S₀ ∧ T = T₀ := by
    simpa [Ty.capt.injEq, Shape.pi.injEq] using hTe
  exact Tm.HasType.substAtom ht₀ hb

/-- β for a closure stored at the root of an atom whose type is that root's
type: `appVar`, and `appCastRefl` where the casts normalize to the identity. -/
theorem Store.Typed.beta {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ S : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)} {T : Ty (s,x)}
    {C : CaptureSet s} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) (hty : Γ.lookupTy x = (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S) : Γ ⊢ t₀.substAtom b : T⟦b.root⟧ :=
  (hty ▸ hσ.lam_of_lookup hx).beta hb

/-- The body and the closing evidence of a stored closure, read in the
current context at the parameter binder.  This is the ingredient `step_uses`
needs at `appVar`, `appCastRefl` and `appCast`: substituting the argument
into `g` bounds the use set of the body by the closure's annotation united
with the argument. -/
theorem Store.Typed.lam_closing {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) :
    ∃ T₀, Γ.lookupTy x = (Π(S₀) T₀) ^ A ∧ (Γ.cons (.opaque S₀)) ⊢ t₀ : T₀ ∧
      (Γ.cons (.opaque S₀)) ⊢ᶜ g : t₀.uses ⊑ (A↑ ∪ [CapAtom.var .here]) :=
  Value.HasType.lam_inv (hσ.lam_of_lookup hx)

/-- β through a function coercion `pi d c`: the argument is cast by `d` and
the result by `c` at the argument. -/
theorem Tm.HasType.betaCast {s : Sig} {Γ : Ctx s} {S₀ S : Ty s} {t₀ : Tm (s,x)}
    {T₀ T : Ty (s,x)} {d : LeCo s} {c : LeCo (s,x)} {b : Atom s}
    (ht₀ : (Γ.cons (.opaque S₀)) ⊢ t₀ : T₀) (hdom : Γ ⊢ d : S ≤ S₀)
    (hcod : (Γ.cons (.opaque S)) ⊢ c : T₀ ≤ T) (hb : Γ ⊢ₐ b : S) :
    Γ ⊢ .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b)) : T⟦b.root⟧ := by
  have hcod' := hcod.subst (Subst.Typed.single hb)
  rw [Subst.single_root] at hcod'
  refine Tm.HasType.cast ?_ hcod'
  simpa [Atom.root] using Tm.HasType.substAtom ht₀ (Atom.HasType.cast hb hdom)

/-- The content of a stored box: its type is the box of the boxed atom's
type, so the atom is typed at the boxed type of the variable's shape. -/
theorem Store.Typed.boxContent {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {b : Atom s} (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .box b) :
    ∃ X, (Γ.lookupTy x).shape = □ X ∧ Γ ⊢ₐ b : X := by
  obtain ⟨X, hE, hb⟩ := Value.HasType.box_inv (hσ.box_of_lookup hx)
  exact ⟨X, by rw [hE]; rfl, hb⟩

/-- Projecting a field of a stored object literal, in full: the field's body
with the self binder replaced by the object's variable has the projection's
type, the object's type is the precise object type at its own annotation, and
the field's closing evidence, read at the same variable, puts the body's use
set below that annotation united with the variable.  `Tm.HasType.projField`
below is the first component, the one preservation uses; `step_uses` reads
the third at the `proj` step. -/
theorem Tm.HasType.projFieldFull {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields (s,x)}
    {ℓ : Label} {t : Tm (s,x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    (Γ ⊢ t.selfAt y : (y ∙ ℓ) ^ [CapAtom.name y ℓ]) ∧
      Γ.lookupTy y = (μ (Telescope.ofLiteral W Wc F.labels)) ^ A ∧
      ∃ g', Γ ⊢ᶜ g' : (t.selfAt y).uses ⊑ (A ∪ [CapAtom.var y]) := by
  have hval := hσ.lookup y
  rw [hx] at hval
  obtain ⟨hTe, hF⟩ := Value.HasType.obj_inv hval
  have hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧) := by
    intro l
    have hlk := hσ.lookupDef y l
    rw [hx] at hlk
    simpa [Value.witnesses] using hlk
  have hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧) := by
    intro l
    have hlk := hσ.lookupDefC y l
    rw [hx] at hlk
    simpa [Value.capWitnesses] using hlk
  have hfields : Γ.lookupFields y = some F.labels := by
    have hlk := hσ.lookupFields y
    rw [hx] at hlk
    simpa [Value.fieldLabels] using hlk
  have hren := Ctx.Ren.selfObj hTe hdef hdefC hfields
  obtain ⟨ht, ⟨g', hg'⟩⟩ := Fields.HasType.getFull F hF ℓ t hg
  refine ⟨?_, hTe, ⟨g'.rename (Rename.subst y), ?_⟩⟩
  · simpa [Tm.selfAt, Ty.rename, Shape.rename, CaptureSet.rename, CapAtom.rename] using
      ht.rename hren
  · have h := hg'.rename hren
    rw [CaptureSet.rename_union, CaptureSet.rename_subst_weaken', ← Tm.uses_rename] at h
    exact h

/-- Projecting a field of a stored object literal: the field's body, with the
self binder replaced by the object's variable, has the projection's type. -/
theorem Tm.HasType.projField {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields (s,x)}
    {ℓ : Label} {t : Tm (s,x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    Γ ⊢ t.selfAt y : (y ∙ ℓ) ^ [CapAtom.name y ℓ] :=
  (Tm.HasType.projFieldFull hσ hx hg).1

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
  | «let» ht hu hf => exact ⟨_, ht, hu, hf⟩

/-- `castPush`: the body of a cast is typed at the type the cast frame
accepts. -/
theorem Tm.HasType.cast_inv {s : Sig} {Γ : Ctx s} {t : Tm s} {e : LeCo s} {U : Ty s}
    (h : Γ ⊢ .cast t e : U) : ∃ T, Γ ⊢ t : T ∧ Γ ⊢ e : T ≤ U := by
  cases h with
  | cast ht he => exact ⟨_, ht, he⟩

/-- `rename`: the body of a let frame, instantiated at the atom the state
carries, is typed at the frame's result type. -/
theorem Tm.HasType.letBody_substAtom {s : Sig} {Γ : Ctx s} {T U : Ty s} {u : Tm (s,x)}
    {a : Atom s} (hu : (Γ.cons (.opaque T)) ⊢ u : U↑) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ u.substAtom a : U := by
  simpa using hu.substAtom ha

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

theorem preservation {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hF : ∀ Γ, ⊢ st.σ : Γ → FormsTyped st.σ Γ)
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) := by
  cases step <;> obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
  case «let» =>
      cases ht with
      | «let» ht' hu hf => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .let hu hf hK⟩
  case castPush =>
      cases ht with
      | cast ht' he => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .cast he hK⟩
  case castVal =>
      cases ht with
      | val hv =>
          cases hK with
          | cast he hK' => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, .val (.cast hv he), hK'⟩
  case castAtom =>
      cases ht with
      | atom ha =>
          cases hK with
          | cast he hK' => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, .atom (.cast ha he), hK'⟩
  case alloc =>
      cases ht with
      | val hv => exact ⟨Rename.succ, preservation_alloc hσ hv hK⟩
  case rename =>
      cases ht with
      | atom ha =>
          cases hK with
          | «let» hu _ hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, Tm.HasType.letBody_substAtom hu ha, hK'⟩
  case appVar hx =>
      cases ht with
      | app ha hb =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, hσ.beta hx (Atom.HasType.var_inv ha).symm hb, hK⟩
  case appCastRefl hx _ hcf hid =>
      cases ht with
      | app ha hb =>
          obtain ⟨C₀, hty⟩ := Ty.shape_eq_iff.mp ((hF Γ hσ).refl ha hcf hid)
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, hσ.beta hx hty hb, hK⟩
  case appCast hx _ hcf =>
      cases ht with
      | app ha hb =>
          obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv (hσ.lam_of_lookup hx)
          obtain ⟨hdom, hcod⟩ := (hF Γ hσ).pi ha hcf (by rw [hTe]; rfl)
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht₀.betaCast hdom hcod hb, hK⟩
  case proj hx hg =>
      cases ht with
      | proj _ _ => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, Tm.HasType.projField hσ hx hg, hK⟩
  case unboxRefl hx hcf hid =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (hσ.unboxRefl_result (hF Γ hσ) hx ha hcf hid), hK⟩
  case unboxCast hx hcf =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (hσ.unboxCast_result (hF Γ hσ) hx ha hcf), hK⟩

end FCdot

end Captures
