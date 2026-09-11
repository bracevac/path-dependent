import Coercions.Classifiers.FCdot.Machine
import Coercions.Classifiers.FCdot.TypingSubst
import Coercions.Classifiers.FCdot.Transparency

namespace Classifiers

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
  | .pack _ _ _ v, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]

theorem Value.fieldLabels_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).fieldLabels = v.fieldLabels
  | .lam _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .obj _ _ _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .box _, _ => by simp [Value.rename, Value.fieldLabels]
  | .cast v _, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]
  | .pack _ _ _ v, ρ => by
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
  | .pack _ _ _ v, ρ => by
      simp [Value.rename, Value.capWitnesses, Value.capWitnesses_rename v ρ]

theorem Value.core_witnesses {s : Sig} :
    ∀ v : Value s, v.core.witnesses = v.witnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.witnesses, Value.core_witnesses v]
  | .pack _ _ _ _ => rfl

theorem Value.core_capWitnesses {s : Sig} :
    ∀ v : Value s, v.core.capWitnesses = v.capWitnesses
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.capWitnesses, Value.core_capWitnesses v]
  | .pack _ _ _ _ => rfl

theorem Value.core_fieldLabels {s : Sig} :
    ∀ v : Value s, v.core.fieldLabels = v.fieldLabels
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => by simp [Value.core, Value.fieldLabels, Value.core_fieldLabels v]
  | .pack _ _ _ _ => rfl

theorem Value.core_isLiteral {s : Sig} : ∀ v : Value s, v.core.IsLiteral
  | .lam _ _ _ _ => trivial
  | .obj _ _ _ _ => trivial
  | .box _ => trivial
  | .cast v _ => by simpa [Value.core] using Value.core_isLiteral v
  -- `Value.IsLiteral` gains no clause, so a pack falls into its catch-all and
  -- `core` is the identity on it.  A packed value is kept out of a store by
  -- `Store.Typed.cons`, which premises `Value.HasType`, and that has no pack rule.
  | .pack _ _ _ _ => trivial

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
  | consC _ hb ih =>
      intro x
      cases x with
      | there y => simpa [Store.lookup] using (ih y).weakenC _ hb

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
  | consC _ _ ih =>
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
  | consC _ _ ih =>
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
  | consC _ _ ih =>
      intro x l
      cases x with
      | there y =>
          simp only [Ctx.lookupDefC_thereC, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.capWitnesses_rename, CapWitnesses.get_rename,
            CaptureSet.substVar, CaptureSet.weaken, CaptureSet.rename_comp,
            Rename.succ_lift_comp_subst_there]

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

/-! ## Continuation weakening -/

theorem Cont.Typed.weaken {s : Sig} {Γ : Ctx s} {K : Cont s} {E : ETy s} {U : Ty s}
    (h : Γ ⊢ₖ K : E ⇒ U) (b : Binding s) :
    (Γ.cons b) ⊢ₖ K↑ : E↑ ⇒ U↑ := by
  induction h with
  | nil => exact .nil
  | «let» hu hf _ ih =>
      refine Cont.Typed.let ?_ ?_ ih
      · have := hu.rename ((Ctx.Ren.succ b).lift (.opaque _))
        simpa [ETy.weaken_rename] using this
      · have := hf.rename ((Ctx.Ren.succ b).lift (.opaque _))
        rwa [CaptureSet.weaken_rename, ← Tm.uses_rename] at this
  | cast he _ ih =>
      exact Cont.Typed.cast (LeCo.HasType.weaken he b) ih
  | castE hg _ ih =>
      exact Cont.Typed.castE (ELeCo.HasType.rename (Ctx.Ren.succ b) hg) ih
  | letex hh hu hf _ ih =>
      refine Cont.Typed.letex (CapCo.HasType.weaken hh b) ?_ ?_ ih
      · have hu' := hu.rename (((Ctx.Ren.succ b).liftC CapBound.star).lift _)
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · have hf' := CapCo.HasType.rename (((Ctx.Ren.succ b).liftC CapBound.star).lift _) hf
        rw [CaptureSet.letexCharge_rename] at hf'
        simpa only [Tm.uses_rename] using hf'

/-- The capture-kind twin of `Cont.Typed.weaken`.  Its premise is B0.5's, and
`.inst C`, the bound the unpack appends, satisfies it. -/
theorem Cont.Typed.weakenC {s : Sig} {Γ : Ctx s} {K : Cont s} {E : ETy s} {U : Ty s}
    (h : Γ ⊢ₖ K : E ⇒ U) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ₖ K.weakenC : ETy.weaken (k := .cap) E ⇒ Ty.weaken (k := .cap) U := by
  induction h with
  | nil => exact .nil
  | «let» hu hf _ ih =>
      refine Cont.Typed.let ?_ ?_ ih
      · have := hu.rename ((Ctx.Ren.succC b hb).lift (.opaque _))
        simpa [ETy.weaken_rename] using this
      · have := hf.rename ((Ctx.Ren.succC b hb).lift (.opaque _))
        rwa [CaptureSet.weaken_rename, ← Tm.uses_rename] at this
  | cast he _ ih =>
      exact Cont.Typed.cast (LeCo.HasType.weakenC he b hb) ih
  | castE hg _ ih =>
      exact Cont.Typed.castE (ELeCo.HasType.rename (Ctx.Ren.succC b hb) hg) ih
  | letex hh hu hf _ ih =>
      refine Cont.Typed.letex (CapCo.HasType.weakenC hh b hb) ?_ ?_ ih
      · have hu' := hu.rename (((Ctx.Ren.succC b hb).liftC CapBound.star).lift _)
        rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
        exact hu'
      · have hf' := CapCo.HasType.rename (((Ctx.Ren.succC b hb).liftC CapBound.star).lift _) hf
        rw [CaptureSet.letexCharge_rename] at hf'
        simpa only [Tm.uses_rename] using hf'

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

/-! ## The two substitution instances the machine uses

The equations of `Subst.selfCast` and the facts that say a term binding is
invisible to the capture spine moved to `TypingSubst.lean`, so that
`FormAlgebra.lean`, which reads them and nothing else of the machine, can
import `TypingSubst` rather than this module. -/

theorem Subst.Typed.selfCast {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {Fs : List Label} (hE : Γ ⊢ E : S₀ ≤ T) :
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
  capInst := by
    intro a C h
    simp only [CapAtom.subst_selfCast, CaptureSet.subst_selfCast]
    exact (Ctx.instOf_cons_eq Γ (.opaque T) (.transparent S₀ W Wc Fs) a C).mp h

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
    | proj e₀ φ => exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)
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

/-! ## The answer sort: isolation, canonical forms, and applying a coercion

**T8, isolation.**  Store free, no fuel, no context predicate.  An existential
answer cannot be widened to a plain one, which is the target's form of "a
result `fresh` cannot flow into a local `any`". -/

/-- Whether an answer is an existential. -/
def ETy.isEx : ETy s → Bool
  | .ex _ _ => true
  | .ty _ => false

@[simp] theorem ETy.isEx_ty (T : Ty s) : (ETy.ty T).isEx = false := rfl
@[simp] theorem ETy.isEx_ex (C : CaptureSet s) (T : Ty (s,c)) : (ETy.ex C T).isEx = true := rfl

/-- **T8.**  An existential stays an existential along answer inclusion. -/
theorem ex_stays_ex {s : Sig} {Γ : Ctx s} :
    ∀ (g : ELeCo s) {E₁ E₂ : ETy s}, Γ ⊢ᵉ g : E₁ ≤ E₂ → E₁.isEx = true → E₂.isEx = true
  | .plain _, _, _, h => by cases h with | plain _ => intro he; exact absurd he (by simp)
  | .pack _ _ _, _, _, h => by cases h with | pack _ _ => intro _; rfl
  | .cong _ _, _, _, h => by cases h with | cong _ _ => intro _; rfl
  | .trans g₁ g₂, _, _, h => by
      cases h with
      | trans h₁ h₂ => intro he; exact ex_stays_ex g₂ h₂ (ex_stays_ex g₁ h₁ he)

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
    {f : LeCo (Sig.scope s)} {X Y : Ty (Sig.scope s)}
    (h : Γ.scope ⊢ f : X ≤ Y) : Γ.scopeInst C ⊢ f : X ≤ Y := by
  have := h.rename (Ctx.Ren.instC (Γ := Γ.consC .root) (C := CaptureSet.weaken (k := .cap) C))
  rwa [LeCo.rename_id, Ty.rename_id, Ty.rename_id] at this

/-- **T-B2.3.**  A typed answer coercion applies to a typed value wrapper. -/
theorem Value.HasTypeE.applyE {s : Sig} {Γ : Ctx s} :
    ∀ (g : ELeCo s) {v : Value s} {E E' : ETy s},
      Γ ⊢ᵥᵉ v : E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ᵥᵉ v.applyE g : E'
  | .plain _, _, _, _, hv, hg => by
      cases hg with | plain he => exact .plain ((hv.ty_inv).cast he)
  | .pack _ _ _, _, _, _, hv, hg => by
      cases hg with | pack hh he => exact .pack hv.ty_inv hh he
  | .cong _ _, _, _, _, hv, hg => by
      cases hg with
      | cong hh hf =>
          obtain ⟨C, h₀, e, v₀, S, rfl, hv₀, hb, he⟩ := pack_canon_val hv
          exact .pack hv₀ (.trans hb hh) (he.trans (LeCo.HasType.atScopeInst hf))
  | .trans g₁ g₂, _, _, _, hv, hg => by
      cases hg with
      | trans h₁ h₂ =>
          exact Value.HasTypeE.applyE g₂ (Value.HasTypeE.applyE g₁ hv h₁) h₂

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
      | pack hh he =>
          obtain ⟨a, rfl, ha⟩ := hp.ty_inv
          exact .pack ha hh he
  | .cong _ _, _, _, _, hp, hg => by
      cases hg with
      | cong hh hf =>
          obtain ⟨C, h₀, e, a, S, rfl, ha, hb, he⟩ := pack_canon hp
          exact .pack ha (.trans hb hh) (he.trans (LeCo.HasType.atScopeInst hf))
  | .trans g₁ g₂, p, _, _, hp, hg => by
      cases hg with
      | trans h₁ h₂ =>
          rw [PAtom.applyE_trans]
          exact PAtom.HasType.applyE g₂ (PAtom.HasType.applyE g₁ hp h₁) h₂

/-! ## Preservation -/

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
    (hσ : ⊢ σ : Γ) (hv : Γ ⊢ᵥ v : T) (hK : Γ ⊢ₖ K ▹ .let u U' f : .ty T ⇒ U) :
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

/-- β: a closure applied at its own function type.  The step enters the body
by one substitution, which instantiates the parameter at the argument, the
arrow's capture binder at the argument's root and the body root at the
universal root, and the last of the three is what asks the context to bind no
root of its own (B1.5, discharged at the machine by `Store.Typed.rootFree`). -/
theorem Value.HasType.beta {s : Sig} {Γ : Ctx s} {A : CaptureSet s} {S₀ S : Dom s}
    {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)} {T : Cod s} {C : CaptureSet s}
    {b : Atom s} (hΓ : Γ.root? = none)
    (hlam : Γ ⊢ᵥ .lam A S₀ t₀ g : (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root))) :
    Γ ⊢ t₀.subst (Subst.enter b) :ᵉ T.subst (Subst.arg b) := by
  obtain ⟨T₀, hTe, ht₀, -⟩ := Value.HasType.lam_inv hlam
  obtain ⟨-, rfl, rfl⟩ : C = A ∧ S = S₀ ∧ T = T₀ := by
    simpa [Ty.capt.injEq, Shape.pi.injEq] using hTe
  have h := ht₀.subst (Subst.Typed.enter hΓ hb)
  rwa [Cod.underRoot_enter] at h

/-- β for a closure stored at the root of an atom whose type is that root's
type: `appVar`, and `appCastRefl` where the casts normalize to the identity. -/
theorem Store.Typed.beta {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {A : CaptureSet s} {S₀ S : Dom s} {t₀ : Tm (Sig.body s)} {g : CapCo (Sig.body s)}
    {T : Cod s} {C : CaptureSet s} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam A S₀ t₀ g) (hty : Γ.lookupTy x = (Π(S) T) ^ C)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root))) :
    Γ ⊢ t₀.subst (Subst.enter b) :ᵉ T.subst (Subst.arg b) :=
  (hty ▸ hσ.lam_of_lookup hx).beta hσ.rootFree hb

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
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root))) :
    Γ ⊢ₐ .cast b (d.subst (Subst.enterC b))
      : S₀.subst (Subst.singleC (.var (Atom.cast b (d.subst (Subst.enterC b))).root)) := by
  have hdom' := hdom.subst (Subst.Typed.enterC (b := b) hΓ)
  rw [Dom.underRoot_enterC, Dom.underRoot_enterC] at hdom'
  exact Atom.HasType.cast hb hdom'

/-- β through a function coercion `pi d c`: the argument is cast by the
domain evidence read at the argument's root, and the result by the codomain
evidence read at the argument. -/
theorem Tm.HasType.betaCast {s : Sig} {Γ : Ctx s} {S₀ S : Dom s} {t₀ : Tm (Sig.body s)}
    {T₀ T : Cod s} {d : LeCo (Sig.scope s)} {c : ELeCo (Sig.body s)} {b : Atom s}
    (hΓ : Γ.root? = none)
    (ht₀ : (Γ.body S₀) ⊢ t₀ :ᵉ T₀.underRoot)
    (hdom : Γ.scope ⊢ d : S.underRoot ≤ S₀.underRoot)
    (hcod : (Γ.body S) ⊢ᵉ c : T₀.underRoot ≤ T.underRoot)
    (hb : Γ ⊢ₐ b : S.subst (Subst.singleC (.var b.root))) :
    Γ ⊢ .castE (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
        (c.subst (Subst.enter b)) :ᵉ T.subst (Subst.arg b) := by
  -- the domain evidence, instantiated at the argument's root
  have hb' := Atom.HasType.castDom hΓ hdom hb
  have hcod' := ELeCo.HasType.subst (Subst.Typed.enter hΓ hb) hcod
  rw [Cod.underRoot_enter, Cod.underRoot_enter] at hcod'
  refine Tm.HasType.castE ?_ hcod'
  have h := ht₀.subst (Subst.Typed.enter hΓ hb')
  rw [Cod.underRoot_enter, Ty.arg_congr T₀ (a := .cast b (d.subst (Subst.enterC b)))
    (a' := b) rfl] at h
  exact h

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
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields ((s,c),x)}
    {ℓ : Label} {t : Tm ((s,c),x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    (Γ ⊢ t.subst (Subst.enterObj y) : (y ∙ ℓ) ^ [CapAtom.name y ℓ]) ∧
      Γ.lookupTy y = (μ (Telescope.ofLiteral W Wc F.labels)) ^ A ∧
      ∃ g', Γ ⊢ᶜ g' : (t.subst (Subst.enterObj y)).uses ⊑ (A ∪ [CapAtom.var y]) := by
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
  have hsub := Subst.Typed.enterObj (W := W) (Wc := Wc) (ls := F.labels)
    hσ.rootFree hTe hdef hdefC hfields
  obtain ⟨ht, ⟨g', hg'⟩⟩ := Fields.HasType.getFull F hF ℓ t hg
  refine ⟨?_, hTe, ⟨g'.subst (Subst.enterObj y), ?_⟩⟩
  · simpa [Ty.subst, Shape.subst, CaptureSet.subst, CapAtom.subst, Subst.rootVar,
      Subst.enterObj, Atom.root] using ht.subst hsub
  · have h := hg'.subst hsub
    rw [CaptureSet.subst_union, CaptureSet.weaken2_subst_enterObj, ← Tm.uses_subst] at h
    simpa [CaptureSet.subst, CapAtom.subst, Subst.rootVar, Subst.enterObj, Atom.root] using h

/-- Projecting a field of a stored object literal: the field's body, with the
self binder replaced by the object's variable, has the projection's type. -/
theorem Tm.HasType.projField {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {A : CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)} {F : Fields ((s,c),x)}
    {ℓ : Label} {t : Tm ((s,c),x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj A W Wc F) (hg : F.get? ℓ = some t) :
    Γ ⊢ t.subst (Subst.enterObj y) : (y ∙ ℓ) ^ [CapAtom.name y ℓ] :=
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

/-- `Tm.HasType.substAtom` at the answer sort. -/
theorem Tm.HasType.substAtomE {s : Sig} {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)} {E : ETy (s,x)}
    {a : Atom s} (hu : (Γ.cons (.opaque T)) ⊢ u :ᵉ E) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ u.substAtom a :ᵉ (E⟦a.root⟧) := by
  have := hu.subst (Subst.Typed.single ha)
  simpa [Tm.substAtom] using this

/-- `Tm.HasType.letBody_substAtom` at the answer sort: what `rename` and
`unpackAtom` produce. -/
theorem Tm.HasType.letBody_substAtomE {s : Sig} {Γ : Ctx s} {T : Ty s} {E : ETy s}
    {u : Tm (s,x)} {a : Atom s}
    (hu : (Γ.cons (.opaque T)) ⊢ u :ᵉ E↑) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ u.substAtom a :ᵉ E := by
  have := Tm.HasType.substAtomE hu ha
  rwa [ETy.weaken_substVar] at this

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

/-! ## The two unpack steps

The eight steps of B2.12, packaged as two lemmas.  Both extend the store by
the witness as an instance binder, read the wrapper's payload in the extended
scope under the residual coercion collapsed by `Subst.instRoot`, transport the
frame's body along `Ctx.Ren.instC`, and weaken the continuation by
`Cont.Typed.weakenC`.  Neither reads a form and neither takes fuel. -/

/-- The frame's body, read in the store's `.inst C` context.  This is
`Ctx.Ren.instC` lifted by the payload binder, at the identity renaming. -/
theorem Tm.HasType.letexBody_instC {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T : Dom s}
    {u : Tm ((s,c),x)} {E : ETy s}
    (hu : ((Γ.consC .star).cons (.opaque T)) ⊢ u :ᵉ
      (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E))) :
    ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ u :ᵉ
      (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) := by
  have h := hu.rename ((Ctx.Ren.instC (Γ := Γ) (C := C)).lift (.opaque T))
  simpa [Binding.rename, Rename.lift_id] using h

/-- The frame's avoidance evidence, read in the store's `.inst C` context. -/
theorem CapCo.HasType.letexCharge_instC {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T : Dom s}
    {u : Tm ((s,c),x)} {f : CapCo ((s,c),x)} {U' : CaptureSet s}
    (hf : ((Γ.consC .star).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)])) :
    ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)]) := by
  have h := CapCo.HasType.rename ((Ctx.Ren.instC (Γ := Γ) (C := C)).lift (.opaque T)) hf
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
  exact (hv.weakenC (.inst C) rfl).cast he'

/-- `unpackAtom`: the store gains the witness as an instance binder, the
continuation is weakened into the new scope, and the body is instantiated at
the wrapper's atom read there. -/
theorem preservation_unpackAtom {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {h : CapCo s} {f : CapCo ((s,c),x)}
    {C C₀ : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {a : Atom s}
    {T : Dom s} {U : Ty s}
    (hσ : ⊢ σ : Γ) (hp : Γ ⊢ₚ .pack C h₀ e a : ∃ᶜ[C₀] T)
    (hK : Γ ⊢ₖ K ▹ .letex u U' h f : ∃ᶜ[C₀] T ⇒ U) :
    State.Typed ⟨σ.consC (.inst C), K.weakenC,
        u.substAtom (.cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot))⟩
      (Ty.weaken (k := .cap) U) := by
  cases hK with
  | letex hh hu hf hK' =>
      cases hp with
      | pack ha hb he =>
          refine ⟨Γ.consC (.inst C), _, hσ.consC rfl, ?_,
            Cont.Typed.weakenC hK' (.inst C) rfl⟩
          exact Tm.HasType.letBody_substAtomE (Tm.HasType.letexBody_instC hu)
            (Atom.HasType.unpackPayload hσ.rootFree ha he)

/-- `unpackVal`: the store gains the witness as an instance binder and then the
literal, which is what `preservation_alloc` already packages. -/
theorem preservation_unpackVal {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm ((s,c),x)} {U' : CaptureSet s} {h : CapCo s} {f : CapCo ((s,c),x)}
    {C C₀ : CaptureSet s} {h₀ : CapCo s} {e : LeCo (Sig.scope s)} {v : Value s}
    {T : Dom s} {U : Ty s}
    (hσ : ⊢ σ : Γ) (hv : Γ ⊢ᵥᵉ .pack C h₀ e v : ∃ᶜ[C₀] T)
    (hK : Γ ⊢ₖ K ▹ .letex u U' h f : ∃ᶜ[C₀] T ⇒ U) :
    State.Typed
      ⟨(σ.consC (.inst C)).cons
          (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot)).core,
        (K.weakenC).weaken,
        u.adjust (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot))⟩
      (Ty.weaken (k := .var) (Ty.weaken (k := .cap) U)) := by
  cases hK with
  | letex hh hu hf hK' =>
      cases hv with
      | pack hv₀ hb he =>
          have hf' : ((Γ.consC (.inst C)).cons (.opaque T)) ⊢ᶜ f :
              u.uses ⊑ CaptureSet.weaken (k := .var)
                (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here]) := by
            have h := CapCo.HasType.letexCharge_instC (C := C) hf
            rwa [show CaptureSet.weaken (k := .var)
                (CaptureSet.weaken (k := .cap) U' ∪ [CapAtom.cvar BVar.here])
              = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
                  ∪ [CapAtom.cvar (.there .here)]) from
              CaptureSet.rename_union _ _ _]
          exact preservation_alloc (hσ.consC rfl)
            (Value.HasType.unpackPayload hσ.rootFree hv₀ he)
            (Cont.Typed.let (Tm.HasType.letexBody_instC hu) hf'
              (Cont.Typed.weakenC hK' (.inst C) rfl))

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
          | cast he hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .val (.plain (hv.ty_inv.cast he)), hK'⟩
  case castAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | cast he hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .atom (PAtom.HasType.applyE (.plain _) hp (.plain he)), hK'⟩
  case alloc =>
      cases ht with
      | val hv =>
          cases hK with
          | «let» hu hf hK' =>
              exact ⟨Rename.succ, preservation_alloc hσ hv.ty_inv (.let hu hf hK')⟩
  case rename =>
      cases ht with
      | atom hp =>
          cases hp with
          | plain ha =>
              cases hK with
              | «let» hu _ hK' =>
                  exact State.Typed.exists_rename_id
                    ⟨Γ, _, hσ, Tm.HasType.letBody_substAtomE hu ha, hK'⟩
  -- The three answer-cast steps.  None has a premise, and none reads a head
  -- form: the frame holds the coercion and `applyE` is total.
  case castEPush =>
      cases ht with
      | castE ht' hg => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .castE hg hK⟩
  case castEVal =>
      cases ht with
      | val hv =>
          cases hK with
          | castE hg hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .val (Value.HasTypeE.applyE _ hv hg), hK'⟩
  case castEAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | castE hg hK' =>
              exact State.Typed.exists_rename_id
                ⟨Γ, _, hσ, .atom (PAtom.HasType.applyE _ hp hg), hK'⟩
  case letex =>
      cases ht with
      | letex ht' hh hu hf =>
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .letex hh hu hf hK⟩
  case unpackAtom =>
      cases ht with
      | atom hp =>
          cases hK with
          | letex hh hu hf hK' =>
              exact ⟨Rename.succ,
                preservation_unpackAtom hσ hp (.letex hh hu hf hK')⟩
  case unpackVal =>
      cases ht with
      | val hv =>
          cases hK with
          | letex hh hu hf hK' =>
              refine ⟨Rename.succ.comp Rename.succ, ?_⟩
              have h := preservation_unpackVal hσ hv (.letex hh hu hf hK')
              simpa only [Ty.weaken, Ty.rename_comp] using h
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
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, ht₀.betaCast hσ.rootFree hdom hcod hb, hK⟩
  case proj hx hg =>
      cases ht with
      | proj _ _ => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, Tm.HasType.projField hσ hx hg, hK⟩
  case unboxRefl hx hcf hid =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (.plain (hσ.unboxRefl_result (hF Γ hσ) hx ha hcf hid)), hK⟩
  case unboxCast hx hcf =>
      cases ht with
      | unbox ha hf =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, .atom (.plain (hσ.unboxCast_result (hF Γ hσ) hx ha hcf)), hK⟩

end FCdot

end Classifiers
