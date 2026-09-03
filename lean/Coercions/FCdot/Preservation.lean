import Coercions.FCdot.Machine
import Coercions.FCdot.TypingSubst
import Coercions.FCdot.Transparency

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
  | .lam S t, ρ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .obj Tel W E F, ρ => by simp [Value.rename, Value.witnesses]
  | .cast v e, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]

theorem Value.fieldLabels_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).fieldLabels = v.fieldLabels
  | .lam S t, ρ => by simp [Value.rename, Value.fieldLabels]
  | .obj Tel W E F, ρ => by simp [Value.rename, Value.fieldLabels]
  | .cast v e, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]

theorem Value.core_witnesses {s : Sig} :
    ∀ v : Value s, v.core.witnesses = v.witnesses
  | .lam _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.witnesses, Value.core_witnesses v]

theorem Value.core_fieldLabels {s : Sig} :
    ∀ v : Value s, v.core.fieldLabels = v.fieldLabels
  | .lam _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.fieldLabels, Value.core_fieldLabels v]

theorem Value.core_isLiteral {s : Sig} : ∀ v : Value s, v.core.IsLiteral
  | .lam _ _ => trivial
  | .obj _ _ _ _ => trivial
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
    ∀ (v : Value s) (T : Ty s), Value.HasType Γ v T →
      ∃ S₀, Value.HasType Γ v.core S₀ ∧ v.core.IsLiteral ∧
        ((v.composite? = none ∧ S₀ = T) ∨
          ∃ E, v.composite? = some E ∧ LeCo.HasType Γ E S₀ T)
  | .lam S t, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .obj Tel W E F, T, h =>
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
              rcases hd with ⟨_, hS⟩ | ⟨E, hE?, _⟩
              · subst hS
                exact ⟨e, by simp [Value.composite?, Value.coercions, hc, LeCo.composite], he⟩
              · simp [Value.composite?, hc] at hE?
          | cons f fs =>
              rcases hd with ⟨hn, _⟩ | ⟨E, hE?, hE⟩
              · simp [Value.composite?, hc] at hn
              · simp only [Value.composite?, hc, Option.some.injEq] at hE?
                subst hE?
                exact ⟨.trans (LeCo.composite f fs) e,
                  by simp [Value.composite?, Value.coercions, hc, LeCo.composite_snoc],
                  .trans hE he⟩

/-! ## Store typing -/

theorem Store.Typed.lookup {s : Sig} {σ : Store s} {Γ : Ctx s} (h : Store.Typed σ Γ) :
    ∀ x : BVar s .var, Value.HasType Γ (σ.lookup x) (Γ.lookupTy x) := by
  induction h with
  | nil => intro x; cases x
  | @cons s0 σ0 Γ0 v T hσ hlit hv ih =>
      intro x
      cases x with
      | here => simpa [Store.lookup, Binding.ty] using hv.weaken _
      | there y => simpa [Store.lookup] using (ih y).weaken _

theorem Store.Typed.lookupFields {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : Store.Typed σ Γ) :
    ∀ x : BVar s .var, Γ.lookupFields x = some (σ.lookup x).fieldLabels := by
  induction h with
  | nil => intro x; cases x
  | @cons s0 σ0 Γ0 v T hσ hlit hv ih =>
      intro x
      cases x with
      | here =>
          simp [Store.lookup, Value.weaken, Value.fieldLabels_rename]
      | there y =>
          simp only [Ctx.lookupFields_there, ih y, Store.lookup, Value.weaken,
            Value.fieldLabels_rename]

theorem Store.Typed.isTransparent {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : Store.Typed σ Γ) (x : BVar s .var) : Γ.IsTransparent x :=
  Ctx.IsTransparent.of_lookup (h.lookupFields x)

theorem Store.Typed.lookupDef {s : Sig} {σ : Store s} {Γ : Ctx s} (h : Store.Typed σ Γ) :
    ∀ (x : BVar s .var) (l : Label),
      Γ.lookupDef x l = some (((σ.lookup x).witnesses.get l).substVar x) := by
  induction h with
  | nil => intro x l; cases x
  | @cons s0 σ0 Γ0 v T hσ hlit hv ih =>
      intro x l
      cases x with
      | here =>
          simp [Store.lookup, Value.weaken, Value.witnesses_rename,
            Witnesses.get_rename, Ty.substVar, Rename.succ_lift_comp_subst_here]
      | there y =>
          simp [Ctx.lookupDef_there, ih y l, Store.lookup, Value.weaken,
            Value.witnesses_rename, Witnesses.get_rename, Ty.substVar, Ty.weaken,
            Rename.succ_lift_comp_subst_there]

/-! ## Continuation weakening -/

theorem Cont.Typed.weaken {s : Sig} {Γ : Ctx s} {K : Cont s} {T U : Ty s}
    (h : Cont.Typed Γ K T U) (b : Binding s) :
    Cont.Typed (Γ.cons b) K.weaken T.weaken U.weaken := by
  induction h with
  | nil => exact .nil
  | «let» hu hK ih =>
      refine Cont.Typed.let ?_ ih
      have := hu.rename ((Ctx.Ren.succ b).lift (.opaque _))
      simpa [Ty.weaken_rename] using this
  | cast he hK ih =>
      exact Cont.Typed.cast (LeCo.HasType.weaken he b) ih

/-! ## Inversions -/

theorem Atom.HasType.var_inv {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Atom.HasType Γ (.var x) T) : T = Γ.lookupTy x := by
  cases h with
  | var => rfl

theorem Value.HasType.lam_inv {s : Sig} {Γ : Ctx s} {S₀ : Ty s} {t₀ : Tm (s,x)}
    {T : Ty s} (h : Value.HasType Γ (.lam S₀ t₀) T) :
    ∃ T₀, T = .pi S₀ T₀ ∧ Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ := by
  cases h with
  | lam ht => exact ⟨_, rfl, ht⟩

theorem Value.HasType.obj_inv {s : Sig} {Γ : Ctx s} {Tel : Telescope (s,x)}
    {W : Witnesses (s,x)} {E : Morphism (s,x)} {F : Fields (s,x)} {T : Ty s}
    (h : Value.HasType Γ (.obj Tel W E F) T) :
    T = .obj Tel ∧ W.Guarded ∧
      Morphism.HasType (Γ.cons (.transparent .top W F.labels)) E Tel ∧
      Fields.HasType (Γ.cons (.transparent (.obj Tel) W F.labels)) F := by
  cases h with
  | obj hG hE hF => exact ⟨rfl, hG, hE, hF⟩

theorem Fields.HasType.get {s : Sig} {Γ : Ctx (s,x)} :
    ∀ (F : Fields (s,x)), Fields.HasType Γ F → ∀ (l : Label) (t : Tm (s,x)),
      F.get? l = some t → Tm.HasType Γ t (.sel .here l)
  | .nil, _, l, t, hg => by simp [Fields.get?] at hg
  | .cons F l' t', h, l, t, hg => by
      cases h with
      | cons hF ht =>
          by_cases hl : l = l'
          · subst hl
            have hte : t = t' := by simpa [Fields.get?] using hg.symm
            subst hte
            exact ht
          · rw [show Fields.get? (.cons F l' t') l = F.get? l by
                simp [Fields.get?, hl]] at hg
            exact Fields.HasType.get F hF l t hg

/-! ## The two substitution instances the machine uses -/

@[simp] theorem Subst.selfCast_root {s : Sig} (E : LeCo (s,x)) :
    (Subst.selfCast E).root = Rename.id := by
  apply Rename.funext'
  intro k x
  cases k
  cases x <;> rfl

theorem Subst.Typed.selfCast {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    {W : Witnesses (s,x)} {Fs : List Label} (hE : LeCo.HasType Γ E S₀ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E.weaken)
      (Γ.cons (.transparent S₀ W Fs)) where
  var := by
    intro y
    cases y with
    | here =>
        show Atom.HasType (Γ.cons (.transparent S₀ W Fs)) (.cast (.var .here) E.weaken)
          (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E.weaken).root)
        have hE' : LeCo.HasType (Γ.cons (.transparent S₀ W Fs)) E.weaken S₀.weaken T.weaken :=
          hE.weaken _
        have hvar : Atom.HasType (Γ.cons (.transparent S₀ W Fs)) (.var .here) S₀.weaken := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Fs)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show Atom.HasType (Γ.cons (.transparent S₀ W Fs)) (.var (.there z))
          (((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E.weaken).root)
        simpa using Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Fs)) (x := .there z)
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
  fields := by
    intro y Fs' hFs'
    cases y with
    | here => simp at hFs'
    | there z =>
        rw [Ctx.lookupFields_there] at hFs'
        simpa using hFs'

/-- The self binder of a stored object literal may be replaced by the
variable it is stored at. -/
theorem Ctx.Ren.selfObj {s : Sig} {Γ : Ctx s} {Tel : Telescope (s,x)}
    {W : Witnesses (s,x)} {Fs : List Label} {y : BVar s .var}
    (hty : Γ.lookupTy y = .obj Tel)
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l).substVar y))
    (hfields : Γ.lookupFields y = some Fs) :
    Ctx.Ren (Γ.cons (.transparent (.obj Tel) W Fs)) (Rename.subst y) Γ where
  ty := by
    intro z
    cases z with
    | here => simpa [Binding.ty] using hty
    | there w => simp
  def_ := by
    intro z l W' hW'
    cases z with
    | here =>
        have hWe : W' = W.get l := by simpa using hW'.symm
        subst hWe
        simpa [Ty.substVar] using hdef l
    | there w =>
        rw [Ctx.lookupDef_there] at hW'
        cases hd : Γ.lookupDef w l with
        | none => rw [hd] at hW'; simp at hW'
        | some W0 =>
            rw [hd] at hW'
            have hWe : W' = W0.weaken := by simpa using hW'.symm
            subst hWe
            simpa using hd
  fields := by
    intro z Fs' hFs'
    cases z with
    | here =>
        have hFe : Fs' = Fs := by simpa using hFs'.symm
        subst hFe
        simpa using hfields
    | there w =>
        rw [Ctx.lookupFields_there] at hFs'
        simpa using hFs'

/-! ## Preservation -/

/-- Typedness of the head form used by the application step: whenever the
head form of a function atom's casts is `pi d c`, `d` and `c` are typed
between the atom's function type and its closure's type; whenever it is the
identity form, the two function types coincide.  Discharged by the
canonical-forms theorem (`CanonicalMetatheory.lean`). -/
structure FormsTyped (σ : Store s) (Γ : Ctx s) : Prop where
  pi : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {n : Nat} {a' : Atom s} {d : LeCo s}
    {c : LeCo (s,x)} {S₀ : Ty s} {T₀ : Ty (s,x)},
    Atom.HasType Γ a (.pi S T) → closedAtomForm σ n a = some (a', .pi d c) →
    Γ.lookupTy a.root = .pi S₀ T₀ →
    LeCo.HasType Γ d S S₀ ∧ LeCo.HasType (Γ.cons (.opaque S)) c T₀ T
  refl : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {n : Nat} {a' : Atom s} {F : Form s},
    Atom.HasType Γ a (.pi S T) → closedAtomForm σ n a = some (a', F) →
    (F = .id ∨ ∃ φ, F = .eqv φ) →
    Γ.lookupTy a.root = .pi S T

theorem preservation {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hF : ∀ Γ, Store.Typed st.σ Γ → FormsTyped st.σ Γ)
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) := by
  cases step with
  | «let» =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | «let» ht' hu =>
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          exact ⟨Γ, _, hσ, ht', Cont.Typed.let hu hK⟩
  | castPush =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | cast ht' he =>
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          exact ⟨Γ, _, hσ, ht', Cont.Typed.cast he hK⟩
  | castVal =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | val hv =>
          cases hK with
          | cast he hK' =>
              refine ⟨Rename.id, ?_⟩
              rw [Ty.rename_id]
              exact ⟨Γ, _, hσ, .val (.cast hv he), hK'⟩
  | castAtom =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | atom ha =>
          cases hK with
          | cast he hK' =>
              refine ⟨Rename.id, ?_⟩
              rw [Ty.rename_id]
              exact ⟨Γ, _, hσ, .atom (.cast ha he), hK'⟩
  | @alloc σ K u v =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | val hv =>
          cases hK with
          | «let» hu hK' =>
              obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v T hv
              refine ⟨Rename.succ, _, _, Store.Typed.cons hσ hlit hcore, ?_,
                Cont.Typed.weaken hK' _⟩
              rcases hd with ⟨hn, hS⟩ | ⟨E, hE?, hE⟩
              · subst hS
                rw [show Tm.adjust u v = u by simp [Tm.adjust, hn]]
                exact hu.refine Ctx.Refines.transparent
              · rw [show Tm.adjust u v = u.subst (Subst.selfCast E.weaken) by
                      simp [Tm.adjust, hE?]]
                have := hu.subst (Subst.Typed.selfCast (W := v.core.witnesses)
                  (Fs := v.core.fieldLabels) hE)
                simpa using this
  | rename =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | atom ha =>
          cases hK with
          | «let» hu hK' =>
              refine ⟨Rename.id, ?_⟩
              rw [Ty.rename_id]
              refine ⟨Γ, _, hσ, ?_, hK'⟩
              have := Tm.HasType.substAtom hu ha
              simpa using this
  | @appVar σ K x b S₀ t₀ hx =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | app ha hb =>
          have hlook := (Atom.HasType.var_inv ha).symm
          have hval := hσ.lookup x
          rw [hx, hlook] at hval
          obtain ⟨T₀, hTe, ht₀⟩ := Value.HasType.lam_inv hval
          injection hTe with _ hS hT'
          subst hS
          subst hT'
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          exact ⟨Γ, _, hσ, Tm.HasType.substAtom ht₀ hb, hK⟩
  | @appCastRefl a σ K b S₀ t₀ n a' F hx hne hcf hid =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | app ha hb =>
          have hval := hσ.lookup a.root
          have hty := (hF Γ hσ).refl ha hcf hid
          rw [hx, hty] at hval
          obtain ⟨T₀, hTe, ht₀⟩ := Value.HasType.lam_inv hval
          injection hTe with _ hS hT'
          subst hS
          subst hT'
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          exact ⟨Γ, _, hσ, Tm.HasType.substAtom ht₀ hb, hK⟩
  | @appCast a σ K b S₀ t₀ n a' d c hx hne hcf =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | app ha hb =>
          have hval := hσ.lookup a.root
          rw [hx] at hval
          obtain ⟨T₀, hTe, ht₀⟩ := Value.HasType.lam_inv hval
          obtain ⟨hdom, hcod⟩ := (hF Γ hσ).pi ha hcf hTe
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          refine ⟨Γ, _, hσ, ?_, hK⟩
          have hcod' := hcod.subst (Subst.Typed.single hb)
          rw [Subst.single_root] at hcod'
          refine Tm.HasType.cast ?_ hcod'
          have := Tm.HasType.substAtom ht₀ (Atom.HasType.cast hb hdom)
          simpa [Atom.root] using this
  | @proj t σ K a l h Tel W E F hx hg =>
      obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
      cases ht with
      | proj ha hh =>
          have hval := hσ.lookup a.root
          rw [hx] at hval
          obtain ⟨hTe, hG, hE, hF⟩ := Value.HasType.obj_inv hval
          have hdef : ∀ l', Γ.lookupDef a.root l' = some ((W.get l').substVar a.root) := by
            intro l'
            have hlk := hσ.lookupDef a.root l'
            rw [hx] at hlk
            simpa [Value.witnesses] using hlk
          have hfields : Γ.lookupFields a.root = some F.labels := by
            have hlk := hσ.lookupFields a.root
            rw [hx] at hlk
            simpa [Value.fieldLabels] using hlk
          have hren := Ctx.Ren.selfObj hTe hdef hfields
          have hterm := (Fields.HasType.get F hF l t hg).rename hren
          refine ⟨Rename.id, ?_⟩
          rw [Ty.rename_id]
          refine ⟨Γ, _, hσ, ?_, hK⟩
          simpa [Tm.selfAt, Ty.rename] using hterm

end FCdot
