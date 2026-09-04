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
  | .lam _ _, _ => by simp [Value.rename, Value.witnesses, Witnesses.rename]
  | .obj _ _, _ => by simp [Value.rename, Value.witnesses]
  | .cast v _, ρ => by
      simp [Value.rename, Value.witnesses, Value.witnesses_rename v ρ]

theorem Value.fieldLabels_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).fieldLabels = v.fieldLabels
  | .lam _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .obj _ _, _ => by simp [Value.rename, Value.fieldLabels]
  | .cast v _, ρ => by
      simp [Value.rename, Value.fieldLabels, Value.fieldLabels_rename v ρ]

theorem Value.core_witnesses {s : Sig} :
    ∀ v : Value s, v.core.witnesses = v.witnesses
  | .lam _ _ => rfl
  | .obj _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.witnesses, Value.core_witnesses v]

theorem Value.core_fieldLabels {s : Sig} :
    ∀ v : Value s, v.core.fieldLabels = v.fieldLabels
  | .lam _ _ => rfl
  | .obj _ _ => rfl
  | .cast v _ => by simp [Value.core, Value.fieldLabels, Value.core_fieldLabels v]

theorem Value.core_isLiteral {s : Sig} : ∀ v : Value s, v.core.IsLiteral
  | .lam _ _ => trivial
  | .obj _ _ => trivial
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
  | .lam _ _, T, h =>
      ⟨T, by simpa [Value.core] using h, by simp [Value.core, Value.IsLiteral],
        Or.inl ⟨by simp [Value.composite?, Value.coercions], rfl⟩⟩
  | .obj _ _, T, h =>
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
            Witnesses.get_rename, Ty.substVar, Ty.rename_comp,
            Rename.succ_lift_comp_subst_here, Ty.rename_id]
      | there y =>
          simp only [Ctx.lookupDef_there, ih y l, Option.map_some, Store.lookup,
            Value.weaken, Value.witnesses_rename, Witnesses.get_rename, Ty.substVar,
            Ty.weaken, Ty.rename_comp, Rename.succ_lift_comp_subst_there]

/-- The closure stored at a variable is typed at the variable's type. -/
theorem Store.Typed.lam_of_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {S₀ : Ty s} {t₀ : Tm (s,x)} (h : ⊢ σ : Γ) (hx : σ.lookup x = .lam S₀ t₀) :
    Γ ⊢ᵥ .lam S₀ t₀ : Γ.lookupTy x :=
  hx ▸ h.lookup x

/-! ## Continuation weakening -/

theorem Cont.Typed.weaken {s : Sig} {Γ : Ctx s} {K : Cont s} {T U : Ty s}
    (h : Γ ⊢ₖ K : T ⇒ U) (b : Binding s) :
    (Γ.cons b) ⊢ₖ K↑ : T↑ ⇒ U↑ := by
  induction h with
  | nil => exact .nil
  | «let» hu _ ih =>
      refine Cont.Typed.let ?_ ih
      have := hu.rename ((Ctx.Ren.succ b).lift (.opaque _))
      simpa [Ty.weaken_rename] using this
  | cast he _ ih =>
      exact Cont.Typed.cast (LeCo.HasType.weaken he b) ih

/-! ## Inversions -/

theorem Atom.HasType.var_inv {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Γ ⊢ₐ .var x : T) : T = Γ.lookupTy x := by
  cases h with
  | var => rfl

theorem Value.HasType.lam_inv {s : Sig} {Γ : Ctx s} {S₀ : Ty s} {t₀ : Tm (s,x)}
    {T : Ty s} (h : Γ ⊢ᵥ .lam S₀ t₀ : T) :
    ∃ T₀, T = .pi S₀ T₀ ∧ (Γ.cons (.opaque S₀)) ⊢ t₀ : T₀ := by
  cases h with
  | lam ht => exact ⟨_, rfl, ht⟩

theorem Value.HasType.obj_inv {s : Sig} {Γ : Ctx s}
    {W : Witnesses (s,x)} {F : Fields (s,x)} {T : Ty s}
    (h : Γ ⊢ᵥ .obj W F : T) :
    T = .obj (Telescope.ofLiteral W F.labels) ∧ W.Guarded ∧
      Fields.HasType
        (Γ.cons (.transparent (.obj (Telescope.ofLiteral W F.labels)) W F.labels)) F := by
  cases h with
  | obj hG hF => exact ⟨rfl, hG, hF⟩

theorem Fields.HasType.get {s : Sig} {Γ : Ctx (s,x)} :
    ∀ (F : Fields (s,x)), Γ ⊢ᶠ F → ∀ (l : Label) (t : Tm (s,x)),
      F.get? l = some t → Γ ⊢ t : .sel .here l
  | .nil, _, l, t, hg => by simp [Fields.get?] at hg
  | .cons F l' t', h, l, t, hg => by
      cases h with
      | cons hF ht =>
          by_cases hl : l = l'
          · subst hl
            obtain rfl : t' = t := by simpa [Fields.get?] using hg
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
    {W : Witnesses (s,x)} {Fs : List Label} (hE : Γ ⊢ E : S₀ ≤ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E↑)
      (Γ.cons (.transparent S₀ W Fs)) where
  var := by
    intro y
    cases y with
    | here =>
        show (Γ.cons (.transparent S₀ W Fs)) ⊢ₐ .cast (.var .here) E↑ :
          ((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E↑).root
        have hE' : (Γ.cons (.transparent S₀ W Fs)) ⊢ E↑ : S₀↑ ≤ T↑ :=
          hE.weaken _
        have hvar : (Γ.cons (.transparent S₀ W Fs)) ⊢ₐ .var .here : S₀↑ := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.transparent S₀ W Fs)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show (Γ.cons (.transparent S₀ W Fs)) ⊢ₐ .var (.there z) :
          ((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E↑).root
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
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧))
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
        obtain rfl : W.get l = W' := by simpa using hW'
        simpa [Ty.substVar] using hdef l
    | there w =>
        rw [Ctx.lookupDef_there] at hW'
        obtain ⟨W0, hd, rfl⟩ := Option.map_eq_some_iff.mp hW'
        simpa using hd
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

/-- Typedness of the head form used by the application step: whenever the
head form of a function atom's casts is `pi d c`, `d` and `c` are typed
between the atom's function type and its closure's type; whenever it is the
identity form, the two function types coincide.  Discharged by the
canonical-forms theorem (`CanonicalForms.lean`). -/
structure FormsTyped (σ : Store s) (Γ : Ctx s) : Prop where
  pi : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {n : Nat} {a' : Atom s} {d : LeCo s}
    {c : LeCo (s,x)} {S₀ : Ty s} {T₀ : Ty (s,x)},
    Γ ⊢ₐ a : .pi S T → σ ⊢ a ⇓ᶜ[n] (a', .pi d c) →
    Γ.lookupTy a.root = .pi S₀ T₀ →
    Γ ⊢ d : S ≤ S₀ ∧ (Γ.cons (.opaque S)) ⊢ c : T₀ ≤ T
  refl : ∀ {a : Atom s} {S : Ty s} {T : Ty (s,x)} {n : Nat} {a' : Atom s} {F : Form s},
    Γ ⊢ₐ a : .pi S T → σ ⊢ a ⇓ᶜ[n] (a', F) →
    (F = .id ∨ ∃ φ, F = .eqv φ) →
    Γ.lookupTy a.root = .pi S T

/-- A step that does not allocate keeps the signature: the result type is
transported along the identity renaming. -/
theorem State.Typed.exists_rename_id {s : Sig} {st : State s} {U : Ty s}
    (h : State.Typed st U) : ∃ ρ : Rename s s, State.Typed st (U.rename ρ) :=
  ⟨Rename.id, by simpa using h⟩

/-- `alloc`: the stripped literal is stored at its own type, and the
continuation body is adjusted to use the new variable under the composite of
the stripped casts. -/
theorem preservation_alloc {s : Sig} {σ : Store s} {Γ : Ctx s} {K : Cont s}
    {u : Tm (s,x)} {v : Value s} {T U : Ty s}
    (hσ : ⊢ σ : Γ) (hv : Γ ⊢ᵥ v : T) (hK : Γ ⊢ₖ K ▹ .let u : T ⇒ U) :
    State.Typed ⟨.cons σ v.core, K↑, u.adjust v⟩ U↑ := by
  cases hK with
  | «let» hu hK' =>
      obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v T hv
      refine ⟨_, _, Store.Typed.cons hσ hlit hcore, ?_, Cont.Typed.weaken hK' _⟩
      rcases hd with ⟨hn, rfl⟩ | ⟨E, hE?, hE⟩
      · rw [show u.adjust v = u by simp [Tm.adjust, hn]]
        exact hu.refine Ctx.Refines.transparent
      · rw [show u.adjust v = u.subst (Subst.selfCast E↑) by simp [Tm.adjust, hE?]]
        simpa using hu.subst (Subst.Typed.selfCast (W := v.core.witnesses)
          (Fs := v.core.fieldLabels) hE)

/-- β: a closure applied at its own function type. -/
theorem Value.HasType.beta {s : Sig} {Γ : Ctx s} {S₀ S : Ty s} {t₀ : Tm (s,x)}
    {T : Ty (s,x)} {b : Atom s}
    (hlam : Γ ⊢ᵥ .lam S₀ t₀ : Π(S) T) (hb : Γ ⊢ₐ b : S) :
    Γ ⊢ t₀.substAtom b : T⟦b.root⟧ := by
  obtain ⟨T₀, hTe, ht₀⟩ := Value.HasType.lam_inv hlam
  obtain ⟨rfl, rfl⟩ := Ty.pi.inj hTe
  exact Tm.HasType.substAtom ht₀ hb

/-- β for a closure stored at the root of an atom whose type is that root's
type: `appVar`, and `appCastRefl` where the casts normalize to the identity. -/
theorem Store.Typed.beta {s : Sig} {σ : Store s} {Γ : Ctx s} {x : BVar s .var}
    {S₀ S : Ty s} {t₀ : Tm (s,x)} {T : Ty (s,x)} {b : Atom s}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup x = .lam S₀ t₀) (hty : Γ.lookupTy x = Π(S) T)
    (hb : Γ ⊢ₐ b : S) : Γ ⊢ t₀.substAtom b : T⟦b.root⟧ :=
  (hty ▸ hσ.lam_of_lookup hx).beta hb

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

/-- Projecting a field of a stored object literal: the field's body, with the
self binder replaced by the object's variable, has the projection's type. -/
theorem Tm.HasType.projField {s : Sig} {σ : Store s} {Γ : Ctx s} {y : BVar s .var}
    {W : Witnesses (s,x)} {F : Fields (s,x)} {ℓ : Label} {t : Tm (s,x)}
    (hσ : ⊢ σ : Γ) (hx : σ.lookup y = .obj W F) (hg : F.get? ℓ = some t) :
    Γ ⊢ t.selfAt y : y ∙ ℓ := by
  have hval := hσ.lookup y
  rw [hx] at hval
  obtain ⟨hTe, _, hF⟩ := Value.HasType.obj_inv hval
  have hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧) := by
    intro l
    have hlk := hσ.lookupDef y l
    rw [hx] at hlk
    simpa [Value.witnesses] using hlk
  have hfields : Γ.lookupFields y = some F.labels := by
    have hlk := hσ.lookupFields y
    rw [hx] at hlk
    simpa [Value.fieldLabels] using hlk
  have hren := Ctx.Ren.selfObj hTe hdef hfields
  simpa [Tm.selfAt, Ty.rename] using (Fields.HasType.get F hF ℓ t hg).rename hren

theorem preservation {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hF : ∀ Γ, ⊢ st.σ : Γ → FormsTyped st.σ Γ)
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) := by
  cases step <;> obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
  case «let» =>
      cases ht with
      | «let» ht' hu => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht', .let hu hK⟩
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
          | «let» hu hK' =>
              exact State.Typed.exists_rename_id ⟨Γ, _, hσ, by simpa using hu.substAtom ha, hK'⟩
  case appVar hx =>
      cases ht with
      | app ha hb =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, hσ.beta hx (Atom.HasType.var_inv ha).symm hb, hK⟩
  case appCastRefl hx _ hcf hid =>
      cases ht with
      | app ha hb =>
          exact State.Typed.exists_rename_id
            ⟨Γ, _, hσ, hσ.beta hx ((hF Γ hσ).refl ha hcf hid) hb, hK⟩
  case appCast hx _ hcf =>
      cases ht with
      | app ha hb =>
          obtain ⟨T₀, hTe, ht₀⟩ := Value.HasType.lam_inv (hσ.lam_of_lookup hx)
          obtain ⟨hdom, hcod⟩ := (hF Γ hσ).pi ha hcf hTe
          exact State.Typed.exists_rename_id ⟨Γ, _, hσ, ht₀.betaCast hdom hcod hb, hK⟩
  case proj hx hg =>
      cases ht with
      | proj _ _ => exact State.Typed.exists_rename_id ⟨Γ, _, hσ, Tm.HasType.projField hσ hx hg, hK⟩

end FCdot
