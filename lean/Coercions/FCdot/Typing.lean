import Coercions.FCdot.Context

/-!
# FCdot typing

Evidence typing assigns endpoints to proof terms.  Term typing has no
subsumption; every inclusion is an explicit `cast`.  Elimination at an atom
(`member`) is the only way member facts flow from a binder's type to its
block.
-/

namespace FCdot

mutual

inductive LeCo.HasType : Ctx s → LeCo s → Ty s → Ty s → Prop where
  | refl : LeCo.HasType Γ (.refl T) T T
  | trans : LeCo.HasType Γ e S M → LeCo.HasType Γ f M T → LeCo.HasType Γ (.trans e f) S T
  | top : LeCo.HasType Γ (.top T) T .top
  | bot : LeCo.HasType Γ (.bot T) .bot T
  | eqToLe : EqCo.HasType Γ φ S T → LeCo.HasType Γ (.eqToLe φ) S T
  | pi :
      LeCo.HasType Γ e S2 S1 →
      LeCo.HasType (Γ.cons (.opaque S2)) f T1 T2 →
      LeCo.HasType Γ (.pi e f) (.pi S1 T1) (.pi S2 T2)
  | obj :
      Morphism.HasType (Γ.cons (.opaque (.obj Tel))) m Tel' →
      LeCo.HasType Γ (.obj Tel m) (.obj Tel) (.obj Tel')
  | member :
      Atom.HasType Γ a S →
      LeCo.HasType Γ e S (.obj Tel) →
      Tel.At i (.le S' T') →
      LeCo.HasType Γ (.member a e i) (S'.substVar a.root) (T'.substVar a.root)

inductive EqCo.HasType : Ctx s → EqCo s → Ty s → Ty s → Prop where
  | refl : EqCo.HasType Γ (.refl T) T T
  | symm : EqCo.HasType Γ φ S T → EqCo.HasType Γ (.symm φ) T S
  | trans : EqCo.HasType Γ φ S M → EqCo.HasType Γ ψ M T → EqCo.HasType Γ (.trans φ ψ) S T
  | def : Γ.lookupDef x ℓ = some W → EqCo.HasType Γ (.def x ℓ) (.sel x ℓ) W
  | member :
      Atom.HasType Γ a S →
      LeCo.HasType Γ e S (.obj Tel) →
      Tel.At i (.eq S' T') →
      EqCo.HasType Γ (.member a e i) (S'.substVar a.root) (T'.substVar a.root)

/-- `Has.HasType Γ h x ℓ`: `h` proves that the block of `x` has field `ℓ`. -/
inductive Has.HasType : Ctx s → Has s → BVar s .var → Label → Prop where
  | member :
      Atom.HasType Γ a S →
      LeCo.HasType Γ e S (.obj Tel) →
      Tel.At i (.has ℓ) →
      Has.HasType Γ (.member a e i) a.root ℓ
  | field :
      Γ.lookupFields x = some Fs → ℓ ∈ Fs →
      Has.HasType Γ (.field ℓ) x ℓ

/-- A morphism proves every proposition of a telescope at the innermost binder. -/
inductive Morphism.HasType : Ctx (s,x) → Morphism (s,x) → Telescope (s,x) → Prop where
  | nil : Morphism.HasType Γ .nil .nil
  | le : Morphism.HasType Γ m Tel → LeCo.HasType Γ e S T →
      Morphism.HasType Γ (.le m e) (.cons Tel (.le S T))
  | eq : Morphism.HasType Γ m Tel → EqCo.HasType Γ φ S T →
      Morphism.HasType Γ (.eq m φ) (.cons Tel (.eq S T))
  | has : Morphism.HasType Γ m Tel → Has.HasType Γ h .here ℓ →
      Morphism.HasType Γ (.has m h) (.cons Tel (.has ℓ))

inductive Atom.HasType : Ctx s → Atom s → Ty s → Prop where
  | var : Atom.HasType Γ (.var x) (Γ.lookupTy x)
  | cast : Atom.HasType Γ a S → LeCo.HasType Γ e S T → Atom.HasType Γ (.cast a e) T
  /-- `Rec-E`: the self block of the object type is the atom's own block. -/
  | unfoldSelf :
      Atom.HasType Γ a (.obj Tel) →
      Atom.HasType Γ (.unfoldSelf a) (.obj (Tel.substVar a.root).weaken)
  /-- `Rec-I`. -/
  | foldSelf :
      Atom.HasType Γ a (.obj (Tel.substVar a.root).weaken) →
      Atom.HasType Γ (.foldSelf Tel a) (.obj Tel)

end

mutual

inductive Tm.HasType : Ctx s → Tm s → Ty s → Prop where
  | atom : Atom.HasType Γ a T → Tm.HasType Γ (.atom a) T
  | val : Value.HasType Γ v T → Tm.HasType Γ (.val v) T
  | app :
      Atom.HasType Γ a (.pi S T) →
      Atom.HasType Γ b S →
      Tm.HasType Γ (.app a b) (T.substVar b.root)
  | proj :
      Atom.HasType Γ a S →
      Has.HasType Γ h a.root ℓ →
      Tm.HasType Γ (.proj a ℓ h) (.sel a.root ℓ)
  | «let» :
      Tm.HasType Γ t T →
      Tm.HasType (Γ.cons (.opaque T)) u U.weaken →
      Tm.HasType Γ (.let t u) U
  | cast : Tm.HasType Γ t S → LeCo.HasType Γ e S T → Tm.HasType Γ (.cast t e) T

inductive Value.HasType : Ctx s → Value s → Ty s → Prop where
  | lam :
      Tm.HasType (Γ.cons (.opaque S)) t T →
      Value.HasType Γ (.lam S t) (.pi S T)
  /-- The telescope evidence is checked with the self binder at type `⊤`:
      only the definitions and fields are available, so an object cannot
      discharge its own telescope by assuming it.  Fields are typed with the
      self binder at the declared object type. -/
  | obj :
      W.Guarded →
      Morphism.HasType (Γ.cons (.transparent .top W F.labels)) E Tel →
      Fields.HasType (Γ.cons (.transparent (.obj Tel) W F.labels)) F →
      Value.HasType Γ (.obj Tel W E F) (.obj Tel)
  | cast : Value.HasType Γ v S → LeCo.HasType Γ e S T → Value.HasType Γ (.cast v e) T

/-- Each field `ℓ = t` has type `self.ℓ`. -/
inductive Fields.HasType : Ctx (s,x) → Fields (s,x) → Prop where
  | nil : Fields.HasType Γ .nil
  | cons : Fields.HasType Γ F → Tm.HasType Γ t (.sel .here ℓ) → Fields.HasType Γ (.cons F ℓ t)

end

end FCdot
