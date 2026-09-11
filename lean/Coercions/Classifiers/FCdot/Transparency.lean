import Coercions.Classifiers.FCdot.TypingRename

namespace Classifiers

/-!
# Transparency is a refinement

`Ctx.Refines Γ Γ'` says that `Γ'` has the same variable types as `Γ` and at
least as many block definitions and field labels.  Every typing family is
monotone in this order; in particular a term typed with an opaque binder is
typed with the corresponding transparent binder, which is what allocation
needs.
-/

namespace FCdot

/-- `Γ'` knows everything `Γ` knows, with the same types. -/
structure Ctx.Refines {s : Sig} (Γ Γ' : Ctx s) : Prop where
  ty : ∀ x, Γ'.lookupTy x = Γ.lookupTy x
  def_ : ∀ x l (W : Shape s), Γ.lookupDef x l = some W → Γ'.lookupDef x l = some W
  defC : ∀ x l (C : CaptureSet s), Γ.lookupDefC x l = some C → Γ'.lookupDefC x l = some C
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields x = some Fs
  /-- Refinement adds block definitions and field labels to term binders and
      never touches the capture spine, so the innermost root is the same. -/
  rootEq : Γ'.root? = Γ.root?
  /-- And so is the level of every binder. -/
  lvlEq : ∀ {k : Kind} (y : BVar s k), Γ'.lvl y = Γ.lvl y
  /-- And so is the answer to whether a capture binder is a root. -/
  capEq : ∀ κ : BVar s .cap, (Γ'.lookupCap κ).isRoot = (Γ.lookupCap κ).isRoot
  /-- And so is the set an instance binder was opened at.  It is the fourth
      capture field, the one `CapEq.HasType.instC` reads. -/
  capInstEq : ∀ κ : BVar s .cap, (Γ'.lookupCap κ).instSet? = (Γ.lookupCap κ).instSet?

namespace Ctx.Refines

theorem refl {Γ : Ctx s} : Ctx.Refines Γ Γ where
  ty := fun _ => rfl
  def_ := fun _ _ _ h => h
  defC := fun _ _ _ h => h
  fields := fun _ _ h => h
  rootEq := rfl
  lvlEq := fun _ => rfl
  capEq := fun _ => rfl
  capInstEq := fun _ => rfl

theorem trans {Γ1 Γ2 Γ3 : Ctx s} (h1 : Ctx.Refines Γ1 Γ2) (h2 : Ctx.Refines Γ2 Γ3) :
    Ctx.Refines Γ1 Γ3 where
  ty := fun x => (h2.ty x).trans (h1.ty x)
  def_ := fun x l W h => h2.def_ x l W (h1.def_ x l W h)
  defC := fun x l C h => h2.defC x l C (h1.defC x l C h)
  fields := fun x Fs h => h2.fields x Fs (h1.fields x Fs h)
  rootEq := h2.rootEq.trans h1.rootEq
  lvlEq := fun y => (h2.lvlEq y).trans (h1.lvlEq y)
  capEq := fun κ => (h2.capEq κ).trans (h1.capEq κ)
  capInstEq := fun κ => (h2.capInstEq κ).trans (h1.capInstEq κ)

theorem cons {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (b : Binding s) :
    Ctx.Refines (Γ.cons b) (Γ'.cons b) where
  ty := by
    intro x
    cases x with
    | here => rfl
    | there y => simp [h.ty y]
  def_ := by
    intro x l W hW
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | transparent T W' Wc' Fs => exact hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  defC := by
    intro x l C hC
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hC
        | transparent T W' Wc' Fs => exact hC
    | there y =>
        rw [Ctx.lookupDefC_there] at hC ⊢
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Wc' Fs' => exact hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs ⊢
        exact h.fields y Fs hFs
  rootEq := by
    rw [Ctx.root?_cons, Ctx.root?_cons, h.rootEq]
  lvlEq := by
    intro k y
    cases y with
    | here => simp [h.rootEq]
    | there y0 => simp [h.lvlEq]
  capEq := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑).isRoot = ((Γ.lookupCap κ0)↑).isRoot
        simp [h.capEq]
  capInstEq := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,x)).instSet? = ((Γ.lookupCap κ0)↑).instSet?
        rw [CapBound.instSet?_weaken, CapBound.instSet?_weaken, h.capInstEq]

/-- Weakening an opaque binder to the transparent binder of the same type. -/
theorem transparent {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)}
    {Fs : List Label} :
    Ctx.Refines (Γ.cons (.opaque T)) (Γ.cons (.transparent T W Wc Fs)) where
  ty := by
    intro x
    cases x with
    | here => rfl
    | there y => rfl
  def_ := by
    intro x l W' hW
    cases x with
    | here => simp at hW
    | there y => rw [Ctx.lookupDef_there] at hW ⊢; exact hW
  defC := by
    intro x l C' hC
    cases x with
    | here => simp at hC
    | there y => rw [Ctx.lookupDefC_there] at hC ⊢; exact hC
  fields := by
    intro x Fs' hFs
    cases x with
    | here => simp at hFs
    | there y => rw [Ctx.lookupFields_there] at hFs ⊢; exact hFs
  rootEq := rfl
  lvlEq := by
    intro k y
    cases y with
    | here => rfl
    | there y0 => rfl
  capEq := by
    intro κ
    cases κ with
    | there κ0 => rfl
  capInstEq := by
    intro κ
    cases κ with
    | there κ0 => rfl

theorem transparentOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {x : BVar s .var}
    (ht : Γ.IsTransparent x) : Γ'.IsTransparent x := by
  obtain ⟨Fs, hFs⟩ := Ctx.isTransparent_iff.mp ht
  exact Ctx.IsTransparent.of_lookup (h.fields x Fs hFs)

theorem consC {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (b : CapBound s) :
    Ctx.Refines (Γ.consC b) (Γ'.consC b) where
  ty := by
    intro x
    cases x with
    | there y => simp [h.ty y]
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC ⊢
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs ⊢
        exact h.fields y Fs hFs
  rootEq := by
    cases b with
    | root => rfl
    | star | upper C | inst C =>
        rw [Ctx.root?_consC_of_not_root _ _ rfl, Ctx.root?_consC_of_not_root _ _ rfl, h.rootEq]
  lvlEq := by
    intro k y
    cases y with
    | here =>
        cases b with
        | root => rfl
        | star | upper C | inst C =>
            rw [Ctx.lvl_consC_here_of_not_root _ _ rfl, Ctx.lvl_consC_here_of_not_root _ _ rfl,
              h.rootEq]
    | there y0 => simp [h.lvlEq]
  capEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑).isRoot = ((Γ.lookupCap κ0)↑).isRoot
        simp [h.capEq]
  capInstEq := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((Γ'.lookupCap κ0)↑ : CapBound (s,c)).instSet? = ((Γ.lookupCap κ0)↑).instSet?
        rw [CapBound.instSet?_weaken, CapBound.instSet?_weaken, h.capInstEq]

/-! ### The scope contexts

A scope, a lambda body and an object body are built from the two `cons`
lemmas above, so refinement passes under all three. -/

theorem scope {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') : Ctx.Refines Γ.scope Γ'.scope :=
  (h.consC .root).consC .star

theorem scopeInst {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (C : CaptureSet s) :
    Ctx.Refines (Γ.scopeInst C) (Γ'.scopeInst C) :=
  (h.consC .root).consC (.inst C↑)

theorem body {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (T : Dom s) :
    Ctx.Refines (Γ.body T) (Γ'.body T) :=
  (h.scope).cons _

theorem objBody {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (T : Ty s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (ls : List Label) :
    Ctx.Refines (Γ.objBody T W Wc ls) (Γ'.objBody T W Wc ls) :=
  (h.consC .root).cons _

end Ctx.Refines

/-! ## Levels under a refinement

The three new fields say that a refinement leaves the capture spine alone,
so every level fact reads the same on both sides.  That is what the `level`
rule needs, and it is why the monotonicity theorems keep their meaning. -/

theorem Ctx.Refines.lvlAtom {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (a : CapAtom s) :
    Γ'.lvlAtom a = Γ.lvlAtom a := by
  cases a <;> simp [Ctx.lvlAtom, h.lvlEq]

theorem Ctx.Refines.isRootB {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') (a : CapAtom s) :
    Γ'.isRootB a = Γ.isRootB a := by
  cases a <;> simp [Ctx.isRootB, h.capEq]

theorem Ctx.Refines.isRoot {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {r : CapAtom s}
    (hr : Γ.IsRoot r) : Γ'.IsRoot r := by
  unfold Ctx.IsRoot
  rw [h.isRootB]
  exact hr

theorem Ctx.Refines.instOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {a : CapAtom s}
    {C : CaptureSet s} (hI : Γ.InstOf a C) : Γ'.InstOf a C := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at hI
  | cvar κ =>
      show (Γ'.lookupCap κ).instSet? = some C
      rw [h.capInstEq]
      exact hI

theorem Ctx.Refines.lvlLe {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {e r : CapAtom s}
    (hl : Γ.LvlLe e r) : Γ'.LvlLe e r := by
  unfold Ctx.LvlLe Ctx.lvlLeB
  rw [h.lvlAtom]
  exact hl

/-! ## Monotonicity of the typing families -/

mutual

/-- The capture family reads a context only at `defC` and through atoms, and
both survive a refinement. -/
theorem CapCo.HasType.refine {Γ Γ' : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) : Γ' ⊢ᶜ f : C ⊑ D := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.refine hR) (hg.refine hR)
  | .elem hs => exact .elem hs
  | .union hf hg => exact .union (hf.refine hR) (hg.refine hR)
  | .capvar ha => exact .capvar (ha.refine hR)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .eqToLe hφ => exact .eqToLe (hφ.refine hR)
  | .level h₁ h₂ => exact .level (hR.isRoot h₁) (hR.lvlLe h₂)

theorem CapEq.HasType.refine {Γ Γ' : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) : Γ' ⊢ᶜ φ : C ≡ D := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .defC hd => exact .defC (hR.defC _ _ _ hd)
  | .instC hI => exact .instC (hR.instOf hI)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem CapStep.HasType.refine {Γ Γ' : Ctx s} {st : CapStep s} {X Y : CaptureSet (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : CapStep.HasType Γ st X Y) : CapStep.HasType Γ' st X Y := by
  match h with
  | .closed hf => exact .closed (hf.refine hR)
  | .incl hs => exact .incl hs

theorem SideC.HasType.refine {Γ Γ' : Ctx s} {q : SideC s} {X Y : CaptureSet (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : SideC.HasType Γ q X Y) : SideC.HasType Γ' q X Y := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.refine hR) (hq.refine hR)

theorem ShapeCo.HasType.refine {Γ Γ' : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ˢ e : S ≤ T) : Γ' ⊢ˢ e : S ≤ T := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.refine hR) (hf.refine hR)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.refine hR)
  | .pi he hf =>
      exact .pi (LeCo.HasType.refine hR.scope he) (ELeCo.HasType.refine (hR.body _) hf)
  | .obj hm => exact .obj (hm.refine hR)
  | .pair he hf => exact .pair (he.refine hR) (hf.refine hR)
  | .bound hAt => exact .bound hAt
  | .intoBnd he => exact .intoBnd (he.refine hR)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .boxed hd => exact .boxed (LeCo.HasType.refine hR hd)

theorem LeCo.HasType.refine {Γ Γ' : Ctx s} {d : LeCo s} {S T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ d : S ≤ T) : Γ' ⊢ d : S ≤ T := by
  match h with
  | .capt he hf => exact .capt (he.refine hR) (hf.refine hR)

theorem ELeCo.HasType.refine {Γ Γ' : Ctx s} {g : ELeCo s} {E E' : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᵉ g : E ≤ E') : Γ' ⊢ᵉ g : E ≤ E' := by
  match h with
  | .plain he => exact .plain (LeCo.HasType.refine hR he)
  | .pack hc he =>
      exact .pack (hc.refine hR) (LeCo.HasType.refine (hR.scopeInst _) he)
  | .cong hc he =>
      exact .cong (hc.refine hR) (LeCo.HasType.refine hR.scope he)
  | .trans hg hh => exact .trans (hg.refine hR) (hh.refine hR)

theorem EqCo.HasType.refine {Γ Γ' : Ctx s} {φ : EqCo s} {S T : Shape s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ φ : S ≡ T) : Γ' ⊢ φ : S ≡ T := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .def hd => exact .def (hR.def_ _ _ _ hd)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem Has.HasType.refine {Γ Γ' : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ hh : x ∋ l) : Γ' ⊢ hh : x ∋ l := by
  match h with
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .field hf hm => exact .field (hR.fields _ _ hf) hm

theorem Side.HasType.refine {Γ Γ' : Ctx s} {σ : Side s} {X Y : Shape (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Side.HasType Γ σ X Y) : Side.HasType Γ' σ X Y := by
  match h with
  | .none => exact .none
  | .some he => exact .some (he.refine hR)

theorem Morphism.HasType.refine {Γ Γ' : Ctx s} {src : Telescope (s,x)} {m : Morphism s}
    {Tel : Telescope (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ m : src ⇒ Tel := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost => exact .le (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .leEq hm hAt hpre hpost => exact .leEq (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.refine hR) hAt (hpre.refine hR) (hpost.refine hR)
  | .eq hm hAt => exact .eq (hm.refine hR) hAt
  | .eqSym hm hAt => exact .eqSym (hm.refine hR) hAt
  | .has hm hAt => exact .has (hm.refine hR) hAt
  | .bnd hm he => exact .bnd (hm.refine hR) (he.refine hR)
  | .leC hm hh hq hq' => exact .leC (hm.refine hR) hh (hq.refine hR) (hq'.refine hR)
  | .eqC hm hAt => exact .eqC (hm.refine hR) hAt
  | .eqSymC hm hAt => exact .eqSymC (hm.refine hR) hAt

theorem Atom.HasType.refine {Γ Γ' : Ctx s} {a : Atom s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ₐ a : T) : Γ' ⊢ₐ a : T := by
  match h with
  | @Atom.HasType.var _ _ x => rw [← hR.ty x]; exact .var
  | .cast ha he => exact .cast (ha.refine hR) (LeCo.HasType.refine hR he)
  | .unfoldSelf ha => exact .unfoldSelf (ha.refine hR)
  | .foldSelf ha => exact .foldSelf (ha.refine hR)
  | .both ha hb hr => exact .both (ha.refine hR) (hb.refine hR) hr
  | .recap ha hf => exact .recap (ha.refine hR) (hf.refine hR)

end

/-- The packed-atom wrapper premises only judgments of the block above. -/
theorem PAtom.HasType.refine {Γ Γ' : Ctx s} {p : PAtom s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ₚ p : E) : Γ' ⊢ₚ p : E := by
  match h with
  | .plain ha => exact .plain (Atom.HasType.refine hR ha)
  | .pack ha hc he =>
      exact .pack (Atom.HasType.refine hR ha) (CapCo.HasType.refine hR hc)
        (LeCo.HasType.refine (hR.scopeInst _) he)

mutual

theorem Tm.HasType.refine {Γ Γ' : Ctx s} {t : Tm s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ t :ᵉ E) : Γ' ⊢ t :ᵉ E := by
  match h with
  | .atom ha => exact .atom (PAtom.HasType.refine hR ha)
  | .val hv => exact .val (hv.refine hR)
  | .app ha hb => exact .app (ha.refine hR) (hb.refine hR)
  | .proj ha hh => exact .proj (ha.refine hR) (hh.refine hR)
  | .let ht hu hf =>
      exact .let (ht.refine hR) (hu.refine (hR.cons _)) (hf.refine (hR.cons _))
  | .cast ht he => exact .cast (ht.refine hR) (LeCo.HasType.refine hR he)
  | .castE ht hg => exact .castE (ht.refine hR) (ELeCo.HasType.refine hR hg)
  | .letex ht hc hu hf =>
      exact .letex (ht.refine hR) (hc.refine hR)
        (hu.refine ((hR.consC .star).cons _)) (hf.refine ((hR.consC .star).cons _))
  | .unbox ha hf => exact .unbox (ha.refine hR) (hf.refine hR)

theorem Value.HasType.refine {Γ Γ' : Ctx s} {v : Value s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᵥ v : T) : Γ' ⊢ᵥ v : T := by
  match h with
  | .lam ht hg => exact .lam (ht.refine (hR.body _)) (hg.refine (hR.body _))
  | .obj hF => exact .obj (hF.refine (hR.objBody _ _ _ _))
  | .box ha => exact .box (ha.refine hR)
  | .cast hv he => exact .cast (hv.refine hR) (LeCo.HasType.refine hR he)

theorem Value.HasTypeE.refine {Γ Γ' : Ctx s} {v : Value s} {E : ETy s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᵥᵉ v : E) : Γ' ⊢ᵥᵉ v : E := by
  match h with
  | .plain hv => exact .plain (hv.refine hR)
  | .pack hv hc he =>
      exact .pack (hv.refine hR) (hc.refine hR) (LeCo.HasType.refine (hR.scopeInst _) he)

theorem Fields.HasType.refine {Γ Γ' : Ctx (s,x)} {F : Fields (s,x)} {A : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶠ[A] F) : Γ' ⊢ᶠ[A] F := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg => exact .cons (hF.refine hR) (ht.refine hR) (hg.refine hR)

end

end FCdot

end Classifiers
