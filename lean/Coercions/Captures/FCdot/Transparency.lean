import Coercions.Captures.FCdot.TypingRename

namespace Captures

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

namespace Ctx.Refines

theorem refl {Γ : Ctx s} : Ctx.Refines Γ Γ where
  ty := fun _ => rfl
  def_ := fun _ _ _ h => h
  defC := fun _ _ _ h => h
  fields := fun _ _ h => h

theorem trans {Γ1 Γ2 Γ3 : Ctx s} (h1 : Ctx.Refines Γ1 Γ2) (h2 : Ctx.Refines Γ2 Γ3) :
    Ctx.Refines Γ1 Γ3 where
  ty := fun x => (h2.ty x).trans (h1.ty x)
  def_ := fun x l W h => h2.def_ x l W (h1.def_ x l W h)
  defC := fun x l C h => h2.defC x l C (h1.defC x l C h)
  fields := fun x Fs h => h2.fields x Fs (h1.fields x Fs h)

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

end Ctx.Refines

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

theorem CapEq.HasType.refine {Γ Γ' : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) : Γ' ⊢ᶜ φ : C ≡ D := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .defC hd => exact .defC (hR.defC _ _ _ hd)
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
      exact .pi (LeCo.HasType.refine hR he) (LeCo.HasType.refine (hR.cons _) hf)
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

mutual

theorem Tm.HasType.refine {Γ Γ' : Ctx s} {t : Tm s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ t : T) : Γ' ⊢ t : T := by
  match h with
  | .atom ha => exact .atom (ha.refine hR)
  | .val hv => exact .val (hv.refine hR)
  | .app ha hb => exact .app (ha.refine hR) (hb.refine hR)
  | .proj ha hh => exact .proj (ha.refine hR) (hh.refine hR)
  | .let ht hu => exact .let (ht.refine hR) (hu.refine (hR.cons _))
  | .cast ht he => exact .cast (ht.refine hR) (LeCo.HasType.refine hR he)
  | .unbox ha hf => exact .unbox (ha.refine hR) (hf.refine hR)

theorem Value.HasType.refine {Γ Γ' : Ctx s} {v : Value s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᵥ v : T) : Γ' ⊢ᵥ v : T := by
  match h with
  | .lam ht => exact .lam (ht.refine (hR.cons _))
  | .obj hF => exact .obj (hF.refine (hR.cons _))
  | .box ha => exact .box (ha.refine hR)
  | .cast hv he => exact .cast (hv.refine hR) (LeCo.HasType.refine hR he)

theorem Fields.HasType.refine {Γ Γ' : Ctx (s,x)} {F : Fields (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Γ ⊢ᶠ F) : Γ' ⊢ᶠ F := by
  match h with
  | .nil => exact .nil
  | .cons hF ht => exact .cons (hF.refine hR) (ht.refine hR)

end

end FCdot

end Captures
