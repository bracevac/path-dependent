import Coercions.FCdot.TypingRename

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
  def_ : ∀ x l W, Γ.lookupDef x l = some W → Γ'.lookupDef x l = some W
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields x = some Fs

namespace Ctx.Refines

theorem refl {Γ : Ctx s} : Ctx.Refines Γ Γ where
  ty := fun _ => rfl
  def_ := fun _ _ _ h => h
  fields := fun _ _ h => h

theorem trans {Γ1 Γ2 Γ3 : Ctx s} (h1 : Ctx.Refines Γ1 Γ2) (h2 : Ctx.Refines Γ2 Γ3) :
    Ctx.Refines Γ1 Γ3 where
  ty := fun x => (h2.ty x).trans (h1.ty x)
  def_ := fun x l W h => h2.def_ x l W (h1.def_ x l W h)
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
        | transparent T W' Fs => exact hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW ⊢
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0.weaken := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            rfl
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Fs' => exact hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs ⊢
        exact h.fields y Fs hFs

/-- Weakening an opaque binder to the transparent binder of the same type. -/
theorem transparent {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)} {Fs : List Label} :
    Ctx.Refines (Γ.cons (.opaque T)) (Γ.cons (.transparent T W Fs)) where
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
  fields := by
    intro x Fs' hFs
    cases x with
    | here => simp at hFs
    | there y => rw [Ctx.lookupFields_there] at hFs ⊢; exact hFs

theorem transparentOf {Γ Γ' : Ctx s} (h : Ctx.Refines Γ Γ') {x : BVar s .var}
    (ht : Γ.IsTransparent x) : Γ'.IsTransparent x := by
  obtain ⟨Fs, hFs⟩ := Ctx.isTransparent_iff.mp ht
  exact Ctx.IsTransparent.of_lookup (h.fields x Fs hFs)

end Ctx.Refines

/-! ## Monotonicity of the typing families -/

mutual

theorem LeCo.HasType.refine {Γ Γ' : Ctx s} {e : LeCo s} {S T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : LeCo.HasType Γ e S T) : LeCo.HasType Γ' e S T := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.refine hR) (hf.refine hR)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.refine hR)
  | .pi he hf => exact .pi (he.refine hR) (hf.refine (hR.cons _))
  | .obj hm => exact .obj (hm.refine (hR.cons _))
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem EqCo.HasType.refine {Γ Γ' : Ctx s} {φ : EqCo s} {S T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : EqCo.HasType Γ φ S T) : EqCo.HasType Γ' φ S T := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.refine hR)
  | .trans hφ hψ => exact .trans (hφ.refine hR) (hψ.refine hR)
  | .def hd => exact .def (hR.def_ _ _ _ hd)
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt

theorem Has.HasType.refine {Γ Γ' : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (hR : Ctx.Refines Γ Γ') (h : Has.HasType Γ hh x l) : Has.HasType Γ' hh x l := by
  match h with
  | .member ha he hAt => exact .member (ha.refine hR) (he.refine hR) hAt
  | .field hf hm => exact .field (hR.fields _ _ hf) hm

theorem Morphism.HasType.refine {Γ Γ' : Ctx (s,x)} {m : Morphism (s,x)}
    {Tel : Telescope (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Morphism.HasType Γ m Tel) : Morphism.HasType Γ' m Tel := by
  match h with
  | .nil => exact .nil
  | .le hm he => exact .le (hm.refine hR) (he.refine hR)
  | .eq hm hφ => exact .eq (hm.refine hR) (hφ.refine hR)
  | .has hm hh => exact .has (hm.refine hR) (hh.refine hR)

theorem Atom.HasType.refine {Γ Γ' : Ctx s} {a : Atom s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Atom.HasType Γ a T) : Atom.HasType Γ' a T := by
  match h with
  | @Atom.HasType.var _ _ x => rw [← hR.ty x]; exact .var
  | .cast ha he => exact .cast (ha.refine hR) (he.refine hR)
  | .unfoldSelf ha => exact .unfoldSelf (ha.refine hR)
  | .foldSelf ha => exact .foldSelf (ha.refine hR)

end

mutual

theorem Tm.HasType.refine {Γ Γ' : Ctx s} {t : Tm s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Tm.HasType Γ t T) : Tm.HasType Γ' t T := by
  match h with
  | .atom ha => exact .atom (ha.refine hR)
  | .val hv => exact .val (hv.refine hR)
  | .app ha hb => exact .app (ha.refine hR) (hb.refine hR)
  | .proj ha hh => exact .proj (ha.refine hR) (hh.refine hR)
  | .let ht hu => exact .let (ht.refine hR) (hu.refine (hR.cons _))
  | .cast ht he => exact .cast (ht.refine hR) (he.refine hR)

theorem Value.HasType.refine {Γ Γ' : Ctx s} {v : Value s} {T : Ty s}
    (hR : Ctx.Refines Γ Γ') (h : Value.HasType Γ v T) : Value.HasType Γ' v T := by
  match h with
  | .lam ht => exact .lam (ht.refine (hR.cons _))
  | .obj hG hE hF => exact .obj hG (hE.refine (hR.cons _)) (hF.refine (hR.cons _))
  | .cast hv he => exact .cast (hv.refine hR) (he.refine hR)

theorem Fields.HasType.refine {Γ Γ' : Ctx (s,x)} {F : Fields (s,x)}
    (hR : Ctx.Refines Γ Γ') (h : Fields.HasType Γ F) : Fields.HasType Γ' F := by
  match h with
  | .nil => exact .nil
  | .cons hF ht => exact .cons (hF.refine hR) (ht.refine hR)

end

end FCdot
