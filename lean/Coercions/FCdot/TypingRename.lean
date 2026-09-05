import Coercions.FCdot.Typing
import Coercions.FCdot.RenameLemmas

/-!
# Renaming of FCdot typing derivations

A *context renaming* `Ctx.Ren Γ ρ Γ'` says that `ρ` embeds `Γ` into `Γ'`:
types are transported by `ρ`, and definitions and field labels of
transparent binders survive.  Every typing family is closed under context
renamings; weakening is the special case `ρ = Rename.succ`.
-/

namespace FCdot

/-! ## Renaming of bindings -/

def Binding.rename : Binding s1 → Rename s1 s2 → Binding s2
  | .opaque T, ρ => .opaque (T.rename ρ)
  | .transparent T W Fs, ρ => .transparent (T.rename ρ) (W.rename ρ.lift) Fs

@[simp] theorem Binding.rename_opaque (T : Ty s1) (ρ : Rename s1 s2) :
    (Binding.opaque T).rename ρ = .opaque (T.rename ρ) := rfl

@[simp] theorem Binding.rename_transparent (T : Ty s1) (W : Witnesses (s1,x))
    (Fs : List Label) (ρ : Rename s1 s2) :
    (Binding.transparent T W Fs).rename ρ = .transparent (T.rename ρ) (W.rename ρ.lift) Fs := rfl

@[simp] theorem Binding.ty_rename (b : Binding s1) (ρ : Rename s1 s2) :
    (b.rename ρ).ty = b.ty.rename ρ := by
  cases b <;> rfl

/-! ## Auxiliary invariants -/

@[simp] theorem Fields.labels_rename {s1 s2 : Sig} :
    ∀ (F : Fields s1) (ρ : Rename s1 s2), (F.rename ρ).labels = F.labels
  | .nil, _ => rfl
  | .cons F l t, ρ => by
      simp [Fields.rename, Fields.labels, Fields.labels_rename F ρ]

/-! ## Context lookups, unfolded -/

@[simp] theorem Ctx.lookupTy_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lookupTy .here = b.ty↑ := rfl

@[simp] theorem Ctx.lookupTy_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).lookupTy (.there y) = (Γ.lookupTy y)↑ := rfl

@[simp] theorem Ctx.lookupDef_here_opaque (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.opaque T)).lookupDef .here l = none := rfl

@[simp] theorem Ctx.lookupDef_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Fs : List Label) (l : Label) :
    (Γ.cons (.transparent T W Fs)).lookupDef .here l = some (W.get l) := rfl

@[simp] theorem Ctx.lookupDef_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var)
    (l : Label) :
    (Γ.cons b).lookupDef (.there y) l = (Γ.lookupDef y l).map Ty.weaken := by
  cases b <;> rfl

@[simp] theorem Ctx.lookupFields_here_opaque (Γ : Ctx s) (T : Ty s) :
    (Γ.cons (.opaque T)).lookupFields .here = none := rfl

@[simp] theorem Ctx.lookupFields_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Fs : List Label) :
    (Γ.cons (.transparent T W Fs)).lookupFields .here = some Fs := rfl

@[simp] theorem Ctx.lookupFields_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).lookupFields (.there y) = Γ.lookupFields y := by
  cases b <;> rfl

/-! ## Transparency of a binder -/

theorem Ctx.isTransparent_iff {Γ : Ctx s} {x : BVar s .var} :
    Γ.IsTransparent x ↔ ∃ Fs, Γ.lookupFields x = some Fs := by
  unfold Ctx.IsTransparent
  cases h : Γ.lookupFields x with
  | none => simp
  | some Fs => simp

theorem Ctx.IsTransparent.of_lookup {Γ : Ctx s} {x : BVar s .var} {Fs : List Label}
    (h : Γ.lookupFields x = some Fs) : Γ.IsTransparent x :=
  Ctx.isTransparent_iff.mpr ⟨Fs, h⟩

@[simp] theorem Ctx.isTransparent_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).IsTransparent (.there y) ↔ Γ.IsTransparent y := by
  unfold Ctx.IsTransparent
  rw [Ctx.lookupFields_there]

@[simp] theorem Ctx.isTransparent_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Fs : List Label) :
    (Γ.cons (.transparent T W Fs)).IsTransparent .here := by
  unfold Ctx.IsTransparent
  simp

@[simp] theorem Ctx.not_isTransparent_here_opaque (Γ : Ctx s) (T : Ty s) :
    ¬ (Γ.cons (.opaque T)).IsTransparent .here := by
  unfold Ctx.IsTransparent
  simp

/-! ## Context renamings -/

/-- `Ctx.Ren Γ ρ Γ'`: `ρ` maps `Γ` into `Γ'`, transporting types by `ρ` and
preserving definitions and field labels of transparent binders. -/
structure Ctx.Ren {s1 s2 : Sig} (Γ : Ctx s1) (ρ : Rename s1 s2) (Γ' : Ctx s2) : Prop where
  ty : ∀ x, Γ'.lookupTy (ρ.var x) = (Γ.lookupTy x).rename ρ
  def_ : ∀ x l W, Γ.lookupDef x l = some W → Γ'.lookupDef (ρ.var x) l = some (W.rename ρ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (ρ.var x) = some Fs

namespace Ctx.Ren

theorem id {Γ : Ctx s} : Ctx.Ren Γ Rename.id Γ where
  ty := fun x => by simp
  def_ := fun x l W h => by simpa using h
  fields := fun x Fs h => h

theorem lift {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (b : Binding s1) :
    Ctx.Ren (Γ.cons b) ρ.lift (Γ'.cons (b.rename ρ)) where
  ty := by
    intro x
    cases x with
    | here =>
        show ((b.rename ρ).ty)↑ = ((b.ty)↑).rename ρ.lift
        rw [Binding.ty_rename, Ty.weaken_rename]
    | there y =>
        show (Γ'.lookupTy (ρ.var y))↑ = ((Γ.lookupTy y)↑).rename ρ.lift
        rw [h.ty y, Ty.weaken_rename]
  def_ := by
    intro x l W hW
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | transparent T W' Fs =>
            have hWe : W = W'.get l := by simpa using hW.symm
            subst hWe
            simp only [Rename.lift_here, Binding.rename_transparent,
              Ctx.lookupDef_here_transparent, Witnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        rw [Rename.lift_there, Ctx.lookupDef_there]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Ty.weaken_rename]
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Fs' => simpa using hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs

theorem transparent {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2} (h : Ctx.Ren Γ ρ Γ')
    {x : BVar s1 .var} (ht : Γ.IsTransparent x) : Γ'.IsTransparent (ρ.var x) := by
  obtain ⟨Fs, hFs⟩ := Ctx.isTransparent_iff.mp ht
  exact Ctx.IsTransparent.of_lookup (h.fields x Fs hFs)

theorem succ {Γ : Ctx s} (b : Binding s) : Ctx.Ren Γ Rename.succ (Γ.cons b) where
  ty := fun x => rfl
  def_ := fun x l W hd => by
    rw [Rename.succ_var, Ctx.lookupDef_there, hd]
    rfl
  fields := fun x Fs hf => by
    rw [Rename.succ_var, Ctx.lookupFields_there]
    exact hf

end Ctx.Ren

/-! ## Evidence and atoms -/

mutual

theorem LeCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {e : LeCo s1} {S T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ e : S ≤ T) :
    Γ' ⊢ (e.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.rename hρ) (hf.rename hρ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.rename hρ)
  | .pi he hf =>
      exact .pi (he.rename hρ) (hf.rename (hρ.lift _))
  | .obj hm => exact .obj (hm.rename hρ)
  | .pair he hf =>
      have := LeCo.HasType.pair (he.rename hρ) (hf.rename hρ)
      simpa [LeCo.rename, Ty.rename, Telescope.append_rename] using this
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := LeCo.HasType.member (a := a.rename ρ) (ha.rename hρ)
        (he.rename hρ) (hAt.rename ρ.lift)
      simpa [LeCo.rename, Ty.substVar_rename, Atom.root_rename] using this

theorem EqCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.rename ρ) : (S.rename ρ) ≡ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.rename hρ)
  | .trans hφ hψ => exact .trans (hφ.rename hρ) (hψ.rename hρ)
  | .def hd => exact .def (hρ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.rename ρ) (ha.rename hρ)
        (he.rename hρ) (hAt.rename ρ.lift)
      simpa [EqCo.rename, Ty.substVar_rename, Atom.root_rename] using this

theorem Has.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.rename ρ) : (ρ.var x) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.rename ρ) (ha.rename hρ)
        (he.rename hρ) (hAt.rename ρ.lift)
      simpa [Has.rename, Atom.root_rename] using this
  | .field hf hm => exact .field (hρ.fields _ _ hf) hm

theorem Side.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {σ : Side s1} {X Y : Ty (s1,x)} (hρ : Ctx.Ren Γ ρ Γ') (h : Side.HasType Γ σ X Y) :
    Side.HasType Γ' (σ.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .none => exact .none
  | .some he =>
      have := Side.HasType.some (he.rename hρ)
      simpa [Side.rename, Ty.weaken_rename] using this

theorem Morphism.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.rename ρ) : (src.rename ρ.lift) ⇒ (Tel.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.rename hρ) (hpost.rename hρ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.rename hρ) (hpost.rename hρ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.rename hρ) (hpost.rename hρ)
  | .eq hm hAt =>
      exact .eq (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .eqSym hm hAt =>
      exact .eqSym (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .has hm hAt =>
      exact .has (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)

theorem Atom.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.rename ρ) : (T.rename ρ) := by
  match h with
  | @Atom.HasType.var _ _ x =>
      rw [← hρ.ty x]
      exact .var
  | .cast ha he => exact .cast (ha.rename hρ) (he.rename hρ)
  | @Atom.HasType.unfoldSelf _ _ a Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (by simpa [Ty.rename] using ha.rename hρ)
      simpa [Atom.rename, Ty.rename, Atom.root_rename, Telescope.weaken_rename,
        Telescope.substVar_rename] using this
  | @Atom.HasType.foldSelf _ _ a Tel ha =>
      have ha' := ha.rename hρ
      simp only [Ty.rename, Telescope.weaken_rename, Telescope.substVar_rename] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (by simpa [Atom.root_rename] using ha')
      simpa [Atom.rename, Ty.rename] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (ha.rename hρ) (hb.rename hρ)
        (by simp [Atom.root_rename, hr])
      simpa [Atom.rename, Ty.rename, Telescope.append_rename] using this

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {t : Tm s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ t : T) :
    Γ' ⊢ (t.rename ρ) : (T.rename ρ) := by
  match h with
  | .atom ha => exact .atom (ha.rename hρ)
  | .val hv => exact .val (hv.rename hρ)
  | @Tm.HasType.app _ _ a S T b ha hb =>
      have := Tm.HasType.app (b := b.rename ρ)
        (by simpa [Ty.rename] using ha.rename hρ) (hb.rename hρ)
      simpa [Tm.rename, Ty.substVar_rename, Atom.root_rename] using this
  | @Tm.HasType.proj _ _ a S hh l ha hhh =>
      have := Tm.HasType.proj (a := a.rename ρ) (ha.rename hρ)
        (by simpa [Atom.root_rename] using hhh.rename hρ)
      simpa [Tm.rename, Ty.rename, Atom.root_rename] using this
  | .let ht hu =>
      refine .let (ht.rename hρ) ?_
      have := hu.rename (hρ.lift _)
      simpa [Ty.weaken_rename] using this
  | .cast ht he => exact .cast (ht.rename hρ) (he.rename hρ)

theorem Value.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {v : Value s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.rename ρ) : (T.rename ρ) := by
  match h with
  | .lam ht => exact .lam (ht.rename (hρ.lift _))
  | @Value.HasType.obj _ F0 _ W0 hF =>
      have hF' := Fields.HasType.rename (hρ.lift _) hF
      have := Value.HasType.obj (Γ := Γ') (W := W0.rename ρ.lift) (F := F0.rename ρ.lift)
        (by simpa [Binding.rename, Ty.rename, Telescope.ofLiteral_rename] using hF')
      simpa [Value.rename, Ty.rename, Telescope.ofLiteral_rename] using this
  | .cast hv he => exact .cast (hv.rename hρ) (he.rename hρ)

theorem Fields.HasType.rename {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {ρ : Rename s1 s2} {F : Fields (s1,x)}
    (hρ : Ctx.Ren Γ ρ.lift Γ') (h : Γ ⊢ᶠ F) :
    Γ' ⊢ᶠ (F.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht =>
      refine .cons (hF.rename hρ) ?_
      have := ht.rename hρ
      simpa [Ty.rename] using this

end

/-! ## Weakening -/

theorem LeCo.HasType.weaken {Γ : Ctx s} {e : LeCo s} {S T : Ty s}
    (h : Γ ⊢ e : S ≤ T) (b : Binding s) :
    (Γ.cons b) ⊢ e↑ : S↑ ≤ T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem EqCo.HasType.weaken {Γ : Ctx s} {φ : EqCo s} {S T : Ty s}
    (h : Γ ⊢ φ : S ≡ T) (b : Binding s) :
    (Γ.cons b) ⊢ (φ.rename Rename.succ) : S↑ ≡ T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Has.HasType.weaken {Γ : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (h : Γ ⊢ hh : x ∋ l) (b : Binding s) :
    Γ.cons b ⊢ hh.rename Rename.succ : (.there x) ∋ l :=
  h.rename (Ctx.Ren.succ b)

theorem Side.HasType.weaken {Γ : Ctx s} {σ : Side s} {X Y : Ty (s,x)}
    (h : Side.HasType Γ σ X Y) (b : Binding s) :
    Side.HasType (Γ.cons b) (σ.rename Rename.succ) (X.rename Rename.succ.lift)
      (Y.rename Rename.succ.lift) :=
  h.rename (Ctx.Ren.succ b)

theorem Morphism.HasType.weaken {Γ : Ctx s} {m : Morphism s} {src Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) (b : Binding s) :
    (Γ.cons b) ⊢ m.rename Rename.succ : src.rename Rename.succ.lift ⇒ Tel.rename Rename.succ.lift :=
  h.rename (Ctx.Ren.succ b)

theorem Atom.HasType.weaken {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T) (b : Binding s) :
    (Γ.cons b) ⊢ₐ a↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Tm.HasType.weaken {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T) (b : Binding s) :
    (Γ.cons b) ⊢ t↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Value.HasType.weaken {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (b : Binding s) :
    (Γ.cons b) ⊢ᵥ v↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

end FCdot
