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

theorem Ty.isSelfName_rename_lift {s1 s2 : Sig} :
    ∀ (T : Ty (s1,x)) (ρ : Rename s1 s2), (T.rename ρ.lift).isSelfName = T.isSelfName
  | .top, _ => rfl
  | .bot, _ => rfl
  | .pi _ _, _ => rfl
  | .obj _, _ => rfl
  | .sel .here _, _ => rfl
  | .sel (.there _) _, _ => rfl

theorem Witnesses.all_isSelfName_rename {s1 s2 : Sig} :
    ∀ (W : Witnesses (s1,x)) (ρ : Rename s1 s2),
      (W.rename ρ.lift).all (fun T => !T.isSelfName) = W.all (fun T => !T.isSelfName)
  | .nil, _ => rfl
  | .cons W l T, ρ => by
      simp [Witnesses.rename, Witnesses.all, Ty.isSelfName_rename_lift T ρ,
        Witnesses.all_isSelfName_rename W ρ]

theorem Witnesses.Guarded.rename {W : Witnesses (s1,x)} (ρ : Rename s1 s2)
    (h : W.Guarded) : (W.rename ρ.lift).Guarded := by
  unfold Witnesses.Guarded at h ⊢
  rw [Witnesses.all_isSelfName_rename W ρ]
  exact h

/-! ## Context lookups, unfolded -/

@[simp] theorem Ctx.lookupTy_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lookupTy .here = b.ty.weaken := rfl

@[simp] theorem Ctx.lookupTy_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).lookupTy (.there y) = (Γ.lookupTy y).weaken := rfl

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
        show ((b.rename ρ).ty).weaken = ((b.ty).weaken).rename ρ.lift
        rw [Binding.ty_rename, Ty.weaken_rename]
    | there y =>
        show (Γ'.lookupTy (ρ.var y)).weaken = ((Γ.lookupTy y).weaken).rename ρ.lift
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
            have hWe : W = W0.weaken := by simpa using hW.symm
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
    {e : LeCo s1} {S T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : LeCo.HasType Γ e S T) :
    LeCo.HasType Γ' (e.rename ρ) (S.rename ρ) (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.rename hρ) (hf.rename hρ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.rename hρ)
  | .pi he hf =>
      exact .pi (he.rename hρ) (hf.rename (hρ.lift _))
  | @LeCo.HasType.obj _ _ Tel m Tel' hm =>
      have := LeCo.HasType.obj (Morphism.HasType.rename hρ hm)
      simpa [LeCo.rename, Ty.rename, Telescope.weaken_rename] using this
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := LeCo.HasType.member (a := a.rename ρ) (ha.rename hρ)
        (he.rename hρ) (hAt.rename ρ.lift)
      simpa [LeCo.rename, Ty.substVar_rename, Atom.root_rename] using this

theorem EqCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : EqCo.HasType Γ φ S T) :
    EqCo.HasType Γ' (φ.rename ρ) (S.rename ρ) (T.rename ρ) := by
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
    (hρ : Ctx.Ren Γ ρ Γ') (h : Has.HasType Γ hh x l) :
    Has.HasType Γ' (hh.rename ρ) (ρ.var x) l := by
  match h with
  | @Has.HasType.member _ _ a S e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.rename ρ) (ha.rename hρ)
        (he.rename hρ) (hAt.rename ρ.lift)
      simpa [Has.rename, Atom.root_rename] using this
  | .field hf hm => exact .field (hρ.fields _ _ hf) hm

theorem Morphism.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope s1} {m : Morphism s1} {Tel : Telescope s1}
    (hρ : Ctx.Ren Γ ρ Γ') (h : Morphism.HasType Γ src m Tel) :
    Morphism.HasType Γ' (src.rename ρ) (m.rename ρ) (Tel.rename ρ) := by
  match h with
  | .nil => exact .nil
  | .le hm he => exact .le (hm.rename hρ) (he.rename hρ)
  | .eq hm hφ => exact .eq (hm.rename hρ) (hφ.rename hρ)
  | @Morphism.HasType.has _ _ _ _ _ j l hm hAt =>
      exact .has (hm.rename hρ) (by simpa [Proposition.rename] using hAt.rename ρ)

theorem Atom.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Atom.HasType Γ a T) :
    Atom.HasType Γ' (a.rename ρ) (T.rename ρ) := by
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

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {t : Tm s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Tm.HasType Γ t T) :
    Tm.HasType Γ' (t.rename ρ) (T.rename ρ) := by
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
    {v : Value s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Value.HasType Γ v T) :
    Value.HasType Γ' (v.rename ρ) (T.rename ρ) := by
  match h with
  | .lam ht => exact .lam (ht.rename (hρ.lift _))
  | @Value.HasType.obj _ F0 _ W0 hG hF =>
      have hF' := Fields.HasType.rename (hρ.lift _) hF
      have := Value.HasType.obj (Γ := Γ') (W := W0.rename ρ.lift) (F := F0.rename ρ.lift)
        (Witnesses.Guarded.rename ρ hG)
        (by simpa [Binding.rename, Ty.rename, Telescope.ofLiteral_rename] using hF')
      simpa [Value.rename, Ty.rename, Telescope.ofLiteral_rename] using this
  | .cast hv he => exact .cast (hv.rename hρ) (he.rename hρ)

theorem Fields.HasType.rename {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {ρ : Rename s1 s2} {F : Fields (s1,x)}
    (hρ : Ctx.Ren Γ ρ.lift Γ') (h : Fields.HasType Γ F) :
    Fields.HasType Γ' (F.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht =>
      refine .cons (hF.rename hρ) ?_
      have := ht.rename hρ
      simpa [Ty.rename] using this

end

/-! ## Weakening -/

theorem LeCo.HasType.weaken {Γ : Ctx s} {e : LeCo s} {S T : Ty s}
    (h : LeCo.HasType Γ e S T) (b : Binding s) :
    LeCo.HasType (Γ.cons b) e.weaken S.weaken T.weaken :=
  h.rename (Ctx.Ren.succ b)

theorem EqCo.HasType.weaken {Γ : Ctx s} {φ : EqCo s} {S T : Ty s}
    (h : EqCo.HasType Γ φ S T) (b : Binding s) :
    EqCo.HasType (Γ.cons b) (φ.rename Rename.succ) S.weaken T.weaken :=
  h.rename (Ctx.Ren.succ b)

theorem Has.HasType.weaken {Γ : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (h : Has.HasType Γ hh x l) (b : Binding s) :
    Has.HasType (Γ.cons b) (hh.rename Rename.succ) (.there x) l :=
  h.rename (Ctx.Ren.succ b)

theorem Atom.HasType.weaken {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Atom.HasType Γ a T) (b : Binding s) :
    Atom.HasType (Γ.cons b) a.weaken T.weaken :=
  h.rename (Ctx.Ren.succ b)

theorem Tm.HasType.weaken {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Tm.HasType Γ t T) (b : Binding s) :
    Tm.HasType (Γ.cons b) t.weaken T.weaken :=
  h.rename (Ctx.Ren.succ b)

theorem Value.HasType.weaken {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Value.HasType Γ v T) (b : Binding s) :
    Value.HasType (Γ.cons b) v.weaken T.weaken :=
  h.rename (Ctx.Ren.succ b)

end FCdot
