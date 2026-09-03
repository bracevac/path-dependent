import Coercions.FCdot.CanonicalTyped
import Coercions.FCdot.TypingRename
import Coercions.FCdot.TypingSubst

/-!
# Environments: closing substitutions and extension

An environment `η : Env s s'` closes the open scope `s'` into the store
scope `s`.  Extending an environment by a typed atom with a typed view
extends the canonical closing of the open context by an opaque binder.
-/

namespace FCdot

namespace Env

@[simp] theorem toSubst_var (η : Env s s') (y : BVar s' .var) : η.toSubst.var y = η.atom y := rfl

@[simp] theorem atom_cons_here (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).atom .here = a := rfl
@[simp] theorem atom_cons_there (η : Env s s') (a : Atom s) (V : View s) (y : BVar s' .var) :
    (η.cons a V).atom (.there y) = η.atom y := rfl
@[simp] theorem view_cons_here (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).view .here = V := rfl
@[simp] theorem view_cons_there (η : Env s s') (a : Atom s) (V : View s) (y : BVar s' .var) :
    (η.cons a V).view (.there y) = η.view y := rfl

/-- The root renaming of an extended environment. -/
theorem toSubst_cons_root (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).toSubst.root = η.toSubst.root.lift.comp (Rename.subst a.root) := by
  apply Rename.funext'
  intro k y
  cases k
  cases y <;> rfl

/-- Closing a weakened type under an extended environment closes the type
under the environment. -/
theorem weaken_rename_cons_root (η : Env s s') (a : Atom s) (V : View s) (T : Ty s') :
    (T.weaken (k := .var)).rename (η.cons a V).toSubst.root = T.rename η.toSubst.root := by
  rw [toSubst_cons_root, Ty.weaken, Ty.rename_comp, ← Rename.comp_assoc, Rename.succ_lift,
    Rename.comp_assoc, Rename.succ_subst, Rename.comp_id]

theorem cons_root_there (η : Env s s') (a : Atom s) (V : View s) (y : BVar s' .var) :
    (η.cons a V).toSubst.root.var (.there y) = η.toSubst.root.var y := rfl

end Env

section

variable {σ : Store s} {Γ : Ctx s}

/-- The closing substitution of a canonical environment is typed. -/
theorem EnvCanon.typed {k : Nat} {η : Env s s'} {Δ : Ctx s'} (h : EnvCanon σ Γ k η Δ) :
    Subst.Typed Δ η.toSubst Γ := h.1

/-- Closing atoms are typed at the closed binder types. -/
theorem EnvCanon.atom {k : Nat} {η : Env s s'} {Δ : Ctx s'} (h : EnvCanon σ Γ k η Δ)
    (y : BVar s' .var) :
    Atom.HasType Γ (η.atom y) ((Δ.lookupTy y).rename η.toSubst.root) := h.1.var y

/-- Stored views are typed. -/
theorem EnvCanon.view {k : Nat} {η : Env s s'} {Δ : Ctx s'} (h : EnvCanon σ Γ k η Δ)
    (y : BVar s' .var) {Tel : Telescope (s,x)}
    (hres : Γ.resolve ((Δ.lookupTy y).rename η.toSubst.root) = .obj Tel) :
    ViewTyped σ Γ k (η.view y) Tel (η.atom y) := h.2.1 y Tel hres

/-- No closing atom is absurd. -/
theorem EnvCanon.notBot {k : Nat} {η : Env s s'} {Δ : Ctx s'} (h : EnvCanon σ Γ k η Δ)
    (y : BVar s' .var) : Γ.resolve ((Δ.lookupTy y).rename η.toSubst.root) ≠ .bot := h.2.2 y

/-- Extending a canonical environment by a typed atom with a typed view
closes the context extended by an opaque binder. -/
theorem EnvCanon.cons {k : Nat} {η : Env s s'} {Δ : Ctx s'} (h : EnvCanon σ Γ k η Δ)
    {T : Ty s'} {a : Atom s} {V : View s}
    (ha : Atom.HasType Γ a (T.rename η.toSubst.root))
    (hV : ∀ Tel : Telescope (s,x), Γ.resolve (T.rename η.toSubst.root) = .obj Tel →
      ViewTyped σ Γ k V Tel a)
    (hnb : Γ.resolve (T.rename η.toSubst.root) ≠ .bot) :
    EnvCanon σ Γ k (η.cons a V) (Δ.cons (.opaque T)) := by
  obtain ⟨hS, hviews, hnbs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y
      cases y with
      | here =>
          simpa [Env.weaken_rename_cons_root] using ha
      | there y =>
          have := hS.var y
          simpa [Env.weaken_rename_cons_root, Env.cons_root_there] using this
    · intro y hy
      cases y with
      | here => exact absurd hy (Ctx.not_isTransparent_here_opaque (Γ := Δ) T)
      | there y =>
          have hy' : Δ.IsTransparent y := by simpa using hy
          have := hS.ty y hy'
          simpa [Env.weaken_rename_cons_root, Env.cons_root_there] using this
    · intro y hy
      cases y with
      | here => exact absurd hy (Ctx.not_isTransparent_here_opaque (Γ := Δ) T)
      | there y =>
          have hy' : Δ.IsTransparent y := by simpa using hy
          simpa [Env.cons_root_there] using hS.transparent y hy'
    · intro y l W hW
      cases y with
      | here => simp at hW
      | there y =>
          simp only [Ctx.lookupDef_there, Option.map_eq_some_iff] at hW
          obtain ⟨W', hW', rfl⟩ := hW
          have := hS.def_ y l W' hW'
          simpa [Env.weaken_rename_cons_root, Env.cons_root_there] using this
    · intro y Fs hFs
      cases y with
      | here => simp at hFs
      | there y =>
          simp only [Ctx.lookupFields_there] at hFs
          simpa [Env.cons_root_there] using hS.fields y Fs hFs
  · intro y Tel hres
    cases y with
    | here =>
        simp only [Env.atom_cons_here, Env.view_cons_here]
        apply hV
        simpa [Env.weaken_rename_cons_root] using hres
    | there y =>
        simp only [Env.atom_cons_there, Env.view_cons_there]
        apply hviews
        simpa [Env.weaken_rename_cons_root, Env.cons_root_there] using hres
  · intro y
    cases y with
    | here => simpa [Env.weaken_rename_cons_root] using hnb
    | there y =>
        have := hnbs y
        simpa [Env.weaken_rename_cons_root, Env.cons_root_there] using this

end

end FCdot
