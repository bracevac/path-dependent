import Coercions.PDot.FCp.TypingSubst

/-!
# Refining a context (plan X2, group g3)

`Γ.Refines Γ'` says that `Γ'` keeps the type of every variable of `Γ` and every definition `Γ`
reads.  An opaque binder refines to a transparent one at the same type, since an opaque binder
defines nothing (`Ctx.Refines.here`).  This is what `MS-LetVal` needs: the frame typed its body at
an opaque binder, and the store binds the literal transparent.

A refinement is a typed substitution at `CoSubst.id` (`Ctx.Refines.typed`, decision D15 of the
groups file).  So the monotonicity of every judgment is its substitution lemma at the identity,
read back by `F.subst_id`, `CoSubst.id_paths`, `F.subst_ofRename` and `F.rename_id`, and under the
self of `Morphism`, `Side` and `Defs` by `PathSubst.lift_ofRename` and `Rename.lift_id`.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

structure Ctx.Refines (Γ Γ' : Ctx s) : Prop where
  ty : ∀ x, Γ'.ty x = Γ.ty x
  defAt : ∀ p A W, Γ.defAt p A = some W → Γ'.defAt p A = some W

/-- Two contexts that bind the newest variable alike read the same node at every path rooted at
it. -/
theorem Ctx.nodeAt_cons_here {Γ Γ' : Ctx s} (b : Binding s) :
    ∀ (p : Path (s,x)), p.root = .here → (Γ'.cons b).nodeAt p = (Γ.cons b).nodeAt p
  | .var .here, _ => by cases b <;> rfl
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      show ((Γ'.cons b).nodeAt p).bind (·.child a) = ((Γ.cons b).nodeAt p).bind (·.child a)
      rw [Ctx.nodeAt_cons_here (Γ := Γ) (Γ' := Γ') b p h]

theorem Ctx.Refines.refl (Γ : Ctx s) : Γ.Refines Γ where
  ty := fun _ => rfl
  defAt := fun _ _ _ h => h

theorem Ctx.Refines.here (Γ : Ctx s) (T : Ty s) (B : Block (s,x)) : (Γ.cons (.opaque T)).Refines (Γ.cons (.transparent T B)) where
  ty := fun x => by cases x <;> rfl
  defAt := fun _ _ _ h => Ctx.defAt_opaque_cons h

theorem Ctx.Refines.cons {Γ Γ' : Ctx s} (h : Γ.Refines Γ') (b : Binding s) : (Γ.cons b).Refines (Γ'.cons b) where
  ty := fun
    | .here => rfl
    | .there y => by
        show (Γ'.ty y).weaken = (Γ.ty y).weaken
        rw [h.ty y]
  defAt := fun p A W hW => by
    rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
    · have e : (Γ'.cons b).nodeAt p = (Γ.cons b).nodeAt p := Ctx.nodeAt_cons_here b p hr
      show ((Γ'.cons b).nodeAt p).bind (·.def A) = some W
      rw [e]
      exact hW
    · obtain ⟨W₀, e₀, rfl⟩ := Ctx.defAt_weaken_some hW
      show (Γ'.cons b).defAt (p₀.rename Rename.succ) A = some (W₀.rename Rename.succ)
      rw [Ctx.defAt_weaken, h.defAt p₀ A W₀ e₀]
      rfl

theorem Ctx.Refines.typed {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : CoSubst.Typed Γ CoSubst.id Γ' where
  var := fun x => .var (by
    rw [CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id]
    exact h.ty x)
  defAt := fun p A W hW => by
    rw [CoSubst.id_paths, Path.subst_ofRename, Path.rename_id, Ty.subst_ofRename, Ty.rename_id]
    exact h.defAt p A W hW

/-! ## Monotonicity of every judgment -/

theorem PEq.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : PEq.HasType Γ π p q → PEq.HasType Γ' π p q := by
  intro hπ
  have h' := PEq.HasType.subst h.typed hπ
  simp only [PEq.subst_id, CoSubst.id_paths, Path.subst_ofRename, Path.rename_id] at h'
  exact h'
theorem PathCo.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : PathCo.HasType Γ P T → PathCo.HasType Γ' P T := by
  intro hP
  have h' := PathCo.HasType.subst h.typed hP
  simp only [PathCo.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'
theorem LeCo.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : LeCo.HasType Γ e S T → LeCo.HasType Γ' e S T := by
  intro he
  have h' := LeCo.HasType.subst h.typed he
  simp only [LeCo.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'
theorem EqCo.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : EqCo.HasType Γ φ S T → EqCo.HasType Γ' φ S T := by
  intro hφ
  have h' := EqCo.HasType.subst h.typed hφ
  simp only [EqCo.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'
theorem Morphism.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Morphism.HasType Γ src m Tel → Morphism.HasType Γ' src m Tel := by
  intro hm
  have h' := Morphism.HasType.subst h.typed hm
  simp only [Morphism.subst_id, CoSubst.id_paths, PathSubst.lift_ofRename, Telescope.subst_ofRename,
    Rename.lift_id, Telescope.rename_id] at h'
  exact h'
theorem Side.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Side.HasType Γ sd X Y → Side.HasType Γ' sd X Y := by
  intro hsd
  have h' := Side.HasType.subst h.typed hsd
  simp only [Side.subst_id, CoSubst.id_paths, PathSubst.lift_ofRename, Ty.subst_ofRename,
    Rename.lift_id, Ty.rename_id] at h'
  exact h'
theorem Tm.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Tm.HasType Γ t T → Tm.HasType Γ' t T := by
  intro ht
  have h' := Tm.HasType.subst h.typed ht
  simp only [Tm.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'
theorem Value.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Value.HasType Γ v T → Value.HasType Γ' v T := by
  intro hv
  have h' := Value.HasType.subst h.typed hv
  simp only [Value.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'
theorem Defs.HasType.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Defs.HasType Γ p ds Tel → Defs.HasType Γ' p ds Tel := by
  intro hds
  have h' := Defs.HasType.subst h.typed hds
  simp only [Defs.subst_id, CoSubst.id_paths, Path.subst_ofRename, Path.rename_id,
    PathSubst.lift_ofRename, Telescope.subst_ofRename, Rename.lift_id, Telescope.rename_id] at h'
  exact h'
theorem Cont.Typed.refines {Γ Γ' : Ctx s} (h : Γ.Refines Γ') : Cont.Typed Γ K T U → Cont.Typed Γ' K T U := by
  intro hK
  have h' := Cont.Typed.subst h.typed hK
  simp only [Cont.subst_id, CoSubst.id_paths, Ty.subst_ofRename, Ty.rename_id] at h'
  exact h'

end PDot.FCp
