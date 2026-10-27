import Coercions.PDot.FCp.Machine

/-!
# FCp typing under renaming (plan X2, group g3)

A renaming `ρ` is typed from `Γ₁` to `Γ₂` when it keeps the type of every variable and every
definition the context reads.  Then every judgment of T.3 renames.  The evidence judgments are one
mutual recursion, the term judgments another, and continuation typing a third.  `LE-Pi`, `VA-Lam`,
`TM-Let` and `K-Let` go under an opaque binder by `Rename.Typed.lift_opaque`.  `VA-Obj` goes under
a transparent binder by `Rename.Typed.lift_transparent`, with `Defs.block_rename` for the block.

A store reads its values weakened, and weakening is the renaming `Rename.succ`.  So a typed store
types every value it reads at the type of its variable (`Store.Typed.get_typed`, decision D14 of
the groups file).

Binders are named in comments.  `(Γ, z : b)` adds one variable, `.here` is the newest.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Binding laws the rules meet under a renaming -/

theorem Ty.weaken_rename (T : Ty s₁) (ρ : Rename s₁ s₂) :
    T.weaken.rename ρ.lift = (T.rename ρ).weaken := by
  rw [Ty.weaken, Ty.weaken, Ty.rename_rename, Ty.rename_rename, Rename.succ_lift]

theorem Telescope.weaken_rename (Tel : Telescope s₁) (ρ : Rename s₁ s₂) :
    Tel.weaken.rename ρ.lift = (Tel.rename ρ).weaken := by
  rw [Telescope.weaken, Telescope.weaken, Telescope.rename_rename, Telescope.rename_rename,
    Rename.succ_lift]

theorem Ty.substPath_rename (T : Ty (s₁,x)) (q : Path s₁) (ρ : Rename s₁ s₂) :
    (T.substPath q).rename ρ = (T.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Ty.substPath, Ty.substPath, Ty.subst_rename, Ty.rename_subst, PathSubst.one_compRename]

theorem Telescope.substPath_rename (Tel : Telescope (s₁,x)) (q : Path s₁) (ρ : Rename s₁ s₂) :
    (Tel.substPath q).rename ρ = (Tel.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Telescope.substPath, Telescope.substPath, Telescope.subst_rename, Telescope.rename_subst,
    PathSubst.one_compRename]

/-- `VA-Obj` weakens its annotation under the self, to make room for the literal's own binder.
That weakening commutes with a renaming lifted under both. -/
theorem Telescope.rename_succ_lift_rename (Tel : Telescope (s₁,x)) (ρ : Rename s₁ s₂) :
    (Tel.rename (Rename.succ (k := .var)).lift).rename ρ.lift.lift =
      (Tel.rename ρ.lift).rename (Rename.succ (k := .var)).lift := by
  rw [Telescope.rename_rename, Telescope.rename_rename, ← Rename.lift_comp, ← Rename.lift_comp,
    Rename.succ_lift]

/-- `DF-Nest` instantiates the outer self of a nested annotation at the path of the literal.
That instantiation commutes with a renaming. -/
theorem Telescope.subst_one_lift_rename (Tel : Telescope ((s₁,x),x)) (p : Path s₁) (ρ : Rename s₁ s₂) :
    (Tel.subst (PathSubst.one p).lift).rename ρ.lift =
      (Tel.rename ρ.lift.lift).subst (PathSubst.one (p.rename ρ)).lift := by
  rw [Telescope.subst_rename, Telescope.rename_subst, ← PathSubst.lift_compRename,
    PathSubst.one_compRename, Rename.lift_pathComp]

/-! ## Reading a context under its newest binder -/

/-- An opaque binder has no block, so a path rooted at it has no node. -/
theorem Ctx.nodeAt_here_opaque (Γ : Ctx s) (T : Ty s) :
    ∀ (p : Path (s,x)), p.root = .here → (Γ.cons (.opaque T)).nodeAt p = none
  | .var .here, _ => rfl
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      show ((Γ.cons (.opaque T)).nodeAt p).bind (·.child a) = none
      rw [Ctx.nodeAt_here_opaque Γ T p h]
      rfl

theorem Ctx.defAt_here_opaque (Γ : Ctx s) (T : Ty s) (p : Path (s,x)) (A : Label)
    (h : p.root = .here) : (Γ.cons (.opaque T)).defAt p A = none := by
  show ((Γ.cons (.opaque T)).nodeAt p).bind (·.def A) = none
  rw [Ctx.nodeAt_here_opaque Γ T p h]
  rfl

/-- A definition read at a weakened path is a weakened definition of the smaller context. -/
theorem Ctx.defAt_weaken_some {Γ : Ctx s} {b : Binding s} {p : Path s} {A : Label} {W : Ty (s,x)}
    (h : (Γ.cons b).defAt (p.rename Rename.succ) A = some W) :
    ∃ W₀, Γ.defAt p A = some W₀ ∧ W = W₀.rename Rename.succ := by
  rw [Ctx.defAt_weaken] at h
  cases e : Γ.defAt p A with
  | none => rw [e] at h; cases h
  | some W₀ =>
      rw [e] at h
      exact ⟨W₀, rfl, (Option.some.inj h).symm⟩

/-- At a path rooted at the newest binder, the node is read off that binder's block, so it renames
when the block does. -/
theorem Ctx.nodeAt_lift_rename {Γ₁ : Ctx s₁} {b₁ : Binding s₁} {Γ₂ : Ctx s₂} {b₂ : Binding s₂}
    {ρ : Rename s₁ s₂}
    (hb : (Γ₂.cons b₂).blockAt .here = ((Γ₁.cons b₁).blockAt .here).map (Block.rename · ρ.lift)) :
    ∀ (p : Path (s₁,x)), p.root = .here →
      (Γ₂.cons b₂).nodeAt (p.rename ρ.lift) = ((Γ₁.cons b₁).nodeAt p).map (Block.rename · ρ.lift)
  | .var .here, _ => hb
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      show ((Γ₂.cons b₂).nodeAt (p.rename ρ.lift)).bind (·.child a) =
        (((Γ₁.cons b₁).nodeAt p).bind (·.child a)).map (Block.rename · ρ.lift)
      rw [Ctx.nodeAt_lift_rename hb p h]
      cases (Γ₁.cons b₁).nodeAt p with
      | none => rfl
      | some B => exact Block.child_rename B ρ.lift a

/-! ## Typed renamings -/

structure Rename.Typed (Γ₁ : Ctx s₁) (ρ : Rename s₁ s₂) (Γ₂ : Ctx s₂) : Prop where
  ty : ∀ x, Γ₂.ty (ρ.var x) = (Γ₁.ty x).rename ρ
  defAt : ∀ p A W, Γ₁.defAt p A = some W → Γ₂.defAt (p.rename ρ) A = some (W.rename ρ)

/-- The types of a lifted renaming, for any two binders whose types agree. -/
theorem Rename.Typed.ty_lift {Γ₁ : Ctx s₁} {ρ : Rename s₁ s₂} {Γ₂ : Ctx s₂} (h : Rename.Typed Γ₁ ρ Γ₂)
    {b₁ : Binding s₁} {b₂ : Binding s₂} (hb : b₂.ty = b₁.ty.rename ρ) :
    ∀ x, (Γ₂.cons b₂).ty (ρ.lift.var x) = ((Γ₁.cons b₁).ty x).rename ρ.lift
  | .here => by
      show b₂.ty.weaken = b₁.ty.weaken.rename ρ.lift
      rw [hb, Ty.weaken_rename]
  | .there y => by
      show (Γ₂.ty (ρ.var y)).weaken = (Γ₁.ty y).weaken.rename ρ.lift
      rw [h.ty y, Ty.weaken_rename]

/-- The definitions of a lifted renaming, for any two binders whose blocks agree. -/
theorem Rename.Typed.defAt_lift {Γ₁ : Ctx s₁} {ρ : Rename s₁ s₂} {Γ₂ : Ctx s₂}
    (h : Rename.Typed Γ₁ ρ Γ₂) {b₁ : Binding s₁} {b₂ : Binding s₂}
    (hb : (Γ₂.cons b₂).blockAt .here = ((Γ₁.cons b₁).blockAt .here).map (Block.rename · ρ.lift))
    (p : Path (s₁,x)) (A : Label) (W : Ty (s₁,x)) (hW : (Γ₁.cons b₁).defAt p A = some W) :
    (Γ₂.cons b₂).defAt (p.rename ρ.lift) A = some (W.rename ρ.lift) := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · have e₁ : (Γ₂.cons b₂).defAt (p.rename ρ.lift) A =
        ((Γ₂.cons b₂).nodeAt (p.rename ρ.lift)).bind (·.def A) := rfl
    have e₂ : ((Γ₁.cons b₁).nodeAt p).bind (·.def A) = some W := hW
    rw [e₁, Ctx.nodeAt_lift_rename hb p hr]
    cases e : (Γ₁.cons b₁).nodeAt p with
    | none => rw [e] at e₂; cases e₂
    | some B =>
        rw [e] at e₂
        have e₃ : B.def A = some W := e₂
        show (B.rename ρ.lift).def A = some (W.rename ρ.lift)
        rw [Block.def_rename, e₃]
        rfl
  · obtain ⟨W₀, e₀, rfl⟩ := Ctx.defAt_weaken_some hW
    have e₁ : (p₀.weaken (k := .var)).rename ρ.lift = (p₀.rename ρ).rename Rename.succ :=
      Path.weaken_rename p₀ ρ
    rw [e₁, Ctx.defAt_weaken, h.defAt p₀ A W₀ e₀]
    show some ((W₀.rename ρ).rename Rename.succ) = some ((W₀.rename Rename.succ).rename ρ.lift)
    rw [Ty.rename_rename, Ty.rename_rename, Rename.succ_lift]

theorem Rename.Typed.succ (Γ : Ctx s) (b : Binding s) : Rename.Typed Γ Rename.succ (Γ.cons b) where
  ty := fun _ => rfl
  defAt := fun p A W h => by rw [Ctx.defAt_weaken, h]; rfl

theorem Rename.Typed.lift_opaque {Γ₁ : Ctx s₁} {ρ : Rename s₁ s₂} {Γ₂ : Ctx s₂} (h : Rename.Typed Γ₁ ρ Γ₂) (T : Ty s₁) : Rename.Typed (Γ₁.cons (.opaque T)) ρ.lift (Γ₂.cons (.opaque (T.rename ρ))) where
  ty := Rename.Typed.ty_lift h rfl
  defAt := Rename.Typed.defAt_lift h rfl

theorem Rename.Typed.lift_transparent {Γ₁ : Ctx s₁} {ρ : Rename s₁ s₂} {Γ₂ : Ctx s₂} (h : Rename.Typed Γ₁ ρ Γ₂) (T : Ty s₁) (B : Block (s₁,x)) : Rename.Typed (Γ₁.cons (.transparent T B)) ρ.lift (Γ₂.cons (.transparent (T.rename ρ) (B.rename ρ.lift))) where
  ty := Rename.Typed.ty_lift h rfl
  defAt := Rename.Typed.defAt_lift h rfl

/-! ## Evidence

One mutual recursion on the evidence block.  `LE-Pi` is the one rule with a premise under a
binder. -/

mutual
theorem PEq.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : PEq.HasType Γ₁ π p q → PEq.HasType Γ₂ (π.rename ρ) (p.rename ρ) (q.rename ρ)
  | .refl => .refl
  | .symm h => .symm (PEq.HasType.rename hρ h)
  | .trans h₁ h₂ => .trans (PEq.HasType.rename hρ h₁) (PEq.HasType.rename hρ h₂)
  | .sel h => .sel (PEq.HasType.rename hρ h)
  | .member (P := P₀) (e := e₀) (i := i) (Tel := Tel) (q := q₀) hP he hi => by
      have he' : LeCo.HasType Γ₂ (e₀.rename ρ) _ (.mu (Tel.rename ρ.lift)) := LeCo.HasType.rename hρ he
      have h := PEq.HasType.member (PathCo.HasType.rename hρ hP) he' (hi.rename ρ.lift)
      show PEq.HasType Γ₂ (.member (P₀.rename ρ) (e₀.rename ρ) i) (P₀.path.rename ρ) ((q₀.substPath P₀.path).rename ρ)
      rw [Path.substPath_rename, ← PathCo.path_rename]
      exact h
theorem PathCo.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : PathCo.HasType Γ₁ P T → PathCo.HasType Γ₂ (P.rename ρ) (T.rename ρ)
  | .var (x := y) h => .var ((hρ.ty y).trans (congrArg (Ty.rename · ρ) h))
  | .sel (P := P₀) (a := a) (i := i) (Tel := Tel) (T := T₀) hP hi => by
      have hP' : PathCo.HasType Γ₂ (P₀.rename ρ) (.mu (Tel.rename ρ.lift)) := PathCo.HasType.rename hρ hP
      have h := PathCo.HasType.sel hP' (hi.rename ρ.lift)
      show PathCo.HasType Γ₂ (.sel (P₀.rename ρ) a i) ((T₀.substPath P₀.path).rename ρ)
      rw [Ty.substPath_rename, ← PathCo.path_rename]
      exact h
  | .cast hP he => .cast (PathCo.HasType.rename hρ hP) (LeCo.HasType.rename hρ he)
  | .alias h₀ hπ hQ => by
      have hπ' := PEq.HasType.rename hρ hπ
      rw [← PathCo.path_rename, ← PathCo.path_rename] at hπ'
      exact .alias (PathCo.HasType.rename hρ h₀) hπ' (PathCo.HasType.rename hρ hQ)
  | .sngl (q := q₀) hP hπ => by
      have hπ' := PEq.HasType.rename hρ hπ
      rw [← PathCo.path_rename] at hπ'
      have h := PathCo.HasType.sngl (PathCo.HasType.rename hρ hP) hπ'
      rw [Ty.sngl_rename]
      exact h
  | .fldI (Q := Q₀) (T := T₀) (p := p₀) (a := a) hQ e => by
      have e' : (Q₀.rename ρ).path = .sel (p₀.rename ρ) a := by rw [PathCo.path_rename, e]; rfl
      have h := PathCo.HasType.fldI (PathCo.HasType.rename hρ hQ) e'
      show PathCo.HasType Γ₂ (.fldI (p₀.rename ρ) a (Q₀.rename ρ)) (.mu (.cons .nil (.fld a (T₀.weaken.rename ρ.lift))))
      rw [Ty.weaken_rename]
      exact h
  | .unfold (P := P₀) (Tel := Tel) hP => by
      have hP' : PathCo.HasType Γ₂ (P₀.rename ρ) (.mu (Tel.rename ρ.lift)) := PathCo.HasType.rename hρ hP
      have h := PathCo.HasType.unfold hP'
      show PathCo.HasType Γ₂ (.unfold (P₀.rename ρ)) (.mu ((Tel.substPath P₀.path).weaken.rename ρ.lift))
      rw [Telescope.weaken_rename, Telescope.substPath_rename, ← PathCo.path_rename]
      exact h
  | .fold (P := P₀) (Tel := Tel) hP => by
      have hP' : PathCo.HasType Γ₂ (P₀.rename ρ) (.mu ((Tel.substPath P₀.path).weaken.rename ρ.lift)) := PathCo.HasType.rename hρ hP
      rw [Telescope.weaken_rename, Telescope.substPath_rename, ← PathCo.path_rename] at hP'
      exact .fold hP'
  | .both (Tel := Tel) (Tel' := Tel') hP hQ e => by
      have hP' : PathCo.HasType Γ₂ _ (.mu (Tel.rename ρ.lift)) := PathCo.HasType.rename hρ hP
      have hQ' : PathCo.HasType Γ₂ _ (.mu (Tel'.rename ρ.lift)) := PathCo.HasType.rename hρ hQ
      have h := PathCo.HasType.both hP' hQ' (by rw [PathCo.path_rename, PathCo.path_rename, e])
      show PathCo.HasType Γ₂ _ (.mu ((Tel ++ Tel').rename ρ.lift))
      rw [Telescope.append_rename]
      exact h
theorem LeCo.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : LeCo.HasType Γ₁ e S T → LeCo.HasType Γ₂ (e.rename ρ) (S.rename ρ) (T.rename ρ)
  | .refl => .refl
  | .trans h₁ h₂ => .trans (LeCo.HasType.rename hρ h₁) (LeCo.HasType.rename hρ h₂)
  | .top => .top
  | .bot => .bot
  | .eqToLe h => .eqToLe (EqCo.HasType.rename hρ h)
  | .pi (S₂ := S₂) he hf => .pi (LeCo.HasType.rename hρ he) (LeCo.HasType.rename (Rename.Typed.lift_opaque hρ S₂) hf)
  | .obj hm => .obj (Morphism.HasType.rename hρ hm)
  | .pair (Tel := Tel) (Tel' := Tel') he hf => by
      have he' : LeCo.HasType Γ₂ _ _ (.mu (Tel.rename ρ.lift)) := LeCo.HasType.rename hρ he
      have hf' : LeCo.HasType Γ₂ _ _ (.mu (Tel'.rename ρ.lift)) := LeCo.HasType.rename hρ hf
      have h := LeCo.HasType.pair he' hf'
      show LeCo.HasType Γ₂ _ _ (.mu ((Tel ++ Tel').rename ρ.lift))
      rw [Telescope.append_rename]
      exact h
  | .bound (Tel := Tel) (i := i) (T := T₀) hi => by
      have hi' : (Tel.rename ρ.lift).At i (.is (T₀.weaken.rename ρ.lift)) := hi.rename ρ.lift
      rw [Ty.weaken_rename] at hi'
      exact .bound hi'
  | .intoBnd (T := T₀) he => by
      have h := LeCo.HasType.intoBnd (LeCo.HasType.rename hρ he)
      show LeCo.HasType Γ₂ _ _ (.mu (.cons .nil (.is (T₀.weaken.rename ρ.lift))))
      rw [Ty.weaken_rename]
      exact h
  | .member (P := P₀) (e := e₀) (i := i) (Tel := Tel) (S' := S') (T' := T') hP he hi => by
      have he' : LeCo.HasType Γ₂ (e₀.rename ρ) _ (.mu (Tel.rename ρ.lift)) := LeCo.HasType.rename hρ he
      have h := LeCo.HasType.member (PathCo.HasType.rename hρ hP) he' (hi.rename ρ.lift)
      show LeCo.HasType Γ₂ (.member (P₀.rename ρ) (e₀.rename ρ) i) ((S'.substPath P₀.path).rename ρ) ((T'.substPath P₀.path).rename ρ)
      rw [Ty.substPath_rename, Ty.substPath_rename, ← PathCo.path_rename]
      exact h
theorem EqCo.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : EqCo.HasType Γ₁ φ S T → EqCo.HasType Γ₂ (φ.rename ρ) (S.rename ρ) (T.rename ρ)
  | .refl => .refl
  | .symm h => .symm (EqCo.HasType.rename hρ h)
  | .trans h₁ h₂ => .trans (EqCo.HasType.rename hρ h₁) (EqCo.HasType.rename hρ h₂)
  | .defP (p := p₀) (A := A) (W := W) h => .defP (hρ.defAt p₀ A W h)
  | .lift (T := T₀) (p := p₀) (q := q₀) hπ => by
      have h := EqCo.HasType.lift (T := T₀.rename ρ.lift) (PEq.HasType.rename hρ hπ)
      rw [Ty.substPath_rename, Ty.substPath_rename]
      exact h
  | .dom h => .dom (EqCo.HasType.rename hρ h)
  | .cod (T₁ := T₁) (T₂ := T₂) (p := p₀) h => by
      have h' := EqCo.HasType.cod (p := p₀.rename ρ) (EqCo.HasType.rename hρ h)
      rw [Ty.substPath_rename, Ty.substPath_rename]
      exact h'
theorem Morphism.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Morphism.HasType Γ₁ src m Tel → Morphism.HasType Γ₂ (src.rename ρ.lift) (m.rename ρ) (Tel.rename ρ.lift)
  | .nil => .nil
  | .le hm hj hpre hpost => .le (Morphism.HasType.rename hρ hm) (hj.rename ρ.lift) (Side.HasType.rename hρ hpre) (Side.HasType.rename hρ hpost)
  | .fld hm hj hsd => .fld (Morphism.HasType.rename hρ hm) (hj.rename ρ.lift) (Side.HasType.rename hρ hsd)
  | .alias hm hj => .alias (Morphism.HasType.rename hρ hm) (hj.rename ρ.lift)
  | .is (Tel := Tel₀) (T := T₀) hm he => by
      have h := Morphism.HasType.is (Morphism.HasType.rename hρ hm) (LeCo.HasType.rename hρ he)
      show Morphism.HasType Γ₂ _ _ (.cons (Tel₀.rename ρ.lift) (.is (T₀.weaken.rename ρ.lift)))
      rw [Ty.weaken_rename]
      exact h
theorem Side.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Side.HasType Γ₁ sd X Y → Side.HasType Γ₂ (sd.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift)
  | .none => .none
  | .some (X := X₀) (Y := Y₀) he => by
      have h := Side.HasType.some (LeCo.HasType.rename hρ he)
      rw [Ty.weaken_rename, Ty.weaken_rename]
      exact h
  | .bot => .bot
  | .top => .top
end

/-! ## Terms, values, definitions

One mutual recursion on the term block.  `VA-Lam` and `TM-Let` go under an opaque binder, `VA-Obj`
under a transparent one. -/

mutual
theorem Tm.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Tm.HasType Γ₁ t T → Tm.HasType Γ₂ (t.rename ρ) (T.rename ρ)
  | .path h => .path (PathCo.HasType.rename hρ h)
  | .val h => .val (Value.HasType.rename hρ h)
  | .app (P := P₀) (Q := Q₀) (T := T₀) hP hQ => by
      have hP' := PathCo.HasType.rename hρ hP
      have h := Tm.HasType.app hP' (PathCo.HasType.rename hρ hQ)
      show Tm.HasType Γ₂ (.app (P₀.rename ρ) (Q₀.rename ρ)) ((T₀.substPath Q₀.path).rename ρ)
      rw [Ty.substPath_rename, ← PathCo.path_rename]
      exact h
  | .lett (T := T₀) (U := U₀) ht hu => by
      have hu' := Tm.HasType.rename (Rename.Typed.lift_opaque hρ T₀) hu
      rw [Ty.weaken_rename] at hu'
      exact .lett (Tm.HasType.rename hρ ht) hu'
  | .cast ht he => .cast (Tm.HasType.rename hρ ht) (LeCo.HasType.rename hρ he)
theorem Value.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Value.HasType Γ₁ v T → Value.HasType Γ₂ (v.rename ρ) (T.rename ρ)
  | .lam (S := S₀) ht => .lam (Tm.HasType.rename (Rename.Typed.lift_opaque hρ S₀) ht)
  | .obj (Tel := Tel) (ds := ds) hds => by
      have h := Defs.HasType.rename (Rename.Typed.lift_transparent hρ (.mu Tel) ds.block) hds
      rw [Defs.block_rename, Telescope.rename_succ_lift_rename] at h
      exact .obj h
  | .cast hv he => .cast (Value.HasType.rename hρ hv) (LeCo.HasType.rename hρ he)
theorem Defs.HasType.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Defs.HasType Γ₁ p ds Tel → Defs.HasType Γ₂ (p.rename ρ) (ds.rename ρ) (Tel.rename ρ.lift)
  | .nil => .nil
  | .typ (p := p₀) (ds := ds₀) (A := A) (U := U) (W := W) hds hA hU => by
      have hA' : A ∉ (ds₀.rename ρ).labels := by rw [Defs.labels_rename]; exact hA
      have hU' : U.rename ρ = (W.rename ρ.lift).substPath (p₀.rename ρ) := by
        rw [hU, Ty.substPath_rename]
      exact .typ (Defs.HasType.rename hρ hds) hA' hU'
  | .path (p := p₀) (ds := ds₀) (a := a) (P := P₀) (Tel := Tel₀) (q := q₀) hds ha hP hq => by
      have ha' : a ∉ (ds₀.rename ρ).labels := by rw [Defs.labels_rename]; exact ha
      have hq' : (P₀.rename ρ).path = (q₀.rename ρ.lift).substPath (p₀.rename ρ) := by
        rw [PathCo.path_rename, hq, Path.substPath_rename]
      have h := Defs.HasType.path (Defs.HasType.rename hρ hds) ha' (PathCo.HasType.rename hρ hP) hq'
      show Defs.HasType Γ₂ _ _ (.cons (Tel₀.rename ρ.lift) (.fld a ((Ty.sngl q₀).rename ρ.lift)))
      rw [Ty.sngl_rename]
      exact h
  | .fn (p := p₀) (ds := ds₀) (a := a) (v := v₀) (S := S₀) (T := T₀) hds ha hl hv => by
      have ha' : a ∉ (ds₀.rename ρ).labels := by rw [Defs.labels_rename]; exact ha
      have hl' : (v₀.rename ρ).isLam = true := by rw [Value.isLam_rename]; exact hl
      have hv' := Value.HasType.rename hρ hv
      rw [Ty.substPath_rename] at hv'
      exact .fn (S := S₀.rename ρ.lift) (T := T₀.rename ρ.lift.lift) (Defs.HasType.rename hρ hds) ha' hl' hv'
  | .nest (p := p₀) (ds := ds₀) (a := a) (ds' := ds') (Tel := Tel₀) (Tel' := Tel') hds ha hds' => by
      have ha' : a ∉ (ds₀.rename ρ).labels := by rw [Defs.labels_rename]; exact ha
      have hds'' := Defs.HasType.rename hρ hds'
      rw [Telescope.subst_one_lift_rename] at hds''
      have h := Defs.HasType.nest (Tel' := Tel'.rename ρ.lift.lift) (Defs.HasType.rename hρ hds) ha' hds''
      show Defs.HasType Γ₂ (p₀.rename ρ) (.fld (ds₀.rename ρ) a (.nest ((Tel'.subst (PathSubst.one p₀).lift).rename ρ.lift) (ds'.rename ρ))) (.cons (Tel₀.rename ρ.lift) (.fld a (.mu (Tel'.rename ρ.lift.lift))))
      rw [Telescope.subst_one_lift_rename]
      exact h
end

/-! ## Continuations -/

theorem Cont.Typed.rename (hρ : Rename.Typed Γ₁ ρ Γ₂) : Cont.Typed Γ₁ K T U → Cont.Typed Γ₂ (K.rename ρ) (T.rename ρ) (U.rename ρ)
  | .nil => .nil
  | .lett (T := T₀) (U := U₀) hu hK => by
      have hu' := Tm.HasType.rename (Rename.Typed.lift_opaque hρ T₀) hu
      rw [Ty.weaken_rename] at hu'
      exact .lett hu' (Cont.Typed.rename hρ hK)
  | .cast he hK => .cast (LeCo.HasType.rename hρ he) (Cont.Typed.rename hρ hK)

/-! ## A typed store types what it reads -/

theorem Store.Typed.get_typed {σ : Store s} {Γ : Ctx s} (h : Store.Typed σ Γ) (x : BVar s .var) : Value.HasType Γ (σ.get x) (Γ.ty x) := by
  induction h with
  | nil => nomatch x
  | @lam s σ Γ S t T _ hv ih =>
      cases x with
      | here => exact Value.HasType.rename (Rename.Typed.succ Γ _) hv
      | there y => exact Value.HasType.rename (Rename.Typed.succ Γ _) (ih y)
  | @obj s σ Γ Tel ds _ hv ih =>
      cases x with
      | here => exact Value.HasType.rename (Rename.Typed.succ Γ _) hv
      | there y => exact Value.HasType.rename (Rename.Typed.succ Γ _) (ih y)

end PDot.FCp
