import Coercions.Nominal.FCn.TypingRename

/-!
# FCn typing under substitution by path evidence (plan X2, group g3)

An evidence substitution `σ` is typed from `Γ₁` to `Γ₂` when it gives every variable path evidence
at the substituted type of the variable, and keeps every definition the context reads, at the
substituted path.  Then every judgment of T.3 but store typing substitutes.  The evidence judgments
are one mutual recursion, the term judgments another, and continuation typing a third.  Each rule
meets its substituted conclusion through the laws of `RenameLemmas.lean`: `Ty.substPath_subst` where
a rule opens a type at a path, `PathCo.path_subst` where it reads the path of evidence, and
`CoSubst.lift_paths` under a binder.

The one-binder case `X.substCo Q` instantiates the newest variable by `Q`.  It is the general
lemma at `CoSubst.Typed.one`, and it is what `MS-LetPath` and the application rules need.  The
case `CoSubst.Typed.selfCast` is what `MS-LetVal` needs when the value carries casts: the body
typed at an opaque binder reads the binder through the composite cast, and the new context binds
it at the type of the core literal.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Substitution of frames and continuations -/

def Frame.subst : Frame s₁ → CoSubst s₁ s₂ → Frame s₂
  | .lett u, σ => .lett (u.subst σ.lift)                                         -- u under z
  | .cast e, σ => .cast (e.subst σ)

def Cont.subst : Cont s₁ → CoSubst s₁ s₂ → Cont s₂
  | .nil, _ => .nil
  | .cons K fr, σ => .cons (K.subst σ) (fr.subst σ)

def Cont.substCo (K : Cont (s,x)) (Q : PathCo s) : Cont s := K.subst (CoSubst.one Q)

theorem CoSubst.lift_id : (CoSubst.id : CoSubst s s).lift = CoSubst.id :=
  (CoSubst.lift_ofRename Rename.id).trans (congrArg CoSubst.ofRename (Rename.lift_id (k := .var)))

theorem Frame.subst_id : ∀ (fr : Frame s), fr.subst CoSubst.id = fr
  | .lett u => by
      show Frame.lett (u.subst CoSubst.id.lift) = _
      rw [CoSubst.lift_id, Tm.subst_id]
  | .cast e => by
      show Frame.cast (e.subst CoSubst.id) = _
      rw [LeCo.subst_id]

theorem Cont.subst_id : ∀ (K : Cont s), K.subst CoSubst.id = K
  | .nil => rfl
  | .cons K fr => by
      show Cont.cons (K.subst CoSubst.id) (fr.subst CoSubst.id) = _
      rw [Cont.subst_id K, Frame.subst_id]

/-! ## Binding laws the rules meet under a substitution -/

theorem Ty.weaken_subst_lift (T : Ty s₁) (σ : PathSubst s₁ s₂) :
    T.weaken.subst σ.lift = (T.subst σ).weaken := by
  rw [Ty.weaken, Ty.weaken, Ty.rename_subst, PathSubst.succ_pathComp_lift, Ty.subst_rename]

theorem Telescope.weaken_subst_lift (Tel : Telescope s₁) (σ : PathSubst s₁ s₂) :
    Tel.weaken.subst σ.lift = (Tel.subst σ).weaken := by
  rw [Telescope.weaken, Telescope.weaken, Telescope.rename_subst, PathSubst.succ_pathComp_lift,
    Telescope.subst_rename]

/-- `VA-Obj` weakens its annotation under the self.  That weakening commutes with a substitution
lifted under both. -/
theorem Telescope.rename_succ_lift_subst (Tel : Telescope (s₁,x)) (σ : PathSubst s₁ s₂) :
    (Tel.rename (Rename.succ (k := .var)).lift).subst σ.lift.lift =
      (Tel.subst σ.lift).rename (Rename.succ (k := .var)).lift := by
  rw [Telescope.rename_subst, Telescope.subst_rename, ← Rename.lift_pathComp,
    PathSubst.succ_pathComp_lift, PathSubst.lift_compRename]

/-- `DF-Nest` instantiates the outer self of a nested annotation at the path of the literal.  That
instantiation commutes with a substitution. -/
theorem Telescope.subst_one_lift_subst (Tel : Telescope ((s₁,x),x)) (p : Path s₁) (σ : PathSubst s₁ s₂) :
    (Tel.subst (PathSubst.one p).lift).subst σ.lift =
      (Tel.subst σ.lift.lift).subst (PathSubst.one (p.subst σ)).lift := by
  rw [Telescope.subst_subst, Telescope.subst_subst, ← PathSubst.comp_lift, ← PathSubst.comp_lift,
    PathSubst.one_comp]

/-! ## Reading a context under its newest binder -/

/-- At a path rooted at the newest binder, the node is read off that binder's block, so it
substitutes when the block does. -/
theorem Ctx.nodeAt_lift_subst {Γ₁ : Ctx s₁} {b₁ : Binding s₁} {Γ₂ : Ctx s₂} {b₂ : Binding s₂}
    {τ : PathSubst s₁ s₂}
    (hb : (Γ₂.cons b₂).blockAt .here = ((Γ₁.cons b₁).blockAt .here).map (Block.subst · τ.lift)) :
    ∀ (p : Path (s₁,x)), p.root = .here →
      (Γ₂.cons b₂).nodeAt (p.subst τ.lift) = ((Γ₁.cons b₁).nodeAt p).map (Block.subst · τ.lift)
  | .var .here, _ => hb
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      show ((Γ₂.cons b₂).nodeAt (p.subst τ.lift)).bind (·.child a) =
        (((Γ₁.cons b₁).nodeAt p).bind (·.child a)).map (Block.subst · τ.lift)
      rw [Ctx.nodeAt_lift_subst hb p h]
      cases (Γ₁.cons b₁).nodeAt p with
      | none => rfl
      | some B => exact Block.child_subst B τ.lift a

/-- An opaque binder defines nothing, so a context that binds the same variable otherwise reads
every definition the opaque one reads. -/
theorem Ctx.defAt_opaque_cons {Γ : Ctx s} {T : Ty s} {b : Binding s} {p : Path (s,x)} {A : Label}
    {W : Ty (s,x)} (h : (Γ.cons (.opaque T)).defAt p A = some W) : (Γ.cons b).defAt p A = some W := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · rw [Ctx.defAt_here_opaque Γ T p A hr] at h
    cases h
  · have e : (Γ.cons b).defAt (p₀.rename Rename.succ) A = (Γ.defAt p₀ A).map (Ty.rename · Rename.succ) :=
      Ctx.defAt_weaken Γ b p₀ A
    have e' : (Γ.cons (.opaque T)).defAt (p₀.rename Rename.succ) A =
        (Γ.defAt p₀ A).map (Ty.rename · Rename.succ) :=
      Ctx.defAt_weaken Γ (.opaque T) p₀ A
    exact e.trans (e'.symm.trans h)

/-- An opaque binder holds no class, so a context that binds the same variable otherwise reads
every class the opaque one reads. -/
theorem Ctx.clsAt_opaque_cons {Γ : Ctx s} {T : Ty s} {b : Binding s} {p : Path (s,x)} {C : Label}
    {U : Ty (s,x)} (h : (Γ.cons (.opaque T)).clsAt p C = some U) : (Γ.cons b).clsAt p C = some U := by
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · rw [Ctx.clsAt_here_opaque Γ T p C hr] at h
    cases h
  · have e : (Γ.cons b).clsAt (p₀.rename Rename.succ) C = (Γ.clsAt p₀ C).map (Ty.rename · Rename.succ) :=
      Ctx.clsAt_weaken Γ b p₀ C
    have e' : (Γ.cons (.opaque T)).clsAt (p₀.rename Rename.succ) C =
        (Γ.clsAt p₀ C).map (Ty.rename · Rename.succ) :=
      Ctx.clsAt_weaken Γ (.opaque T) p₀ C
    exact e.trans (e'.symm.trans h)

/-! ## Typed evidence substitutions -/

structure CoSubst.Typed (Γ₁ : Ctx s₁) (σ : CoSubst s₁ s₂) (Γ₂ : Ctx s₂) : Prop where
  var : ∀ x, PathCo.HasType Γ₂ (σ.var x) ((Γ₁.ty x).subst σ.paths)
  defAt : ∀ p A W, Γ₁.defAt p A = some W → Γ₂.defAt (p.subst σ.paths) A = some (W.subst σ.paths)
  clsAt : ∀ p C U, Γ₁.clsAt p C = some U → Γ₂.clsAt (p.subst σ.paths) C = some (U.subst σ.paths)

/-- The variables of a lifted substitution, for any two binders whose types agree.  The old
variables are weakened, which is `PathCo.HasType.rename` at `Rename.succ`. -/
theorem CoSubst.Typed.var_lift {Γ₁ : Ctx s₁} {σ : CoSubst s₁ s₂} {Γ₂ : Ctx s₂} (h : CoSubst.Typed Γ₁ σ Γ₂)
    {b₁ : Binding s₁} {b₂ : Binding s₂} (hb : b₂.ty = b₁.ty.subst σ.paths) :
    ∀ x, PathCo.HasType (Γ₂.cons b₂) (σ.lift.var x) (((Γ₁.cons b₁).ty x).subst σ.lift.paths)
  | .here => .var (by
      show b₂.ty.weaken = b₁.ty.weaken.subst σ.lift.paths
      rw [CoSubst.lift_paths, hb, Ty.weaken_subst_lift])
  | .there y => by
      have h₁ := PathCo.HasType.rename (Rename.Typed.succ Γ₂ b₂) (h.var y)
      show PathCo.HasType (Γ₂.cons b₂) ((σ.var y).rename Rename.succ) ((Γ₁.ty y).weaken.subst σ.lift.paths)
      rw [CoSubst.lift_paths, Ty.weaken_subst_lift]
      exact h₁

/-- The definitions of a lifted substitution, for any two binders whose blocks agree. -/
theorem CoSubst.Typed.defAt_lift {Γ₁ : Ctx s₁} {σ : CoSubst s₁ s₂} {Γ₂ : Ctx s₂}
    (h : CoSubst.Typed Γ₁ σ Γ₂) {b₁ : Binding s₁} {b₂ : Binding s₂}
    (hb : (Γ₂.cons b₂).blockAt .here = ((Γ₁.cons b₁).blockAt .here).map (Block.subst · σ.paths.lift))
    (p : Path (s₁,x)) (A : Label) (W : Ty (s₁,x)) (hW : (Γ₁.cons b₁).defAt p A = some W) :
    (Γ₂.cons b₂).defAt (p.subst σ.lift.paths) A = some (W.subst σ.lift.paths) := by
  rw [CoSubst.lift_paths]
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · have e₁ : (Γ₂.cons b₂).defAt (p.subst σ.paths.lift) A =
        ((Γ₂.cons b₂).nodeAt (p.subst σ.paths.lift)).bind (·.def A) := rfl
    have e₂ : ((Γ₁.cons b₁).nodeAt p).bind (·.def A) = some W := hW
    rw [e₁, Ctx.nodeAt_lift_subst hb p hr]
    cases e : (Γ₁.cons b₁).nodeAt p with
    | none => rw [e] at e₂; cases e₂
    | some B =>
        rw [e] at e₂
        have e₃ : B.def A = some W := e₂
        show (B.subst σ.paths.lift).def A = some (W.subst σ.paths.lift)
        rw [Block.def_subst, e₃]
        rfl
  · obtain ⟨W₀, e₀, rfl⟩ := Ctx.defAt_weaken_some hW
    have e₁ : (p₀.weaken (k := .var)).subst σ.paths.lift = (p₀.subst σ.paths).rename Rename.succ :=
      Path.weaken_subst_lift p₀ σ.paths
    rw [e₁, Ctx.defAt_weaken, h.defAt p₀ A W₀ e₀]
    show some ((W₀.subst σ.paths).weaken) = some (W₀.weaken.subst σ.paths.lift)
    rw [Ty.weaken_subst_lift]

/-- The classes of a lifted substitution, for any two binders whose blocks agree. -/
theorem CoSubst.Typed.clsAt_lift {Γ₁ : Ctx s₁} {σ : CoSubst s₁ s₂} {Γ₂ : Ctx s₂}
    (h : CoSubst.Typed Γ₁ σ Γ₂) {b₁ : Binding s₁} {b₂ : Binding s₂}
    (hb : (Γ₂.cons b₂).blockAt .here = ((Γ₁.cons b₁).blockAt .here).map (Block.subst · σ.paths.lift))
    (p : Path (s₁,x)) (C : Label) (U : Ty (s₁,x)) (hU : (Γ₁.cons b₁).clsAt p C = some U) :
    (Γ₂.cons b₂).clsAt (p.subst σ.lift.paths) C = some (U.subst σ.lift.paths) := by
  rw [CoSubst.lift_paths]
  rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
  · have e₁ : (Γ₂.cons b₂).clsAt (p.subst σ.paths.lift) C =
        ((Γ₂.cons b₂).nodeAt (p.subst σ.paths.lift)).bind (·.cls C) := rfl
    have e₂ : ((Γ₁.cons b₁).nodeAt p).bind (·.cls C) = some U := hU
    rw [e₁, Ctx.nodeAt_lift_subst hb p hr]
    cases e : (Γ₁.cons b₁).nodeAt p with
    | none => rw [e] at e₂; cases e₂
    | some B =>
        rw [e] at e₂
        have e₃ : B.cls C = some U := e₂
        show (B.subst σ.paths.lift).cls C = some (U.subst σ.paths.lift)
        rw [Block.cls_subst, e₃]
        rfl
  · obtain ⟨U₀, e₀, rfl⟩ := Ctx.clsAt_weaken_some hU
    have e₁ : (p₀.weaken (k := .var)).subst σ.paths.lift = (p₀.subst σ.paths).rename Rename.succ :=
      Path.weaken_subst_lift p₀ σ.paths
    rw [e₁, Ctx.clsAt_weaken, h.clsAt p₀ C U₀ e₀]
    show some ((U₀.subst σ.paths).weaken) = some (U₀.weaken.subst σ.paths.lift)
    rw [Ty.weaken_subst_lift]

theorem CoSubst.Typed.one {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : CoSubst.Typed (Γ.cons (.opaque S)) (CoSubst.one Q) Γ where
  var := fun
    | .here => by
        show PathCo.HasType Γ Q (S.weaken.subst (CoSubst.one Q).paths)
        have e : S.weaken.subst (PathSubst.one Q.path) = S := Ty.weaken_substPath S Q.path
        rw [CoSubst.one_paths, e]
        exact hQ
    | .there y => .var (by
        show Γ.ty y = (Γ.ty y).weaken.subst (CoSubst.one Q).paths
        rw [CoSubst.one_paths]
        exact (Ty.weaken_substPath (Γ.ty y) Q.path).symm)
  defAt := fun p A W hW => by
    rw [CoSubst.one_paths]
    rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
    · rw [Ctx.defAt_here_opaque Γ S p A hr] at hW
      cases hW
    · obtain ⟨W₀, e₀, rfl⟩ := Ctx.defAt_weaken_some hW
      have e₁ : (p₀.weaken (k := .var)).subst (PathSubst.one Q.path) = p₀ := by
        rw [Path.subst_one, Path.weaken_substPath]
      have e₂ : (W₀.rename Rename.succ).subst (PathSubst.one Q.path) = W₀ := Ty.weaken_substPath W₀ Q.path
      rw [e₁, e₂]
      exact e₀
  clsAt := fun p C U hU => by
    rw [CoSubst.one_paths]
    rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
    · rw [Ctx.clsAt_here_opaque Γ S p C hr] at hU
      cases hU
    · obtain ⟨U₀, e₀, rfl⟩ := Ctx.clsAt_weaken_some hU
      have e₁ : (p₀.weaken (k := .var)).subst (PathSubst.one Q.path) = p₀ := by
        rw [Path.subst_one, Path.weaken_substPath]
      have e₂ : (U₀.rename Rename.succ).subst (PathSubst.one Q.path) = U₀ := Ty.weaken_substPath U₀ Q.path
      rw [e₁, e₂]
      exact e₀

theorem CoSubst.Typed.lift_opaque {Γ₁ : Ctx s₁} {σ : CoSubst s₁ s₂} {Γ₂ : Ctx s₂} (h : CoSubst.Typed Γ₁ σ Γ₂) (T : Ty s₁) : CoSubst.Typed (Γ₁.cons (.opaque T)) σ.lift (Γ₂.cons (.opaque (T.subst σ.paths))) where
  var := CoSubst.Typed.var_lift h rfl
  defAt := CoSubst.Typed.defAt_lift h rfl
  clsAt := CoSubst.Typed.clsAt_lift h rfl

theorem CoSubst.Typed.lift_transparent {Γ₁ : Ctx s₁} {σ : CoSubst s₁ s₂} {Γ₂ : Ctx s₂} (h : CoSubst.Typed Γ₁ σ Γ₂) (T : Ty s₁) (B : Block (s₁,x)) : CoSubst.Typed (Γ₁.cons (.transparent T B)) σ.lift (Γ₂.cons (.transparent (T.subst σ.paths) (B.subst σ.paths.lift))) where
  var := CoSubst.Typed.var_lift h rfl
  defAt := CoSubst.Typed.defAt_lift h rfl
  clsAt := CoSubst.Typed.clsAt_lift h rfl

/-- `MS-LetVal` with a composite cast `E : S ≤ T`: a body typed at `z : opaque T` reads `z` as
`cast (var z) E↑` in a context that binds `z` at `S`, opaque or transparent. -/
theorem CoSubst.Typed.selfCast {Γ : Ctx s} {E : LeCo s} {S T : Ty s} (hE : LeCo.HasType Γ E S T) (b : Binding s) (hb : b.ty = S) : CoSubst.Typed (Γ.cons (.opaque T)) (CoSubst.selfCast E) (Γ.cons b) where
  var := fun
    | .here => by
        show PathCo.HasType (Γ.cons b) (.cast (.var .here) (E.rename Rename.succ))
          (T.weaken.subst (CoSubst.selfCast E).paths)
        rw [CoSubst.selfCast_paths, Ty.subst_ofRename, Ty.rename_id]
        exact .cast (.var (by show b.ty.weaken = S.weaken; rw [hb]))
          (LeCo.HasType.rename (Rename.Typed.succ Γ b) hE)
    | .there y => .var (by
        show (Γ.ty y).weaken = (Γ.ty y).weaken.subst (CoSubst.selfCast E).paths
        rw [CoSubst.selfCast_paths, Ty.subst_ofRename, Ty.rename_id])
  defAt := fun p A W hW => by
    rw [CoSubst.selfCast_paths, Path.subst_ofRename, Path.rename_id, Ty.subst_ofRename, Ty.rename_id]
    exact Ctx.defAt_opaque_cons hW
  clsAt := fun p C U hU => by
    rw [CoSubst.selfCast_paths, Path.subst_ofRename, Path.rename_id, Ty.subst_ofRename, Ty.rename_id]
    exact Ctx.clsAt_opaque_cons hU

/-! ## Evidence

One mutual recursion on the evidence block.  `LE-Pi` goes under an opaque binder. -/

mutual
theorem PEq.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : PEq.HasType Γ₁ π p q → PEq.HasType Γ₂ (π.subst σ) (p.subst σ.paths) (q.subst σ.paths)
  | .refl => .refl
  | .symm h => .symm (PEq.HasType.subst hσ h)
  | .trans h₁ h₂ => .trans (PEq.HasType.subst hσ h₁) (PEq.HasType.subst hσ h₂)
  | .sel h => .sel (PEq.HasType.subst hσ h)
  | .member (P := P₀) (e := e₀) (i := i) (Tel := Tel) (q := q₀) hP he hi => by
      have he' : LeCo.HasType Γ₂ (e₀.subst σ) _ (.mu (Tel.subst σ.paths.lift)) := LeCo.HasType.subst hσ he
      have h := PEq.HasType.member (PathCo.HasType.subst hσ hP) he' (hi.subst σ.paths.lift)
      show PEq.HasType Γ₂ (.member (P₀.subst σ) (e₀.subst σ) i) (P₀.path.subst σ.paths) ((q₀.substPath P₀.path).subst σ.paths)
      rw [Path.substPath_subst, ← PathCo.path_subst]
      exact h
theorem PathCo.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : PathCo.HasType Γ₁ P T → PathCo.HasType Γ₂ (P.subst σ) (T.subst σ.paths)
  | .var (x := y) h => by
      have h₁ := hσ.var y
      rw [h] at h₁
      exact h₁
  | .sel (P := P₀) (a := a) (i := i) (Tel := Tel) (T := T₀) hP hi => by
      have hP' : PathCo.HasType Γ₂ (P₀.subst σ) (.mu (Tel.subst σ.paths.lift)) := PathCo.HasType.subst hσ hP
      have h := PathCo.HasType.sel hP' (hi.subst σ.paths.lift)
      show PathCo.HasType Γ₂ (.sel (P₀.subst σ) a i) ((T₀.substPath P₀.path).subst σ.paths)
      rw [Ty.substPath_subst, ← PathCo.path_subst]
      exact h
  | .cast hP he => .cast (PathCo.HasType.subst hσ hP) (LeCo.HasType.subst hσ he)
  | .alias h₀ hπ hQ => by
      have hπ' := PEq.HasType.subst hσ hπ
      rw [← PathCo.path_subst, ← PathCo.path_subst] at hπ'
      exact .alias (PathCo.HasType.subst hσ h₀) hπ' (PathCo.HasType.subst hσ hQ)
  | .sngl (q := q₀) hP hπ => by
      have hπ' := PEq.HasType.subst hσ hπ
      rw [← PathCo.path_subst] at hπ'
      have h := PathCo.HasType.sngl (PathCo.HasType.subst hσ hP) hπ'
      rw [Ty.sngl_subst]
      exact h
  | .fldI (Q := Q₀) (T := T₀) (p := p₀) (a := a) hQ e => by
      have e' : (Q₀.subst σ).path = .sel (p₀.subst σ.paths) a := by rw [PathCo.path_subst, e]; rfl
      have h := PathCo.HasType.fldI (PathCo.HasType.subst hσ hQ) e'
      show PathCo.HasType Γ₂ (.fldI (p₀.subst σ.paths) a (Q₀.subst σ)) (.mu (.cons .nil (.fld a (T₀.weaken.subst σ.paths.lift))))
      rw [Ty.weaken_subst_lift]
      exact h
  | .unfold (P := P₀) (Tel := Tel) hP => by
      have hP' : PathCo.HasType Γ₂ (P₀.subst σ) (.mu (Tel.subst σ.paths.lift)) := PathCo.HasType.subst hσ hP
      have h := PathCo.HasType.unfold hP'
      show PathCo.HasType Γ₂ (.unfold (P₀.subst σ)) (.mu ((Tel.substPath P₀.path).weaken.subst σ.paths.lift))
      rw [Telescope.weaken_subst_lift, Telescope.substPath_subst, ← PathCo.path_subst]
      exact h
  | .fold (P := P₀) (Tel := Tel) hP => by
      have hP' : PathCo.HasType Γ₂ (P₀.subst σ) (.mu ((Tel.substPath P₀.path).weaken.subst σ.paths.lift)) := PathCo.HasType.subst hσ hP
      rw [Telescope.weaken_subst_lift, Telescope.substPath_subst, ← PathCo.path_subst] at hP'
      exact .fold hP'
  | .both (Tel := Tel) (Tel' := Tel') hP hQ e => by
      have hP' : PathCo.HasType Γ₂ _ (.mu (Tel.subst σ.paths.lift)) := PathCo.HasType.subst hσ hP
      have hQ' : PathCo.HasType Γ₂ _ (.mu (Tel'.subst σ.paths.lift)) := PathCo.HasType.subst hσ hQ
      have h := PathCo.HasType.both hP' hQ' (by rw [PathCo.path_subst, PathCo.path_subst, e])
      show PathCo.HasType Γ₂ _ (.mu ((Tel ++ Tel').subst σ.paths.lift))
      rw [Telescope.append_subst]
      exact h
theorem LeCo.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : LeCo.HasType Γ₁ e S T → LeCo.HasType Γ₂ (e.subst σ) (S.subst σ.paths) (T.subst σ.paths)
  | .refl => .refl
  | .trans h₁ h₂ => .trans (LeCo.HasType.subst hσ h₁) (LeCo.HasType.subst hσ h₂)
  | .top => .top
  | .bot => .bot
  | .eqToLe h => .eqToLe (EqCo.HasType.subst hσ h)
  | .pi (S₂ := S₂) he hf => by
      have hf' := LeCo.HasType.subst (CoSubst.Typed.lift_opaque hσ S₂) hf
      rw [CoSubst.lift_paths] at hf'
      exact .pi (LeCo.HasType.subst hσ he) hf'
  | .obj hm => .obj (Morphism.HasType.subst hσ hm)
  | .pair (Tel := Tel) (Tel' := Tel') he hf => by
      have he' : LeCo.HasType Γ₂ _ _ (.mu (Tel.subst σ.paths.lift)) := LeCo.HasType.subst hσ he
      have hf' : LeCo.HasType Γ₂ _ _ (.mu (Tel'.subst σ.paths.lift)) := LeCo.HasType.subst hσ hf
      have h := LeCo.HasType.pair he' hf'
      show LeCo.HasType Γ₂ _ _ (.mu ((Tel ++ Tel').subst σ.paths.lift))
      rw [Telescope.append_subst]
      exact h
  | .bound (Tel := Tel) (i := i) (T := T₀) hi => by
      have hi' : (Tel.subst σ.paths.lift).At i (.is (T₀.weaken.subst σ.paths.lift)) := hi.subst σ.paths.lift
      rw [Ty.weaken_subst_lift] at hi'
      exact .bound hi'
  | .intoBnd (T := T₀) he => by
      have h := LeCo.HasType.intoBnd (LeCo.HasType.subst hσ he)
      show LeCo.HasType Γ₂ _ _ (.mu (.cons .nil (.is (T₀.weaken.subst σ.paths.lift))))
      rw [Ty.weaken_subst_lift]
      exact h
  | .member (P := P₀) (e := e₀) (i := i) (Tel := Tel) (S' := S') (T' := T') hP he hi => by
      have he' : LeCo.HasType Γ₂ (e₀.subst σ) _ (.mu (Tel.subst σ.paths.lift)) := LeCo.HasType.subst hσ he
      have h := LeCo.HasType.member (PathCo.HasType.subst hσ hP) he' (hi.subst σ.paths.lift)
      show LeCo.HasType Γ₂ (.member (P₀.subst σ) (e₀.subst σ) i) ((S'.substPath P₀.path).subst σ.paths) ((T'.substPath P₀.path).subst σ.paths)
      rw [Ty.substPath_subst, Ty.substPath_subst, ← PathCo.path_subst]
      exact h
  | .seal (p := p₀) (C := C) (U := U) h => .seal (hσ.clsAt p₀ C U h)
theorem EqCo.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : EqCo.HasType Γ₁ φ S T → EqCo.HasType Γ₂ (φ.subst σ) (S.subst σ.paths) (T.subst σ.paths)
  | .refl => .refl
  | .symm h => .symm (EqCo.HasType.subst hσ h)
  | .trans h₁ h₂ => .trans (EqCo.HasType.subst hσ h₁) (EqCo.HasType.subst hσ h₂)
  | .defP (p := p₀) (A := A) (W := W) h => .defP (hσ.defAt p₀ A W h)
  | .lift (T := T₀) (p := p₀) (q := q₀) hπ => by
      have h := EqCo.HasType.lift (T := T₀.subst σ.paths.lift) (PEq.HasType.subst hσ hπ)
      rw [Ty.substPath_subst, Ty.substPath_subst]
      exact h
  | .dom h => .dom (EqCo.HasType.subst hσ h)
  | .cod (T₁ := T₁) (T₂ := T₂) (p := p₀) h => by
      have h' := EqCo.HasType.cod (p := p₀.subst σ.paths) (EqCo.HasType.subst hσ h)
      rw [Ty.substPath_subst, Ty.substPath_subst]
      exact h'
theorem Morphism.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Morphism.HasType Γ₁ src m Tel → Morphism.HasType Γ₂ (src.subst σ.paths.lift) (m.subst σ) (Tel.subst σ.paths.lift)
  | .nil => .nil
  | .le hm hj hpre hpost => .le (Morphism.HasType.subst hσ hm) (hj.subst σ.paths.lift) (Side.HasType.subst hσ hpre) (Side.HasType.subst hσ hpost)
  | .fld hm hj hsd => .fld (Morphism.HasType.subst hσ hm) (hj.subst σ.paths.lift) (Side.HasType.subst hσ hsd)
  | .alias hm hj => .alias (Morphism.HasType.subst hσ hm) (hj.subst σ.paths.lift)
  | .is (Tel := Tel₀) (T := T₀) hm he => by
      have h := Morphism.HasType.is (Morphism.HasType.subst hσ hm) (LeCo.HasType.subst hσ he)
      show Morphism.HasType Γ₂ _ _ (.cons (Tel₀.subst σ.paths.lift) (.is (T₀.weaken.subst σ.paths.lift)))
      rw [Ty.weaken_subst_lift]
      exact h
theorem Side.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Side.HasType Γ₁ sd X Y → Side.HasType Γ₂ (sd.subst σ) (X.subst σ.paths.lift) (Y.subst σ.paths.lift)
  | .none => .none
  | .some (X := X₀) (Y := Y₀) he => by
      have h := Side.HasType.some (LeCo.HasType.subst hσ he)
      rw [Ty.weaken_subst_lift, Ty.weaken_subst_lift]
      exact h
  | .bot => .bot
  | .top => .top
end

/-! ## Terms, values, definitions

One mutual recursion on the term block.  `VA-Lam` and `TM-Let` go under an opaque binder, `VA-Obj`
under a transparent one, whose block substitutes by `Defs.block_subst`. -/

mutual
theorem Tm.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Tm.HasType Γ₁ t T → Tm.HasType Γ₂ (t.subst σ) (T.subst σ.paths)
  | .path h => .path (PathCo.HasType.subst hσ h)
  | .val h => .val (Value.HasType.subst hσ h)
  | .app (P := P₀) (Q := Q₀) (T := T₀) hP hQ => by
      have hP' := PathCo.HasType.subst hσ hP
      have h := Tm.HasType.app hP' (PathCo.HasType.subst hσ hQ)
      show Tm.HasType Γ₂ (.app (P₀.subst σ) (Q₀.subst σ)) ((T₀.substPath Q₀.path).subst σ.paths)
      rw [Ty.substPath_subst, ← PathCo.path_subst]
      exact h
  | .lett (T := T₀) (U := U₀) ht hu => by
      have hu' := Tm.HasType.subst (CoSubst.Typed.lift_opaque hσ T₀) hu
      rw [CoSubst.lift_paths, Ty.weaken_subst_lift] at hu'
      exact .lett (Tm.HasType.subst hσ ht) hu'
  | .cast ht he => .cast (Tm.HasType.subst hσ ht) (LeCo.HasType.subst hσ he)
theorem Value.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Value.HasType Γ₁ v T → Value.HasType Γ₂ (v.subst σ) (T.subst σ.paths)
  | .lam (S := S₀) ht => by
      have ht' := Tm.HasType.subst (CoSubst.Typed.lift_opaque hσ S₀) ht
      rw [CoSubst.lift_paths] at ht'
      exact .lam ht'
  | .obj (Tel := Tel) (ds := ds) hds => by
      have h := Defs.HasType.subst (CoSubst.Typed.lift_transparent hσ (.mu Tel) ds.block) hds
      rw [← CoSubst.lift_paths σ, Defs.block_subst, CoSubst.lift_paths σ,
        Telescope.rename_succ_lift_subst] at h
      exact .obj h
  | .cast hv he => .cast (Value.HasType.subst hσ hv) (LeCo.HasType.subst hσ he)
theorem Defs.HasType.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Defs.HasType Γ₁ p ds Tel → Defs.HasType Γ₂ (p.subst σ.paths) (ds.subst σ) (Tel.subst σ.paths.lift)
  | .nil => .nil
  | .typ (p := p₀) (ds := ds₀) (A := A) (U := U) (W := W) hds hA hU => by
      have hA' : A ∉ (ds₀.subst σ).labels := by rw [Defs.labels_subst]; exact hA
      have hU' : U.subst σ.paths = (W.subst σ.paths.lift).substPath (p₀.subst σ.paths) := by
        rw [hU, Ty.substPath_subst]
      exact .typ (Defs.HasType.subst hσ hds) hA' hU'
  | .path (p := p₀) (ds := ds₀) (a := a) (P := P₀) (Tel := Tel₀) (q := q₀) hds ha hP hq => by
      have ha' : a ∉ (ds₀.subst σ).labels := by rw [Defs.labels_subst]; exact ha
      have hq' : (P₀.subst σ).path = (q₀.subst σ.paths.lift).substPath (p₀.subst σ.paths) := by
        rw [PathCo.path_subst, hq, Path.substPath_subst]
      have h := Defs.HasType.path (Defs.HasType.subst hσ hds) ha' (PathCo.HasType.subst hσ hP) hq'
      show Defs.HasType Γ₂ _ _ (.cons (Tel₀.subst σ.paths.lift) (.fld a ((Ty.sngl q₀).subst σ.paths.lift)))
      rw [Ty.sngl_subst]
      exact h
  | .fn (p := p₀) (ds := ds₀) (a := a) (v := v₀) (S := S₀) (T := T₀) hds ha hl hv => by
      have ha' : a ∉ (ds₀.subst σ).labels := by rw [Defs.labels_subst]; exact ha
      have hl' : (v₀.subst σ).isLam = true := by rw [Value.isLam_subst]; exact hl
      have hv' := Value.HasType.subst hσ hv
      rw [Ty.substPath_subst] at hv'
      exact .fn (S := S₀.subst σ.paths.lift) (T := T₀.subst σ.paths.lift.lift) (Defs.HasType.subst hσ hds) ha' hl' hv'
  | .nest (p := p₀) (ds := ds₀) (a := a) (ds' := ds') (Tel := Tel₀) (Tel' := Tel') hds ha hds' => by
      have ha' : a ∉ (ds₀.subst σ).labels := by rw [Defs.labels_subst]; exact ha
      have hds'' := Defs.HasType.subst hσ hds'
      rw [Telescope.subst_one_lift_subst] at hds''
      have h := Defs.HasType.nest (Tel' := Tel'.subst σ.paths.lift.lift) (Defs.HasType.subst hσ hds) ha' hds''
      show Defs.HasType Γ₂ (p₀.subst σ.paths) (.fld (ds₀.subst σ) a (.nest ((Tel'.subst (PathSubst.one p₀).lift).subst σ.paths.lift) (ds'.subst σ))) (.cons (Tel₀.subst σ.paths.lift) (.fld a (.mu (Tel'.subst σ.paths.lift.lift))))
      rw [Telescope.subst_one_lift_subst]
      exact h
  | .cls (p := p₀) (ds := ds₀) (C := C) (U := U) (TelB := TelB) hds hC hU => by
      have hC' : C ∉ (ds₀.subst σ).labels := by rw [Defs.labels_subst]; exact hC
      have hU' : U.subst σ.paths = (Ty.mu (TelB.subst σ.paths.lift.lift)).substPath (p₀.subst σ.paths) := by
        rw [hU, Ty.substPath_subst]; rfl
      exact .cls (Defs.HasType.subst hσ hds) hC' hU'
end

/-! ## Continuations -/

theorem Cont.Typed.subst (hσ : CoSubst.Typed Γ₁ σ Γ₂) : Cont.Typed Γ₁ K T U → Cont.Typed Γ₂ (K.subst σ) (T.subst σ.paths) (U.subst σ.paths)
  | .nil => .nil
  | .lett (T := T₀) (U := U₀) hu hK => by
      have hu' := Tm.HasType.subst (CoSubst.Typed.lift_opaque hσ T₀) hu
      rw [CoSubst.lift_paths, Ty.weaken_subst_lift] at hu'
      exact .lett hu' (Cont.Typed.subst hσ hK)
  | .cast he hK => .cast (LeCo.HasType.subst hσ he) (Cont.Typed.subst hσ hK)

/-! ## Instantiating one binder by path evidence

Each is the general lemma at `CoSubst.Typed.one`, with `CoSubst.one_paths`. -/

theorem PEq.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : PEq.HasType (Γ.cons (.opaque S)) π p q → PEq.HasType Γ (π.substCo Q) (p.substPath Q.path) (q.substPath Q.path) := by
  intro h
  have h' := PEq.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths, Path.subst_one, Path.subst_one] at h'
  exact h'
theorem PathCo.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : PathCo.HasType (Γ.cons (.opaque S)) P T → PathCo.HasType Γ (P.substCo Q) (T.substPath Q.path) := by
  intro h
  have h' := PathCo.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem LeCo.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : LeCo.HasType (Γ.cons (.opaque S)) e T U → LeCo.HasType Γ (e.substCo Q) (T.substPath Q.path) (U.substPath Q.path) := by
  intro h
  have h' := LeCo.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem EqCo.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : EqCo.HasType (Γ.cons (.opaque S)) φ T U → EqCo.HasType Γ (φ.substCo Q) (T.substPath Q.path) (U.substPath Q.path) := by
  intro h
  have h' := EqCo.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem Morphism.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Morphism.HasType (Γ.cons (.opaque S)) src m Tel → Morphism.HasType Γ (src.subst (PathSubst.one Q.path).lift) (m.substCo Q) (Tel.subst (PathSubst.one Q.path).lift) := by
  intro h
  have h' := Morphism.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem Side.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Side.HasType (Γ.cons (.opaque S)) sd X Y → Side.HasType Γ (sd.substCo Q) (X.subst (PathSubst.one Q.path).lift) (Y.subst (PathSubst.one Q.path).lift) := by
  intro h
  have h' := Side.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem Tm.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Tm.HasType (Γ.cons (.opaque S)) t T → Tm.HasType Γ (t.substCo Q) (T.substPath Q.path) := by
  intro h
  have h' := Tm.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem Value.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Value.HasType (Γ.cons (.opaque S)) v T → Value.HasType Γ (v.substCo Q) (T.substPath Q.path) := by
  intro h
  have h' := Value.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'
theorem Defs.HasType.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Defs.HasType (Γ.cons (.opaque S)) p ds Tel → Defs.HasType Γ (p.substPath Q.path) (ds.substCo Q) (Tel.subst (PathSubst.one Q.path).lift) := by
  intro h
  have h' := Defs.HasType.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths, Path.subst_one] at h'
  exact h'
theorem Cont.Typed.substCo {Γ : Ctx s} {Q : PathCo s} {S : Ty s} (hQ : PathCo.HasType Γ Q S) : Cont.Typed (Γ.cons (.opaque S)) K T U → Cont.Typed Γ (K.substCo Q) (T.substPath Q.path) (U.substPath Q.path) := by
  intro h
  have h' := Cont.Typed.subst (CoSubst.Typed.one hQ) h
  rw [CoSubst.one_paths] at h'
  exact h'

end Nominal.FCn
