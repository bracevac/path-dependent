import Coercions.Paths.FCdot.TypingSubst

namespace Paths

/-!
# Path substitution of FCdot evidence derivations

`PSub s1 s2` sends each variable to a `PathCo`, and `LeCo.psubst` and its
family (`Syntax.lean`) carry evidence along it: an atom becomes the path of
its root, `member` becomes `memberP`, and `def` becomes `defP`.  This module
proves that the substitution preserves typing, as one mutual induction over
the seven evidence judgments (`LeCo.HasType.psubst`, `Atom.HasType.psubst`
and their five companions).  It is what closes the coercion of a field of a
nested literal over the store (decision 24, P1.5 amendment): the self of the
literal at a variable goes to that variable, and the self of the literal at a
deeper path goes to the node the table wrote there.  Terms and values are
never substituted (Fact 1).

The types are substituted by `Ty.subst` through `PSub.paths`, so the module
opens with the composition law of path substitutions and its consequences for
`substPath` and for weakening.
-/

namespace FCdot

/-! ## Composing path substitutions -/

namespace PathSubst

/-- Apply `σ`, then `τ`. -/
def comp (σ : PathSubst s1 s2) (τ : PathSubst s2 s3) : PathSubst s1 s3 where
  var := fun x => (σ.var x).subst τ

/-- A weakening followed by a lifted substitution is the substitution
followed by a weakening. -/
theorem succ_pathComp_lift {s1 s2 : Sig} (σ : PathSubst s1 s2) :
    (Rename.succ (k := .var)).pathComp σ.lift = σ.compRename Rename.succ :=
  PathSubst.funext' (fun _ => rfl)

end PathSubst

theorem Path.subst_subst {s1 s2 s3 : Sig} (p : Path s1) (σ : PathSubst s1 s2)
    (τ : PathSubst s2 s3) : (p.subst σ).subst τ = p.subst (σ.comp τ) := by
  induction p with
  | var x => rfl
  | sel p ℓ ih => exact congrArg (Path.sel · ℓ) ih

theorem Path.weaken_subst_lift {s1 s2 : Sig} (p : Path s1) (σ : PathSubst s1 s2) :
    (p.weaken (k := .var)).subst σ.lift = (p.subst σ).weaken := by
  rw [Path.weaken, Path.rename_subst, PathSubst.succ_pathComp_lift, Path.weaken,
    Path.subst_rename]

theorem PathSubst.comp_lift {s1 s2 s3 : Sig} (σ : PathSubst s1 s2) (τ : PathSubst s2 s3) :
    (σ.comp τ).lift = σ.lift.comp τ.lift := by
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y => exact (Path.weaken_subst_lift (σ.var y) τ).symm

mutual

theorem Ty.subst_subst {s1 s2 s3 : Sig} :
    ∀ (T : Ty s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (T.subst σ).subst τ = T.subst (σ.comp τ)
  | .bot, _, _ => rfl
  | .sel p ℓ, σ, τ => by simp only [Ty.subst, Path.subst_subst]
  | .pi S T, σ, τ => by
      simp only [Ty.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ.lift τ.lift,
        PathSubst.comp_lift]
  | .obj Tel, σ, τ => by
      simp only [Ty.subst, Telescope.subst_subst Tel σ.lift τ.lift, PathSubst.comp_lift]

theorem Proposition.subst_subst {s1 s2 s3 : Sig} :
    ∀ (P : Proposition s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (P.subst σ).subst τ = P.subst (σ.comp τ)
  | .le S T, σ, τ => by
      simp only [Proposition.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ τ]
  | .eq S T, σ, τ => by
      simp only [Proposition.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ τ]
  | .has ℓ, _, _ => rfl
  | .bnd T, σ, τ => by simp only [Proposition.subst, Ty.subst_subst T σ τ]
  | .hasVal ℓ, _, _ => rfl
  | .alias q, σ, τ => by simp only [Proposition.subst, Path.subst_subst q σ τ]

theorem Telescope.subst_subst {s1 s2 s3 : Sig} :
    ∀ (Tel : Telescope s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (Tel.subst σ).subst τ = Tel.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons Tel P, σ, τ => by
      simp only [Telescope.subst, Telescope.subst_subst Tel σ τ, Proposition.subst_subst P σ τ]

end

theorem Witnesses.subst_subst {s1 s2 s3 : Sig} :
    ∀ (W : Witnesses s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (W.subst σ).subst τ = W.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons W ℓ T, σ, τ => by
      simp only [Witnesses.subst, Witnesses.subst_subst W σ τ, Ty.subst_subst T σ τ]

/-! ### Instantiating the self and weakening, against a path substitution -/

/-- Instantiating the self at `q` and then substituting is substituting under
the self and then instantiating at the image of `q`. -/
theorem PathSubst.one_comp {s1 s2 : Sig} (q : Path s1) (σ : PathSubst s1 s2) :
    (PathSubst.one q).comp σ = σ.lift.comp (PathSubst.one (q.subst σ)) := by
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y =>
      show σ.var y = ((σ.var y).weaken (k := .var)).subst (PathSubst.one (q.subst σ))
      rw [Path.subst_one, Path.weaken_substPath]

theorem Path.substPath_subst {s1 s2 : Sig} (p : Path (s1,x)) (q : Path s1)
    (σ : PathSubst s1 s2) :
    (p.substPath q).subst σ = (p.subst σ.lift).substPath (q.subst σ) := by
  rw [← Path.subst_one, ← Path.subst_one, Path.subst_subst, Path.subst_subst,
    PathSubst.one_comp]

theorem Ty.substPath_subst {s1 s2 : Sig} (T : Ty (s1,x)) (q : Path s1)
    (σ : PathSubst s1 s2) :
    (T.substPath q).subst σ = (T.subst σ.lift).substPath (q.subst σ) := by
  rw [Ty.substPath, Ty.substPath, Ty.subst_subst, Ty.subst_subst, PathSubst.one_comp]

theorem Telescope.substPath_subst {s1 s2 : Sig} (Tel : Telescope (s1,x)) (q : Path s1)
    (σ : PathSubst s1 s2) :
    (Tel.substPath q).subst σ = (Tel.subst σ.lift).substPath (q.subst σ) := by
  rw [Telescope.substPath, Telescope.substPath, Telescope.subst_subst,
    Telescope.subst_subst, PathSubst.one_comp]

theorem Witnesses.substPath_subst {s1 s2 : Sig} (W : Witnesses (s1,x)) (q : Path s1)
    (σ : PathSubst s1 s2) :
    (W.substPath q).subst σ = (W.subst σ.lift).substPath (q.subst σ) := by
  rw [Witnesses.substPath, Witnesses.substPath, Witnesses.subst_subst,
    Witnesses.subst_subst, PathSubst.one_comp]

theorem Ty.weaken_subst {s1 s2 : Sig} (T : Ty s1) (σ : PathSubst s1 s2) :
    (T.weaken (k := .var)).subst σ.lift = (T.subst σ).weaken := by
  rw [Ty.weaken, Ty.rename_subst, PathSubst.succ_pathComp_lift, Ty.weaken, Ty.subst_rename]

theorem Telescope.weaken_subst {s1 s2 : Sig} (Tel : Telescope s1) (σ : PathSubst s1 s2) :
    (Tel.weaken (k := .var)).subst σ.lift = (Tel.subst σ).weaken := by
  rw [Telescope.weaken, Telescope.rename_subst, PathSubst.succ_pathComp_lift,
    Telescope.weaken, Telescope.subst_rename]

theorem Block.weaken_subst {s1 s2 : Sig} (B : Block s1) (σ : PathSubst s1 s2) :
    (B.weaken (k := .var)).subst σ.lift = (B.subst σ).weaken := by
  rw [Block.weaken, Block.rename_subst, PathSubst.succ_pathComp_lift, Block.weaken,
    Block.subst_rename]

/-- The singleton of a path substitutes as its path does. -/
theorem Ty.snglOf_subst {s1 s2 : Sig} (q : Path s1) (σ : PathSubst s1 s2) :
    (Ty.snglOf q).subst σ = Ty.snglOf (q.subst σ) := by
  simp only [Ty.snglOf, Ty.subst, Telescope.subst, Proposition.subst, Path.weaken_subst_lift]

/-! ### Telescopes against a path substitution -/

theorem Telescope.At.subst {s1 s2 : Sig} {Tel : Telescope s1} {i : Nat} {P : Proposition s1}
    (h : Tel.At i P) (σ : PathSubst s1 s2) : (Tel.subst σ).At i (P.subst σ) := by
  induction h with
  | @here Tel P =>
      rw [← Telescope.length_subst Tel σ]
      exact Telescope.At.here
  | there _ ih => exact Telescope.At.there ih

@[simp] theorem Telescope.append_subst {s1 s2 : Sig} :
    ∀ (Tel Tel' : Telescope s1) (σ : PathSubst s1 s2),
      (Tel ++ Tel').subst σ = Tel.subst σ ++ Tel'.subst σ
  | _, .nil, _ => rfl
  | Tel, .cons Tel' P, σ => by
      simp [Telescope.append_cons, Telescope.subst, Telescope.append_subst Tel Tel' σ]

theorem Witnesses.eqEntriesOf_subst {s1 s2 : Sig} (self : BVar s1 .var)
    (self' : BVar s2 .var) (W₀ : Witnesses s1) (σ : PathSubst s1 s2)
    (hself : σ.var self = .var self') :
    ∀ W : Witnesses s1,
      (W₀.subst σ).eqEntriesOf self' (W.subst σ) = (W₀.eqEntriesOf self W).subst σ
  | .nil => rfl
  | .cons W ℓ T => by
      simp [Witnesses.subst, Witnesses.eqEntriesOf, Telescope.subst, Proposition.subst,
        Ty.subst, Path.subst, hself, Witnesses.eqEntriesOf_subst self self' W₀ σ hself W,
        Witnesses.get_subst]

@[simp] theorem Witnesses.eqEntries_subst {s1 s2 : Sig} (W : Witnesses (s1,x))
    (σ : PathSubst s1 s2) :
    (W.subst σ.lift).eqEntries = W.eqEntries.subst σ.lift :=
  Witnesses.eqEntriesOf_subst .here .here W σ.lift rfl W

@[simp] theorem Telescope.hasEntries_subst {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (ls : List Label) (σ : PathSubst s1 s2),
      (Tel.hasEntries ls).subst σ = (Tel.subst σ).hasEntries ls
  | _, [], _ => rfl
  | Tel, l :: ls, σ => by
      simp [Telescope.hasEntries, Telescope.hasEntries_subst (Tel.cons (.has l)) ls σ,
        Telescope.subst, Proposition.subst]

@[simp] theorem Telescope.hasValEntries_subst {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (ls : List Label) (σ : PathSubst s1 s2),
      (Tel.hasValEntries ls).subst σ = (Tel.subst σ).hasValEntries ls
  | _, [], _ => rfl
  | Tel, l :: ls, σ => by
      simp [Telescope.hasValEntries, Telescope.hasValEntries_subst (Tel.cons (.hasVal l)) ls σ,
        Telescope.subst, Proposition.subst]

/-- The precise telescope of a literal substitutes as its witnesses do. -/
theorem Telescope.ofLiteral_subst {s1 s2 : Sig} (W : Witnesses (s1,x))
    (ls vls : List Label) (σ : PathSubst s1 s2) :
    (Telescope.ofLiteral W ls vls).subst σ.lift
      = Telescope.ofLiteral (W.subst σ.lift) ls vls := by
  simp [Telescope.ofLiteral]

/-! ## The paths of a path substitution -/

/-- Lifting a `PSub` lifts the path substitution it induces. -/
@[simp] theorem PSub.lift_paths {s1 s2 : Sig} (σ : PSub s1 s2) :
    σ.lift.paths = σ.paths.lift := by
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y =>
      show ((σ.var y).rename Rename.succ).path = ((σ.var y).path).weaken
      rw [PathCo.path_rename]
      rfl

@[simp] theorem PSub.paths_var {s1 s2 : Sig} (σ : PSub s1 s2) (x : BVar s1 .var) :
    σ.paths.var x = (σ.var x).path := rfl

/-! ## The walk under an opaque binder

An opaque binder has no block, so a path rooted at it has none, and every
other path is a weakened path of the smaller context. -/

/-- A path over `(s,x)` is rooted at the new binder or is a weakened path. -/
theorem Path.root_here_or_weaken {s : Sig} :
    ∀ p : Path (s,x), p.root = .here ∨ ∃ p₀ : Path s, p = p₀.weaken (k := .var)
  | .var .here => Or.inl rfl
  | .var (.there y) => Or.inr ⟨.var y, rfl⟩
  | .sel p a =>
      match Path.root_here_or_weaken p with
      | .inl h => Or.inl h
      | .inr ⟨p₀, h⟩ => Or.inr ⟨.sel p₀ a, by rw [h]; rfl⟩

theorem Ctx.blockPass_here_opaque {s : Sig} (Γ : Ctx s) (T : Ty s)
    (k : Path (s,x) → Option (Block (s,x))) :
    ∀ p : Path (s,x), p.root = .here → (Γ.cons (.opaque T)).blockPass k p = none
  | .var .here, _ => rfl
  | .var (.there _), h => by cases h
  | .sel p a, h => by
      simp only [Ctx.blockPass]
      rw [Ctx.blockPass_here_opaque Γ T k p h]

theorem Ctx.lookupBlock_here_opaque {s : Sig} (Γ : Ctx s) (T : Ty s) (p : Path (s,x))
    (h : p.root = .here) : (Γ.cons (.opaque T)).lookupBlock p = none := by
  unfold Ctx.lookupBlock
  cases (Γ.cons (.opaque T)).aliasBudget with
  | zero => rfl
  | succ n => exact Ctx.blockPass_here_opaque Γ T _ p h

theorem Ctx.nodeBlock_here_opaque {s : Sig} (Γ : Ctx s) (T : Ty s) (p : Path (s,x))
    (h : p.root = .here) : (Γ.cons (.opaque T)).nodeBlock p = none :=
  Ctx.blockPass_here_opaque Γ T _ p h

/-! ## Typed path substitutions -/

/-- What a path substitution asks of the two contexts.  `var` is where the
`node` rule is used: the self of a nested literal goes to `node p W ls vls`,
typed at the literal's precise type, which is the self binder's type.  `defP`
and `def_` carry definitions, and `lookupB` and `nodeB` carry the two walks,
the second of which the `node` rule reads. -/
structure PSub.Typed {s1 s2 : Sig} (Γ1 : Ctx s1) (σ : PSub s1 s2) (Γ2 : Ctx s2) : Prop where
  var : ∀ x, Γ2 ⊢ᵖ σ.var x : (Γ1.lookupTy x).subst σ.paths
  defP : ∀ p ℓ W, Γ1.lookupDefP p ℓ = some W →
    Γ2.lookupDefP (p.subst σ.paths) ℓ = some (W.subst σ.paths)
  def_ : ∀ x ℓ W, Γ1.lookupDef x ℓ = some W →
    Γ2.lookupDefP (σ.var x).path ℓ = some (W.subst σ.paths)
  lookupB : ∀ p B, Γ1.lookupBlock p = some B →
    Γ2.lookupBlock (p.subst σ.paths) = some (B.subst σ.paths)
  nodeB : ∀ p B, Γ1.nodeBlock p = some B →
    Γ2.nodeBlock (p.subst σ.paths) = some (B.subst σ.paths)

namespace PSub.Typed

/-- The definition a walk carried by a path substitution reads. -/
theorem defP_of_lookupB {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hB : ∀ p B, Γ1.lookupBlock p = some B →
      Γ2.lookupBlock (p.subst σ.paths) = some (B.subst σ.paths))
    (p : Path s1) (ℓ : Label) (W : Ty s1) (hd : Γ1.lookupDefP p ℓ = some W) :
    Γ2.lookupDefP (p.subst σ.paths) ℓ = some (W.subst σ.paths) := by
  unfold Ctx.lookupDefP at hd ⊢
  cases hbk : Γ1.lookupBlock p with
  | none => rw [hbk] at hd; exact absurd hd (by simp)
  | some B =>
      cases B with
      | fwd r => rw [hbk] at hd; exact absurd hd (by simp)
      | obj W₀ ls vls ch =>
          rw [hbk] at hd
          obtain rfl : W₀.get ℓ = W := by simpa using hd
          simp only [hB _ _ hbk, Block.subst, Witnesses.get_subst]

/-- Lifting under an opaque binder, which is what the `pi` case of the
substitution lemma needs: a path rooted at the parameter has no block, and
every other path is carried by weakening. -/
theorem lift {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (h : PSub.Typed Γ1 σ Γ2) (T : Ty s1) :
    PSub.Typed (Γ1.cons (.opaque T)) σ.lift (Γ2.cons (.opaque (T.subst σ.paths))) := by
  have hB : ∀ (p : Path (s1,x)) (B : Block (s1,x)), (Γ1.cons (.opaque T)).lookupBlock p = some B →
      (Γ2.cons (.opaque (T.subst σ.paths))).lookupBlock (p.subst σ.lift.paths)
        = some (B.subst σ.lift.paths) := by
    intro p B hp
    rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
    · rw [Ctx.lookupBlock_here_opaque Γ1 T p hr] at hp
      exact absurd hp (by simp)
    · obtain ⟨B₀, hB₀, rfl⟩ := Ctx.lookupBlock_strengthen Γ1 _ hp
      have hw := Ctx.lookupBlock_weaken Γ2 (.opaque (T.subst σ.paths)) (h.lookupB p₀ B₀ hB₀)
      rw [PSub.lift_paths, Path.weaken_subst_lift, Block.weaken_subst]
      exact hw
  refine ⟨?_, defP_of_lookupB hB, ?_, hB, ?_⟩
  · intro x
    cases x with
    | here =>
        show (Γ2.cons (.opaque (T.subst σ.paths))) ⊢ᵖ .var .here :
          ((Γ1.cons (.opaque T)).lookupTy .here).subst σ.lift.paths
        have he : ((Γ1.cons (.opaque T)).lookupTy .here).subst σ.lift.paths
            = (Γ2.cons (.opaque (T.subst σ.paths))).lookupTy .here := by
          simp only [Ctx.lookupTy_here, Binding.ty, PSub.lift_paths, Ty.weaken_subst]
        rw [he]
        exact .var
    | there y =>
        show (Γ2.cons (.opaque (T.subst σ.paths))) ⊢ᵖ (σ.var y).rename Rename.succ :
          ((Γ1.cons (.opaque T)).lookupTy (.there y)).subst σ.lift.paths
        rw [Ctx.lookupTy_there, PSub.lift_paths, Ty.weaken_subst]
        exact (h.var y).weaken _
  · intro x ℓ W hW
    cases x with
    | here => simp at hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        cases hd : Γ1.lookupDef y ℓ with
        | none => rw [hd] at hW; simp at hW
        | some W₀ =>
            rw [hd] at hW
            obtain rfl : W₀.weaken (k := .var) = W := by simpa using hW
            have hw := Ctx.lookupDefP_weaken Γ2 (.opaque (T.subst σ.paths)) (h.def_ y ℓ W₀ hd)
            show (Γ2.cons (.opaque (T.subst σ.paths))).lookupDefP
              ((σ.var y).rename Rename.succ).path ℓ = _
            rw [PathCo.path_rename, PSub.lift_paths, Ty.weaken_subst]
            exact hw
  · intro p B hp
    rcases Path.root_here_or_weaken p with hr | ⟨p₀, rfl⟩
    · rw [Ctx.nodeBlock_here_opaque Γ1 T p hr] at hp
      exact absurd hp (by simp)
    · obtain ⟨B₀, hB₀, rfl⟩ := Ctx.nodeBlock_strengthen Γ1 _ hp
      have hw := Ctx.nodeBlock_weaken Γ2 (.opaque (T.subst σ.paths)) (h.nodeB p₀ B₀ hB₀)
      rw [PSub.lift_paths, Path.weaken_subst_lift, Block.weaken_subst]
      exact hw

end PSub.Typed

/-! ## The substitution lemma

One mutual induction over the seven evidence judgments.  The cases that are
not bookkeeping are `member`, which becomes `memberP` and needs the
substitution to commute with the instantiation of the self
(`Ty.substPath_subst`), `unfoldSelf` and `foldSelf`, the same on telescopes,
`pi`, which lifts under the opaque parameter, and `node`, which reads
`nodeB`. -/

mutual

theorem LeCo.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {e : LeCo s1} {S T : Ty s1} (h : Γ1 ⊢ e : S ≤ T) :
    Γ2 ⊢ e.psubst σ : S.subst σ.paths ≤ T.subst σ.paths := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.psubst hσ) (hf.psubst hσ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.psubst hσ)
  | .pi he hf =>
      have hf' := hf.psubst (hσ.lift _)
      rw [PSub.lift_paths] at hf'
      exact .pi (he.psubst hσ) hf'
  | .obj hm => exact .obj (hm.psubst hσ)
  | .pair he hf =>
      have := LeCo.HasType.pair (he.psubst hσ) (hf.psubst hσ)
      simpa [LeCo.psubst, Ty.subst, Telescope.append_subst] using this
  | .bound hAt =>
      have hAt' := hAt.subst σ.paths.lift
      simp only [Proposition.subst, Ty.weaken_subst] at hAt'
      exact .bound hAt'
  | .intoBnd he =>
      have := LeCo.HasType.intoBnd (he.psubst hσ)
      simpa [LeCo.psubst, Ty.subst, Telescope.subst, Proposition.subst,
        Ty.weaken_subst] using this
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := LeCo.HasType.memberP (ha.psubst hσ) (he.psubst hσ) (hAt.subst σ.paths.lift)
      rw [Atom.path_psubst] at this
      rw [← Ty.substPath_var, ← Ty.substPath_var, Ty.substPath_subst, Ty.substPath_subst]
      exact this
  | @LeCo.HasType.memberP _ _ P S e Tel i S' T' hP he hAt =>
      have := LeCo.HasType.memberP (hP.psubst hσ) (he.psubst hσ) (hAt.subst σ.paths.lift)
      rw [PathCo.path_psubst] at this
      rw [Ty.substPath_subst, Ty.substPath_subst]
      exact this

theorem EqCo.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {φ : EqCo s1} {S T : Ty s1} (h : Γ1 ⊢ φ : S ≡ T) :
    Γ2 ⊢ φ.psubst σ : S.subst σ.paths ≡ T.subst σ.paths := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.psubst hσ)
  | .trans hφ hψ => exact .trans (hφ.psubst hσ) (hψ.psubst hσ)
  | .def hd => exact .defP (hσ.def_ _ _ _ hd)
  | .defP hd => exact .defP (hσ.defP _ _ _ hd)
  | @EqCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.memberP (ha.psubst hσ) (he.psubst hσ) (hAt.subst σ.paths.lift)
      rw [Atom.path_psubst] at this
      rw [← Ty.substPath_var, ← Ty.substPath_var, Ty.substPath_subst, Ty.substPath_subst]
      exact this
  | @EqCo.HasType.memberP _ _ P S e Tel i S' T' hP he hAt =>
      have := EqCo.HasType.memberP (hP.psubst hσ) (he.psubst hσ) (hAt.subst σ.paths.lift)
      rw [PathCo.path_psubst] at this
      rw [Ty.substPath_subst, Ty.substPath_subst]
      exact this

theorem Side.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {sd : Side s1} {X Y : Ty (s1,x)} (h : Side.HasType Γ1 sd X Y) :
    Side.HasType Γ2 (sd.psubst σ) (X.subst σ.paths.lift) (Y.subst σ.paths.lift) := by
  match h with
  | .none => exact .none
  | .bot => exact .bot
  | .top => exact .top
  | .some he =>
      have := Side.HasType.some (he.psubst hσ)
      rw [← Ty.weaken_subst, ← Ty.weaken_subst] at this
      exact this

theorem Morphism.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {src : Telescope (s1,x)} {m : Morphism s1}
    {Tel : Telescope (s1,x)} (h : Γ1 ⊢ m : src ⇒ Tel) :
    Γ2 ⊢ m.psubst σ : src.subst σ.paths.lift ⇒ Tel.subst σ.paths.lift := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.psubst hσ) (hAt.subst σ.paths.lift) (hpre.psubst hσ) (hpost.psubst hσ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.psubst hσ) (hAt.subst σ.paths.lift) (hpre.psubst hσ) (hpost.psubst hσ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.psubst hσ) (hAt.subst σ.paths.lift) (hpre.psubst hσ)
        (hpost.psubst hσ)
  | .eq hm hAt => exact .eq (hm.psubst hσ) (hAt.subst σ.paths.lift)
  | .eqSym hm hAt => exact .eqSym (hm.psubst hσ) (hAt.subst σ.paths.lift)
  | .has hm hAt => exact .has (hm.psubst hσ) (hAt.subst σ.paths.lift)
  | .bnd hm he =>
      have := Morphism.HasType.bnd (hm.psubst hσ) (he.psubst hσ)
      simpa [Morphism.psubst, Telescope.subst, Proposition.subst, Ty.subst,
        Ty.weaken_subst] using this
  | .hasVal hm hAt => exact .hasVal (hm.psubst hσ) (hAt.subst σ.paths.lift)
  | .hasOfVal hm hAt => exact .hasOfVal (hm.psubst hσ) (hAt.subst σ.paths.lift)
  | .aliasCopy hm hAt => exact .aliasCopy (hm.psubst hσ) (hAt.subst σ.paths.lift)

theorem Atom.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {a : Atom s1} {T : Ty s1} (h : Γ1 ⊢ₐ a : T) :
    Γ2 ⊢ᵖ a.psubst σ : T.subst σ.paths := by
  match h with
  | @Atom.HasType.var _ _ x => exact hσ.var x
  | .cast ha he => exact .cast (ha.psubst hσ) (he.psubst hσ)
  | @Atom.HasType.unfoldSelf _ _ a Tel ha =>
      have := PathCo.HasType.unfoldSelf (ha.psubst hσ)
      rw [Atom.path_psubst] at this
      show Γ2 ⊢ᵖ PathCo.unfoldSelf (a.psubst σ) :
        Ty.obj (((Tel.substVar a.root).weaken (k := .var)).subst σ.paths.lift)
      rw [Telescope.weaken_subst, ← Telescope.substPath_var, Telescope.substPath_subst]
      exact this
  | @Atom.HasType.foldSelf _ _ a Tel ha =>
      have ha' := ha.psubst hσ
      change Γ2 ⊢ᵖ a.psubst σ :
        Ty.obj (((Tel.substVar a.root).weaken (k := .var)).subst σ.paths.lift) at ha'
      rw [Telescope.weaken_subst, ← Telescope.substPath_var, Telescope.substPath_subst] at ha'
      have e : (Path.var a.root).subst σ.paths = (a.psubst σ).path := by
        rw [Atom.path_psubst]; rfl
      rw [e] at ha'
      exact .foldSelf ha'
  | .both ha hb hr =>
      have := PathCo.HasType.both (ha.psubst hσ) (hb.psubst hσ)
        (by rw [Atom.path_psubst, Atom.path_psubst, hr])
      simpa [Atom.psubst, Ty.subst, Telescope.append_subst] using this
  | @Atom.HasType.sngl _ _ a S α q ha hα =>
      have hα' := hα.psubst hσ
      change Γ2 ⊢ α.psubst σ : (σ.var a.root).path ≋ q.subst σ.paths at hα'
      rw [← Atom.path_psubst] at hα'
      have := PathCo.HasType.sngl (ha.psubst hσ) hα'
      rw [Ty.snglOf_subst]
      exact this

theorem PathCo.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {P : PathCo s1} {T : Ty s1} (h : Γ1 ⊢ᵖ P : T) :
    Γ2 ⊢ᵖ P.psubst σ : T.subst σ.paths := by
  match h with
  | @PathCo.HasType.var _ _ x => exact hσ.var x
  | @PathCo.HasType.sel _ _ P Tel i a hP hAt =>
      have := PathCo.HasType.sel (hP.psubst hσ) (hAt.subst σ.paths.lift)
      rw [PathCo.path_psubst] at this
      exact this
  | .cast hP he => exact .cast (hP.psubst hσ) (he.psubst hσ)
  | .alias hα hP =>
      have hα' := hα.psubst hσ
      rw [← PathCo.path_psubst] at hα'
      exact .alias hα' (hP.psubst hσ)
  | @PathCo.HasType.unfoldSelf _ _ P Tel hP =>
      have := PathCo.HasType.unfoldSelf (hP.psubst hσ)
      rw [PathCo.path_psubst] at this
      show Γ2 ⊢ᵖ (P.psubst σ).unfoldSelf :
        Ty.obj (((Tel.substPath P.path).weaken (k := .var)).subst σ.paths.lift)
      rw [Telescope.weaken_subst, Telescope.substPath_subst]
      exact this
  | @PathCo.HasType.foldSelf _ _ P Tel hP =>
      have hP' := hP.psubst hσ
      change Γ2 ⊢ᵖ P.psubst σ :
        Ty.obj (((Tel.substPath P.path).weaken (k := .var)).subst σ.paths.lift) at hP'
      rw [Telescope.weaken_subst, Telescope.substPath_subst, ← PathCo.path_psubst] at hP'
      exact .foldSelf hP'
  | .both hP hQ hr =>
      have := PathCo.HasType.both (hP.psubst hσ) (hQ.psubst hσ)
        (by rw [PathCo.path_psubst, PathCo.path_psubst, hr])
      simpa [PathCo.psubst, Ty.subst, Telescope.append_subst] using this
  | .sngl hP hα =>
      have hα' := hα.psubst hσ
      rw [← PathCo.path_psubst] at hα'
      have := PathCo.HasType.sngl (hP.psubst hσ) hα'
      rw [Ty.snglOf_subst]
      exact this
  | @PathCo.HasType.node _ _ p W ls vls ch hs hn =>
      have hn' := hσ.nodeB _ _ hn
      simp only [Block.subst, Witnesses.substPath_subst] at hn'
      have := PathCo.HasType.node (Γ := Γ2) (Path.isSel_subst σ.paths hs) hn'
      show Γ2 ⊢ᵖ PathCo.node (p.subst σ.paths) (W.subst σ.paths.lift) ls vls :
        Ty.obj ((Telescope.ofLiteral W ls vls).subst σ.paths.lift)
      rw [Telescope.ofLiteral_subst]
      exact this

theorem AliasCo.HasType.psubst {s1 s2 : Sig} {Γ1 : Ctx s1} {σ : PSub s1 s2} {Γ2 : Ctx s2}
    (hσ : PSub.Typed Γ1 σ Γ2) {α : AliasCo s1} {p q : Path s1} (h : Γ1 ⊢ α : p ≋ q) :
    Γ2 ⊢ α.psubst σ : p.subst σ.paths ≋ q.subst σ.paths := by
  match h with
  | .refl => exact .refl
  | .symm hα => exact .symm (hα.psubst hσ)
  | .trans hα hβ => exact .trans (hα.psubst hσ) (hβ.psubst hσ)
  | .sel hα => exact .sel (hα.psubst hσ)
  | @AliasCo.HasType.member _ _ P S e Tel i q hP he hAt =>
      have := AliasCo.HasType.member (hP.psubst hσ) (he.psubst hσ) (hAt.subst σ.paths.lift)
      rw [PathCo.path_psubst] at this
      rw [Path.substPath_subst]
      exact this

end

end FCdot

end Paths
