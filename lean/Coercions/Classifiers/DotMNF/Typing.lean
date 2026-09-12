import Coercions.Classifiers.DotMNF.Syntax
import Coercions.Classifiers.FCdot.Context

namespace Classifiers

/-!
# DOT-MNF^cc typing

Subcapturing, shape subtyping, subtyping, term typing and definition typing,
as five mutually inductive families.  They live in `Type`, not in `Prop`:
the translation of Plan III §8 is a function on derivations and therefore
needs `Type`-valued elimination.

Term typing carries a use set as its first index, `U; Γ ⊢ t : T`, as in
Capless Fig. 2 and Reacap Fig. 4.  A value is pure, its use set is empty and
its type's capture set is the use set of its body without the binder; `Var`
refines the binder's capture set to `{x}`; `sub` stays on every term, as
vanilla's is, and carries the use-set subsumption beside the subtyping.

Well-formedness appears only as a premise of the two rules that introduce a
type out of thin air: the domain annotation of a lambda and the result type
of a `let`.  Everything else is derived from those, so no side predicate on
derivations is needed.

One deviation from the surface presentation of §3.4: `{}-I` is stated as

```text
Γ, x : (μ(x. S)) ^ U ⊢ d : S   ⟹   Γ ⊢ ν(x. d) : (μ(x. S)) ^ U
```

rather than with the *opened* self type `S^x` as the binding for `x`.  With
intrinsic scoping a context entry lives in the signature *before* its own
binder, so `S^x` cannot be an entry.  The two are interderivable, since
`Rec-I` and `Rec-E` convert between `x : μ(x. S)` and `x : S^x`, and the
shape chosen here is the one that matches `FCdot.Ctx` binder for binder.

The fragment of §3.2 is enforced in the rules that need it (plan §13 items
8 and 9): `Rec-I` and `Rec-E` carry `Shape.Decl` premises for the bodies
they open and close, as does `Wf.mu`.  Intersections are *not* restricted:
`And₁`, `And₂`, `And` and `And-I` apply to arbitrary operands, since a
non-declaration operand `B` translates to the one-proposition telescope
`[⊑ ⟦B⟧]` -- the self-bound proposition of `FCdot` (plan §13 item 9).  The
declaration shapes are still the only bodies a `μ` may bind, because a bound
proposition never mentions the self.  `{}-I` no longer restricts aliasing
among the definitions: the target's alias-tolerant resolution
(`FCdot.Ctx.resolve`) admits same-block aliases and cycles (a cyclic alias
resolves to `⊤`), so the self-alias restriction that used to accompany
`Defs.Distinct` here is gone.

## Subcapturing at a variable

`sc-var` reads the binder's *declared* capture set off the context,
`Γ ⊢ {x} <:ᶜ (Γ(x)).captureSet`, as Capless and Reacap Fig. 4 state it and
as the target's `FCdot.CapCo.capvar` reads it off `Ctx.lookupTy` through the
atom rule `Atom.HasType.var`.  The form with a typing premise,
`U; Γ ⊢ x : S ^ C ⟹ Γ ⊢ {x} <:ᶜ C`, is the derived rule `Subcap.ofVar`
below: it is admissible, so nothing is lost, and it cannot be the primitive,
because `Var` already refines the capture set of `x` to `{x}`, so the
declared set of the binder is unreachable from any typing derivation.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Contexts -/

/-- A context is a list of types, newest binder first.  A binder introduced
by an object literal remembers the literal's definitions and the capture set
assigned to the literal (`consSelf`); its type is `(μ(x. S)) ^ U` like any
other binder, and `lookup` does not distinguish the two.  The translation of
Plan III §8 does: such a binder is typed at the literal's precise type in the
target.  A platform capture binder (`consC`) carries no bound: it is rigid. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Ty s → Ctx (s,x)
  | consSelf : Ctx s → Defs (s,x) → Shape (s,x) → CaptureSet s → Ctx (s,x)
  | consC : Ctx s → Ctx (s,c)
  /-- A scope root: the capture binder a lambda body or an object body opens
      for itself.  It carries no payload, exactly as `consC` carries none, so
      `Platform.ctx` and `Platform.store` are textually unchanged and every
      platform binder is still rigid. -/
  | consRoot : Ctx s → Ctx (s,c)
  /-- An instance binder: the capture binder a pack opens for its witness,
      carrying the witness set it stands for.  It is Capless's
      `CBinding.inst`, and it is the one binder `Subcap.inst` reads. -/
  | consInst : Ctx s → CaptureSet s → Ctx (s,c)
  /-- A platform capture binder with a declared classifier.  `consC` is this
      binder with no declaration, and it translates to `∗`.  It is a seventh
      constructor and not a payload on `consC`, so that `Platform.ctx`,
      `Platform.store` and every existing source example keep their context
      (decision 10). -/
  | consCls : Ctx s → Cls.Classifier → Ctx (s,c)

/-- The type of a variable, weakened into the current scope.  The self
binder of a literal has type `(μ S) ^ U`, weakened, which is the plan's
`U↑`. -/
def Ctx.lookup : Ctx s → BVar s .var → Ty s
  | .cons _ T, .here => T.weaken
  | .cons Γ _, .there y => (Γ.lookup y).weaken
  | .consSelf _ _ S U, .here => (Ty.capt U (.mu S)).weaken
  | .consSelf Γ _ _ _, .there y => (Γ.lookup y).weaken
  | .consC Γ, .there y => (Γ.lookup y).weaken
  | .consRoot Γ, .there y => (Γ.lookup y).weaken
  | .consInst Γ _, .there y => (Γ.lookup y).weaken
  | .consCls Γ _, .there y => (Γ.lookup y).weaken

/-- The set an instance binder stands for, weakened into the current scope,
if the binder is an instance binder at all. -/
def Ctx.instSet? : Ctx s → BVar s .cap → Option (CaptureSet s)
  | .cons Γ _, .there κ => (Γ.instSet? κ).map CaptureSet.weaken
  | .consSelf Γ _ _ _, .there κ => (Γ.instSet? κ).map CaptureSet.weaken
  | .consC Γ, .there κ => (Γ.instSet? κ).map CaptureSet.weaken
  | .consC _, .here => none
  | .consRoot Γ, .there κ => (Γ.instSet? κ).map CaptureSet.weaken
  | .consRoot _, .here => none
  | .consInst _ C, .here => some C.weaken
  | .consInst Γ _, .there κ => (Γ.instSet? κ).map CaptureSet.weaken
  | .consCls _ _, .here => none
  | .consCls Γ _, .there κ => (Γ.instSet? κ).map CaptureSet.weaken

/-- `κ` is an instance binder standing for `C`.  An `abbrev`, so `Decidable`
is synthesised and a derivation may discharge it by `decide`. -/
abbrev Ctx.InstOf (Γ : Ctx s) (κ : BVar s .cap) (C : CaptureSet s) : Prop :=
  Γ.instSet? κ = some C

/-- The classifier a capture binder declares, if it declares one.  Only a
`consCls` binder does, which is Fact 2 on the source side.  A classifier is
closed data, so nothing is weakened on the way out. -/
def Ctx.clsOfB : Ctx s → BVar s .cap → Option Cls.Classifier
  | .consCls _ c, .here => some c
  | .consCls Γ _, .there κ => Γ.clsOfB κ
  | .cons Γ _, .there κ => Γ.clsOfB κ
  | .consSelf Γ _ _ _, .there κ => Γ.clsOfB κ
  | .consC Γ, .there κ => Γ.clsOfB κ
  | .consC _, .here => none
  | .consRoot Γ, .there κ => Γ.clsOfB κ
  | .consRoot _, .here => none
  | .consInst Γ _, .there κ => Γ.clsOfB κ
  | .consInst _ _, .here => none

/-- The classifier an atom's binder declares.  It answers only at a capture
binder, mirroring the target's `FCdot.Ctx.clsOf?`. -/
def Ctx.clsOf? : Ctx s → CapAtom s → Option Cls.Classifier
  | Γ, .cvar κ => Γ.clsOfB κ
  | _, _ => none

/-- `a` is a binder with declared classifier `c`.  An `abbrev`, so
`Decidable` is synthesised and a derivation may discharge it by `decide`,
which is `Ctx.InstOf`'s discipline. -/
abbrev Ctx.ClsOf (Γ : Ctx s) (a : CapAtom s) (c : Cls.Classifier) : Prop :=
  Γ.clsOf? a = some c

/-! ### The classified binder is read back

A declared classifier is read back at the binder, which is the discipline
`Ctx.InstOf` set.  The other two facts of the new constructor, that it is a
rigid capture binder and not a scope root, are stated with the level
machinery below, where `Ctx.rootB` and `Ctx.root?` are in scope. -/

/-- A declared classifier is read back at the binder, by `decide`. -/
theorem Ctx.clsOf_consCls (c : Cls.Classifier) :
    (Ctx.nil.consCls c).ClsOf (.cvar .here) c := by
  simp [Ctx.ClsOf, Ctx.clsOf?, Ctx.clsOfB]

/-! ## Where a written type's reading comes from

`Shape.expand` threads one capture set down a written type, and this is
where that set comes from at the position the type is written at.  The
source has no universal root atom (decision 23), so a position with no
enclosing root binder reads `any` as the program's platform set.  The rest
of the source's level machinery is the `Levels` section below. -/

/-- The innermost root binder of a source context, if it has one.  It is the
target's `FCdot.Ctx.root?` over the source's six constructors. -/
def Ctx.root? : Ctx s → Option (BVar s .cap)
  | .nil => none
  | .consRoot _ => some .here
  | .consC Γ => Γ.root?.map .there
  | .consInst Γ _ => Γ.root?.map .there
  | .cons Γ _ => Γ.root?.map .there
  | .consSelf Γ _ _ _ => Γ.root?.map .there
  | .consCls Γ _ => Γ.root?.map .there

/-- The reading of a position: the innermost root of the context as a
singleton, and the program's platform set `P` where the context has none.
It is not used by `expand`.  It is the statement of where the reading set an
`expand` is called at comes from, and it is what an example cites when it
writes a type at a position inside a lambda body. -/
def Ctx.reading (Γ : Ctx s) (P : CaptureSet s) : CaptureSet s :=
  match Γ.root? with
  | some κ => [CapAtom.cvar κ]
  | none => P

/-! ## Levels

**B3.4.**  The target's level machinery (`FCdot/Context.lean:169-231`) over
the source's five context constructors that append a binder.  A level is a
position on the spine and not a field on a binding.  The level of a binder
is the innermost root binder of the prefix that precedes it, and a root is
its own level.  `none` is the outermost level, and `FCdot.depthGe none d` is
`true`, which says that a binder with no enclosing root is absorbed by every
root.  That is the compiler's unscoped reading.

`FCdot.BVar.depth` and `FCdot.depthGe` are reused and not copied, because
the source already reads `FCdot`'s `BVar`.  The source names no universal
root atom (decision 23), so the outermost level is named by no atom here,
and a notation is below no root (decision 30). -/

/-- The level of a binder: the innermost root of the prefix before it, and
itself when the binder is a root.  `none` is the outermost level. -/
def Ctx.lvl : Ctx s → BVar s k → Option (BVar s .cap)
  | .consRoot _, .here => some .here
  | .consC Γ, .here => Γ.root?.map .there
  | .consInst Γ _, .here => Γ.root?.map .there
  | .cons Γ _, .here => Γ.root?.map .there
  | .consSelf Γ _ _ _, .here => Γ.root?.map .there
  | .consCls Γ _, .here => Γ.root?.map .there
  | .consRoot Γ, .there y => (Γ.lvl y).map .there
  | .consC Γ, .there y => (Γ.lvl y).map .there
  | .consInst Γ _, .there y => (Γ.lvl y).map .there
  | .cons Γ _, .there y => (Γ.lvl y).map .there
  | .consSelf Γ _ _ _, .there y => (Γ.lvl y).map .there
  | .consCls Γ _, .there y => (Γ.lvl y).map .there

/-- The binder is a scope root.  Only `consRoot` opens one, so a platform
capture binder and an instance binder are `false` at their own binder. -/
def Ctx.rootB : Ctx s → BVar s .cap → Bool
  | .consRoot _, .here => true
  | .consC _, .here => false
  | .consInst _ _, .here => false
  | .consCls _ _, .here => false
  | .consRoot Γ, .there κ => Γ.rootB κ
  | .consC Γ, .there κ => Γ.rootB κ
  | .consInst Γ _, .there κ => Γ.rootB κ
  | .cons Γ _, .there κ => Γ.rootB κ
  | .consSelf Γ _ _ _, .there κ => Γ.rootB κ
  | .consCls Γ _, .there κ => Γ.rootB κ

/-- The atom is a scope root of the source context.  There is no universal
root on the source side, so only a capture binder can be one. -/
def Ctx.isRootB (Γ : Ctx s) : CapAtom s → Bool
  | .cvar κ => Γ.rootB κ
  | _ => false

/-- `e` is at or outside the level of `r`.  A notation is below no root, so
the function is `false` there on either side (decision 30). -/
def Ctx.lvlLeB (Γ : Ctx s) : CapAtom s → CapAtom s → Bool
  | .var x, .cvar ρ => FCdot.depthGe ((Γ.lvl x).map FCdot.BVar.depth) (some ρ.depth)
  | .cvar κ, .cvar ρ => FCdot.depthGe ((Γ.lvl κ).map FCdot.BVar.depth) (some ρ.depth)
  | .sel x _, .cvar ρ => FCdot.depthGe ((Γ.lvl x).map FCdot.BVar.depth) (some ρ.depth)
  /- A projection is at the level of what it projects (decision D8 of K2).
     The target reads through a projection on both sides already, so the
     clause is added for the two calculi to agree. -/
  | .proj a _, r => Γ.lvlLeB a r
  | _, _ => false

/-- `r` is a scope root of `Γ`.  An `abbrev`, so that `Decidable` is
synthesised and `by decide` works. -/
abbrev Ctx.IsRoot (Γ : Ctx s) (r : CapAtom s) : Prop := Γ.isRootB r = true

/-- `e` is at or outside the level of `r`.  An `abbrev`, for the same
reason. -/
abbrev Ctx.LvlLe (Γ : Ctx s) (e r : CapAtom s) : Prop := Γ.lvlLeB e r = true

/-- A classified binder is not a scope root, exactly as `consC` is not. -/
theorem Ctx.rootB_consCls {s : Sig} (Γ : Ctx s) (c : Cls.Classifier) :
    (Γ.consCls c).rootB .here = false := rfl

/-- And it does not become the innermost root of its own context. -/
theorem Ctx.root?_consCls {s : Sig} (Γ : Ctx s) (c : Cls.Classifier) :
    (Γ.consCls c).root? = Γ.root?.map .there := rfl

/-! ### The spine facts

Each is a short induction on the context, mirroring `FCdot/Levels.lean:30-60`
one for one.  Two small arithmetic steps come first, because every proof
below reads a comparison of depths. -/

/-- A comparison is kept by a smaller right side. -/
theorem Ctx.depthGe_step {m : Option Nat} {a b : Nat}
    (h : FCdot.depthGe m (some a) = true) (hb : b ≤ a) :
    FCdot.depthGe m (some b) = true := by
  cases m with
  | none => rfl
  | some m₀ =>
      simp only [FCdot.depthGe, decide_eq_true_eq] at h ⊢
      exact Nat.le_trans hb h

/-- One binder deeper on both sides is the same comparison.  This is the
whole content of the weakening commutations below. -/
theorem Ctx.depthGe_there {s : Sig} {k0 : Kind} (o : Option (BVar s .cap))
    (ρ : BVar s .cap) :
    FCdot.depthGe ((o.map (BVar.there (k0 := k0))).map FCdot.BVar.depth)
        (some (BVar.there (k0 := k0) ρ).depth)
      = FCdot.depthGe (o.map FCdot.BVar.depth) (some ρ.depth) := by
  cases o with
  | none => rfl
  | some κ =>
      simp only [Option.map_some, FCdot.BVar.depth_there, FCdot.depthGe, decide_eq_decide]
      exact ⟨fun h => Nat.le_of_succ_le_succ h, fun h => Nat.succ_le_succ h⟩

/-- The innermost root binder is a root. -/
theorem Ctx.root?_isRoot {s : Sig} (Γ : Ctx s) :
    ∀ {ρ : BVar s .cap}, Γ.root? = some ρ → Γ.rootB ρ = true := by
  induction Γ with
  | nil => intro ρ h; simp [Ctx.root?] at h
  | consRoot Γ ih =>
      intro ρ h
      simp only [Ctx.root?, Option.some.injEq] at h
      subst h
      rfl
  | cons Γ T ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [Ctx.root?, hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.rootB]
          exact ih hr
  | consSelf Γ d S U ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [Ctx.root?, hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.rootB]
          exact ih hr
  | consC Γ ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [Ctx.root?, hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.rootB]
          exact ih hr
  | consInst Γ C ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [Ctx.root?, hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.rootB]
          exact ih hr
  | consCls Γ c ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [Ctx.root?, hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.rootB]
          exact ih hr

/-- A root binder is at its own level. -/
theorem Ctx.lvl_root {s : Sig} (Γ : Ctx s) :
    ∀ {κ : BVar s .cap}, Γ.rootB κ = true → Γ.lvl κ = some κ := by
  induction Γ with
  | nil => intro κ _; cases κ
  | consRoot Γ ih =>
      intro κ h
      cases κ with
      | here => rfl
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]
  | cons Γ T ih =>
      intro κ h
      cases κ with
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]
  | consSelf Γ d S U ih =>
      intro κ h
      cases κ with
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]
  | consC Γ ih =>
      intro κ h
      cases κ with
      | here => simp [Ctx.rootB] at h
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]
  | consInst Γ C ih =>
      intro κ h
      cases κ with
      | here => simp [Ctx.rootB] at h
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]
  | consCls Γ c ih =>
      intro κ h
      cases κ with
      | here => simp [Ctx.rootB] at h
      | there κ₀ =>
          simp only [Ctx.rootB] at h
          simp only [Ctx.lvl, ih h, Option.map_some]

/-- A level is a root. -/
theorem Ctx.lvl_isRoot {s : Sig} (Γ : Ctx s) :
    ∀ {k : Kind} {y : BVar s k} {κ₀ : BVar s .cap},
      Γ.lvl y = some κ₀ → Γ.rootB κ₀ = true := by
  induction Γ with
  | nil => intro k y κ₀ _; cases y
  | consRoot Γ ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          simp only [Ctx.lvl, Option.some.injEq] at h
          subst h
          rfl
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl
  | cons Γ T ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [Ctx.lvl, hr] at h
          | some ρ =>
              simp only [Ctx.lvl, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl
  | consSelf Γ d S U ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [Ctx.lvl, hr] at h
          | some ρ =>
              simp only [Ctx.lvl, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl
  | consC Γ ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [Ctx.lvl, hr] at h
          | some ρ =>
              simp only [Ctx.lvl, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl
  | consInst Γ C ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [Ctx.lvl, hr] at h
          | some ρ =>
              simp only [Ctx.lvl, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl
  | consCls Γ c ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [Ctx.lvl, hr] at h
          | some ρ =>
              simp only [Ctx.lvl, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [Ctx.lvl, hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB]
              exact ih hl

/-- The innermost root has minimal depth among the roots. -/
theorem Ctx.root?_min {s : Sig} (Γ : Ctx s) :
    ∀ {ρ κ : BVar s .cap}, Γ.root? = some ρ → Γ.rootB κ = true →
      ρ.depth ≤ κ.depth := by
  induction Γ with
  | nil => intro ρ κ h _; simp [Ctx.root?] at h
  | consRoot Γ ih =>
      intro ρ κ h _
      simp only [Ctx.root?, Option.some.injEq] at h
      subst h
      exact Nat.zero_le _
  | cons Γ T ih =>
      intro ρ κ h hκ
      cases κ with
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [Ctx.root?, hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB] at hκ
              simp only [FCdot.BVar.depth_there]
              exact Nat.succ_le_succ (ih hr hκ)
  | consSelf Γ d S U ih =>
      intro ρ κ h hκ
      cases κ with
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [Ctx.root?, hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB] at hκ
              simp only [FCdot.BVar.depth_there]
              exact Nat.succ_le_succ (ih hr hκ)
  | consC Γ ih =>
      intro ρ κ h hκ
      cases κ with
      | here => simp [Ctx.rootB] at hκ
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [Ctx.root?, hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB] at hκ
              simp only [FCdot.BVar.depth_there]
              exact Nat.succ_le_succ (ih hr hκ)
  | consInst Γ C ih =>
      intro ρ κ h hκ
      cases κ with
      | here => simp [Ctx.rootB] at hκ
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [Ctx.root?, hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB] at hκ
              simp only [FCdot.BVar.depth_there]
              exact Nat.succ_le_succ (ih hr hκ)
  | consCls Γ c ih =>
      intro ρ κ h hκ
      cases κ with
      | here => simp [Ctx.rootB] at hκ
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [Ctx.root?, hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.rootB] at hκ
              simp only [FCdot.BVar.depth_there]
              exact Nat.succ_le_succ (ih hr hκ)

/-- A context with no root binder has every binder at the outermost level. -/
theorem Ctx.root?_none {s : Sig} (Γ : Ctx s) :
    ∀ {k : Kind} (y : BVar s k), Γ.root? = none → Γ.lvl y = none := by
  induction Γ with
  | nil => intro k y _; cases y
  | consRoot Γ ih => intro k y h; simp [Ctx.root?] at h
  | cons Γ T ih =>
      intro k y h
      simp only [Ctx.root?, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [Ctx.lvl, h]
      | there y₀ => simp [Ctx.lvl, ih y₀ h]
  | consSelf Γ d S U ih =>
      intro k y h
      simp only [Ctx.root?, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [Ctx.lvl, h]
      | there y₀ => simp [Ctx.lvl, ih y₀ h]
  | consC Γ ih =>
      intro k y h
      simp only [Ctx.root?, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [Ctx.lvl, h]
      | there y₀ => simp [Ctx.lvl, ih y₀ h]
  | consInst Γ C ih =>
      intro k y h
      simp only [Ctx.root?, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [Ctx.lvl, h]
      | there y₀ => simp [Ctx.lvl, ih y₀ h]
  | consCls Γ c ih =>
      intro k y h
      simp only [Ctx.root?, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [Ctx.lvl, h]
      | there y₀ => simp [Ctx.lvl, ih y₀ h]

/-- A root is at or outside its own level. -/
theorem Ctx.LvlLe.refl_of_root {s : Sig} {Γ : Ctx s} {r : CapAtom s}
    (h : Γ.IsRoot r) : Γ.LvlLe r r := by
  cases r with
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | sel x A => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | any => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | fresh => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | proj a φ => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | cvar κ =>
      simp only [Ctx.IsRoot, Ctx.isRootB] at h
      have hκ : Γ.lvl κ = some κ := Γ.lvl_root h
      simp [Ctx.LvlLe, Ctx.lvlLeB, hκ, FCdot.depthGe]

/-- A projection is at the level of what it projects.  The clause of
`Ctx.lvlLeB` read as an equation, and the step every proof below takes at a
projected atom. -/
@[simp] theorem Ctx.lvlLeB_proj {s : Sig} (Γ : Ctx s) (a : CapAtom s) (φ : Cls.Kind)
    (r : CapAtom s) : Γ.lvlLeB (.proj a φ) r = Γ.lvlLeB a r := rfl

/-- A root at a smaller depth is still at or outside the level of `e`.  The
inner step of transitivity, by induction on `e` because a projection reads
through to what it projects. -/
theorem Ctx.lvlLe_depth_step {s : Sig} {Γ : Ctx s} {κ ρ : BVar s .cap} :
    ∀ {e : CapAtom s}, Γ.LvlLe e (.cvar κ) → ρ.depth ≤ κ.depth → Γ.LvlLe e (.cvar ρ)
  | .var _, h, hd => Ctx.depthGe_step h hd
  | .cvar _, h, hd => Ctx.depthGe_step h hd
  | .sel _ _, h, hd => Ctx.depthGe_step h hd
  | .any, h, _ => by simp [Ctx.LvlLe, Ctx.lvlLeB] at h
  | .fresh, h, _ => by simp [Ctx.LvlLe, Ctx.lvlLeB] at h
  | .proj a _, h, hd => Ctx.lvlLe_depth_step (e := a) h hd

/-- Transitivity through a root. -/
theorem Ctx.LvlLe.trans {s : Sig} {Γ : Ctx s} {e r r' : CapAtom s}
    (hr : Γ.IsRoot r) (h₁ : Γ.LvlLe e r) (h₂ : Γ.LvlLe r r') : Γ.LvlLe e r' := by
  cases r with
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | sel x A => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | any => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | fresh => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | proj a φ => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | cvar κ =>
      simp only [Ctx.IsRoot, Ctx.isRootB] at hr
      have hκ : Γ.lvl κ = some κ := Γ.lvl_root hr
      cases r' with
      | var x => simp [Ctx.LvlLe, Ctx.lvlLeB] at h₂
      | sel x A => simp [Ctx.LvlLe, Ctx.lvlLeB] at h₂
      | any => simp [Ctx.LvlLe, Ctx.lvlLeB] at h₂
      | fresh => simp [Ctx.LvlLe, Ctx.lvlLeB] at h₂
      | proj a φ => simp [Ctx.LvlLe, Ctx.lvlLeB] at h₂
      | cvar ρ =>
          have hd : ρ.depth ≤ κ.depth := by
            simp only [Ctx.LvlLe, Ctx.lvlLeB, hκ, Option.map_some, FCdot.depthGe,
              decide_eq_true_eq] at h₂
            exact h₂
          exact Ctx.lvlLe_depth_step h₁ hd

/-! ### The weakening commutations

Appending a binder at the innermost end never changes the level of an older
binder, because every `.there` clause of `Ctx.lvl` recurses into the tail
and never reads the head binder.  One lemma per appending constructor. -/

/-- A term binder. -/
theorem Ctx.lvlLeB_weaken {s : Sig} (Γ : Ctx s) (T : Ty s) (e r : CapAtom s) :
    (Γ.cons T).lvlLeB (CapAtom.weaken (k := .var) e) (CapAtom.weaken (k := .var) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-- The self binder of a literal. -/
theorem Ctx.lvlLeB_weakenSelf {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) (e r : CapAtom s) :
    (Γ.consSelf d S U).lvlLeB (CapAtom.weaken (k := .var) e) (CapAtom.weaken (k := .var) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-- A rigid capture binder. -/
theorem Ctx.lvlLeB_weakenC {s : Sig} (Γ : Ctx s) (e r : CapAtom s) :
    (Γ.consC).lvlLeB (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-- A scope root. -/
theorem Ctx.lvlLeB_weakenRoot {s : Sig} (Γ : Ctx s) (e r : CapAtom s) :
    (Γ.consRoot).lvlLeB (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-- An instance binder. -/
theorem Ctx.lvlLeB_weakenInst {s : Sig} (Γ : Ctx s) (C : CaptureSet s) (e r : CapAtom s) :
    (Γ.consInst C).lvlLeB (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-- A classified capture binder. -/
theorem Ctx.lvlLeB_weakenCls {s : Sig} (Γ : Ctx s) (c : Cls.Classifier) (e r : CapAtom s) :
    (Γ.consCls c).lvlLeB (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      = Γ.lvlLeB e r := by
  induction e with
  | var x => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | cvar κ => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | sel x A => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | any => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | fresh => cases r <;> first | rfl | exact Ctx.depthGe_there _ _
  | proj a φ ih => first | exact ih | simpa [CapAtom.rename] using ih

/-! ## The scope contexts

The three contexts a scope opens, mirroring `FCdot.Ctx.scope`,
`FCdot.Ctx.body` and `FCdot.Ctx.objBody` binder for binder, so that
`Ctx.translate` is a homomorphism on them. -/

/-- A declaration shape under the class root the object body opens. -/
abbrev Shape.underRoot (S : Shape (s,x)) : Shape ((s,c),x) := S.rename Rename.succ.lift

/-- A scope: its own root, then the arrow's capture binder. -/
def Ctx.scope (Γ : Ctx s) : Ctx ((s,c),c) := (Γ.consRoot).consC

/-- The scope a pack opens: its own root, then the witness binder, bound to
the witness set.  It is the source's copy of `FCdot.Ctx.scopeInst`. -/
def Ctx.scopeInst (Γ : Ctx s) (C : CaptureSet s) : Ctx ((s,c),c) :=
  (Γ.consRoot).consInst C.weaken

/-- A lambda body: a scope, then the parameter at the domain read under the
body root. -/
def Ctx.body (Γ : Ctx s) (T : Dom s) : Ctx (((s,c),c),x) := Γ.scope.cons T.underRoot

/-- An object body: the class root, then the self binder, which remembers
the definitions and the assigned capture set as `consSelf` always did. -/
def Ctx.objBody (Γ : Ctx s) (d : Defs ((s,c),x)) (S : Shape (s,x)) (U : CaptureSet s) :
    Ctx ((s,c),x) :=
  (Γ.consRoot).consSelf d S.underRoot U.weaken

/-! ### T-B3.1, the scope order on the source side

In a lambda body the parameter and the arrow's capture binder have the same
level, and that level is the body root.  This is the target's
`FCdot.Ctx.body_lvl_param`, `body_lvl_arrow` and `body_lvl_root`
(`FCdot/Context.lean:278, 282, 286`) on the source, and it is the sentence
"parameter `any`s are at the same level as the function's local `any`".
Both sides compute, so each proof is `rfl`. -/

/-- The parameter of a body is at the level of the body root. -/
theorem Ctx.body_lvl_param {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .var) .here = some (.there (.there .here)) := rfl

/-- The arrow's capture binder is at the same level, the body root. -/
theorem Ctx.body_lvl_arrow {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .cap) (.there .here) = some (.there (.there .here)) := rfl

/-- And the body root is its own level. -/
theorem Ctx.body_lvl_root {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .cap) (.there (.there .here)) = some (.there (.there .here)) := rfl

/-- The body root is a root of the body context. -/
theorem Ctx.body_isRoot {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).IsRoot (.cvar (.there (.there .here))) := rfl


/-! ## The judgments -/

mutual

/-- Subcapturing `Γ ⊢ C₁ <:ᶜ C₂`, Reacap Fig. 4. -/
inductive Subcap : {s : Sig} → Ctx s → CaptureSet s → CaptureSet s → Type where
  | refl {s : Sig} {Γ : Ctx s} {C : CaptureSet s} : Subcap Γ C C
  | trans {s : Sig} {Γ : Ctx s} {C1 C2 C3 : CaptureSet s} :
      Subcap Γ C1 C2 → Subcap Γ C2 C3 → Subcap Γ C1 C3
  /-- A syntactic inclusion, decided. -/
  | elem {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s} :
      CaptureSet.Subset C1 C2 → Subcap Γ C1 C2
  | union {s : Sig} {Γ : Ctx s} {C1 C2 D : CaptureSet s} :
      Subcap Γ C1 D → Subcap Γ C2 D → Subcap Γ (C1 ∪ C2) D
  /-- `sc-var`: a binder is below the capture set it is declared at. -/
  | var {s : Sig} {Γ : Ctx s} {x : BVar s .var} :
      Subcap Γ [.var x] (Γ.lookup x).captureSet
  /-- An instance binder is above the set it stands for.  It is Capless's
      `cinstr` (`Capless/Subcapturing.lean:28-33`), and it is what the pack's
      residual reads. -/
  | inst {s : Sig} {Γ : Ctx s} {κ : BVar s .cap} {C : CaptureSet s} :
      Ctx.InstOf Γ κ C → Subcap Γ C [.cvar κ]
  /-- **B3.5.**  `Γ ⊢ {e} <:ᶜ {κ}` when `κ` is a scope root and the level of
      `e` is `κ` or encloses it.  B0's rule on the source, with a capture
      binder on the right and no universal root (decision 23).  Both sides
      are singletons, both premises are `Bool` computable, and a set-shaped
      conclusion is a `union` of instances.

      The rule is directional where the compiler's test is not, and that is
      decision 34: the level order relates the arrow's capture binder and
      the body root in both directions, but this rule asks for a root on its
      right and the arrow binder is a `consC`, so only the direction from
      the arrow binder to the body root is an instance. -/
  | level {s : Sig} {Γ : Ctx s} {e : CapAtom s} {κ : BVar s .cap} :
      Ctx.IsRoot Γ (.cvar κ) → Ctx.LvlLe Γ e (.cvar κ) →
      Subcap Γ [e] [.cvar κ]
  /-- `sc-sel-lower`: the lower bound of a capture member. -/
  | selLower {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {c1 c2 D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.cap A c1 c2) ^ D)) →
      Subcap Γ c1 [.sel x A]
  /-- `sc-sel-upper`: the upper bound of a capture member. -/
  | selUpper {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {c1 c2 D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.cap A c1 c2) ^ D)) →
      Subcap Γ [.sel x A] c2
  /-- A projection only drops atoms, so a projected set is below the set it
      projects.  The source twin of `FCdot.CapCo.HasType.unprojC`. -/
  | unproj {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} :
      Subcap Γ (CaptureSet.proj C φ) C
  /-- `sc-proj` (`Subcapt.lean:69`), stated on a set: a set every capability
      of which carries a classifier `φ` admits loses nothing under the
      projection at `φ`.  The source twin of `FCdot.CapCo.HasType.projC`. -/
  | proj {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} :
      CapKind Γ C φ → Subcap Γ C (CaptureSet.proj C φ)
  /-- The congruence.  `sc-var` at a projection is this rule composed with
      `var`, since `[a].proj ψ` is `[a ↾ ψ]`.  The source twin of
      `FCdot.CapCo.HasType.projMono`. -/
  | projMono {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {ψ : Cls.Kind} :
      Subcap Γ C D → Subcap Γ (CaptureSet.proj C ψ) (CaptureSet.proj D ψ)

/-- Capture kinding `Γ ⊢ C :ᶜ φ`: every capability the set `C` reaches
carries a classifier that `φ` admits.  It is `Type`-valued and it lives in
this block, because `ksel` premises `HasTy` and because the translation is a
function into the target's `FCdot.KindCo` (decision D1 of K2).  It mirrors
`FCdot.KindCo.HasType` rule by rule, with `ksel` in place of `kmember`.
Every rule concludes about a general atom and reads `CapAtom.base` and
`CapAtom.kindOf`, which is `Cls.Kind.top` at a bare atom, so the family
covers a bare atom exactly as Capless(K)'s does. -/
inductive CapKind : {s : Sig} → Ctx s → CaptureSet s → Cls.Kind → Type where
  /-- k-empty (`Subcapt.lean:55`). -/
  | nil {s : Sig} {Γ : Ctx s} {φ : Cls.Kind} : CapKind Γ [] φ
  /-- k-union (`Subcapt.lean:53`). -/
  | cons {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {φ : Cls.Kind} :
      CapKind Γ [a] φ → CapKind Γ C φ → CapKind Γ (a :: C) φ
  /-- k-cbound and k-absurd in one (`Subcapt.lean:50,54`), read through
      `CapAtom.kindOf`, which is `⊤` at a bare atom.  At a bare atom the
      premise asks that `φ` admit every classifier, which is what a root
      stands for. -/
  | kproj {s : Sig} {Γ : Ctx s} {a : CapAtom s} {φ : Cls.Kind} :
      a.kindOf.Subkind φ → CapKind Γ [a] φ
  /-- k-label and k-label-absurd in one (`Subcapt.lean:51-52`), at a binder
      that declares a classifier.  A `consC` binder declares none and is
      kinded only by `kproj`: an unwritten classifier means unknown, which
      is the K1 addendum and the revised decision 9. -/
  | kcls {s : Sig} {Γ : Ctx s} {a : CapAtom s} {c : Cls.Classifier} {φ : Cls.Kind} :
      Ctx.ClsOf Γ a.base c → (a.kindOf.Contains c → φ.Contains c) →
      CapKind Γ [a] φ
  /-- k-var (`Subcapt.lean:48`), at the source's own `sc-var`. -/
  | kvar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {x : BVar s .var} {φ : Cls.Kind} :
      a.base = CapAtom.var x →
      CapKind Γ (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ →
      CapKind Γ [a] φ
  /-- k-cvar (`Subcapt.lean:49`).  The source's only set-bounded capture
      binder is the instance binder, so `Ctx.InstOf` is the whole premise. -/
  | kcvar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap}
      {C : CaptureSet s} {φ : Cls.Kind} :
      a.base = CapAtom.cvar κ → Ctx.InstOf Γ κ C →
      CapKind Γ (CaptureSet.proj C a.kindOf) φ → CapKind Γ [a] φ
  /-- The elimination of a kind-bounded capture member `{C : φ}`, beside
      `Subcap.selUpper`.  It translates to `FCdot.KindCo.kmember`. -/
  | ksel {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {φ : Cls.Kind} {D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.capk A φ) ^ D)) →
      CapKind Γ [.sel x A] φ
  /-- A projection only shrinks a set, so a kinded set stays kinded under
      one. -/
  | kprojS {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {ψ φ : Cls.Kind} :
      CapKind Γ C φ → CapKind Γ (CaptureSet.proj C ψ) φ
  /-- k-sub (`Subcapt.lean:99-109`), a primitive constructor. -/
  | ksub {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ₁ φ₂ : Cls.Kind} :
      CapKind Γ C φ₁ → φ₁.Subkind φ₂ → CapKind Γ C φ₂
  /-- Kinding is antitone along subcapturing.  The source twin of
      `FCdot.Ctx.KindLe.mono`, and what `SubShape.capkI` needs at a
      literal. -/
  | kle {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {φ : Cls.Kind} :
      Subcap Γ C D → CapKind Γ D φ → CapKind Γ C φ

/-- Shape subtyping.  Vanilla's subtyping, on shapes, with capturing types
where vanilla had types, plus `cap` for capture-member declarations and
`box` for the box former.  No `Rec` rule: recursion is `Rec-I`/`Rec-E` on
variables. -/
inductive SubShape : {s : Sig} → Ctx s → Shape s → Shape s → Type where
  | top {s : Sig} {Γ : Ctx s} {S : Shape s} : SubShape Γ S .top
  | bot {s : Sig} {Γ : Ctx s} {S : Shape s} : SubShape Γ .bot S
  | refl {s : Sig} {Γ : Ctx s} {S : Shape s} : SubShape Γ S S
  | trans {s : Sig} {Γ : Ctx s} {S M T : Shape s} :
      SubShape Γ S M → SubShape Γ M T → SubShape Γ S T
  | and1 {s : Sig} {Γ : Ctx s} {S T : Shape s} : SubShape Γ (.and S T) S
  | and2 {s : Sig} {Γ : Ctx s} {S T : Shape s} : SubShape Γ (.and S T) T
  | and {s : Sig} {Γ : Ctx s} {S T U : Shape s} :
      SubShape Γ S T → SubShape Γ S U → SubShape Γ S (.and T U)
  | fld {s : Sig} {Γ : Ctx s} {a : Label} {T U : Ty s} :
      Sub Γ T U → SubShape Γ (.fld a T) (.fld a U)
  | typ {s : Sig} {Γ : Ctx s} {A : Label} {S1 S2 T1 T2 : Shape s} :
      SubShape Γ S2 S1 → SubShape Γ T1 T2 →
      SubShape Γ (.typ A S1 T1) (.typ A S2 T2)
  /-- `Cap`: contravariant in the lower bound, covariant in the upper. -/
  | cap {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 c1' c2' : CaptureSet s} :
      Subcap Γ c1' c1 → Subcap Γ c2 c2' →
      SubShape Γ (.cap A c1 c2) (.cap A c1' c2')
  /-- `Boxed`. -/
  | box {s : Sig} {Γ : Ctx s} {T T' : Ty s} :
      Sub Γ T T' → SubShape Γ (.box T) (.box T')
  /-- `Sel-<:`. -/
  | selUpper {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {S T : Shape s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.typ A S T) ^ C)) →
      SubShape Γ (.sel (.var x) A) T
  /-- `<:-Sel`. -/
  | selLower {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {S T : Shape s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.typ A S T) ^ C)) →
      SubShape Γ S (.sel (.var x) A)
  /-- Contravariant domain, covariant codomain.  Both arrows' capture
      binders are opened at one scope, and that scope has a root of its own,
      as the target's `FCdot.ShapeCo.HasType.pi` does. -/
  | all {s : Sig} {Γ : Ctx s} {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Sub Γ.scope T2.underRoot T1.underRoot →
      ESub (Γ.body T2) U1.underRoot U2.underRoot →
      SubShape Γ (.all T1 U1) (.all T2 U2)
  /-- Introduction of a kind bound: a set-bounded member whose upper bound
      is kinded at `φ` is below the member bounded by `φ`.  It is sound by
      `FCdot.Ctx.KindLe.mono`, and it is how a literal reaches a kind bound,
      since there is no definition form for `capk` (decision 17). -/
  | capkI {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 : CaptureSet s} {φ : Cls.Kind} :
      CapKind Γ c2 φ → SubShape Γ (.cap A c1 c2) (.capk A φ)
  /-- Widening of a kind bound. -/
  | capk {s : Sig} {Γ : Ctx s} {A : Label} {φ₁ φ₂ : Cls.Kind} :
      φ₁.Subkind φ₂ → SubShape Γ (.capk A φ₁) (.capk A φ₂)

/-- Subtyping on capturing types: `Capt`. -/
inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | capt {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} :
      SubShape Γ S S' → Subcap Γ C C' → Sub Γ (S ^ C) (S' ^ C')

/-- Inclusion between answers.  `pack` widens a plain answer at a witness,
which is the compiler's own widening step and is subsumption on the source
side, so no source term former for a pack is needed (decision 19).  `exist`
is Capless's `EType` congruence (`Capless/Subtyping.lean:22-24`) with the
source's own rigid binder under a scope root. -/
inductive ESub : {s : Sig} → Ctx s → ETy s → ETy s → Type where
  | ty {s : Sig} {Γ : Ctx s} {T T' : Ty s} : Sub Γ T T' → ESub Γ (.ty T) (.ty T')
  /-- Packing: the witness is below the declared bound, and the residual
      inclusion is read under an instance binding for the witness, under a
      root of its own (decision 20). -/
  | pack {s : Sig} {Γ : Ctx s} {C C₀ : CaptureSet s} {T' : Ty s} {T : Ty (s,c)} :
      Subcap Γ C C₀ →
      Sub (Γ.scopeInst C) ((T'.weaken (k := .cap)).weaken (k := .cap)) (Dom.underRoot T) →
      ESub Γ (.ty T') (∃ᶜ[C₀] T)
  /-- Congruence: the bound is covariant and both bodies are read under a
      scope of their own. -/
  | exist {s : Sig} {Γ : Ctx s} {C₀ C₀' : CaptureSet s} {T T' : Ty (s,c)} :
      Subcap Γ C₀ C₀' →
      Sub Γ.scope (Dom.underRoot T) (Dom.underRoot T') →
      ESub Γ (∃ᶜ[C₀] T) (∃ᶜ[C₀'] T')

/-- Term typing `U; Γ ⊢ t : E`, the use set first.  The type index is an
answer (B2.10); a term with a plain type is indexed at `.ty T`. -/
inductive HasTy : {s : Sig} → CaptureSet s → Ctx s → Tm s → ETy s → Type where
  | var {s : Sig} {Γ : Ctx s} {x : BVar s .var} :
      HasTy [.var x] Γ (.path (.var x)) (.ty ((Γ.lookup x).shape ^ [.var x]))
  /-- `All-I`.  A value is pure and its type's capture set is the use set of
      its body without the binder. -/
  | lam {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {T1 : Dom s} {t : Tm (Sig.body s)}
      {T2 : Cod s} :
      HasTy (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here])
        (Γ.body T1) t T2.underRoot → Ty.Wf T1 →
      HasTy [] Γ (.val (.lam T1 t)) (.ty ((Shape.all T1 T2) ^ U))
  /-- `All-E`. -/
  | app {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x y : BVar s .var}
      {T1 : Dom s} {T2 : Cod s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.all T1 T2) ^ C)) →
      HasTy U Γ (.path (.var y)) (.ty (T1.subst (Subst.singleC (.var y)))) →
      HasTy U Γ (.app x y) (T2.subst (Subst.arg y))
  /-- `{}-I`.  The self binder remembers the definitions and the capture set
      assigned to the literal. -/
  | obj {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {d : Defs ((s,c),x)} {S : Shape (s,x)} :
      DefsTy (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here])
        (Γ.objBody d S U) d S.underRoot →
      Defs.Distinct d →
      HasTy [] Γ (.val (.obj d)) (.ty ((Shape.mu S) ^ U))
  /-- `Box`: boxing is pure. -/
  | box {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var} {T : Ty s} :
      HasTy U Γ (.path (.var x)) (.ty T) →
      HasTy [] Γ (.val (.box x)) (.ty ((Shape.box T) ^ []))
  /-- `{}-E`. -/
  | proj {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {a : Label} {T : Ty s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.fld a T) ^ C)) →
      HasTy U Γ (.proj x a) (.ty T)
  | «let» {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {u : Tm (s,x)}
      {T T' : Ty s} :
      HasTy U Γ t (.ty T) →
      HasTy (CaptureSet.weaken U) (Γ.cons T) u (.ty (Ty.weaken T')) →
      Ty.Wf T' →
      HasTy U Γ (.let t u) (.ty T')
  /-- `Unbox`: the boxed set is charged against the use set. -/
  | unbox {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape s} {C D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.box (S ^ C)) ^ D)) →
      Subcap Γ C U →
      HasTy U Γ (.unbox C x) (.ty (S ^ C))
  /-- Unpacking an existential answer: the head's bound is charged to the
      declared use set, the answer avoids both opened binders, and the body
      may name the opened binder in its own use set.  It is Capless's
      `letex` (`Capless/Typing.lean:58-61`) with D6's declared use set. -/
  | letex {s : Sig} {Γ : Ctx s} {U₁ U₂ C₀ : CaptureSet s} {t : Tm s}
      {u : Tm ((s,c),x)} {T : Ty (s,c)} {E : ETy s} :
      HasTy U₁ Γ t (∃ᶜ[C₀] T) →
      Subcap Γ C₀ U₂ →
      HasTy (CaptureSet.weaken (CaptureSet.weaken (k := .cap) U₂) ∪ [.cvar (.there .here)])
        ((Γ.consC).cons T) u (ETy.weaken (ETy.weaken (k := .cap) E)) →
      HasTy (U₁ ∪ U₂) Γ (.letex t u) E
  /-- `Rec-I`, for declaration-shaped bodies. -/
  | recI {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape (s,x)} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((S.substVar x) ^ C)) → Shape.Decl S →
      HasTy U Γ (.path (.var x)) (.ty ((Shape.mu S) ^ C))
  /-- `Rec-E`, for declaration-shaped bodies. -/
  | recE {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape (s,x)} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty ((Shape.mu S) ^ C)) → Shape.Decl S →
      HasTy U Γ (.path (.var x)) (.ty ((S.substVar x) ^ C))
  /-- `And-I`, on variables only. -/
  | andI {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S1 S2 : Shape s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (.ty (S1 ^ C)) →
      HasTy U Γ (.path (.var x)) (.ty (S2 ^ C)) →
      HasTy U Γ (.path (.var x)) (.ty ((Shape.and S1 S2) ^ C))
  | sub {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {E E' : ETy s} :
      HasTy U Γ t E → ESub Γ E E' → Subcap Γ U U' → HasTy U' Γ t E'

/-- Definition typing. -/
inductive DefsTy : {s : Sig} → CaptureSet s → Ctx s → Defs s → Shape s → Type where
  | typ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {A : Label} {S : Shape s} :
      DefsTy U Γ (.typ A S) (.typ A S S)
  | cap {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {A : Label} {c : CaptureSet s} :
      DefsTy U Γ (.cap A c) (.cap A c c)
  | trm {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {a : Label} {t : Tm s} {T : Ty s} :
      HasTy U Γ t (.ty T) → DefsTy U Γ (.trm a t) (.fld a T)
  | and {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d1 d2 : Defs s} {S1 S2 : Shape s} :
      DefsTy U Γ d1 S1 → DefsTy U Γ d2 S2 → DefsTy U Γ (.and d1 d2) (.and S1 S2)

end

/-! ## Member-free source evidence

**T-B3.4, step 3.**  Source subcapturing that reads no telescope and no
instance binder: it is `refl`, `trans`, `elem`, `union`, `var` and `level`,
and now the three projection rules, and it excludes `inst`, `selLower` and
`selUpper`.  Those three are exactly the rules whose translation is
`eqToLe` or `member`, which are exactly the two target rules
`FCdot.CapCo.MemberFree` excludes, and exactly where a bad capture bound can
enter (example C3).  Kinding evidence that reads no telescope is the same
restriction on `CapKind`: it excludes `ksel`, exactly as
`FCdot.KindCo.MemberFree` excludes `kmember`.

The two are one mutual block, because `Subcap.proj` premises a kinding and
`CapKind.kle` premises a subcapturing.  That is why they sit here, beside
the judgments, and not in `DotToFCdot/Evidence.lean` where the subcapturing
half was stated before K2. -/

mutual

/-- Source subcapturing that reads no telescope and no instance binder. -/
inductive Subcap.MemberFree : {s : Sig} → {Γ : Ctx s} → {C D : CaptureSet s} →
    Subcap Γ C D → Prop where
  | refl {s : Sig} {Γ : Ctx s} {C : CaptureSet s} :
      (Subcap.refl (Γ := Γ) (C := C)).MemberFree
  | trans {s : Sig} {Γ : Ctx s} {C1 C2 C3 : CaptureSet s}
      {d : Subcap Γ C1 C2} {e : Subcap Γ C2 C3} :
      d.MemberFree → e.MemberFree → (Subcap.trans d e).MemberFree
  | elem {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
      (h : CaptureSet.Subset C1 C2) : (Subcap.elem (Γ := Γ) h).MemberFree
  | union {s : Sig} {Γ : Ctx s} {C1 C2 D : CaptureSet s}
      {d : Subcap Γ C1 D} {e : Subcap Γ C2 D} :
      d.MemberFree → e.MemberFree → (Subcap.union d e).MemberFree
  | var {s : Sig} {Γ : Ctx s} {x : BVar s .var} :
      (Subcap.var (Γ := Γ) (x := x)).MemberFree
  | level {s : Sig} {Γ : Ctx s} {e : CapAtom s} {κ : BVar s .cap}
      (h₁ : Ctx.IsRoot Γ (.cvar κ)) (h₂ : Ctx.LvlLe Γ e (.cvar κ)) :
      (Subcap.level h₁ h₂).MemberFree
  | unproj {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} :
      (Subcap.unproj (Γ := Γ) (C := C) (φ := φ)).MemberFree
  | proj {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
      {g : CapKind Γ C φ} : g.MemberFree → (Subcap.proj g).MemberFree
  | projMono {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {ψ : Cls.Kind}
      {d : Subcap Γ C D} : d.MemberFree → (Subcap.projMono (ψ := ψ) d).MemberFree

/-- Source kinding that reads no telescope: no `ksel`. -/
inductive CapKind.MemberFree : {s : Sig} → {Γ : Ctx s} → {C : CaptureSet s} →
    {φ : Cls.Kind} → CapKind Γ C φ → Prop where
  | nil {s : Sig} {Γ : Ctx s} {φ : Cls.Kind} :
      (CapKind.nil (Γ := Γ) (φ := φ)).MemberFree
  | cons {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s} {φ : Cls.Kind}
      {g : CapKind Γ [a] φ} {h : CapKind Γ C φ} :
      g.MemberFree → h.MemberFree → (CapKind.cons g h).MemberFree
  | kproj {s : Sig} {Γ : Ctx s} {a : CapAtom s} {φ : Cls.Kind}
      (h : a.kindOf.Subkind φ) : (CapKind.kproj (Γ := Γ) (a := a) h).MemberFree
  | kcls {s : Sig} {Γ : Ctx s} {a : CapAtom s} {c : Cls.Classifier} {φ : Cls.Kind}
      (h₁ : Ctx.ClsOf Γ a.base c) (h₂ : a.kindOf.Contains c → φ.Contains c) :
      (CapKind.kcls h₁ h₂).MemberFree
  | kvar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {x : BVar s .var} {φ : Cls.Kind}
      (h : a.base = CapAtom.var x)
      {g : CapKind Γ (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ} :
      g.MemberFree → (CapKind.kvar h g).MemberFree
  | kcvar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap}
      {C : CaptureSet s} {φ : Cls.Kind}
      (h : a.base = CapAtom.cvar κ) (hi : Ctx.InstOf Γ κ C)
      {g : CapKind Γ (CaptureSet.proj C a.kindOf) φ} :
      g.MemberFree → (CapKind.kcvar h hi g).MemberFree
  | kprojS {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {ψ φ : Cls.Kind}
      {g : CapKind Γ C φ} : g.MemberFree → (CapKind.kprojS (ψ := ψ) g).MemberFree
  | ksub {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ₁ φ₂ : Cls.Kind}
      {g : CapKind Γ C φ₁} (h : φ₁.Subkind φ₂) :
      g.MemberFree → (CapKind.ksub g h).MemberFree
  | kle {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {φ : Cls.Kind}
      {f : Subcap Γ C D} {g : CapKind Γ D φ} :
      f.MemberFree → g.MemberFree → (CapKind.kle f g).MemberFree

end

/-- Term typing at a plain answer.  Every statement that was written
`HasTy U Γ t T` with `T` a type is this one: the index of `HasTy` is an
answer since B2.10, and a plain answer is `.ty T`. -/
abbrev HasTyP {s : Sig} (U : CaptureSet s) (Γ : Ctx s) (t : Tm s) (T : Ty s) : Type :=
  HasTy U Γ t (.ty T)

/-! ## Derived rules

Four rules the plan's rule list uses in derived form.  None of them is
primitive; all four are definitions on derivations, so a translation may use
them. -/

/-- Reflexivity of subtyping, from the two reflexivities it pairs. -/
def Sub.refl {s : Sig} {Γ : Ctx s} : (T : Ty s) → Sub Γ T T
  | .capt _ _ => .capt .refl .refl

/-- Reflexivity of answer inclusion, from the reflexivity of its parts. -/
def ESub.refl {s : Sig} {Γ : Ctx s} : (E : ETy s) → ESub Γ E E
  | .ty T => .ty (Sub.refl T)
  | .ex _ T => .exist .refl (Sub.refl (Dom.underRoot T))

/-- The empty capture set is below every capture set. -/
def Subcap.empty {s : Sig} {Γ : Ctx s} (C : CaptureSet s) : Subcap Γ [] C :=
  .elem (CaptureSet.nil_subset C)

/-- `sc-var` in the form the plan lists it: from *any* typing of the
variable at a capture set, the variable is below that set.  Admissible by
induction on the typing derivation: `Var` concludes at `{x}` itself, the
three variable rules pass the capture set through, and `sub` composes the
capture-set half of its subtyping premise. -/
def Subcap.ofVar {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
    {S : Shape s} {C : CaptureSet s} :
    HasTy U Γ (.path (.var x)) (.ty (S ^ C)) → Subcap Γ [.var x] C
  | .var => .refl
  | .recI h _ => Subcap.ofVar h
  | .recE h _ => Subcap.ofVar h
  | .andI h _ => Subcap.ofVar h
  | .sub h (.ty (.capt _ g)) _ => .trans (Subcap.ofVar h) g

/-- A pure term may be used at any use set: `sub` on the use set alone. -/
def HasTy.widen {s : Sig} {Γ : Ctx s} {t : Tm s} {E : ETy s}
    (h : HasTy [] Γ t E) (U : CaptureSet s) : HasTy U Γ t E :=
  .sub h (ESub.refl E) (Subcap.empty U)

/-- The same for a block of definitions, field by field. -/
def DefsTy.widen {s : Sig} {Γ : Ctx s} {d : Defs s} {S : Shape s} :
    DefsTy [] Γ d S → (U : CaptureSet s) → DefsTy U Γ d S
  | .typ, _ => .typ
  | .cap, _ => .cap
  | .trm h, U => .trm (h.widen U)
  | .and h1 h2, U => .and (h1.widen U) (h2.widen U)

end DotMNF

end Classifiers
