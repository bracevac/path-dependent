import Coercions.CapturesCC.DotMNF.Syntax

namespace CapturesCC

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

/-! ## The scope contexts

The three contexts a scope opens, mirroring `FCdot.Ctx.scope`,
`FCdot.Ctx.body` and `FCdot.Ctx.objBody` binder for binder, so that
`Ctx.translate` is a homomorphism on them. -/

/-- A declaration shape under the class root the object body opens. -/
abbrev Shape.underRoot (S : Shape (s,x)) : Shape ((s,c),x) := S.rename Rename.succ.lift

/-- A scope: its own root, then the arrow's capture binder. -/
def Ctx.scope (Γ : Ctx s) : Ctx ((s,c),c) := (Γ.consRoot).consC

/-- A lambda body: a scope, then the parameter at the domain read under the
body root. -/
def Ctx.body (Γ : Ctx s) (T : Dom s) : Ctx (((s,c),c),x) := Γ.scope.cons T.underRoot

/-- An object body: the class root, then the self binder, which remembers
the definitions and the assigned capture set as `consSelf` always did. -/
def Ctx.objBody (Γ : Ctx s) (d : Defs ((s,c),x)) (S : Shape (s,x)) (U : CaptureSet s) :
    Ctx ((s,c),x) :=
  (Γ.consRoot).consSelf d S.underRoot U.weaken

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
  /-- `sc-sel-lower`: the lower bound of a capture member. -/
  | selLower {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {c1 c2 D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.cap A c1 c2) ^ D) →
      Subcap Γ c1 [.sel x A]
  /-- `sc-sel-upper`: the upper bound of a capture member. -/
  | selUpper {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {c1 c2 D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.cap A c1 c2) ^ D) →
      Subcap Γ [.sel x A] c2

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
      HasTy U Γ (.path (.var x)) ((Shape.typ A S T) ^ C) →
      SubShape Γ (.sel (.var x) A) T
  /-- `<:-Sel`. -/
  | selLower {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {A : Label} {S T : Shape s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.typ A S T) ^ C) →
      SubShape Γ S (.sel (.var x) A)
  /-- Contravariant domain, covariant codomain.  Both arrows' capture
      binders are opened at one scope, and that scope has a root of its own,
      as the target's `FCdot.ShapeCo.HasType.pi` does. -/
  | all {s : Sig} {Γ : Ctx s} {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Sub Γ.scope T2.underRoot T1.underRoot →
      Sub (Γ.body T2) U1.underRoot U2.underRoot →
      SubShape Γ (.all T1 U1) (.all T2 U2)

/-- Subtyping on capturing types: `Capt`. -/
inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | capt {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} :
      SubShape Γ S S' → Subcap Γ C C' → Sub Γ (S ^ C) (S' ^ C')

/-- Term typing `U; Γ ⊢ t : T`, the use set first. -/
inductive HasTy : {s : Sig} → CaptureSet s → Ctx s → Tm s → Ty s → Type where
  | var {s : Sig} {Γ : Ctx s} {x : BVar s .var} :
      HasTy [.var x] Γ (.path (.var x)) ((Γ.lookup x).shape ^ [.var x])
  /-- `All-I`.  A value is pure and its type's capture set is the use set of
      its body without the binder. -/
  | lam {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {T1 : Dom s} {t : Tm (Sig.body s)}
      {T2 : Cod s} :
      HasTy (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here])
        (Γ.body T1) t T2.underRoot → Ty.Wf T1 →
      HasTy [] Γ (.val (.lam T1 t)) ((Shape.all T1 T2) ^ U)
  /-- `All-E`. -/
  | app {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x y : BVar s .var}
      {T1 : Dom s} {T2 : Cod s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.all T1 T2) ^ C) →
      HasTy U Γ (.path (.var y)) (T1.subst (Subst.singleC (.var y))) →
      HasTy U Γ (.app x y) (T2.subst (Subst.arg y))
  /-- `{}-I`.  The self binder remembers the definitions and the capture set
      assigned to the literal. -/
  | obj {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {d : Defs ((s,c),x)} {S : Shape (s,x)} :
      DefsTy (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here])
        (Γ.objBody d S U) d S.underRoot →
      Defs.Distinct d →
      HasTy [] Γ (.val (.obj d)) ((Shape.mu S) ^ U)
  /-- `Box`: boxing is pure. -/
  | box {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var} {T : Ty s} :
      HasTy U Γ (.path (.var x)) T →
      HasTy [] Γ (.val (.box x)) ((Shape.box T) ^ [])
  /-- `{}-E`. -/
  | proj {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {a : Label} {T : Ty s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.fld a T) ^ C) →
      HasTy U Γ (.proj x a) T
  | «let» {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {u : Tm (s,x)}
      {T T' : Ty s} :
      HasTy U Γ t T →
      HasTy (CaptureSet.weaken U) (Γ.cons T) u (Ty.weaken T') →
      Ty.Wf T' →
      HasTy U Γ (.let t u) T'
  /-- `Unbox`: the boxed set is charged against the use set. -/
  | unbox {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape s} {C D : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.box (S ^ C)) ^ D) →
      Subcap Γ C U →
      HasTy U Γ (.unbox C x) (S ^ C)
  /-- `Rec-I`, for declaration-shaped bodies. -/
  | recI {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape (s,x)} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((S.substVar x) ^ C) → Shape.Decl S →
      HasTy U Γ (.path (.var x)) ((Shape.mu S) ^ C)
  /-- `Rec-E`, for declaration-shaped bodies. -/
  | recE {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S : Shape (s,x)} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) ((Shape.mu S) ^ C) → Shape.Decl S →
      HasTy U Γ (.path (.var x)) ((S.substVar x) ^ C)
  /-- `And-I`, on variables only. -/
  | andI {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var}
      {S1 S2 : Shape s} {C : CaptureSet s} :
      HasTy U Γ (.path (.var x)) (S1 ^ C) →
      HasTy U Γ (.path (.var x)) (S2 ^ C) →
      HasTy U Γ (.path (.var x)) ((Shape.and S1 S2) ^ C)
  | sub {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {T T' : Ty s} :
      HasTy U Γ t T → Sub Γ T T' → Subcap Γ U U' → HasTy U' Γ t T'

/-- Definition typing. -/
inductive DefsTy : {s : Sig} → CaptureSet s → Ctx s → Defs s → Shape s → Type where
  | typ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {A : Label} {S : Shape s} :
      DefsTy U Γ (.typ A S) (.typ A S S)
  | cap {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {A : Label} {c : CaptureSet s} :
      DefsTy U Γ (.cap A c) (.cap A c c)
  | trm {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {a : Label} {t : Tm s} {T : Ty s} :
      HasTy U Γ t T → DefsTy U Γ (.trm a t) (.fld a T)
  | and {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d1 d2 : Defs s} {S1 S2 : Shape s} :
      DefsTy U Γ d1 S1 → DefsTy U Γ d2 S2 → DefsTy U Γ (.and d1 d2) (.and S1 S2)

end

/-! ## Derived rules

Four rules the plan's rule list uses in derived form.  None of them is
primitive; all four are definitions on derivations, so a translation may use
them. -/

/-- Reflexivity of subtyping, from the two reflexivities it pairs. -/
def Sub.refl {s : Sig} {Γ : Ctx s} : (T : Ty s) → Sub Γ T T
  | .capt _ _ => .capt .refl .refl

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
    HasTy U Γ (.path (.var x)) (S ^ C) → Subcap Γ [.var x] C
  | .var => .refl
  | .recI h _ => Subcap.ofVar h
  | .recE h _ => Subcap.ofVar h
  | .andI h _ => Subcap.ofVar h
  | .sub h (.capt _ g) _ => .trans (Subcap.ofVar h) g

/-- A pure term may be used at any use set: `sub` on the use set alone. -/
def HasTy.widen {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasTy [] Γ t T) (U : CaptureSet s) : HasTy U Γ t T :=
  .sub h (Sub.refl T) (Subcap.empty U)

/-- The same for a block of definitions, field by field. -/
def DefsTy.widen {s : Sig} {Γ : Ctx s} {d : Defs s} {S : Shape s} :
    DefsTy [] Γ d S → (U : CaptureSet s) → DefsTy U Γ d S
  | .typ, _ => .typ
  | .cap, _ => .cap
  | .trm h, U => .trm (h.widen U)
  | .and h1 h2, U => .and (h1.widen U) (h2.widen U)

end DotMNF

end CapturesCC
