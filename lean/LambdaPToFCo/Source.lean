import LambdaPFC.Typing

/-!
# Flat path-dependent source fragment

This file isolates the smallest LambdaPFC fragment needed by the explicit-
coercion translation.  It deliberately reuses LambdaPFC's intrinsically
scoped paths, dependent types, and telescope.  In particular, there is no
second collection of term and type contexts.

A flat type package stores a type definition `T` directly at label `A`:

```text
  < y; A = T > : < x : {y}; A : T .. T >
```

If a path `p` has that exact package type, selecting the direct member gives
the interval `T .. T`.  Consequently the proper type `p.A` has both inclusions
`T <: p.A` and `p.A <: T`.  The fragment's derivations live in `Type`, rather
than `Prop`, so a later elaborator can recurse over the chosen proof and emit
explicit target evidence.

Only direct member lookup (`Path.Ty.sel_r`) is admitted here.  LambdaPFC's
record-spine lookup, functions, and general interval/pair subtyping remain in
the host calculus; they can be added to the translation independently.
-/

namespace LambdaPToFCo
namespace Source

open LambdaPFC

/-- The exact type assigned to a flat package containing `A = witness`.

The member signature is weakened because the first component of a LambdaPFC
pair binds one path variable in its second component.  The stored witness does
not use that binder. -/
def exactPackageTy (first : Fin n) (label : Name) (witness : Ty n) : Ty n :=
  .Pair (.Single (.var first)) label (Tau.intv witness witness).weaken

/-- Proof-relevant evidence that `package.label` is a direct, exact abstract
type member whose stored witness is `witness`.

The existential `first` is retained as data because it is part of the package
type.  No run-time realization or store evidence is involved. -/
structure ExactMember (context : Ctx n) (package : Path n) (label : Name)
    (witness : Ty n) : Type where
  first : Fin n
  packageTyping :
    LambdaPFC.Path.Ty context package
      (.ty (exactPackageTy first label witness))

namespace ExactMember

/-- Direct selection from an exact package synthesizes the exact interval
`witness .. witness`. -/
def selection
    (member : ExactMember context package label witness) :
    LambdaPFC.Path.Ty context (package.sel label)
      (.intv witness witness) := by
  simpa only [exactPackageTy, Tau.weaken_open] using
    member.packageTyping.sel_r

/-- Hence the path-dependent proper type `package.label` is well formed. -/
def selectionWf
    (member : ExactMember context package label witness) :
    LambdaPFC.Tau.Wf context (.ty (.TSel package label)) :=
  .sel member.selection .refl

end ExactMember

/-- The flat fragment of subtyping that a first translation milestone needs.

`widen` connects the singleton type synthesized for a term path with the
ordinary type synthesized for that path.  `selectLower` and `selectUpper` are
the genuinely path-dependent cases. -/
inductive Sub : (context : Ctx n) -> Ty n -> Ty n -> Type where
| refl : Sub context T T
| trans : Sub context S T -> Sub context T U -> Sub context S U
| top : Sub context T .Top
| widen :
    LambdaPFC.Path.Ty context path (.ty T) ->
    Sub context (.Single path) T
| selectLower :
    ExactMember context package label witness ->
    Sub context witness (.TSel package label)
| selectUpper :
    ExactMember context package label witness ->
    Sub context (.TSel package label) witness

namespace Sub

/-- Forget the flat-fragment restriction and recover the corresponding
LambdaPFC subtyping derivation. -/
def toLambdaPFC : Sub context S T ->
    LambdaPFC.Tau.Sub context (.ty S) (.ty T)
| .refl => .refl
| .trans first second =>
    .trans first.toLambdaPFC second.toLambdaPFC
| .top => .top
| .widen pathTyping => .widen pathTyping
| .selectLower member => .sel_lo member.selection .refl
| .selectUpper member => .sel_hi member.selection .refl

end Sub

/-- Minimal term typing for constructing an exact type package and using
fragment subtyping.  Existing LambdaPFC syntax is retained verbatim.

The target well-formedness proof in `sub` is kept explicit.  It is not an
implicit appeal to host typing: the later elaborator will receive the whole
chosen typing derivation as input. -/
inductive HasType : (context : Ctx n) -> Tm n -> Ty n -> Type where
| path :
    LambdaPFC.Path.Ty context path (.ty T) ->
    HasType context (.path path) (.Single path)
| typePackage :
    LambdaPFC.Tau.Wf context (.ty witness) ->
    HasType context
      (.pair first label (.type witness))
      (exactPackageTy first label witness)
| sub :
    HasType context term S ->
    Sub context S T ->
    LambdaPFC.Tau.Wf context (.ty T) ->
    HasType context term T

namespace HasType

/-- Forget the flat-fragment restriction and recover ordinary LambdaPFC term
typing. -/
def toLambdaPFC : HasType context term T ->
    LambdaPFC.Tm.Ty context term T
| .path pathTyping => .path pathTyping
| .typePackage witnessWf => .tpair witnessWf
| .sub termTyping subtype targetWf =>
    .sub termTyping.toLambdaPFC subtype.toLambdaPFC targetWf

end HasType

/-! ## A small static regression

The first context contains a value `y : Top`.  We construct the package
`<y; A = Top>`, then consider it bound as the newest variable `p`.  The exact
member evidence below derives both directions between `Top` and `p.A` and
embeds them into the full LambdaPFC judgments.
-/

namespace Regression

def label : Name := 0

def firstContext : Ctx 1 :=
  Ctx.nil.snoc .Top

def packageType : Ty 1 :=
  exactPackageTy 0 label .Top

def packageConstruction :
    HasType firstContext
      (.pair 0 label (.type .Top))
      packageType :=
  .typePackage .top

def packageConstructionInLambdaPFC :
    LambdaPFC.Tm.Ty firstContext
      (.pair 0 label (.type .Top))
      packageType :=
  packageConstruction.toLambdaPFC

def packageContext : Ctx 2 :=
  firstContext.snoc packageType

def member :
    ExactMember packageContext (.var 0) label .Top := by
  refine { first := 1, packageTyping := ?_ }
  simpa only [packageContext, firstContext, packageType, exactPackageTy,
    Ctx.lookup, Ty.weaken, Ty.rename, Tau.weaken, Tau.rename, Path.rename,
    FinFun.weaken, FinFun.id] using
    (LambdaPFC.Path.Ty.var :
      LambdaPFC.Path.Ty packageContext (.var 0)
        (.ty (packageContext.lookup 0)))

def lower :
    Sub packageContext .Top (.TSel (.var 0) label) :=
  .selectLower member

def upper :
    Sub packageContext (.TSel (.var 0) label) .Top :=
  .selectUpper member

def lowerInLambdaPFC :
    LambdaPFC.Tau.Sub packageContext
      (.ty .Top) (.ty (.TSel (.var 0) label)) :=
  lower.toLambdaPFC

def upperInLambdaPFC :
    LambdaPFC.Tau.Sub packageContext
      (.ty (.TSel (.var 0) label)) (.ty .Top) :=
  upper.toLambdaPFC

end Regression

end Source
end LambdaPToFCo
