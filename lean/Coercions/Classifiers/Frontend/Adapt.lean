import Coercions.Classifiers.Frontend.Search
import Coercions.Classifiers.Frontend.Ann

/-!
# The result types of the typer, and the cases of variables, boxes and unboxings

The typer of this front end elaborates: it returns the term it typed, which
may hold boxes, unboxings and unpackings the program did not write.  So a
result carries the annotated term beside its use set, its answer and the
derivation of the version's `HasTy` about the term's erasure
(`lean/Coercions/Classifiers/DotMNF/Typing.lean`).  Soundness is the result
type, and there is no soundness theorem to prove.

`HasTy` is indexed by an answer, a type or an existential over a capture
binder.  Variables, boxes and unboxings always have a plain answer, so every
case of this module concludes at `.ty T`.

This module holds the result types and the cases that the typer calls and
that do not recurse.

- `varSynth`, a variable at the least use set and the least capture set the
  rules give it.  It is the first view of the search, `varView`.
- `boxCheck?`, the `Box` rule in checking mode.  Against a goal `(□ T) ^ C`
  the variable is checked at `T` by a checker the typer passes in.
- `unboxSynth?`, the `Unbox` rule in synthesis mode.  It reads the first view
  of the variable that is a box of a type whose capture set is the unboxing's
  own, and charges that set to the use set.
- `adaptVar?`, box inference at a variable checked against a goal.

The views a variable has come from the search
(`lean/Coercions/Classifiers/Frontend/Search.lean`), so an unboxing reaches
a box through the upper bound of a type member as well as through the
declared type.

## Box inference

A program need not write its boxes.  Where a variable `x` is checked against
a goal `G`, `adaptVar?` tries three rules in order.

1. Plain checking.  A program that needs no box is not changed.
2. If no view of `x` is a box, the value `□ x` is checked against `G`:
   against a box goal by `boxCheck?`, otherwise by synthesis and the
   subtyping search.  The search reaches `G` through the lower bound of a
   type member, so a field declared at `z.A` with `A` bounded by a box takes
   a box.
3. If a view of `x` is a box `□(S ^ C)`, the unboxing `C ⊸ x` is synthesized
   and moved to `G` by the search.  The unboxing charges `C` to the use set.

The inserted term is `□ x` or `C ⊸ x`, which the typer returns in place of
`x`.  A fourth rule, in synthesis, is `unboxFirst?`: a receiver or a function
whose views have a box and no field or function type is unboxed at the set
of its first box view.  The same rule fills the set of an unboxing the
program wrote without one, since `Unbox` fixes that set to the boxed one.
Where the inserted term is not in a position that takes a term, the typer
binds it by a `let`.

These are the places where the Scala compiler adapts a box, at an expected
type, and in its order: plain first, then a box where the actual type is not
boxed, an unboxing where it is.  An insertion the rules do not license is a
`none`, never an ill-typed term, since every result carries its derivation.

Nothing of this module is part of the metatheory and no definition here lives
in a namespace of the version.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs Ctx Sub SubShape
  Subcap ESub HasTy DefsTy)
open scoped Classifiers.DotMNF

/-! ## The result types -/

/-- A synthesized typing: the elaborated term, its use set, its answer, and
the derivation about its erasure. -/
structure Elab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The answer. -/
  ans : ETy s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase ans

/-- A typing at a given answer: the elaborated term, its use set, and the
derivation about its erasure. -/
structure Checked {s : Sig} (Γ : Ctx s) (E : ETy s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase E

/-- A typing of a variable at a given type, at some use set. -/
structure VarChecked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty T)

/-- A typing of a definition list against a declaration shape.  `DefsTy`
types every definition at one use set, so the derivation is given at every
use set the least one is below. -/
structure DefsElab {s : Sig} (Γ : Ctx s) (S : Shape s) where
  /-- The elaborated definitions. -/
  tm : ADefs s
  /-- The least use set of the definitions. -/
  uses : CaptureSet s
  /-- The derivation at every larger use set. -/
  deriv : (U : CaptureSet s) → Subcap Γ uses U → DefsTy U Γ tm.erase S

/-- A typing at a given answer read as a synthesized one. -/
def Checked.toElab {s : Sig} {Γ : Ctx s} {E : ETy s} (r : Checked Γ E) : Elab Γ :=
  ⟨r.tm, r.uses, E, r.deriv⟩

/-! ## Widening a use set -/

/-- `sub` on the use set alone. -/
def widenUses {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {E : ETy s}
    (h : HasTy U Γ t E) (e : Subcap Γ U U') : HasTy U' Γ t E :=
  HasTy.sub h (ESub.refl E) e

/-- The left operand of a join, widened to the join. -/
def widenLeft {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {E : ETy s}
    (h : HasTy U Γ t E) (V : CaptureSet s) : HasTy (capJoin U V) Γ t E :=
  widenUses h (.elem (capJoin_left U V))

/-- The right operand of a join, widened to the join. -/
def widenRight {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {t : Tm s} {E : ETy s}
    (U : CaptureSet s) (h : HasTy V Γ t E) : HasTy (capJoin U V) Γ t E :=
  widenUses h (.elem (capJoin_right U V))

/-! ## A variable -/

/-- A variable at the least sets: `{}` and its declared type for a binder
declared at the empty set, `{x}` and its declared shape at `{x}` otherwise.
This is the first view of the variable. -/
def varSynth {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Elab Γ :=
  let v := varView Γ x
  ⟨.path (.var x), v.uses, .ty v.ty, v.deriv⟩

/-! ## A box value in checking mode -/

/-- `Box` against a goal `(□ T) ^ C`: the variable is checked at `T` by
`chk`, and the box is pure, so the goal's set is reached from `{}`
(`lean/Coercions/Classifiers/DotMNF/Typing.lean`, `HasTy.box`).  Any other
goal is `none`. -/
def boxCheck? {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    (chk : (T : Ty s) → Option (VarChecked Γ x T)) (G : Ty s) :
    Option (HasTy [] Γ (.val (.box x)) (.ty G)) :=
  match G with
  | .capt C (.box T) =>
      (chk T).map fun r =>
        HasTy.sub (HasTy.box r.deriv) (.ty (.capt .refl (Subcap.empty C))) .refl
  | _ => none

/-! ## An unboxing in synthesis mode -/

/-- An unboxing read off one view: the view must be a box of a type whose
capture set is `C`.  The use set is `C` joined with the view's own, the least
set the `Unbox` rule allows. -/
def unboxOfView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s) (v : View Γ x) :
    Option (Elab Γ) :=
  match hv : v.ty with
  | .capt _ (.box (.capt C' S)) =>
      if hc : C' = C then
        some ⟨.unbox (some C) x, capJoin C v.uses, .ty (S ^ C),
          HasTy.unbox (widenRight C (hc ▸ hv ▸ v.deriv)) (.elem (capJoin_left C v.uses))⟩
      else none
  | _ => none

/-- `Unbox` at the first view of the list that is a box of a type at the
capture set `C`.  The views of the search include the upper bound of a
selection, so `C ⊸ e` with `e : o.A` reaches the box `o.A` stands for. -/
def unboxSynth? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s)
    (vs : List (View Γ x)) : Option (Elab Γ) :=
  firstSome (unboxOfView C) vs

/-! ## Moving a typing to a goal -/

/-- A synthesized typing moved to a goal by a decided equality or by the
answer search, at the set fuel `c` and the shape fuel `n`. -/
def subsume? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) (r : Elab Γ) (E : ETy s) :
    Option (Checked Γ E) :=
  if h : r.ans = E then some ⟨r.tm, r.uses, h ▸ r.deriv⟩
  else (esub? D c n r.ans E).map fun e => ⟨r.tm, r.uses, HasTy.sub r.deriv e .refl⟩

/-! ## Box inference at a variable -/

/-- The capture set of the boxed type of the first view that is a box.
`none` when no view of the variable is a box. -/
def firstBoxSet? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (CaptureSet s) :=
  firstSome (fun v =>
    match v.ty with
    | .capt _ (.box (.capt C _)) => some C
    | _ => none) vs

/-- The value `□ x` at a goal.  Against a box goal the variable is checked at
the boxed type by `chk`.  Otherwise the box of the first view, which `Box`
types at the empty use set, is moved to the goal by the search. -/
def boxAt? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (c n : Nat)
    (chk : (T : Ty s) → Option (VarChecked Γ x T)) (G : Ty s) : Option (Checked Γ (.ty G)) :=
  ((boxCheck? chk G).map fun d => (⟨.box x, [], d⟩ : Checked Γ (.ty G))).orElse fun _ =>
    let v := varView Γ x
    subsume? D c n ⟨.box x, [], .ty ((Shape.box v.ty) ^ []), HasTy.box v.deriv⟩ (.ty G)

/-- Rules two and three of box inference, with plain checking already
failed: `□ x` when no view of `x` is a box, `C ⊸ x` at the set of the first
box view otherwise. -/
def adaptInsert? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (c n : Nat)
    (chk : (T : Ty s) → Option (VarChecked Γ x T)) (vs : List (View Γ x)) (G : Ty s) :
    Option (Checked Γ (.ty G)) :=
  match firstBoxSet? vs with
  | none => boxAt? D c n chk G
  | some C => (unboxSynth? C vs).bind fun r => subsume? D c n r (.ty G)

/-- Box inference at a variable checked against a goal: plain checking by
`chk`, then `adaptInsert?`.  `chk` is the variable checker of the typer and
`vs` the views of the variable, so the module needs no typer.  The result
holds the variable itself, `□ x` or `C ⊸ x`. -/
def adaptVar? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (c n : Nat)
    (chk : (T : Ty s) → Option (VarChecked Γ x T)) (vs : List (View Γ x)) (G : Ty s) :
    Option (Checked Γ (.ty G)) :=
  ((chk G).map fun r => (⟨.path (.var x), r.uses, r.deriv⟩ : Checked Γ (.ty G))).orElse fun _ =>
    adaptInsert? D c n chk vs G

/-- Rule four of box inference: a variable unboxed at the set of its first
box view.  The typer uses it at a receiver or a function whose views have
no field or function type, and at an unboxing written with no set. -/
def unboxFirst? {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (Elab Γ) :=
  (firstBoxSet? vs).bind fun C => unboxSynth? C vs

/-! ## Tests

The two judgments of C7 that the version derives with a box and with an
unboxing (`lean/Coercions/Classifiers/DotMNF/Examples.lean`, `C7box1` and
`C7unbox`), and the rejections of the same cases.  The contexts are the
version's, so every capture binder of a scope is in them: `κ₁` sits under
the two body roots and arrow binders of the two lambdas. -/

section Tests

open Classifiers.DotMNF.Examples

/-- `κ₁` at the signature of `C7Ctxe`. -/
private abbrev k1e : BVar (Sig.body (Sig.body ([],c,c)),x,x) .cap := .there (.there C7k1)

/-- `κ₂` at the signature of `C7Ctxe`. -/
private abbrev k2e : BVar (Sig.body (Sig.body ([],c,c)),x,x) .cap := .there (.there C7k2)

/-- `κ₁` at the signature of `C7Ctxz`, under the class root and the self. -/
private abbrev k1z : BVar ((Sig.body (Sig.body ([],c,c)),c),x) .cap := .there (.there C7k1)

/-- `κ₂` at the signature of `C7Ctxz`. -/
private abbrev k2z : BVar ((Sig.body (Sig.body ([],c,c)),c),x) .cap := .there (.there C7k2)

/-- `f₁` at the signature of `C7Ctxz`. -/
private abbrev f1z : BVar ((Sig.body (Sig.body ([],c,c)),c),x) .var := up2 (up .here)

/-- `f₁` at the signature of `C7Ctxe`. -/
private abbrev f1e : BVar (Sig.body (Sig.body ([],c,c)),x,x) .var := .there (.there (up .here))

/-- One unit of the table and of the view closure. -/
private def b1 : Budget := { decls := 1, views := 1, sub := 2, cap := 2, typer := 0, obj := 0 }

/-- A variable checked at a goal by its first view, exactly or through the
search, at one unit of the table and of the search. -/
private def checkFirst {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    Option (VarChecked Γ x T) :=
  let v := varView Γ x
  if h : v.ty = T then some ⟨v.uses, h ▸ v.deriv⟩
  else (sub? (decls b1 Γ) 2 2 v.ty T).map fun e => ⟨v.uses, HasTy.sub v.deriv (.ty e) .refl⟩

/-- The unboxing of C7's client synthesizes the use set and the type of the
version's `C7unbox`. -/
example : (unboxSynth? [CapAtom.cvar k1e] [varView C7Ctxe .here]).map (fun r => (r.uses, r.ans))
    = some ([CapAtom.cvar k1e], .ty (arrowS ^ [CapAtom.cvar k1e])) := by decide

/-- An unboxing at a set that is not the box's own is rejected. -/
example : (unboxSynth? [] [varView C7Ctxe .here]).isSome = false := by decide

/-- A variable that is not a box is not unboxed: `f₁` is a closure. -/
example : (unboxSynth? [CapAtom.cvar k1e] [varView C7Ctxe f1e]).isSome = false := by decide

/-- The field `e₁ = □ f₁` of C7 checks at its declared type, by `sc-var`
from `{f₁}` to `{κ₁}`. -/
example : (boxCheck? (checkFirst C7Ctxz f1z) ((Shape.box (capTy k1z)) ^ [])).isSome = true := by
  decide +kernel

/-- Boxing `f₁` at a box of the other capability is rejected. -/
example : (boxCheck? (checkFirst C7Ctxz f1z) ((Shape.box (capTy k2z)) ^ [])).isSome = false := by
  decide +kernel

/-- A goal that is not a box is rejected. -/
example : (boxCheck? (checkFirst C7Ctxz f1z) (capTy k1z)).isSome = false := by decide

/-- A pure binder is its own first view at the empty use set. -/
example : ((varSynth C7Ctxe .here).uses, (varSynth C7Ctxe .here).ans) =
    ([], .ty ((Shape.box (capTy k1e)) ^ [])) := by decide

/-- A binder declared at a capability is used at its own atom. -/
example : (varSynth C7Ctxe f1e).uses = [CapAtom.var f1e] := by decide

/-- Box inference at one variable of a context, with `checkFirst` as the
plain checker: the inserted term and its use set. -/
private def adaptAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Option (ATm s × CaptureSet s) :=
  (adaptVar? (decls b1 Γ) 2 2 (checkFirst Γ x) (views (decls b1 Γ) b1 x) G).map
    fun r => (r.tm, r.uses)

/-- The field `e₁ = f₁` of C7 with no box written, checked at its declared
type: the second rule inserts `□ f₁`, at the empty use set. -/
example : adaptAt C7Ctxz f1z ((Shape.box (capTy k1z)) ^ []) = some (.box f1z, []) := by
  decide +kernel

/-- The client's `(e : (⊤ → ⊤) ^ {κ₁})`: the third rule inserts
`{κ₁} ⊸ e`, which charges `{κ₁}`. -/
example : adaptAt C7Ctxe .here (capTy k1e) =
    some (.unbox (some [CapAtom.cvar k1e]) .here, [CapAtom.cvar k1e]) := by decide +kernel

/-- A variable whose type already reaches the goal is not changed. -/
example : adaptAt C7Ctxe f1e (capTy k1e) = some (.path (.var f1e), [CapAtom.var f1e]) := by
  decide +kernel

/-- Boxing `f₁` at a box of the other capability is rejected, and so is
unboxing `e` at a capability of the other one. -/
example : adaptAt C7Ctxz f1z ((Shape.box (capTy k2z)) ^ []) = none := by decide +kernel

example : adaptAt C7Ctxe .here (capTy k2e) = none := by decide +kernel

/-- The fourth rule at `e`: the unboxing at the set of its first box view. -/
example : (unboxFirst? (views (decls b1 C7Ctxe) b1 .here)).map (fun r => (r.tm, r.uses, r.ans)) =
    some (.unbox (some [CapAtom.cvar k1e]) .here, [CapAtom.cvar k1e], .ty (capTy k1e)) := by
  decide +kernel

/-- A closure has no box view, so the fourth rule does not apply to it. -/
example : (unboxFirst? (views (decls b1 C7Ctxe) b1 f1e)).isSome = false := by decide +kernel

end Tests

end ClassifiersFrontend
