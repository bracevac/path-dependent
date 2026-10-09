import Coercions.Captures.Frontend.Avoid
import Coercions.Captures.Frontend.Ann

/-!
# Result types of the typer, and box inference at a variable

The typer elaborates.  It returns the term it typed, which may contain boxes
and unboxings the program did not write.  A result holds the elaborated term,
its use set, its type, and a derivation of `HasTy` for the term's erasure.
Soundness is therefore the result type.

This module defines the result types and the typer's cases that do not
recurse into a term.

- `varSynth`: a variable at the least use set and capture set the rules give
  it, its first view.
- `fnViewsF`, `fldViewsF`, `boxViewsF`: the function types, the fields at a
  label and the boxes a variable has.  They use the member lookup of
  `Look.lean`, which follows the upper bounds of type members, so an
  unboxing reaches a box that a member stands for.
- `boxCheckF`: the `Box` rule in checking mode.  Against a goal `(□ T) ^ C`
  the variable is checked at `T`.
- `unboxAll`: the `Unbox` rule at every box found with the unboxing's capture
  set.  It charges that set to the use set.
- `adaptVarF`: box inference at a variable checked against a goal.

## Box inference

A program need not write its boxes.  Where a variable `x` is checked against
a goal `G`, `adaptVarF` tries three rules in order.

1. Plain checking by the `var` goal of `Sub.lean`.  A program that needs no
   box is not changed.
2. If the lookup finds no box in `x`, `□ x` is checked against `G`.  A box
   goal uses `boxCheckF`.  Any other goal uses the subtyping algorithm, which
   reaches `G` through the lower bound of a type member.  So a field declared
   at `z.A` with `A` bounded by a box takes a box.
3. If the lookup finds a box `□(S ^ C)`, the unboxing `C ⊸ x` at the set `C`
   of the first box is checked against `G`.  It charges `C` to the use set.

A receiver or function with a box and no field or function type is unboxed at
the set of its first box, with `unboxAll` and `firstBoxSet`.

This follows `adaptBoxed` in `cc/CheckCaptures.scala`.  It adapts when the
box status differs, inserts a box when the position is covariant and the value
is not boxed, and charges the boxed set when it unboxes.  The compiler finds a
boxed bound through a chain of upper bounds in `findImpureUpperBound`, as the
lookup does.  An insertion the rules do not license gives `none`.

Everything here runs on the tank of `Fuel.lean` and is framed: it keeps a marked
tank, never adds fuel, and does the same with more fuel.
-/

namespace CapturesFrontend

open Frontend.Fuel CapturesFrontend.Core
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Ctx Sub SubShape Subcap
  HasTy DefsTy)
open scoped Captures.DotMNF

/-! ## The result types -/

/-- A synthesized typing: the elaborated term, its use set, its type, and a
derivation for its erasure. -/
structure Elab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase ty

/-- A typing at a given type: the elaborated term, its use set, and a
derivation for its erasure. -/
structure Checked {s : Sig} (Γ : Ctx s) (T : Ty s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase T

/-- A typing of a variable at a given type, at some use set. -/
structure VarChecked {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) T

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

/-- A checked typing read as a synthesized one. -/
def Checked.toElab {s : Sig} {Γ : Ctx s} {T : Ty s} (r : Checked Γ T) : Elab Γ :=
  ⟨r.tm, r.uses, T, r.deriv⟩

/-- An optional answer as a list of at most one. -/
def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

/-! ## Widening a use set -/

/-- `sub` on the use set alone. -/
def widenUses {s : Sig} {Γ : Ctx s} {U U' : CaptureSet s} {t : Tm s} {T : Ty s}
    (h : HasTy U Γ t T) (e : Subcap Γ U U') : HasTy U' Γ t T :=
  HasTy.sub h (Sub.refl T) e

/-- The left operand of a join, widened to the join. -/
def widenLeft {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (h : HasTy U Γ t T) (V : CaptureSet s) : HasTy (capJoin U V) Γ t T :=
  widenUses h (.elem (capJoin_left U V))

/-- The right operand of a join, widened to the join. -/
def widenRight {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {t : Tm s} {T : Ty s}
    (U : CaptureSet s) (h : HasTy V Γ t T) : HasTy (capJoin U V) Γ t T :=
  widenUses h (.elem (capJoin_right U V))

/-! ## A variable and its first view -/

/-- A variable at the least sets: `{}` and its declared type for a binder
declared at the empty set, `{x}` and its declared shape otherwise.  This is
the variable's first view. -/
def varSynth {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Elab Γ :=
  let v := varView Γ x
  ⟨.path (.var x), v.uses, v.ty, v.deriv⟩

/-- A view split into its use set, capture set and shape, the form the
lookup's answers apply to. -/
structure VView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The capture set. -/
  cs : CaptureSet s
  /-- The shape. -/
  sh : Shape s
  /-- The derivation. -/
  deriv : Var Γ x uses cs sh

/-- A typing of a variable, split into its parts. -/
def viewOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} :
    (U : CaptureSet s) → (T : Ty s) → HasTy U Γ (.path (.var x)) T → VView Γ x
  | U, .capt C S, d => ⟨U, C, S, d⟩

/-- The first view of a variable, split into its parts. -/
def vview {s : Sig} (Γ : Ctx s) (x : BVar s .var) : VView Γ x :=
  viewOf (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv

/-! ## Lookups from the first view -/

/-- The shapes of a variable that carry the key, looked up from the shape of
its first view.  The index of the lookup is the fuel left. -/
def lookVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Fu (List (Found Γ x (vview Γ x).sh)) :=
  fun t => look Γ t.left [] x (vview Γ x).sh k t

/-- Read a function shape off a found shape. -/
def Core.Found.fn? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (e : Found Γ x V) :
    Option ((T1 : Ty s) × (T2 : Ty (s,x)) × VarFn Γ x V (.all T1 T2)) :=
  match h : e.ty with
  | .all T1 T2 => some ⟨T1, T2, fun U C d => h ▸ e.f U C d⟩
  | _ => none

/-- Read a field at `a` off a found shape. -/
def Core.Found.fld? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (a : Label)
    (e : Found Γ x V) : Option ((T : Ty s) × VarFn Γ x V (.fld a T)) :=
  match h : e.ty with
  | .fld b T => if hb : b = a then some ⟨T, fun U C d => hb ▸ h ▸ e.f U C d⟩ else none
  | _ => none

/-- Read a box off a found shape, with the boxed type split. -/
def Core.Found.box? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (e : Found Γ x V) :
    Option ((C : CaptureSet s) × (S : Shape s) × VarFn Γ x V (.box (S ^ C))) :=
  match h : e.ty with
  | .box (.capt C S) => some ⟨C, S, fun U D d => h ▸ e.f U D d⟩
  | _ => none

/-- A function type a variable has, with the derivation. -/
structure FnView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The capture set of the function. -/
  cs : CaptureSet s
  /-- The domain. -/
  dom : Ty s
  /-- The codomain, under the domain's binder. -/
  cod : Ty (s,x)
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ((Shape.all dom cod) ^ cs)

/-- A field a variable has at a given label, with the derivation. -/
structure FldView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The capture set of the object. -/
  cs : CaptureSet s
  /-- The type of the field. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ((Shape.fld a ty) ^ cs)

/-- A box a variable has, with the derivation.  The boxed type is
`bsh ^ bcs`. -/
structure BoxView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The capture set of the box. -/
  cs : CaptureSet s
  /-- The capture set of the boxed type. -/
  bcs : CaptureSet s
  /-- The shape of the boxed type. -/
  bsh : Shape s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ((Shape.box (bsh ^ bcs)) ^ cs)

/-- Every function type the lookup finds in a variable, in the order found. -/
def fnViewsF {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Fu (List (FnView Γ x)) :=
  Fu.bind (lookVar Γ x .fn) fun es =>
    Fu.ret (es.filterMap fun e => e.fn?.map fun p =>
      ⟨(vview Γ x).uses, (vview Γ x).cs, p.1, p.2.1, p.2.2 _ _ (vview Γ x).deriv⟩)

/-- Every field at `a` the lookup finds in a variable, in the order found. -/
def fldViewsF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) : Fu (List (FldView Γ x a)) :=
  Fu.bind (lookVar Γ x (.fld a)) fun es =>
    Fu.ret (es.filterMap fun e => (e.fld? a).map fun p =>
      ⟨(vview Γ x).uses, (vview Γ x).cs, p.1, p.2 _ _ (vview Γ x).deriv⟩)

/-- Every box the lookup finds in a variable, in the order found. -/
def boxViewsF {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Fu (List (BoxView Γ x)) :=
  Fu.bind (lookVar Γ x .box) fun es =>
    Fu.ret (es.filterMap fun e => e.box?.map fun p =>
      ⟨(vview Γ x).uses, (vview Γ x).cs, p.1, p.2.1, p.2.2 _ _ (vview Γ x).deriv⟩)

/-! ## Checking a variable, and moving a typing to a goal -/

/-- A variable checked plainly, by the `var` goal from its first view. -/
def checkVarF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    Fu (Option (VarChecked Γ x T)) :=
  mapO (varF Γ x T) fun p => ⟨p.1, p.2⟩

/-- A synthesized typing moved to a goal by equality or by the subtyping
algorithm. -/
def subsumeF {s : Sig} (Γ : Ctx s) (r : Elab Γ) (T : Ty s) : Fu (Option (Checked Γ T)) :=
  if h : r.ty = T then Fu.ret (some ⟨r.tm, r.uses, h ▸ r.deriv⟩)
  else mapO (subF Γ r.ty T) fun e => ⟨r.tm, r.uses, HasTy.sub r.deriv e .refl⟩

/-! ## A box value in checking mode -/

/-- `Box` against a goal `(□ T) ^ C`.  The variable is checked at `T`.  The
box is pure, so the goal's set is reached from `{}` (`HasTy.box`).  Any
other goal gives `none`. -/
def boxCheckF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Fu (Option (HasTy [] Γ (.val (.box x)) G)) :=
  match G with
  | .capt C S =>
      match S with
      | .box T => mapO (checkVarF Γ x T) fun r =>
          HasTy.sub (HasTy.box r.deriv) (.capt .refl (Subcap.empty C)) .refl
      | _ => Fu.ret none

/-- The box of a variable at its first view, at the empty use set. -/
def boxValue {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Elab Γ :=
  ⟨.box x, [], (Shape.box (varView Γ x).ty) ^ [], HasTy.box (varView Γ x).deriv⟩

/-! ## An unboxing -/

/-- `Unbox` at a box whose boxed set is `C'`, at the set `C = C'`.  The use
set is `C` joined with the box's own, the least set `Unbox` allows. -/
def unboxAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {U D C C' : CaptureSet s} {S : Shape s}
    (hc : C' = C) (d : HasTy U Γ (.path (.var x)) ((Shape.box (S ^ C')) ^ D)) :
    HasTy (capJoin C U) Γ (.unbox C x) (S ^ C) := by
  cases hc
  exact HasTy.unbox (widenRight C d) (.elem (capJoin_left C U))

/-- An unboxing read off one box, which must hold a type with capture set
`C`. -/
def unboxOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s) (b : BoxView Γ x) :
    Option (Elab Γ) :=
  if hc : b.bcs = C then some ⟨.unbox C x, capJoin C b.uses, b.bsh ^ C, unboxAt hc b.deriv⟩
  else none

/-- `Unbox` at every box with the capture set `C`.  The boxes include those
reached through the upper bound of a type member, so `C ⊸ e` with `e : o.A`
reaches the box that `o.A` stands for. -/
def unboxAll {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s) (bs : List (BoxView Γ x)) :
    List (Elab Γ) :=
  bs.filterMap (unboxOf C)

/-- The capture set of the boxed type of the first box, or `none`. -/
def firstBoxSet {s : Sig} {Γ : Ctx s} {x : BVar s .var} (bs : List (BoxView Γ x)) :
    Option (CaptureSet s) :=
  bs.head?.map (·.bcs)

/-! ## Box inference at a variable -/

/-- Rules 2 and 3 of box inference, after plain checking has failed.  This is
`□ x` when the lookup finds no box in `x`, and `C ⊸ x` at the set of the
first box otherwise. -/
def adaptInsertF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Fu (Option (Checked Γ G)) :=
  Fu.bind (boxViewsF Γ x) fun bs =>
    match firstBoxSet bs with
    | none =>
        Fu.orElse (mapO (boxCheckF Γ x G) fun d => (⟨.box x, [], d⟩ : Checked Γ G))
          fun _ => subsumeF Γ (boxValue Γ x) G
    | some C => Fu.firstSome (fun r => subsumeF Γ r G) (unboxAll C bs)

/-- Box inference at a variable checked against a goal: plain checking, then
`adaptInsertF`.  The result holds `x`, `□ x` or `C ⊸ x`. -/
def adaptVarF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) : Fu (Option (Checked Γ G)) :=
  Fu.orElse (mapO (checkVarF Γ x G) fun r => (⟨.path (.var x), r.uses, r.deriv⟩ : Checked Γ G))
    fun _ => adaptInsertF Γ x G

/-! ## The frame lemmas -/

/-- The lookup from the fuel left is framed, as `declsAt` is. -/
theorem lookVar_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Framed (lookVar Γ x k) where
  absorbs t ht := (look_framed Γ t.left [] x _ k).absorbs t ht
  spends t := (look_framed Γ t.left [] x _ k).spends t
  shift := by
    intro t r t' h ho j
    exact (look_agree Γ t.left (t.left + j) (Nat.le_add_right _ _) [] x (vview Γ x).sh k).sim
      t r t' h ho j

theorem fnViewsF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Framed (fnViewsF Γ x) :=
  bind_framed (lookVar_framed _ _ _) fun _ => ret_framed _

theorem fldViewsF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) :
    Framed (fldViewsF Γ x a) :=
  bind_framed (lookVar_framed _ _ _) fun _ => ret_framed _

theorem boxViewsF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Framed (boxViewsF Γ x) :=
  bind_framed (lookVar_framed _ _ _) fun _ => ret_framed _

theorem checkVarF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) :
    Framed (checkVarF Γ x T) :=
  mapO_framed _ (varF_framed _ _ _)

theorem subsumeF_framed {s : Sig} (Γ : Ctx s) (r : Elab Γ) (T : Ty s) :
    Framed (subsumeF Γ r T) :=
  dite_framed (fun _ => ret_framed _) (fun _ => mapO_framed _ (subF_framed _ _ _))

theorem boxCheckF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (boxCheckF Γ x G) := by
  cases G with
  | capt C S =>
    cases S with
    | box T => exact mapO_framed _ (checkVarF_framed _ _ _)
    | _ => exact ret_framed _

theorem adaptInsertF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (adaptInsertF Γ x G) := by
  refine bind_framed (boxViewsF_framed _ _) fun bs => ?_
  dsimp only
  split
  · exact orElse_framed (mapO_framed _ (boxCheckF_framed _ _ _)) (subsumeF_framed _ _ _)
  · exact firstSome_framed (fun _ => subsumeF_framed _ _ _) _

theorem adaptVarF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (adaptVarF Γ x G) :=
  orElse_framed (mapO_framed _ (checkVarF_framed _ _ _)) (adaptInsertF_framed _ _ _)

/-! ## Tests

The two hand-written judgments of C7, with a box and with an unboxing
(`C7box1` and `C7unbox` in `DotMNF/Examples.lean`), and the
rejections of the same cases, each from a full tank of `defaultFuel` units. -/

section Tests

open Captures.DotMNF.Examples

/-- `κ₁` in `C7Ctxe`. -/
private abbrev k1e : BVar ([],c,c,x,x,x,x) .cap := .there (.there (.there (.there (.there .here))))

/-- `κ₁` in `C7Ctxz`. -/
private abbrev k1z : BVar ([],c,c,x,x,x) .cap := .there (.there (.there (.there .here)))

/-- The unboxings of a variable at the set `C`, with their use sets and
types. -/
private def unboxesAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (C : CaptureSet s) :
    List (CaptureSet s × Ty s) :=
  (unboxAll C (boxViewsF Γ x ⟨defaultFuel, false⟩).1).map fun r => (r.uses, r.ty)

/-- The unboxing of C7's client gets the use set and type of `C7unbox`. -/
example : unboxesAt C7Ctxe .here [CapAtom.cvar k1e] =
    [([CapAtom.cvar k1e], arrowS ^ [CapAtom.cvar k1e])] := by decide +kernel

/-- An unboxing at a set that is not the box's own is rejected. -/
example : unboxesAt C7Ctxe .here [] = [] := by decide +kernel

/-- A variable that is not a box is not unboxed: `f₁` is a closure. -/
example : unboxesAt C7Ctxe (.there (.there (.there .here))) [CapAtom.cvar k1e] = [] := by
  decide +kernel

/-- The `Box` rule in checking mode, from a full tank. -/
private def boxChecks {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) : Bool :=
  (boxCheckF Γ x G ⟨defaultFuel, false⟩).1.isSome

/-- The field `e₁ = □ f₁` of C7 checks at its declared type, by `sc-var`
from `{f₁}` to `{κ₁}`. -/
example : boxChecks C7Ctxz (.there (.there .here)) ((Shape.box (capTy k1z)) ^ []) = true := by
  decide +kernel

/-- Boxing `f₁` at a box of the other capability is rejected. -/
example : boxChecks C7Ctxz (.there (.there .here))
    ((Shape.box (capTy (.there (.there (.there .here))))) ^ []) = false := by
  decide +kernel

/-- A goal that is not a box is rejected. -/
example : boxChecks C7Ctxz (.there (.there .here)) (capTy k1z) = false := by decide +kernel

/-- A pure binder is its own first view at the empty use set. -/
example : ((varSynth C7Ctxe .here).uses, (varSynth C7Ctxe .here).ty) =
    ([], (Shape.box (capTy k1e)) ^ []) := by decide

/-- A binder declared at a capability is used at its own atom. -/
example : (varSynth C7Ctxe (.there (.there (.there .here)))).uses =
    [CapAtom.var (.there (.there (.there .here)))] := by decide

/-- Box inference at a variable from a full tank.  It returns the inserted
term and its use set. -/
private def adaptAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Option (ATm s × CaptureSet s) :=
  (adaptVarF Γ x G ⟨defaultFuel, false⟩).1.map fun r => (r.tm, r.uses)

/-- The field `e₁ = f₁` of C7 with no box written: rule 2 inserts `□ f₁` at the
empty use set. -/
example : adaptAt C7Ctxz (.there (.there .here)) ((Shape.box (capTy k1z)) ^ []) =
    some (.box (.there (.there .here)), []) := by decide +kernel

/-- The client's `(e : (⊤ → ⊤) ^ {κ₁})`: rule 3 inserts `{κ₁} ⊸ e`, which
charges `{κ₁}`. -/
example : adaptAt C7Ctxe .here (capTy k1e) =
    some (.unbox [CapAtom.cvar k1e] .here, [CapAtom.cvar k1e]) := by decide +kernel

/-- A variable whose type already reaches the goal is not changed. -/
example : adaptAt C7Ctxe (.there (.there (.there .here))) (capTy k1e) =
    some (.path (.var (.there (.there (.there .here)))),
      [CapAtom.var (.there (.there (.there .here)))]) := by decide +kernel

/-- Boxing `f₁` at a box of the other capability is rejected, and so is
unboxing `e` at the other capability. -/
example : adaptAt C7Ctxz (.there (.there .here))
    ((Shape.box (capTy (.there (.there (.there .here))))) ^ []) = none := by decide +kernel

example : adaptAt C7Ctxe .here (capTy (.there (.there (.there (.there .here))))) = none := by
  decide +kernel

/-- The first box of `e` holds a type at `{κ₁}`, and a closure has no box. -/
example : firstBoxSet (boxViewsF C7Ctxe .here ⟨defaultFuel, false⟩).1 =
    some [CapAtom.cvar k1e] := by decide +kernel

example : firstBoxSet (boxViewsF C7Ctxe (.there (.there (.there .here))) ⟨defaultFuel, false⟩).1 =
    none := by decide +kernel

end Tests

end CapturesFrontend
