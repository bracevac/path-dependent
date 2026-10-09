import Coercions.CapturesCC.Frontend.Avoid
import Coercions.CapturesCC.Frontend.Ann

/-!
# Result types of the typer, and box adaptation at a variable

The typer elaborates.  It returns the term it typed, which may hold boxes,
unboxings and unpackings the program did not write.  A result carries the
annotated term, its use set, its answer and a derivation of `HasTy` about the
term's erasure (`lean/Coercions/CapturesCC/DotMNF/Typing.lean`).  The
derivation is the soundness proof, so there is no soundness theorem.

This module defines the result types and the typer's cases that do not
recurse into a term.

- `varSynth`: a variable at its first view (`varView`).
- `fnViewsF`, `fldViewsF`, `boxViewsF`: the function types, the fields at a
  label and the boxes a variable has, found by the member lookup of
  `Look.lean`.  The lookup follows upper bounds of type members, so an
  unboxing reaches a box that a member stands for.
- `boxCheckF`: the `Box` rule in checking mode.  Against a goal `(□ T) ^ C`
  the variable is checked at `T` by the `var` goal of `Sub.lean`.
- `unboxAll`: the `Unbox` rule at every box found with the given capture set.
- `adaptVarF`: box adaptation at a variable checked against a goal.

## Box adaptation

A program need not write its boxes.  `adaptVarF` first checks the variable `x`
plainly against the goal `G`.  If that fails, it compares the box status of
`x` and of `G`, as `adaptBoxed` in `cc/CheckCaptures.scala` does.  The status
of `x` is boxed when the lookup finds a box in it.  The status of `G` is
boxed when `G` is a box.

- `x` boxed and `G` not: `x` is unboxed at each box found, `C ⊸ x` at the
  box's own set `C`.  This charges `C` to the use set, as the compiler
  charges the boxed set.
- `G` boxed and `x` not: `x` is boxed, `□ x`.  The box of the first view is
  then moved to `G` by the subtyping goal, which reaches `G` through the lower
  bound of a type member.
- The statuses agree: both are tried, unboxing first.  The compiler adapts
  only when the statuses differ.  Here a box may still be needed, because the
  calculus has no rule that lets a box pass where another box type is
  expected.

The first insertion that checks wins.  An insertion the rules do not license
gives `none`, never an ill-typed term.

A receiver or function that has a box and no field or function type is
unboxed at the set of its first box (`unboxAll`, `firstBoxSet`).

Everything here runs on the tank of `Fuel.lean` and is framed.  Nothing here
belongs to the metatheory.
-/

namespace CapturesCCFrontend

open Frontend.Fuel CapturesCCFrontend.Core
open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub SubShape
  Subcap ESub HasTy DefsTy Subst)
open scoped CapturesCC.DotMNF

/-! ## The result types -/

/-- A synthesized typing. -/
structure Elab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The answer. -/
  ans : ETy s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase ans

/-- A typing at a given answer. -/
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

/-- A typing of a definition list against a declaration shape.  `DefsTy` has
one use set for all definitions, so the derivation holds at every set above
the least one. -/
structure DefsElab {s : Sig} (Γ : Ctx s) (S : Shape s) where
  /-- The elaborated definitions. -/
  tm : ADefs s
  /-- The least use set of the definitions. -/
  uses : CaptureSet s
  /-- The derivation at every larger use set. -/
  deriv : (U : CaptureSet s) → Subcap Γ uses U → DefsTy U Γ tm.erase S

/-- A typing at a plain answer. -/
structure PElab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase (.ty ty)

/-- A typing at an existential answer `∃ᶜ[bnd] body`. -/
structure XElab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The bound of the witness. -/
  bnd : CaptureSet s
  /-- The type under the witness binder. -/
  body : Ty (s,c)
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase (∃ᶜ[bnd] body)

/-- A checked typing as a synthesized one. -/
def Checked.toElab {s : Sig} {Γ : Ctx s} {E : ETy s} (r : Checked Γ E) : Elab Γ :=
  ⟨r.tm, r.uses, E, r.deriv⟩

/-- A typing at a plain answer as a synthesized one. -/
def PElab.toElab {s : Sig} {Γ : Ctx s} (r : PElab Γ) : Elab Γ := ⟨r.tm, r.uses, .ty r.ty, r.deriv⟩

/-- A typing checked at a plain type, with the type kept. -/
def Checked.toPElab {s : Sig} {Γ : Ctx s} {T : Ty s} (r : Checked Γ (.ty T)) : PElab Γ :=
  ⟨r.tm, r.uses, T, r.deriv⟩

/-- A synthesized typing split by the form of its answer. -/
def Elab.split {s : Sig} {Γ : Ctx s} (r : Elab Γ) : PElab Γ ⊕ XElab Γ :=
  match r with
  | ⟨tm, uses, .ty T, d⟩ => .inl ⟨tm, uses, T, d⟩
  | ⟨tm, uses, .ex C T, d⟩ => .inr ⟨tm, uses, C, T, d⟩

/-- An optional answer as a list of at most one. -/
def listO {α : Type} : Option α → List α
  | some a => [a]
  | none => []

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

/-! ## A variable and its first view -/

/-- A variable at its first view: `{}` and its declared type if the binder is
declared at the empty set, `{x}` and its declared shape otherwise. -/
def varSynth {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Elab Γ :=
  let v := varView Γ x
  ⟨.path (.var x), v.uses, .ty v.ty, v.deriv⟩

/-- A view split into use set, capture set and shape. -/
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
    (U : CaptureSet s) → (T : Ty s) → HasTy U Γ (.path (.var x)) (.ty T) → VView Γ x
  | U, .capt C S, d => ⟨U, C, S, d⟩

/-- The first view of a variable, split into its parts. -/
def vview {s : Sig} (Γ : Ctx s) (x : BVar s .var) : VView Γ x :=
  viewOf (varView Γ x).uses (varView Γ x).ty (varView Γ x).deriv

/-! ## Lookups from the first view -/

/-- The shapes of a variable that carry the key, looked up from the shape of
its first view. -/
def lookVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (k : Key) :
    Fu (List (Found Γ x (vview Γ x).sh)) :=
  fun t => look Γ t.left [] x (vview Γ x).sh k t

/-- Read a function shape off a found shape. -/
def Core.Found.fn? {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Shape s} (e : Found Γ x V) :
    Option ((T1 : Dom s) × (T2 : Cod s) × VarFn Γ x V (.all T1 T2)) :=
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
  /-- The domain, under the arrow's capture binder. -/
  dom : Dom s
  /-- The codomain, under the arrow's capture binder and the parameter. -/
  cod : Cod s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.all dom cod) ^ cs))

/-- A field a variable has at a given label, with the derivation. -/
structure FldView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The capture set of the object. -/
  cs : CaptureSet s
  /-- The type of the field. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.fld a ty) ^ cs))

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
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.box (bsh ^ bcs)) ^ cs))

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

/-- A synthesized typing moved to a goal by equality or by the answer goal,
which packs a plain answer into an existential goal. -/
def subsumeF {s : Sig} (Γ : Ctx s) (r : Elab Γ) (E : ETy s) : Fu (Option (Checked Γ E)) :=
  if h : r.ans = E then Fu.ret (some ⟨r.tm, r.uses, h ▸ r.deriv⟩)
  else mapO (esubF Γ r.ans E) fun e => ⟨r.tm, r.uses, HasTy.sub r.deriv e .refl⟩

/-! ## A box value -/

/-- `Box` against a goal `(□ T) ^ C`.  The variable is checked at `T`.  A box
is pure, so `C` is reached from `{}` (`HasTy.box`).  Any other goal gives
`none`. -/
def boxCheckF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Fu (Option (HasTy [] Γ (.val (.box x)) (.ty G))) :=
  match G with
  | .capt C S =>
      match S with
      | .box T => mapO (checkVarF Γ x T) fun r =>
          HasTy.sub (HasTy.box r.deriv) (.ty (.capt .refl (Subcap.empty C))) .refl
      | _ => Fu.ret none

/-- The box of a variable at its first view, at the empty use set. -/
def boxValue {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Elab Γ :=
  ⟨.box x, [], .ty ((Shape.box (varView Γ x).ty) ^ []), HasTy.box (varView Γ x).deriv⟩

/-! ## An unboxing -/

/-- `Unbox` at a box whose boxed set is `C'`, at the set `C = C'`.  The use
set is `C` joined with the box's own. -/
def unboxAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {U D C C' : CaptureSet s} {S : Shape s}
    (hc : C' = C) (d : HasTy U Γ (.path (.var x)) (.ty ((Shape.box (S ^ C')) ^ D))) :
    HasTy (capJoin C U) Γ (.unbox C x) (.ty (S ^ C)) := by
  cases hc
  exact HasTy.unbox (widenRight C d) (.elem (capJoin_left C U))

/-- An unboxing read off one box, which must hold a type with capture set
`C`. -/
def unboxOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s) (b : BoxView Γ x) :
    Option (PElab Γ) :=
  if hc : b.bcs = C then some ⟨.unbox (some C) x, capJoin C b.uses, b.bsh ^ C, unboxAt hc b.deriv⟩
  else none

/-- `Unbox` at every box with the capture set `C`.  The boxes include those
reached through the upper bound of a type member. -/
def unboxAll {s : Sig} {Γ : Ctx s} {x : BVar s .var} (C : CaptureSet s) (bs : List (BoxView Γ x)) :
    List (PElab Γ) :=
  bs.filterMap (unboxOf C)

/-- Every box unboxed at its own boxed set. -/
def unboxEach {s : Sig} {Γ : Ctx s} {x : BVar s .var} (bs : List (BoxView Γ x)) : List (PElab Γ) :=
  bs.filterMap fun b => unboxOf b.bcs b

/-- The capture set of the boxed type of the first box, or `none`. -/
def firstBoxSet {s : Sig} {Γ : Ctx s} {x : BVar s .var} (bs : List (BoxView Γ x)) :
    Option (CaptureSet s) :=
  bs.head?.map (·.bcs)

/-! ## Box adaptation at a variable -/

/-- A type is boxed: its shape is a box. -/
def isBoxTy {s : Sig} : Ty s → Bool
  | .capt _ (.box _) => true
  | _ => false

/-- The box `□ x` moved to a goal: against a box goal by `boxCheckF`, and
otherwise the box of the first view moved by the subtyping goal. -/
def boxIntoF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) : Fu (Option (Checked Γ (.ty G))) :=
  Fu.orElse (mapO (boxCheckF Γ x G) fun d => (⟨.box x, [], d⟩ : Checked Γ (.ty G)))
    fun _ => subsumeF Γ (boxValue Γ x) (.ty G)

/-- The first unboxing of `bs` that the subtyping goal moves to `G`. -/
def unboxIntoF {s : Sig} (Γ : Ctx s) {x : BVar s .var} (bs : List (BoxView Γ x)) (G : Ty s) :
    Fu (Option (Checked Γ (.ty G))) :=
  Fu.firstSome (fun r => subsumeF Γ r.toElab (.ty G)) (unboxEach bs)

/-- Box adaptation after plain checking has failed.  A boxed variable against
an unboxed goal is only unboxed.  Otherwise unboxing is tried first, then
boxing. -/
def adaptInsertF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Fu (Option (Checked Γ (.ty G))) :=
  Fu.bind (boxViewsF Γ x) fun bs =>
    if !bs.isEmpty && !isBoxTy G then unboxIntoF Γ bs G
    else Fu.orElse (unboxIntoF Γ bs G) fun _ => boxIntoF Γ x G

/-- Box adaptation at a variable checked against a goal: plain checking, then
`adaptInsertF`.  The result holds `x`, `□ x` or `C ⊸ x`. -/
def adaptVarF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Fu (Option (Checked Γ (.ty G))) :=
  Fu.orElse (mapO (checkVarF Γ x G) fun r => (⟨.path (.var x), r.uses, r.deriv⟩ : Checked Γ (.ty G)))
    fun _ => adaptInsertF Γ x G

/-! ## The frame lemmas -/

/-- The lookup is framed. -/
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

theorem subsumeF_framed {s : Sig} (Γ : Ctx s) (r : Elab Γ) (E : ETy s) :
    Framed (subsumeF Γ r E) :=
  dite_framed (fun _ => ret_framed _) (fun _ => mapO_framed _ (esubF_framed _ _ _))

theorem boxCheckF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (boxCheckF Γ x G) := by
  cases G with
  | capt C S =>
    cases S with
    | box T => exact mapO_framed _ (checkVarF_framed _ _ _)
    | _ => exact ret_framed _

theorem boxIntoF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (boxIntoF Γ x G) :=
  orElse_framed (mapO_framed _ (boxCheckF_framed _ _ _)) (subsumeF_framed _ _ _)

theorem unboxIntoF_framed {s : Sig} (Γ : Ctx s) {x : BVar s .var} (bs : List (BoxView Γ x))
    (G : Ty s) : Framed (unboxIntoF Γ bs G) :=
  firstSome_framed (fun _ => subsumeF_framed _ _ _) _

theorem adaptInsertF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (adaptInsertF Γ x G) :=
  bind_framed (boxViewsF_framed _ _) fun _ =>
    ite_framed (unboxIntoF_framed _ _ _) (orElse_framed (unboxIntoF_framed _ _ _) (boxIntoF_framed _ _ _))

theorem adaptVarF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Framed (adaptVarF Γ x G) :=
  orElse_framed (mapO_framed _ (checkVarF_framed _ _ _)) (adaptInsertF_framed _ _ _)

/-! ## Tests

The judgments `C7box1` and `C7unbox` of
`lean/Coercions/CapturesCC/DotMNF/Examples.lean`, and rejections of the same
cases, each from a full tank of `defaultFuel` units. -/

section Tests

open CapturesCC.DotMNF.Examples

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

/-- The unboxings of a variable at the set `C`, with use sets and types. -/
private def unboxesAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (C : CaptureSet s) :
    List (CaptureSet s × Ty s) :=
  (unboxAll C (boxViewsF Γ x ⟨defaultFuel, false⟩).1).map fun r => (r.uses, r.ty)

/-- The unboxing of C7's client has the use set and type of `C7unbox`. -/
example : unboxesAt C7Ctxe .here [CapAtom.cvar k1e] =
    [([CapAtom.cvar k1e], arrowS ^ [CapAtom.cvar k1e])] := by decide +kernel

/-- An unboxing at a set that is not the box's own is rejected. -/
example : unboxesAt C7Ctxe .here [] = [] := by decide +kernel

/-- `f₁` is a closure, not a box. -/
example : unboxesAt C7Ctxe f1e [CapAtom.cvar k1e] = [] := by decide +kernel

/-- The `Box` rule in checking mode, from a full tank. -/
private def boxChecks {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) : Bool :=
  (boxCheckF Γ x G ⟨defaultFuel, false⟩).1.isSome

/-- The field `e₁ = □ f₁` of C7 checks at its declared type by `sc-var`. -/
example : boxChecks C7Ctxz f1z ((Shape.box (capTy k1z)) ^ []) = true := by decide +kernel

/-- Boxing `f₁` at a box of the other capability is rejected. -/
example : boxChecks C7Ctxz f1z ((Shape.box (capTy k2z)) ^ []) = false := by decide +kernel

/-- A goal that is not a box is rejected. -/
example : boxChecks C7Ctxz f1z (capTy k1z) = false := by decide +kernel

/-- A pure binder has the empty use set. -/
example : ((varSynth C7Ctxe .here).uses, (varSynth C7Ctxe .here).ans) =
    ([], .ty ((Shape.box (capTy k1e)) ^ [])) := by decide

/-- A binder declared at a capability is used at its own atom. -/
example : (varSynth C7Ctxe f1e).uses = [CapAtom.var f1e] := by decide

/-- Box adaptation at a variable from a full tank: the term and its use set. -/
private def adaptAt {s : Sig} (Γ : Ctx s) (x : BVar s .var) (G : Ty s) :
    Option (ATm s × CaptureSet s) :=
  (adaptVarF Γ x G ⟨defaultFuel, false⟩).1.map fun r => (r.tm, r.uses)

/-- The field `e₁ = f₁` of C7 with no box written: the goal is boxed and `f₁`
is not, so `□ f₁` is inserted. -/
example : adaptAt C7Ctxz f1z ((Shape.box (capTy k1z)) ^ []) = some (.box f1z, []) := by
  decide +kernel

/-- The client's `(e : (⊤ → ⊤) ^ {κ₁})`: `e` is boxed and the goal is not, so
`{κ₁} ⊸ e` is inserted. -/
example : adaptAt C7Ctxe .here (capTy k1e) =
    some (.unbox (some [CapAtom.cvar k1e]) .here, [CapAtom.cvar k1e]) := by decide +kernel

/-- A variable whose type already reaches the goal is not changed. -/
example : adaptAt C7Ctxe f1e (capTy k1e) = some (.path (.var f1e), [CapAtom.var f1e]) := by
  decide +kernel

/-- Boxing `f₁` at the other capability's box is rejected, and so is unboxing
`e` at the other capability. -/
example : adaptAt C7Ctxz f1z ((Shape.box (capTy k2z)) ^ []) = none := by decide +kernel

example : adaptAt C7Ctxe .here (capTy k2e) = none := by decide +kernel

/-- Both statuses boxed: `e` against `□ (⊤ ^ {})`.  Unboxing gives a closure,
which is no box, and then `□ e` checks, since `e` itself is below `⊤ ^ {}`. -/
example : adaptAt C7Ctxe .here ((Shape.box (Shape.top ^ [])) ^ []) = some (.box .here, []) := by
  decide +kernel

/-- The first box of `e` holds a type at `{κ₁}`, and a closure has no box. -/
example : firstBoxSet (boxViewsF C7Ctxe .here ⟨defaultFuel, false⟩).1 =
    some [CapAtom.cvar k1e] := by decide +kernel

example : firstBoxSet (boxViewsF C7Ctxe f1e ⟨defaultFuel, false⟩).1 = none := by decide +kernel

end Tests

end CapturesCCFrontend
