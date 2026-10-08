import Coercions.CapturesCC.Frontend.Pipeline
import Coercions.CapturesCC.Frontend.Pretty

/-!
# The examples end to end

The programs of the version's `DotMNF/Examples.lean` are written in the front
end's notation, taken through the whole front end, and compared with the
version's hand written derivations.  The pure programs E1 to E8 run over the
empty platform.  The capture programs run over the platform `πc` of
`Resolve.lean`, with capabilities `k1` and `k2`, or over `πz`, the same two
binders named `fs` and `k2`, for the programs whose capability is a file
system.  Both are the version's `platCtx`.

## What is compared

For each program, the term the resolver returns, or the erasure of the
elaborated term when the typer inserted something.  The use set and the type
the typer found.  The verdict of the target checker on the translation of the
derivation, and on the use set evidence the translation emits.  Derivations
are not compared, because `DotMNF.HasTy` is data with no decidable equality.
`tmOfDeriv`, `usesOfDeriv` and `tyOfDeriv` read the term, use set and type off
the version's derivations.

## The checks of a program

Every function of the front end is structural, so the kernel reduces it.  The
term is compared by `decide`, or by `decide +kernel` when it is the elaborated
one.  The use set and the type are compared by `decide +kernel`.  The two
checker runs go through `expect`.  The theorem `Ek_compiles` says that the
program compiles, and `Ek_checks` is `compile_checks_get` at it, so the
checker accepts the translation.

A program the version types under a context is typed there, through
`synthIn?`.  E6, C5, the caller of `freshCell`, the call of `process`, the
capture parameter that is called and the unpackings at `Z1Ctx` are such
programs.

A `Budget` bounds the search.  The budget of each program is one at which the
program is found.  It is not claimed least.

## Where the typer finds a smaller judgment

Without an ascription that names the version's type, the typer finds the least
use set and type the rules allow.  C2 types at `{k2}` against the version's
`{k1, k2}`, C5 at `{it, it.C}` against `{fs, k2}`, and the caller of
`freshCell` at `{fc, fs, un}` against `{fs, un, fs, un}`.  Each time the
version's judgment is reached from the typer's by one `sub` that the search
finds, which `reachesAt` decides.

## Rejections and levels

A rejection by a written type is a kernel fact.  A rejection by a level escape
carries a certificate that reads `Ctx.caps`, which the kernel does not reduce,
so the verdict is an `expect` test.  The certificate at the goal the typer
reached is a theorem of its own, `Esc_rejected'` for the escape and
`top_escape_rejected` for the escape at the top of a program.  The checks W1
and W5 ask the subcapturing search for the steps of the level order at the
version's contexts.

## The run tests

S2 and C2 are run from the platform's initial store, printed with the
platform's own names, and pinned at the step count at which they become final.
E2 is run beside them over the empty platform.
-/

namespace CapturesCCFrontend

open CapturesCC
open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (CapAtom CaptureSet Shape Ty ETy Tm Ctx HasTy HasTyP Subcap State Steps)
open scoped CapturesCC.DotMNF

section Examples

open CapturesCC.DotMNF.Examples

/-! ## Reading a derivation of the version -/

/-- The term a derivation of the version is about. -/
def tmOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : Tm s := t

/-- The use set a derivation of the version is about. -/
def usesOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : CaptureSet s := U

/-- The type a derivation of the version is about. -/
def tyOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : Ty s := T

/-! ## The decidable things -/

/-- The resolved term, erased into the version's syntax. -/
def compiledTm (Λ : LabelTable) (π : PlatformNames) (e : STm) : Option (Tm π.sig) :=
  (resolveTop Λ π e).map ATm.erase

/-- The elaborated term, erased.  It differs from the resolved one when the
typer inserted a box, an unboxing or an unpacking. -/
def elaboratedTm (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option (Tm π.sig) :=
  (compile b Λ π e).toOption.map fun r => r.2.tm.erase

/-- The use set and the type the typer found. -/
def compiledJudgment (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option (CaptureSet π.sig × Ty π.sig) :=
  (compile b Λ π e).toOption.map fun r => (r.2.use, r.2.ty)

/-- The target checker's verdict on the translation of the derivation.  It is
`false` when the front end returns no derivation. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) : Bool :=
  match compile b Λ π e with
  | .ok r => FCdot.checkTm π.plat.ctx.translate r.2.deriv.translate r.2.ty.translate
  | _ => false

/-- The target checker's verdict on the use set evidence the translation
emits. -/
def compiledUsesVerdict (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) : Bool :=
  match compile b Λ π e with
  | .ok r =>
      FCdot.checkCap π.plat.ctx.translate r.2.deriv.translateUses r.2.deriv.translate.uses
        r.2.use.translate
  | _ => false

/-- What `compile_checks_get` concludes at a program that compiles. -/
def CheckerAccepts (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm)
    (h : (compile b Λ π e).isOk = true) : Prop :=
  FCdot.checkTm π.plat.ctx.translate ((compile b Λ π e).get h).2.deriv.translate
    ((compile b Λ π e).get h).2.ty.translate = true

/-- The two checker verdicts at a typing found at an open context. -/
def openVerdicts {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Bool × Bool :=
  match v with
  | .ok r =>
      (FCdot.checkTmE Γ.translate r.deriv.translate r.ans.translate,
        FCdot.checkCap Γ.translate r.deriv.translateUses r.deriv.translate.uses r.uses.translate)
  | _ => (false, false)

/-- **The target checker accepts a typing found at an open context.**  The open
twin of `compile_checks_get`. -/
theorem synthIn_checks_get {s : Sig} {Γ : Ctx s} {b : Budget} {ps : CaptureSet s} {a : ATm s}
    (hwf : Γ.Wf) (h : (synthIn? b Γ ps a).isOk = true) :
    FCdot.checkTmE Γ.translate ((synthIn? b Γ ps a).get h).deriv.translate
      ((synthIn? b Γ ps a).get h).ans.translate = true :=
  FCdot.checkTmE_complete (DotMNF.HasTy.translate_typed _ hwf)

/-- The subcapturing search at a context. -/
def subcapFound {s : Sig} (b : Budget) (Γ : Ctx s) (C D : CaptureSet s) : Bool :=
  (subcap? (decls b Γ) b.cap C D).isSome

/-- Two contexts are equal binder by binder. -/
def ctxEq {s : Sig} (Γ Δ : Ctx s) : Bool :=
  match Γ, Δ with
  | .nil, .nil => true
  | .cons Γ' T, .cons Δ' U => decide (T = U) && ctxEq Γ' Δ'
  | .consSelf Γ' d S U, .consSelf Δ' d' S' U' =>
      decide (d = d') && decide (S = S') && decide (U = U') && ctxEq Γ' Δ'
  | .consC Γ', .consC Δ' => ctxEq Γ' Δ'
  | .consRoot Γ', .consRoot Δ' => ctxEq Γ' Δ'
  | .consInst Γ' C, .consInst Δ' D => decide (C = D) && ctxEq Γ' Δ'
  | _, _ => false
termination_by structural Γ

/-- A verdict that rejects by a level escape at the goal `C <: D` in the
context `Γ`. -/
def escapesAt {α : Type} {s : Sig} (v : Verdict α) (Γ : Ctx s) (C D : CaptureSet s) : Bool :=
  match v with
  | .rejected (.levelEscape (s := s') Γ' C' D' _ _) =>
      if h : s' = s then ctxEq (h ▸ Γ') Γ && decide (h ▸ C' = C) && decide (h ▸ D' = D)
      else false
  | _ => false

/-! ## E1: bad bounds under a lambda

The annotated `let` is retyped through the bad bounds chain.  The version's
derivation is `E1`. -/

/-- `λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤}..{a : ⊤}} = x in y`. -/
def E1src : STm := cc% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

/-- The budget of E1. -/
def bE1 : Budget := { decls := 1, views := 0, sub := 2, cap := 1, typer := 3, obj := 0 }

example : compiledTm Λc .empty E1src = some (tmOfDeriv E1) := by decide

example : compiledJudgment bE1 Λc .empty E1src = some (usesOfDeriv E1, tyOfDeriv E1) := by
  decide +kernel

#eval expect (compiledVerdict bE1 Λc .empty E1src)
  "E1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE1 Λc .empty E1src)
  "E1: the target checker rejects the use set evidence"

/-- E1 compiles. -/
theorem E1_compiles : (compile bE1 Λc .empty E1src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E1. -/
theorem E1_checks : CheckerAccepts bE1 Λc .empty E1src E1_compiles :=
  compile_checks_get E1_compiles

/-! ## E2: a recursive object with a self referential member

The outer `let` avoids `x.A` at `⊤`.  The version's derivation is `E2`. -/

/-- `let x = ν(s : {A : E2A..E2A} ∧ {a : E2A}. {type A = E2A} ∧ {a = λ(y : s.A). y})
in let f = x.a in f f`, with `E2A` the shape `∀(y : s.A) s.A`. -/
def E2src : STm :=
  cc% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

/-- The budget of E2. -/
def bE2 : Budget := { decls := 1, views := 2, sub := 2, cap := 1, typer := 7, obj := 1 }

example : compiledTm Λc .empty E2src = some (tmOfDeriv E2) := by decide

example : compiledJudgment bE2 Λc .empty E2src = some (usesOfDeriv E2, tyOfDeriv E2) := by
  decide +kernel

#eval expect (compiledVerdict bE2 Λc .empty E2src)
  "E2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE2 Λc .empty E2src)
  "E2: the target checker rejects the use set evidence"

/-- E2 compiles. -/
theorem E2_compiles : (compile bE2 Λc .empty E2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts bE2 Λc .empty E2src E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation is
`E3`. -/

/-- `λ(x : {A : ⊥..{a : ⊤}} ∧ {A : {b : ⊤}..⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y`. -/
def E3src : STm :=
  cc% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

/-- The budget of E3. -/
def bE3 : Budget := { decls := 1, views := 1, sub := 2, cap := 1, typer := 5, obj := 0 }

example : compiledTm Λc .empty E3src = some (tmOfDeriv E3) := by decide

example : compiledJudgment bE3 Λc .empty E3src = some (usesOfDeriv E3, tyOfDeriv E3) := by
  decide +kernel

#eval expect (compiledVerdict bE3 Λc .empty E3src)
  "E3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE3 Λc .empty E3src)
  "E3: the target checker rejects the use set evidence"

/-- E3 compiles. -/
theorem E3_compiles : (compile bE3 Λc .empty E3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E3. -/
theorem E3_checks : CheckerAccepts bE3 Λc .empty E3src E3_compiles :=
  compile_checks_get E3_compiles

/-! ## E4: typing with no realizer

Two rounds of the declaration table.  The version's derivation is `E4`. -/

/-- `λ(x : {B : {A : ⊥..⊤}..{A : {a : ⊤}..⊤}}). λ(w : {A : ⊥..⊤}). λ(n : {a : ⊤}).
let g = λ(y : w.A). y in g n`. -/
def E4src : STm :=
  cc% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
         λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

/-- The budget of E4. -/
def bE4 : Budget := { decls := 2, views := 1, sub := 2, cap := 1, typer := 6, obj := 0 }

example : compiledTm Λc .empty E4src = some (tmOfDeriv E4) := by decide

example : compiledJudgment bE4 Λc .empty E4src = some (usesOfDeriv E4, tyOfDeriv E4) := by
  decide +kernel

#eval expect (compiledVerdict bE4 Λc .empty E4src)
  "E4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE4 Λc .empty E4src)
  "E4: the target checker rejects the use set evidence"

/-- E4 compiles. -/
theorem E4_compiles : (compile bE4 Λc .empty E4src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E4. -/
theorem E4_checks : CheckerAccepts bE4 Λc .empty E4src E4_compiles :=
  compile_checks_get E4_compiles

/-! ## E5: an object returned from a function

The application renames the result's member to `w`, and the outer `let`
keeps `w.A`.  The version's derivation is `E5`. -/

/-- `λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
in let o = f w in o.a`. -/
def E5src : STm :=
  cc% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
         in let o = f w in o.a

/-- The budget of E5. -/
def bE5 : Budget := { decls := 1, views := 1, sub := 2, cap := 1, typer := 7, obj := 1 }

example : compiledTm Λc .empty E5src = some (tmOfDeriv E5) := by decide

example : compiledJudgment bE5 Λc .empty E5src = some (usesOfDeriv E5, tyOfDeriv E5) := by
  decide +kernel

#eval expect (compiledVerdict bE5 Λc .empty E5src)
  "E5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE5 Λc .empty E5src)
  "E5: the target checker rejects the use set evidence"

/-- E5 compiles. -/
theorem E5_compiles : (compile bE5 Λc .empty E5src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts bE5 Λc .empty E5src E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The version types E6 at `E6Ctx1`, which binds `n : {a : ⊤}`.  So the literal
is resolved under the name `n` and typed at that context. -/

/-- `ν(x : {T : {a : ⊤}..{a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})`. -/
def E6src : STm :=
  cc% ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

/-- The names of `E6Ctx1`. -/
def E6names : NameEnv ([],x) := PlatformNames.empty.names.cons "n"

/-- E6 as resolved. -/
def E6ann : ATm ([],x) := (resolveIn Λc E6names E6src).getD (.path (.var .here))

/-- The budget of E6. -/
def bE6 : Budget := { decls := 1, views := 2, sub := 2, cap := 1, typer := 5, obj := 1 }

/-- `E6Ctx1` is well formed. -/
theorem E6Ctx1_wf : E6Ctx1.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc E6names E6src).map ATm.erase = some (tmOfDeriv E6) := by decide

example : judgmentOf (synthIn? bE6 E6Ctx1 [] E6ann) =
    some (usesOfDeriv E6, .ty (tyOfDeriv E6)) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bE6 E6Ctx1 [] E6ann) == (true, true))
  "E6: the target checker rejects the translation or the use set evidence"

/-- E6 is typed at `E6Ctx1`. -/
theorem E6_compiles : (synthIn? bE6 E6Ctx1 [] E6ann).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E6 at the translation of
`E6Ctx1`. -/
theorem E6_checks :
    FCdot.checkTmE E6Ctx1.translate ((synthIn? bE6 E6Ctx1 [] E6ann).get E6_compiles).deriv.translate
      ((synthIn? bE6 E6Ctx1 [] E6ann).get E6_compiles).ans.translate = true :=
  synthIn_checks_get E6Ctx1_wf E6_compiles

/-! ## E7: two type members that name each other

The version's derivation is `E7`.  Nothing is searched. -/

/-- `ν(x : {A : x.B..x.B} ∧ {B : x.A..x.A}. {type A = x.B} ∧ {type B = x.A})`. -/
def E7src : STm :=
  cc% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})

/-- The budget of E7. -/
def bE7 : Budget := { decls := 0, views := 0, sub := 0, cap := 1, typer := 3, obj := 1 }

example : compiledTm Λc .empty E7src = some (tmOfDeriv E7) := by decide

example : compiledJudgment bE7 Λc .empty E7src = some (usesOfDeriv E7, tyOfDeriv E7) := by
  decide +kernel

#eval expect (compiledVerdict bE7 Λc .empty E7src)
  "E7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE7 Λc .empty E7src)
  "E7: the target checker rejects the use set evidence"

/-- E7 compiles. -/
theorem E7_compiles : (compile bE7 Λc .empty E7src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts bE7 Λc .empty E7src E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: refining an abstract type

The version gives one term two derivations, `E8` and `E8b`, at one
judgment.  The typer finds that judgment. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`. -/
def E8src : STm := cc% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

/-- The budget of E8. -/
def bE8 : Budget := { decls := 0, views := 1, sub := 0, cap := 1, typer := 3, obj := 0 }

example : compiledTm Λc .empty E8src = some (tmOfDeriv E8) := by decide

example : tmOfDeriv E8b = tmOfDeriv E8 := rfl

example : compiledJudgment bE8 Λc .empty E8src = some (usesOfDeriv E8, tyOfDeriv E8) := by
  decide +kernel

example : compiledJudgment bE8 Λc .empty E8src = some (usesOfDeriv E8b, tyOfDeriv E8b) := by
  decide +kernel

#eval expect (compiledVerdict bE8 Λc .empty E8src)
  "E8: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE8 Λc .empty E8src)
  "E8: the target checker rejects the use set evidence"

/-- E8 compiles. -/
theorem E8_compiles : (compile bE8 Λc .empty E8src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts bE8 Λc .empty E8src E8_compiles :=
  compile_checks_get E8_compiles

/-! ## C7: a container of boxed capabilities, boxes written

The fields check by the box rule, and the client unboxes at `{k1}`.  The
version's derivation is `C7_typed`. -/

/-- C7 with its boxes and its unboxing written. -/
def C7boxSrc : STm :=
  cc% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

/-- The budget of C7 with its boxes written. -/
def bC7box : Budget := { decls := 0, views := 2, sub := 1, cap := 2, typer := 8, obj := 1 }

example : compiledTm Λc πc C7boxSrc = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm bC7box Λc πc C7boxSrc = some (tmOfDeriv C7_typed) := by decide +kernel

example : compiledJudgment bC7box Λc πc C7boxSrc =
    some (usesOfDeriv C7_typed, tyOfDeriv C7_typed) := by
  decide +kernel

#eval expect (compiledVerdict bC7box Λc πc C7boxSrc)
  "C7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC7box Λc πc C7boxSrc)
  "C7: the target checker rejects the use set evidence"

/-- C7 with its boxes written compiles. -/
theorem C7box_compiles : (compile bC7box Λc πc C7boxSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with its boxes
written. -/
theorem C7box_checks : CheckerAccepts bC7box Λc πc C7boxSrc C7box_compiles :=
  compile_checks_get C7box_compiles

/-! ## C7 with no box in any term

`C7src` of `Typer.lean`.  The typer inserts `□ f1` and `□ f2` at the fields and
`{k1} ⊸ e` at the ascription.  The elaborated term is the version's. -/

example : compiledTm Λc πc C7src ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm bC7 Λc πc C7src = some (tmOfDeriv C7_typed) := by decide +kernel

example : compiledJudgment bC7 Λc πc C7src =
    some (usesOfDeriv C7_typed, tyOfDeriv C7_typed) := by
  decide +kernel

#eval expect (compiledVerdict bC7 Λc πc C7src)
  "C7 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC7 Λc πc C7src)
  "C7 with no box: the target checker rejects the use set evidence"

/-- C7 with no box in any term compiles. -/
theorem C7_compiles : (compile bC7 Λc πc C7src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with no box in any
term. -/
theorem C7_checks : CheckerAccepts bC7 Λc πc C7src C7_compiles :=
  compile_checks_get C7_compiles

/-! ## S3: a type member at a boxed capturing type

The bounds of a type member are shapes, so the program writes the box in the
member.  The client unboxes through the upper bound of `o.A`.  The version's
derivation is `S3_typed`. -/

/-- S3, its box and its unboxing written. -/
def S3src : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : □((∀(u : ⊤) ⊤) ^ {f}) .. □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem : z.A}.
                   {type A = □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem = □ f})
        in let e = o.elem in {f} ⊸ e

/-- The budget of S3. -/
def bS3 : Budget := { decls := 1, views := 2, sub := 2, cap := 1, typer := 7, obj := 1 }

example : compiledTm Λc πc S3src = some (tmOfDeriv S3_typed) := by decide

example : compiledJudgment bS3 Λc πc S3src =
    some (usesOfDeriv S3_typed, tyOfDeriv S3_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS3 Λc πc S3src)
  "S3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS3 Λc πc S3src)
  "S3: the target checker rejects the use set evidence"

/-- S3 compiles. -/
theorem S3_compiles : (compile bS3 Λc πc S3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S3. -/
theorem S3_checks : CheckerAccepts bS3 Λc πc S3src S3_compiles :=
  compile_checks_get S3_compiles

/-! ## C2: capture polymorphism by a capture member

The client reads `x.run`, whose set is `{x.C}`.  The typer finds the judgment
`{k2}` and `(⊤ → ⊤) ^ {k2}`, since the answer is the client at `b`, whose
member is `{k2}`.  The version's `{k1, k2}` is reached by one `sub`. -/

/-- C2, with the call `x.run u` in direct style. -/
def C2src : STm :=
  cc% let c = λ(x : μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

/-- The budget of C2. -/
def bC2 : Budget := { decls := 1, views := 2, sub := 1, cap := 3, typer := 9, obj := 1 }

example : compiledTm Λc πc C2src = some (tmOfDeriv C2_typed) := by decide

example : elaboratedTm bC2 Λc πc C2src = some (tmOfDeriv C2_typed) := by decide +kernel

example : compiledJudgment bC2 Λc πc C2src =
    some ([CapAtom.cvar k2], (Shape.all unitTy (.ty unitTy)) ^ [CapAtom.cvar k2]) := by
  decide +kernel

example : topReaches { bC2 with sub := 2 } πc (resolveTop Λc πc C2src) (usesOfDeriv C2_typed)
    (.ty (tyOfDeriv C2_typed)) = true := by
  decide +kernel

#eval expect (compiledVerdict bC2 Λc πc C2src)
  "C2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC2 Λc πc C2src)
  "C2: the target checker rejects the use set evidence"

/-- C2 compiles. -/
theorem C2_compiles : (compile bC2 Λc πc C2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C2. -/
theorem C2_checks : CheckerAccepts bC2 Λc πc C2src C2_compiles :=
  compile_checks_get C2_compiles

/-! ## S1: `withFile` with an explicit capture parameter

`withFile` is bound by an ascription at its signature.  Its result `any` is
read at the top of the program as the platform set.  The judgment is the
version's `S1_typed`, `{fs, k2}` and `⊤ ^ {fs, k2}`.  The program runs over
`πz`. -/

/-- S1. -/
def S1progSrc : STm :=
  cc% let withFile =
        (λ(cp : μ(c. {C^ : {}..{fs}}) ^ {}).
           λ(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}).
             let fl = ν(f : {read : (∀(u : ⊤) ⊤) ^ {f}}. {read = λ(u : ⊤). u}) in op fl
         : (∀(cp : μ(c. {C^ : {}..{fs}}))
              (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
                ^ {fs, cp}) ^ {fs}) in
      let cp = ν(c : {C^ : {fs}..{fs}}. {C^ = {fs}}) in
      let op = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}). λ(u : ⊤). u in
      let g = withFile cp in
      let r = g op in
      r

/-- The budget of S1. -/
def bS1 : Budget := { decls := 0, views := 1, sub := 2, cap := 5, typer := 10, obj := 1 }

example : compiledTm Λc πz S1progSrc = some (tmOfDeriv S1_typed) := by decide

example : compiledJudgment bS1 Λc πz S1progSrc =
    some (usesOfDeriv S1_typed, tyOfDeriv S1_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS1 Λc πz S1progSrc)
  "S1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS1 Λc πz S1progSrc)
  "S1: the target checker rejects the use set evidence"

/-- S1 compiles. -/
theorem S1_compiles : (compile bS1 Λc πz S1progSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S1. -/
theorem S1_checks : CheckerAccepts bS1 Λc πz S1progSrc S1_compiles :=
  compile_checks_get S1_compiles

/-! ## S2: a class with a capture set parameter

`mk` is bound by an ascription at its signature, with `any` in its result,
read as the platform set.  The caller's answer leaves scope at the upper bound
of the member, `{fs}`.  The judgment is the version's `S2_typed`. -/

/-- S2. -/
def S2src : STm :=
  cc% let mk =
        (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in it
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {any}) ^ {fs}) in
      let un = (λ(y : ⊤). y : ⊤) in
      let it = mk un in let n = it.next in let r = n un in r

/-- The budget of S2. -/
def bS2 : Budget := { decls := 1, views := 2, sub := 1, cap := 3, typer := 10, obj := 1 }

example : compiledTm Λc πz S2src = some (tmOfDeriv S2_typed) := by decide

example : compiledJudgment bS2 Λc πz S2src =
    some (usesOfDeriv S2_typed, tyOfDeriv S2_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS2 Λc πz S2src)
  "S2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS2 Λc πz S2src)
  "S2: the target checker rejects the use set evidence"

/-- S2 compiles. -/
theorem S2_compiles : (compile bS2 Λc πz S2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S2. -/
theorem S2_checks : CheckerAccepts bS2 Λc πz S2src S2_compiles :=
  compile_checks_get S2_compiles

/-! ## C5: the caller of `mk`, at the version's own context

The version types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  The
typer finds `{it, it.C}` and `⊤ ^ {it.C}`.  The version's `{fs, k2}` and
`⊤ ^ {fs}` are reached by one `sub`. -/

/-- `let n = it.next in let r = n un in r`. -/
def C5src : STm := cc% let n = it.next in let r = n un in r

/-- The names of `S2Ctx3`: the platform, then `mk`, `un` and `it`. -/
def C5names : NameEnv ([],c,c,x,x,x) := ((πz.names.cons "mk").cons "un").cons "it"

/-- C5 as resolved. -/
def C5ann : ATm ([],c,c,x,x,x) := (resolveIn Λc C5names C5src).getD (.path (.var .here))

/-- The budget of C5. -/
def bC5 : Budget := { decls := 0, views := 2, sub := 0, cap := 3, typer := 4, obj := 0 }

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc C5names C5src).map ATm.erase = some (tmOfDeriv C5_typed) := by decide

example : judgmentOf (synthIn? bC5 S2Ctx3 platSet3 C5ann) =
    some ([CapAtom.var .here, CapAtom.sel .here lC], .ty (Shape.top ^ [CapAtom.sel .here lC])) := by
  decide +kernel

example : reachesAt { bC5 with sub := 1, decls := 1 } S2Ctx3 platSet3 C5ann (usesOfDeriv C5_typed)
    (.ty (tyOfDeriv C5_typed)) = true := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bC5 S2Ctx3 platSet3 C5ann) == (true, true))
  "C5: the target checker rejects the translation or the use set evidence"

/-- C5 is typed at `S2Ctx3`. -/
theorem C5_compiles : (synthIn? bC5 S2Ctx3 platSet3 C5ann).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C5 at the translation of
`S2Ctx3`. -/
theorem C5_checks :
    FCdot.checkTmE S2Ctx3.translate ((synthIn? bC5 S2Ctx3 platSet3 C5ann).get C5_compiles).deriv.translate
      ((synthIn? bC5 S2Ctx3 platSet3 C5ann).get C5_compiles).ans.translate = true :=
  synthIn_checks_get S2Ctx3_wf C5_compiles

/-! ## Z1: `freshCell`

The signature writes `fresh` in the result.  The typer reads it as the
version's `Z1Ty`, an existential bounded by `{fs, u}`, and the arrow rule packs
the cell.  The term and the judgment are the version's `Z1_plat`. -/

/-- `freshCell`, bound by an ascription. -/
def Z1progSrc : STm :=
  cc% (λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs})

/-- The budget of Z1. -/
def bZ1prog : Budget := { decls := 0, views := 0, sub := 1, cap := 1, typer := 9, obj := 1 }

example : compiledTm Λc πz Z1progSrc = some (tmOfDeriv Z1_plat) := by decide

example : compiledJudgment bZ1prog Λc πz Z1progSrc =
    some (usesOfDeriv Z1_plat, tyOfDeriv Z1_plat) := by
  decide +kernel

/-- `readAt` expands the `any`s, of which there are none, and reads `fresh` as
the existential.  This is the version's W4. -/
example : readAt platCtx platSet (Z1TyF k1) = Z1Ty k1 := by decide

#eval expect (compiledVerdict bZ1prog Λc πz Z1progSrc)
  "Z1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bZ1prog Λc πz Z1progSrc)
  "Z1: the target checker rejects the use set evidence"

/-- Z1 compiles. -/
theorem Z1_compiles : (compile bZ1prog Λc πz Z1progSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z1. -/
theorem Z1_checks : CheckerAccepts bZ1prog Λc πz Z1progSrc Z1_compiles :=
  compile_checks_get Z1_compiles

/-! ## The caller of `freshCell`, at `Z1Ctx`

`Z1callerAnn` of `Resolve.lean`, at the budget `bZ1` of `Typer.lean`.  The
`let` becomes a `letex`, and the elaborated term erases to the term of the
version's `Z1_caller`.  The typer finds `{fc, un}`, and the version's
`Z1Use ∪ Z1Use` is reached by one `sub`. -/

example : erasedOf (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) = some (tmOfDeriv Z1_caller) := by
  decide +kernel

example : judgmentOf (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) =
    some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here],
      .ty ((Shape.all unitTy (.ty unitTy)) ^ [])) := by
  decide +kernel

example : reachesAt { bZ1 with cap := 4, sub := 1 } Z1Ctx ps2z Z1callerAnn
    (usesOfDeriv Z1_caller) (.ty (tyOfDeriv Z1_caller)) = true := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) == (true, true))
  "the caller of freshCell: the target checker rejects the translation or the use set evidence"

/-- The caller of `freshCell` is typed at `Z1Ctx`. -/
theorem Z1caller_compiles : (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the caller of `freshCell`
at the translation of `Z1Ctx`. -/
theorem Z1caller_checks :
    FCdot.checkTmE Z1Ctx.translate
      ((synthIn? bZ1 Z1Ctx ps2z Z1callerAnn).get Z1caller_compiles).deriv.translate
      ((synthIn? bZ1 Z1Ctx ps2z Z1callerAnn).get Z1caller_compiles).ans.translate = true :=
  synthIn_checks_get Z1Ctx_wf Z1caller_compiles

/-! ## An unpacking whose answer is existential, at `Z1Ctx`

`let c1 = fc un in fc un`, `Z1TailAnn` of `Resolve.lean`.  The answer is the
second call's existential, moved past the witness and the payload of the
first. -/

example : judgmentOf (synthIn? bTail Z1Ctx ps2z Z1TailAnn) =
    some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here],
      ∃ᶜ[Z1Use] (fileS ^ [CapAtom.cvar .here])) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bTail Z1Ctx ps2z Z1TailAnn) == (true, true))
  "the unpacking: the target checker rejects the translation or the use set evidence"

/-- The unpacking is typed at `Z1Ctx`. -/
theorem Z1tail_compiles : (synthIn? bTail Z1Ctx ps2z Z1TailAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the unpacking at the
translation of `Z1Ctx`. -/
theorem Z1tail_checks :
    FCdot.checkTmE Z1Ctx.translate
      ((synthIn? bTail Z1Ctx ps2z Z1TailAnn).get Z1tail_compiles).deriv.translate
      ((synthIn? bTail Z1Ctx ps2z Z1TailAnn).get Z1tail_compiles).ans.translate = true :=
  synthIn_checks_get Z1Ctx_wf Z1tail_compiles

/-! ## Two calls of `freshCell`, at `Z1Ctx`

Each call is unpacked by a `letex` of its own, so the body runs under two
opened capture binders.  Neither is a root, and the search relates neither to
the other.  This is the version's `Z_two_calls_no_level`. -/

/-- `let c1 = fc un in let c2 = fc un in un`, as resolved. -/
def twoCallsAnn : ATm ([],c,c,x,x) :=
  (resolveIn Λc z1Names (cc% let c1 = fc un in let c2 = fc un in un)).getD (.path (.var .here))

/-- The budget of the two calls. -/
def bTwo : Budget := { decls := 0, views := 0, sub := 0, cap := 1, typer := 4, obj := 0 }

example : erasedOf (synthIn? bTwo Z1Ctx ps2z twoCallsAnn) =
    some (.letex (.app (.there .here) .here)
      (.letex (.app (.there (.there (.there .here))) (.there (.there .here)))
        (.path (.var (.there (.there (.there (.there .here)))))))) := by
  decide +kernel

example : (synthIn? bTwo Z1Ctx ps2z twoCallsAnn).toOption.map (·.ans) = some (.ty unitTy) := by
  decide +kernel

example : subcapFound {} Z1BodyCtxSrc [CapAtom.cvar Zk1'] [CapAtom.cvar Zk2'] = false := by
  decide +kernel

example : subcapFound {} Z1BodyCtxSrc [CapAtom.cvar Zk2'] [CapAtom.cvar Zk1'] = false := by
  decide +kernel

/-! ## Z2 and W3: `makeLogger`

The parameter is written `any`, which reads as the arrow's own binder, and the
result is `fresh`.  The written type resolves to the version's `W3TyAny`, and
the typer reaches `Z2Ty`, whose witness is the parameter. -/

/-- `makeLogger`, bound by an ascription. -/
def Z2src : STm :=
  cc% (λ(l : (∀(u : ⊤) ⊤) ^ {any}).
          let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {})

/-- The budget of Z2. -/
def bZ2 : Budget := { decls := 0, views := 0, sub := 1, cap := 1, typer := 9, obj := 1 }

example : resolveTy Λc πz.names
    (ccTy% (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {}) =
      some W3TyAny := by
  decide

example : elaboratedTm bZ2 Λc πz Z2src = some (tmOfDeriv Z2_plat) := by decide +kernel

example : compiledJudgment bZ2 Λc πz Z2src = some (usesOfDeriv Z2_plat, tyOfDeriv Z2_plat) := by
  decide +kernel

#eval expect (compiledVerdict bZ2 Λc πz Z2src)
  "Z2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bZ2 Λc πz Z2src)
  "Z2: the target checker rejects the use set evidence"

/-- Z2 compiles. -/
theorem Z2_compiles : (compile bZ2 Λc πz Z2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z2. -/
theorem Z2_checks : CheckerAccepts bZ2 Λc πz Z2src Z2_compiles :=
  compile_checks_get Z2_compiles

/-! ## Z3: `mk` with a `fresh` result

S2's `mk` with the result written `fresh`.  The typer packs a payload at the
payload's own type, and the literal's precise type is not the iterator type.
So the body ascribes the literal's variable at the iterator type.  The term,
the use set and the type are the version's `Z3_plat`. -/

/-- `mk` with a `fresh` result, its body ascribed. -/
def Z3src : STm :=
  cc% (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in
                 (it : μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fs})
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fresh})
             ^ {fs})

/-- The budget of Z3. -/
def bZ3 : Budget := { decls := 0, views := 1, sub := 2, cap := 2, typer := 10, obj := 1 }

example : compiledTm Λc πz Z3src = some (tmOfDeriv Z3_plat) := by decide

example : compiledJudgment bZ3 Λc πz Z3src = some (usesOfDeriv Z3_plat, tyOfDeriv Z3_plat) := by
  decide +kernel

#eval expect (compiledVerdict bZ3 Λc πz Z3src)
  "Z3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bZ3 Λc πz Z3src)
  "Z3: the target checker rejects the use set evidence"

/-- Z3 compiles. -/
theorem Z3_compiles : (compile bZ3 Λc πz Z3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z3. -/
theorem Z3_checks : CheckerAccepts bZ3 Λc πz Z3src Z3_compiles :=
  compile_checks_get Z3_compiles

/-! ## W2: `process` and its call

`W2defSrc` of `Typer.lean` writes the parameter `any`, which reads as the
arrow's own binder.  It elaborates to the version's `W2Tm`, and its type
reaches `W2Ty` by one `sub`.  The call `p f` is typed at the version's
`W2CallCtx` at the use set `{f}` and the type `⊤`. -/

/-- The budget of `process`. -/
def bW2 : Budget := { decls := 0, views := 0, sub := 0, cap := 1, typer := 3, obj := 0 }

/-- The budget of the call. -/
def bW2call : Budget := { decls := 0, views := 0, sub := 0, cap := 0, typer := 2, obj := 0 }

example : elaboratedTm bW2 Λc πc W2defSrc = some W2Tm := by decide +kernel

example : topReaches { bW2 with sub := 2 } πc (resolveTop Λc πc W2defSrc) [] (.ty W2Ty) = true := by
  decide +kernel

#eval expect (compiledVerdict bW2 Λc πc W2defSrc)
  "W2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bW2 Λc πc W2defSrc)
  "W2: the target checker rejects the use set evidence"

/-- `process` compiles. -/
theorem W2_compiles : (compile bW2 Λc πc W2defSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of `process`. -/
theorem W2_checks : CheckerAccepts bW2 Λc πc W2defSrc W2_compiles :=
  compile_checks_get W2_compiles

example : judgmentOf (synthIn? bW2call W2CallCtx ps2c (.app (.there .here) .here)) =
    some (usesOfDeriv W2_call, .ty (tyOfDeriv W2_call)) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bW2call W2CallCtx ps2c (.app (.there .here) .here)) ==
    (true, true))
  "the call of process: the target checker rejects the translation or the use set evidence"

/-- The call of `process` is typed at `W2CallCtx`. -/
theorem W2call_compiles :
    (synthIn? bW2call W2CallCtx ps2c (.app (.there .here) .here)).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the call of `process` at
the translation of `W2CallCtx`. -/
theorem W2call_checks :
    FCdot.checkTmE W2CallCtx.translate
      ((synthIn? bW2call W2CallCtx ps2c (.app (.there .here) .here)).get
        W2call_compiles).deriv.translate
      ((synthIn? bW2call W2CallCtx ps2c (.app (.there .here) .here)).get
        W2call_compiles).ans.translate = true :=
  synthIn_checks_get W2CallCtx_wf W2call_compiles

/-! ## W2 deep: `any` below a field of a domain

`deepSrc` of `Typer.lean`.  The version's `W2_deep_rejected` says that the
written type is not one the version reads.  The front end rejects it with that
reason. -/

example : (compile {} Λc πc deepSrc).reason?.map Reason.name = some "anyNotOk" := by
  decide +kernel

#eval expect ((compile {} Λc πc deepSrc).reason?.map Reason.name == some "anyNotOk")
  "W2 deep: not rejected for its written type"

/-! ## A: a capture parameter that is called

`P1ann` of `Resolve.lean`, under `unit : ⊤`.  The call is charged to the
function and to the argument.  The closure is pure. -/

/-- The budget of the call of a capture parameter. -/
def bP1 : Budget := { decls := 0, views := 0, sub := 0, cap := 1, typer := 4, obj := 0 }

/-- The context of `P1ann`. -/
def P1Ctx : Ctx ([],c,c,x) := platCtx.cons unitTy

/-- `P1Ctx` is well formed. -/
theorem P1Ctx_wf : P1Ctx.Wf := ctxWf?_sound _ (by decide +kernel)

example : judgmentOf (synthIn? bP1 P1Ctx (CaptureSet.weaken πc.set) P1ann) =
    some ([], .ty ((Shape.all ((Shape.all unitTy (.ty unitTy)) ^ [CapAtom.cvar .here])
      (.ty unitTy)) ^ [])) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? bP1 P1Ctx (CaptureSet.weaken πc.set) P1ann) == (true, true))
  "A: the target checker rejects the translation or the use set evidence"

/-- The call of a capture parameter is typed. -/
theorem P1_compiles : (synthIn? bP1 P1Ctx (CaptureSet.weaken πc.set) P1ann).isOk = true := by
  decide +kernel

/-- The target checker accepts its translation. -/
theorem P1_checks :
    FCdot.checkTmE P1Ctx.translate
      ((synthIn? bP1 P1Ctx (CaptureSet.weaken πc.set) P1ann).get P1_compiles).deriv.translate
      ((synthIn? bP1 P1Ctx (CaptureSet.weaken πc.set) P1ann).get P1_compiles).ans.translate =
      true :=
  synthIn_checks_get P1Ctx_wf P1_compiles

/-! ## W1: the levels of two nested bodies

At `W1Ctx2`, the body of a lambda inside the body of another, the search finds
the level steps the version's `W1` derives: the outer root below the inner
one, and both parameters below the inner root.  It does not find the inner
root below the outer one.  The inner parameter is found below the outer root
by `sc-var`, since the parameter has the pure type `⊤`, and not by the level
rule, which `W1_outer_not_inner` denies. -/

example : subcapFound { cap := 1 } W1Ctx2 [CapAtom.cvar W1outRoot] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound { cap := 1 } W1Ctx2 [CapAtom.var W1outParam] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound { cap := 1 } W1Ctx2 [CapAtom.var W1inParam] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound {} W1Ctx2 [CapAtom.cvar W1inRoot] [CapAtom.cvar W1outRoot] = false := by
  decide +kernel

/-! ## W5: the escape of a callback, at the version's context

At `W5Ctx`, the body of a callback under an older root, the search finds the
callback's parameter below its own body root, the version's `W5_level_own`,
and does not find it below the older root.  The certificate builder rejects
that goal, and `W5_escape_rejected` is the certificate. -/

example : subcapFound {} W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kb] = true := by decide +kernel

example : subcapFound {} W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout] = false := by
  decide +kernel

#eval expect ((certify? W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout]).map Reason.name ==
    some "levelEscape")
  "W5: the escape goal is not certified"

/-- The parameter of the callback resolves to its arrow binder, at every
depth. -/
theorem W5_caps (n : Nat) :
    W5Ctx.translate.caps n (CaptureSet.translate [CapAtom.var W5f]) =
      [FCdot.CapAtom.cvar (.there .here)] := by
  rw [show CaptureSet.translate [CapAtom.var W5f] = [FCdot.CapAtom.var .here] from rfl,
    FCdot.Ctx.caps_cons, FCdot.Ctx.capsAtom_var, FCdot.Ctx.caps_nil, List.append_nil]
  exact caps_self _ (by decide +kernel) n

/-- **W5, rejected.**  No member-free subcapturing puts the callback's
parameter below the root of the scope outside the call. -/
theorem W5_escape_rejected :
    ¬ ∃ d : Subcap W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout], d.MemberFree :=
  escape_rejected_at (ctxWf?_sound _ (by decide +kernel)) (FCdot.CapAtom.cvar W5kout)
    (fun m => by rw [caps_self _ (by decide +kernel) m]; decide +kernel) 0
    (by rw [W5_caps]; decide +kernel)

/-! ## The escape

`EscSrc` of `Notation.lean`: `λ(g : ⊤). let cb : A = λ(f : File ^ {any}).
λ(u : ⊤). f in cb`, where the annotation `A` reads its result `any`s as the
root of `g`'s body.  The callback is typed at its own type, bound to `cb`, and
moved to `A` by the arrow rule, which opens the callback's scope and reaches
`{f} <: {κ_g}`.  The certificate builder rejects that goal.  The goal sits in
`EscGoalCtx`, which binds `cb`. -/

/-- The callback's own type, `∀(f : File ^ {κ}) (∀(u : ⊤) File ^ {f}) ^ {f}`. -/
def cbTy {s : Sig} : Ty s :=
  (Shape.all (fileS ^ [CapAtom.cvar .here])
    (.ty ((Shape.all unitTy (.ty (fileS ^ [CapAtom.var (.there (.there .here))]))) ^
      [CapAtom.var .here]))) ^ []

/-- The context of the goal: the body of `λ(g : ⊤)`, then `cb`, then the
callback's scope. -/
def EscGoalCtx : Ctx (Sig.body (Sig.body ([],c,c),x)) :=
  ((platCtx.body unitTy).cons cbTy).body (fileS ^ [CapAtom.cvar .here])

/-- The root of `g`'s body, read in `EscGoalCtx`. -/
def escRoot : BVar (Sig.body (Sig.body ([],c,c),x)) .cap :=
  .there (.there (.there (.there (.there (.there .here)))))

#eval expect ((resolveTop Λc πc EscSrc).map (fun a => escapesAt (synthTop? {} πc a) EscGoalCtx
    [CapAtom.var .here] [CapAtom.cvar escRoot]) == some true)
  "the escape: not rejected at the goal in EscGoalCtx"

#eval expect ((compile {} Λc πc EscSrc).reason?.map Reason.name == some "levelEscape")
  "the escape: compile does not reject it"

/-- The parameter of the callback resolves to its arrow binder, at every
depth. -/
theorem Esc_caps (n : Nat) :
    EscGoalCtx.translate.caps n (CaptureSet.translate [CapAtom.var .here]) =
      [FCdot.CapAtom.cvar (.there .here)] := by
  rw [show CaptureSet.translate [CapAtom.var (.here : BVar (Sig.body (Sig.body ([],c,c),x)) .var)]
      = [FCdot.CapAtom.var .here] from rfl,
    FCdot.Ctx.caps_cons, FCdot.Ctx.capsAtom_var, FCdot.Ctx.caps_nil, List.append_nil]
  exact caps_self _ (by decide +kernel) n

/-- **The escape, rejected at the goal the typer reached.**  No member-free
subcapturing puts `{f}` below the root of `g`'s body, in the context that
binds `cb`. -/
theorem Esc_rejected' :
    ¬ ∃ d : Subcap EscGoalCtx [CapAtom.var .here] [CapAtom.cvar escRoot], d.MemberFree :=
  escape_rejected_at (ctxWf?_sound _ (by decide +kernel)) (FCdot.CapAtom.cvar escRoot)
    (fun m => by rw [caps_self _ (by decide +kernel) m]; decide +kernel) 0
    (by rw [Esc_caps]; decide +kernel)

/-! ## The escape at the top of a program

`TopEscSrc` of `Typer.lean` binds the same callback at the top, where the
result `any` reads as the platform set and the source has no root.  The goal
is `{f} <: {fs, k2}` in `TopGoalCtx`, and the certificate's root is the
universal one, which the source cannot name. -/

/-- The context of the goal at the top. -/
def TopGoalCtx : Ctx (Sig.body ([],c,c,x)) :=
  (platCtx.cons cbTy).body (fileS ^ [CapAtom.cvar .here])

/-- The platform set, read in `TopGoalCtx`. -/
def topPlat : CaptureSet (Sig.body ([],c,c,x)) :=
  [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
    CapAtom.cvar (.there (.there (.there (.there .here))))]

#eval expect ((resolveTop Λc πc TopEscSrc).map (fun a => escapesAt (synthTop? {} πc a) TopGoalCtx
    [CapAtom.var .here] topPlat) == some true)
  "the escape at the top: not rejected at the goal in TopGoalCtx"

/-- The parameter of the callback resolves to its arrow binder, at every
depth. -/
theorem Top_caps (n : Nat) :
    TopGoalCtx.translate.caps n (CaptureSet.translate [CapAtom.var .here]) =
      [FCdot.CapAtom.cvar (.there .here)] := by
  rw [show CaptureSet.translate [CapAtom.var (.here : BVar (Sig.body ([],c,c,x)) .var)]
      = [FCdot.CapAtom.var .here] from rfl,
    FCdot.Ctx.caps_cons, FCdot.Ctx.capsAtom_var, FCdot.Ctx.caps_nil, List.append_nil]
  exact caps_self _ (by decide +kernel) n

/-- **The escape at the top, rejected at the goal the typer reached.**  No
member-free subcapturing puts `{f}` below the platform set, in the context
that binds `cb`. -/
theorem top_escape_rejected :
    ¬ ∃ d : Subcap TopGoalCtx [CapAtom.var .here] topPlat, d.MemberFree :=
  escape_rejected_at (ctxWf?_sound _ (by decide +kernel)) FCdot.CapAtom.top
    (fun m => by rw [caps_self _ (by decide +kernel) m]; decide +kernel) 0
    (by rw [Top_caps]; decide +kernel)

/-! ## The effect theorem

`compile_effect_safety_get` at C2, for a run of the version's term from the
platform's initial store and a variable `x` the reached state reads.  The
capability is `k1`.  The premise, that the use set the typer found does not
hold `k1`, is decided by the kernel.  The elaborated term equals the version's
term, so the run transfers. -/

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, a variable the reached state reads is not rooted at `k1` in
the matched target state. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile bC2 Λc πc C2src).get C2_compiles).2.tm.erase = C2tm := by
    decide +kernel
  exact compile_effect_safety_get C2_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-! ## The log of a compiled program

`compile_lvl_safety` speaks of each entry of the log `levelSteps` reads off the
derivation.  C2 has 126 entries and S1 has 92. -/

example : (compileLog bC2 Λc πc C2src).length = 126 := by decide +kernel

example : (compileLog bS1 Λc πz S1progSrc).length = 92 := by decide +kernel

/-! ## The run tests

`compileAndRun` at a step budget of 40, printed with the platform's own names.
Each run is pinned at the step count at which it becomes final.

S2 answers with `un`, the identity it passed to the iterator, in fifteen
steps.  C2 answers with the client at `b` in twelve.  E2 answers with the
identity at the literal's member in six. -/

/-- The step budget of the runs. -/
def runBudget : Nat := 40

/-- Whether the driver's answer is a final state.  It is `false` when the
program does not compile. -/
def runFinal? (b : Budget) (m : Nat) (π : PlatformNames) (e : STm) : Bool :=
  match compileAndRun b m Λc π e with
  | .ok r => final? r.2
  | _ => false

#eval ppRunOver Λc ["fs", "k2"] (compileAndRun bS2 runBudget Λc πz S2src)

example : ppRunTmOver Λc ["fs", "k2"] (compileAndRun bS2 runBudget Λc πz S2src) = "x3" := by
  decide +kernel

example : (runFinal? bS2 15 πz S2src && ! runFinal? bS2 14 πz S2src) = true := by
  decide +kernel

#eval ppRunOver Λc ["k1", "k2"] (compileAndRun bC2 runBudget Λc πc C2src)

example : ppRunTmOver Λc ["k1", "k2"] (compileAndRun bC2 runBudget Λc πc C2src) = "x6" := by
  decide +kernel

example : (runFinal? bC2 12 πc C2src && ! runFinal? bC2 11 πc C2src) = true := by
  decide +kernel

#eval ppRun Λc (compileAndRun bE2 runBudget Λc .empty E2src)

example : ppRunTm Λc (compileAndRun bE2 runBudget Λc .empty E2src) = "x1" := by
  decide +kernel

example : (runFinal? bE2 6 .empty E2src && ! runFinal? bE2 5 .empty E2src) = true := by
  decide +kernel

end Examples

end CapturesCCFrontend
