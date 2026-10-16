import Coercions.CapturesCC.Frontend.Pipeline
import Coercions.CapturesCC.Frontend.Pretty

/-!
# The examples end to end

DotMNF is the calculus the typer targets.  The programs of
`DotMNF/Examples.lean`, the programs of `Notation.lean` and `Typer.lean`, and
the programs written here are taken through the whole front end.  Where
`DotMNF/Examples.lean` has a hand written derivation, the term and the
judgment are compared with it.  The pure programs run over the empty platform.
The capture programs run over the platform `πc` of `Resolve.lean`, with
capabilities `k1` and `k2`, or over `πz`, the same two binders named `fs` and
`k2`, for the programs whose capability is a file system.  Both are DotMNF's
`platCtx`.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer and the machine.  That includes a rejection by a level
escape: `certify?` resolves capture sets with `capsS`, the structural form of
`FCdot.Ctx.caps`.  `Esc_compile_rejected` and `TopEsc_compile_rejected` state
the rejection `compile` returns, certificate and goal included.  Every check
runs at `defaultFuel`.

For a program that compiles:

- The term, by `decide`.  This is the resolved term, or the erasure of the
  elaborated term when the typer inserted a box, an unboxing or an unpacking
  (by `decide +kernel`, since it runs the typer).
- `Ek_type`: the use set and the answer the typer finds and the tank it
  leaves, by `decide +kernel`.  The tank left is `defaultFuel` minus the units
  the typing used, and it is unmarked.
- The target checker's verdict on the translation of the derivation and on
  the use set evidence, through `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program.

A program that `DotMNF/Examples.lean` types under a context is typed there.
Its `Ek_type` is a fact about `judgIn`, its `Ek_compiles` about `synthIn?`, and
its `Ek_checks` is `synthIn_checks_get`, the open twin of `compile_checks_get`.

For a program the typer rejects:

- `Ek_verdict`: no answer, and the tank left unmarked, by `decide +kernel`.
- `Ek_rejected`: `compile` returns no result at every budget
  (`judgAt_rejects`).  Above `defaultFuel` this is `synthTop?_stable`, and
  below it `synthTop?_mono`.
- `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive that goal (`var?_reject`).  So no fuel and no other
  order of the alternatives would find it.

For a program at the recursion limit, `Ek_limit`: no answer, and the tank
marked, by `decide +kernel`.  The verdict is the recursion limit, not a
rejection by the rules.

Derivations are not compared, since `DotMNF.HasTy` is data with no decidable
equality and the typer may reach a judgment by another route.  No term, use
set or type is copied from `DotMNF/Examples.lean`: `tmOfDeriv`, `usesOfDeriv`
and `tyOfDeriv` read them off its derivations.  A judgment written here is a
type in the notation, resolved over the program's platform (`pureAt`).

## The programs by verdict

Accepted at the judgment of `DotMNF/Examples.lean`: E5, E6 at `E6Ctx1`, E7,
E8, C7 with its boxes written and with no box written, S3, S1, S2, Z1, Z2, Z3,
the call of `process` at `W2CallCtx`, and the unpacking at `Z1Ctx` whose
answer is existential.

Accepted at a least judgment, from which that judgment is reached by one
`sub`: C2 at `{k2}`, C5 at `{it, it.C}`, the caller of `freshCell` at
`{fc, fs, un}`, and `process`.  E2 is typed at the type avoidance gives,
`∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`, where the hand written derivation concludes
`⊤`.

Accepted at a judgment written here: `freshCell` bound by a `let` whose
answer is written with `fresh`, the existential annotations cov2 and cov4,
the projection cov3, a callback that keeps what it captures inside its own
scope, a capture parameter that is called, two calls of `freshCell`, and an
unpacking whose payload leaves by the level rule.

Accepted, and found by no search over the declared types of the context: PA1,
a function at a member selected through a recursive shape.  P4, a field four
steps down the upper bound of a selection.  P5, an intersection of two
function types applied to an argument only the second accepts.  R1 to R4, a
projection with two fields of which only the second lets the rest of the
program type.  E1s and E3s, which are E1 and E3 with the middle type written.
The alias chains of sixteen and thirty two links.  BX2 and BX, where a boxed
variable meets a boxed goal, unboxing fails and boxing succeeds.

Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
program does not write, and the typer chooses none.  A1 has a written `let`
annotation the bound value does not meet, and a written annotation binds.
Each has its `¬ Alg` fact.  Rejected with a reason: `any` below a field of a
domain, an existential answer outside every scope, and the three escapes of
a callback.  The escape and the escape at the top carry a certificate at the
goal the typer reached, and the kernel computes that rejection.

At the recursion limit: LP, a check through `∀` bodies that reaches the same
goal under one more binder at every level.  PF, Pierce's divergence of F<:,
whose goal comes back under a new binder that it names.

## Levels, effects and runs

W1 and W5 ask subcapturing for the steps of the level order.
`compile_effect_safety_get` at C2 says that a run of C2 never reads a variable
rooted at `k1`.  At `ReadK2Src` it says the same of a run that reads a
variable declared at `{k2}`, next to a variable declared at `{k1}` that the
run never reads.  The logs `levelSteps` reads off the derivations of C2 and S1
are pinned in size.  `compile_lvl_safety_get` is applied to an entry of the
log of C7, whose premise holds at every capture binder, and to an entry of
the log of `CallbackSrc`, whose premise holds at one root and fails at another.  S2 and C2 are run from the platform's initial store,
printed with the platform's own names, and pinned at the step count at which
they become final.  E2 is run beside them over the empty platform.

## Annotations erased

Every closed program above, and the programs of `Elab.lean` with their
written forms, is taken through the front end again with its annotations
erased, in five ways: every lambda domain (`D`), every self shape (`S`), the
domain of every lambda passed as an argument (`A`), the domain of every lambda
in a checked position (`C`), and `C` with every self shape erased too (`G`).
`row` gives the verdict on each, by `decide +kernel`.  `RejectedWith`,
`erasedCell_same` and `erasedCell_other` read a cell as a fact about
`compile`.  Each erased program that compiles has its `_checks` theorem.

## Completeness at the direct sites

Each erased program whose empty slots sit at direct sites, as `Canon` of
`Pipeline.lean` names them, has a `_complete` theorem: it compiles as its
written form does, fill, term, use set, type and derivation, at every budget
from some fuel on (`CompilesAs`, `compile_complete_canonAt`).  These are the
erased programs of the tables that compile at the written term but those
whose self shapes the rounds form, and SideCurry, whose inner lambda takes its
domain through an intersection.  Mid is a call argument the typer accepts at a
formal other than the dominant one, which the elaborator rejects.
-/

namespace CapturesCCFrontend

open CapturesCC
open Frontend.Fuel CapturesCCFrontend.Core
open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (CapAtom CaptureSet Shape Ty ETy Tm Ctx HasTy HasTyP Subcap State Steps)
open scoped CapturesCC.DotMNF

section Examples

open CapturesCC.DotMNF.Examples

/-! ## Reading a derivation of DotMNF -/

/-- The term a derivation of DotMNF is about. -/
def tmOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : Tm s := t

/-- The use set a derivation of DotMNF is about. -/
def usesOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : CaptureSet s := U

/-- The type a derivation of DotMNF is about. -/
def tyOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTyP U Γ t T) : Ty s := T

/-! ## The decidable things -/

/-- The resolved term, erased into DotMNF's syntax. -/
def compiledTm (Λ : LabelTable) (π : PlatformNames) (e : STm) : Option (Tm π.sig) :=
  (resolveTop Λ π e).map ATm.erase

/-- The elaborated term, erased.  It differs from the resolved one when the
typer inserted a box, an unboxing or an unpacking. -/
def elaboratedTm (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option (Tm π.sig) :=
  (compile b Λ π e).toOption.map fun r => r.2.tm.erase

/-- The judgment at the empty use set and a type written in the notation,
resolved over the platform `π`. -/
def pureAt (π : PlatformNames) (T : SType) : Option (CaptureSet π.sig × ETy π.sig) :=
  (resolveTy Λc π.names T).map fun T' => ([], .ty T')

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

/-- What `compile_checks_get` concludes at a program that compiles: the
target checker accepts the translation of its derivation. -/
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

/-- A verdict that is a sequence whose first step is not a success is not a
success. -/
theorem Verdict.isOk_bind_false {α β : Type} {v : Verdict α} {f : α → Verdict β}
    (h : v.isOk = false) : (v.bind f).isOk = false := by
  cases v with
  | ok a => simp [Verdict.isOk] at h
  | rejected r => rfl
  | unknown => rfl

/-- A rejection that leaves the tank unmarked is a rejection at every budget.
`judgAt` marks the tank of a program with no resolution, so the program
resolves with every slot written, and `compile_full` makes its compile the
typer's verdict.  Above the fuel of the check this is `synthTop?_stable`.  Below it, an answer
would be kept by `synthTop?_mono` and contradict the check.  With no
candidate, `synthIn?` is `rejected` or `unknown`, and `compile` passes either
on. -/
theorem judgAt_rejects {π : PlatformNames} {e : STm} {n k : Nat}
    (h : judgAt π e n = (none, ⟨k, false⟩)) (b : Budget) : (compile b Λc π e).isOk = false := by
  unfold judgAt at h
  cases hr : resolveTop Λc π e with
  | none =>
    rw [hr] at h
    cases h
  | some a =>
    rw [hr] at h
    simp only [Prod.mk.injEq, Option.map_eq_none_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hs : synthTopF n π a = (none, ⟨k, false⟩) := by rw [← h1, ← h2]
    have hnone : (synthTopF b.fuel π a).1 = none := by
      rcases Nat.le_total n b.fuel with hle | hle
      · have := synthTop?_stable hs (b.fuel - n)
        rwa [Nat.add_sub_cancel' hle] at this
      · cases hc : (synthTopF b.fuel π a).1 with
        | none => rfl
        | some c =>
          have := synthTop?_mono hc hle
          rw [h1] at this
          cases this
    have hin : (synthIn? b π.plat.ctx π.set a).isOk = false := by
      unfold synthIn?
      unfold synthTopF at hnone
      cases hq : synthInF π.plat.ctx π.set a b.fuel with
      | mk o t =>
        rw [hq] at hnone
        cases hnone
        simp only
        split
        · rfl
        · split <;> rfl
    rw [compile_full hr]
    unfold compileLanded synthTop?
    exact Verdict.isOk_bind_false (Verdict.isOk_bind_false hin)

/-- Subcapturing at a context, from a full tank of the budget's fuel. -/
def subcapFound {s : Sig} (b : Budget) (Γ : Ctx s) (C D : CaptureSet s) : Bool :=
  (Core.subcap? Γ C D b.fuel).1.isSome

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

The annotated `let` is typed through the bad bounds chain in DotMNF's
derivation `E1`.  The chain passes the middle `x.A`, which the program does
not write, so the typer rejects the program, as the Scala compiler does.  The
goal it rejects is the check of the body `y` against the annotation. -/

/-- `λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤}..{a : ⊤}} = x in y`. -/
def E1src : STm := cc% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

example : compiledTm Λc .empty E1src = some (tmOfDeriv E1) := by decide

/-- The body of E1's lambda, then the `let` binder `y` at the type of `x`. -/
def E1yCtx : Ctx (Sig.body ([] : Sig),x) := E1Ctx.cons E1Dom

/-- The typer rejects E1 after 11 units, with the tank unmarked. -/
theorem E1_verdict : judgAt .empty E1src = (none, ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-- E1 does not compile at any budget. -/
theorem E1_rejected (b : Budget) : (compile b Λc .empty E1src).isOk = false :=
  judgAt_rejects E1_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation. -/
theorem E1_not_alg : ¬ Alg ⟨_, E1yCtx, .var .here E1Dom E1Res⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E1yCtx .here E1Res) 5 = true))
  have hv : (varView E1yCtx .here).ty = E1Dom := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## E2: a recursive object with a self referential member

The outer `let` has no annotation, and its body's type mentions the bound
variable.  Avoidance replaces `x.A` by its upper bound with `x` avoided,
`∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`, as `TypeOps.avoid` does.  The hand written
derivation `E2` gives `⊤`.  The term is the same. -/

/-- `let x = ν(s : {A : E2A..E2A} ∧ {a : E2A}. {type A = E2A} ∧ {a = λ(y : s.A). y})
in let f = x.a in f f`, with `E2A` the shape `∀(y : s.A) s.A`. -/
def E2src : STm :=
  cc% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

example : compiledTm Λc .empty E2src = some (tmOfDeriv E2) := by decide

/-- E2 is typed at the avoided type, from 60 units. -/
theorem E2_type : judgAt .empty E2src =
    (some (usesOfDeriv E2, .ty Core.E2AvoidedTy), ⟨defaultFuel - 60, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E2src)
  "E2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E2src)
  "E2: the target checker rejects the use set evidence"

/-- E2 compiles. -/
theorem E2_compiles : (compile {} Λc .empty E2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts {} Λc .empty E2src E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  DotMNF's derivation `E3`
passes the middle `x.A`, which the program does not write, so the typer
rejects the program, as the Scala compiler does.  The goal it rejects is the
check of the body `y` against the annotation. -/

/-- `λ(x : {A : ⊥..{a : ⊤}} ∧ {A : {b : ⊤}..⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y`. -/
def E3src : STm :=
  cc% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

example : compiledTm Λc .empty E3src = some (tmOfDeriv E3) := by decide

/-- The body of the inner lambda, then the `let` binder `y : {b : ⊤}`. -/
def E3yCtx : Ctx (Sig.body (Sig.body ([] : Sig)),x) := E3Ctx2.cons E3T2

/-- The typer rejects E3 after 11 units, with the tank unmarked. -/
theorem E3_verdict : judgAt .empty E3src = (none, ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-- E3 does not compile at any budget. -/
theorem E3_rejected (b : Budget) : (compile b Λc .empty E3src).isOk = false :=
  judgAt_rejects E3_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3_not_alg : ¬ Alg ⟨_, E3yCtx, .var .here E3T2 E3T1⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E3yCtx .here E3T1) 5 = true))
  have hv : (varView E3yCtx .here).ty = E3T2 := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## E4: typing with no realizer

DotMNF's derivation `E4` widens `w` to `x.B`, a subsumption through a
middle the program does not write, so the typer rejects the program, as the
Scala compiler does.  The goal it rejects is the argument `n` of `g n`
against the domain `w.A`, in `E4Ctx4`, where `g` has the type the typer gives
it. -/

/-- `λ(x : {B : {A : ⊥..⊤}..{A : {a : ⊤}..⊤}}). λ(w : {A : ⊥..⊤}). λ(n : {a : ⊤}).
let g = λ(y : w.A). y in g n`. -/
def E4src : STm :=
  cc% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
         λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

example : compiledTm Λc .empty E4src = some (tmOfDeriv E4) := by decide

/-- The typer gives `g` the type `E4G`, so the goal of `g n`
sits in `E4Ctx4`. -/
example : judgIn E4Ctx3 [] (.lam ((Shape.sel (.var (.there (up .here))) lA) ^ [])
    (.path (.var .here))) = (some ([], .ty (E4G (up .here))), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The typer rejects E4 after 16 units, with the tank unmarked. -/
theorem E4_verdict : judgAt .empty E4src = (none, ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- E4 does not compile at any budget. -/
theorem E4_rejected (b : Budget) : (compile b Λc .empty E4src).isOk = false :=
  judgAt_rejects E4_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4_not_alg :
    ¬ Alg ⟨_, E4Ctx4,
      .var (.there .here) E4Int ((Shape.sel (.var (.there (up .here))) lA) ^ [])⟩ :=
  E4_var_not_alg

/-! ## E5: an object returned from a function

The application renames the result's member to `w`, and the outer `let`
keeps `w.A`.  DotMNF's derivation is `E5`. -/

/-- `λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
in let o = f w in o.a`. -/
def E5src : STm :=
  cc% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
         in let o = f w in o.a

example : compiledTm Λc .empty E5src = some (tmOfDeriv E5) := by decide

/-- E5 is typed at DotMNF's judgment, from 20 units. -/
theorem E5_type : judgAt .empty E5src =
    (some (usesOfDeriv E5, .ty (tyOfDeriv E5)), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E5src)
  "E5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E5src)
  "E5: the target checker rejects the use set evidence"

/-- E5 compiles. -/
theorem E5_compiles : (compile {} Λc .empty E5src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts {} Λc .empty E5src E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

DotMNF types E6 at `E6Ctx1`, which binds `n : {a : ⊤}`.  So the literal
is resolved under the name `n` and typed at that context. -/

/-- `ν(x : {T : {a : ⊤}..{a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})`. -/
def E6src : STm :=
  cc% ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

/-- The names of `E6Ctx1`. -/
def E6names : NameEnv ([],x) := PlatformNames.empty.names.cons "n"

/-- E6 as resolved. -/
def E6ann : ATm ([],x) := (resolveIn Λc E6names E6src).getD (.path (.var .here))

/-- `E6Ctx1` is well formed. -/
theorem E6Ctx1_wf : E6Ctx1.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc E6names E6src).map ATm.erase = some (tmOfDeriv E6) := by decide

/-- E6 is typed at `E6Ctx1` at DotMNF's judgment, from 13 units. -/
theorem E6_type : judgIn E6Ctx1 [] E6ann =
    (some (usesOfDeriv E6, .ty (tyOfDeriv E6)), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} E6Ctx1 [] E6ann) == (true, true))
  "E6: the target checker rejects the translation or the use set evidence"

/-- E6 is typed at `E6Ctx1`. -/
theorem E6_compiles : (synthIn? {} E6Ctx1 [] E6ann).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E6 at the translation of
`E6Ctx1`. -/
theorem E6_checks :
    FCdot.checkTmE E6Ctx1.translate ((synthIn? {} E6Ctx1 [] E6ann).get E6_compiles).deriv.translate
      ((synthIn? {} E6Ctx1 [] E6ann).get E6_compiles).ans.translate = true :=
  synthIn_checks_get E6Ctx1_wf E6_compiles

/-! ## E7: two type members that name each other

DotMNF's derivation is `E7`.  Nothing is compared. -/

/-- `ν(x : {A : x.B..x.B} ∧ {B : x.A..x.A}. {type A = x.B} ∧ {type B = x.A})`. -/
def E7src : STm :=
  cc% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})

example : compiledTm Λc .empty E7src = some (tmOfDeriv E7) := by decide

/-- E7 is typed at DotMNF's judgment, from 1 unit. -/
theorem E7_type : judgAt .empty E7src =
    (some (usesOfDeriv E7, .ty (tyOfDeriv E7)), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E7src)
  "E7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E7src)
  "E7: the target checker rejects the use set evidence"

/-- E7 compiles. -/
theorem E7_compiles : (compile {} Λc .empty E7src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts {} Λc .empty E7src E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: refining an abstract type

DotMNF gives one term two derivations, `E8` and `E8b`, at one
judgment.  The typer finds that judgment. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`. -/
def E8src : STm := cc% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

example : compiledTm Λc .empty E8src = some (tmOfDeriv E8) := by decide

example : tmOfDeriv E8b = tmOfDeriv E8 := rfl

example : (usesOfDeriv E8b, tyOfDeriv E8b) = (usesOfDeriv E8, tyOfDeriv E8) := by decide

/-- E8 is typed at DotMNF's judgment, from 13 units. -/
theorem E8_type : judgAt .empty E8src =
    (some (usesOfDeriv E8, .ty (tyOfDeriv E8)), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E8src)
  "E8: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E8src)
  "E8: the target checker rejects the use set evidence"

/-- E8 compiles. -/
theorem E8_compiles : (compile {} Λc .empty E8src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts {} Λc .empty E8src E8_compiles :=
  compile_checks_get E8_compiles

/-! ## E1s and E3s: the middle written

E1 and E3 with the middle type `x.A` written.  A `let` annotation types the
whole `let`, so `let u : x.A = t in u` ascribes `x.A` to `t`.  Each step is
then one goal the typer asks, and both programs compile at DotMNF's
types. -/

/-- E1 with the middle written is typed at `∀(x : E1Dom) E1Res`, from 20 units. -/
theorem E1s_type : judgAt .empty E1ssrc =
    (some ([], .ty ((Shape.all E1Dom (.ty E1Res)) ^ [])), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E1ssrc)
  "E1s: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E1ssrc)
  "E1s: the target checker rejects the use set evidence"

/-- E1 with the middle written compiles. -/
theorem E1s_compiles : (compile {} Λc .empty E1ssrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem E1s_checks : CheckerAccepts {} Λc .empty E1ssrc E1s_compiles :=
  compile_checks_get E1s_compiles

/-- E3 with the middle written is typed at `∀(x : E3Dom) ∀(z : E3T2) E3T1`,
from 18 units. -/
theorem E3s_type : judgAt .empty E3ssrc =
    (some ([], .ty ((Shape.all E3Dom (.ty ((Shape.all E3T2 (.ty E3T1)) ^ []))) ^ [])),
      ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E3ssrc)
  "E3s: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E3ssrc)
  "E3s: the target checker rejects the use set evidence"

/-- E3 with the middle written compiles. -/
theorem E3s_compiles : (compile {} Λc .empty E3ssrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem E3s_checks : CheckerAccepts {} Λc .empty E3ssrc E3s_compiles :=
  compile_checks_get E3s_compiles

/-! ## C7: a container of boxed capabilities, boxes written

The fields check by the box rule, and the client unboxes at `{k1}`.  DotMNF's
derivation is `C7_typed`. -/

/-- C7 with its boxes and its unboxing written. -/
def C7boxSrc : STm :=
  cc% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

example : compiledTm Λc πc C7boxSrc = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7boxSrc = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with its boxes written is typed at DotMNF's judgment, from 31
units. -/
theorem C7box_type : judgAt πc C7boxSrc =
    (some (usesOfDeriv C7_typed, .ty (tyOfDeriv C7_typed)), ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C7boxSrc)
  "C7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C7boxSrc)
  "C7: the target checker rejects the use set evidence"

/-- C7 with its boxes written compiles. -/
theorem C7box_compiles : (compile {} Λc πc C7boxSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with its boxes
written. -/
theorem C7box_checks : CheckerAccepts {} Λc πc C7boxSrc C7box_compiles :=
  compile_checks_get C7box_compiles

/-! ## C7 with no box in any term

`C7src` of `Typer.lean`.  The typer inserts `□ f1` and `□ f2` at the fields and
`{k1} ⊸ e` at the ascription.  The elaborated term is DotMNF's. -/

example : compiledTm Λc πc C7src ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7src = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with no box written is typed at DotMNF's judgment, from 80 units. -/
theorem C7_type : judgAt πc C7src =
    (some (usesOfDeriv C7_typed, .ty (tyOfDeriv C7_typed)), ⟨defaultFuel - 80, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C7src)
  "C7 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C7src)
  "C7 with no box: the target checker rejects the use set evidence"

/-- C7 with no box in any term compiles. -/
theorem C7_compiles : (compile {} Λc πc C7src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with no box in any
term. -/
theorem C7_checks : CheckerAccepts {} Λc πc C7src C7_compiles :=
  compile_checks_get C7_compiles

/-! ## S3: a type member at a boxed capturing type

The bounds of a type member are shapes, so the program writes the box in the
member.  The client unboxes through the upper bound of `o.A`.  DotMNF's
derivation is `S3_typed`. -/

/-- S3, its box and its unboxing written. -/
def S3src : STm :=
  cc% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : □((∀(u : ⊤) ⊤) ^ {f}) .. □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem : z.A}.
                   {type A = □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem = □ f})
        in let e = o.elem in {f} ⊸ e

example : compiledTm Λc πc S3src = some (tmOfDeriv S3_typed) := by decide

/-- S3 is typed at DotMNF's judgment, from 46 units. -/
theorem S3_type : judgAt πc S3src =
    (some (usesOfDeriv S3_typed, .ty (tyOfDeriv S3_typed)), ⟨defaultFuel - 46, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S3src)
  "S3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S3src)
  "S3: the target checker rejects the use set evidence"

/-- S3 compiles. -/
theorem S3_compiles : (compile {} Λc πc S3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S3. -/
theorem S3_checks : CheckerAccepts {} Λc πc S3src S3_compiles :=
  compile_checks_get S3_compiles

/-! ## C2: capture polymorphism by a capture member

The client reads `x.run`, whose set is `{x.C}`.  The typer finds the judgment
`{k2}` and `(⊤ → ⊤) ^ {k2}`, since the answer is the client at `b`, whose
member is `{k2}`.  DotMNF's `{k1, k2}` is reached by one `sub`. -/

/-- C2, with the call `x.run u` in direct style. -/
def C2src : STm :=
  cc% let c = λ(x : μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

example : compiledTm Λc πc C2src = some (tmOfDeriv C2_typed) := by decide

example : elaboratedTm {} Λc πc C2src = some (tmOfDeriv C2_typed) := by decide +kernel

/-- C2 is typed at `{k2}` and `(⊤ → ⊤) ^ {k2}`, from 214 units. -/
theorem C2_type : judgAt πc C2src =
    (some ([CapAtom.cvar k2], .ty ((Shape.all unitTy (.ty unitTy)) ^ [CapAtom.cvar k2])),
      ⟨defaultFuel - 214, false⟩) := by
  decide +kernel

example : topReaches {} πc (resolveTop Λc πc C2src) (usesOfDeriv C2_typed)
    (.ty (tyOfDeriv C2_typed)) = true := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C2src)
  "C2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C2src)
  "C2: the target checker rejects the use set evidence"

/-- C2 compiles. -/
theorem C2_compiles : (compile {} Λc πc C2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C2. -/
theorem C2_checks : CheckerAccepts {} Λc πc C2src C2_compiles :=
  compile_checks_get C2_compiles

/-! ## S1: `withFile` with an explicit capture parameter

`withFile` is bound by an ascription at its signature.  Its result `any` is
read at the top of the program as the platform set.  The judgment is DotMNF's
`S1_typed`, `{fs, k2}` and `⊤ ^ {fs, k2}`.  The program runs over `πz`. -/

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

example : compiledTm Λc πz S1progSrc = some (tmOfDeriv S1_typed) := by decide

/-- S1 is typed at DotMNF's judgment, from 86 units. -/
theorem S1_type : judgAt πz S1progSrc =
    (some (usesOfDeriv S1_typed, .ty (tyOfDeriv S1_typed)), ⟨defaultFuel - 86, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz S1progSrc)
  "S1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz S1progSrc)
  "S1: the target checker rejects the use set evidence"

/-- S1 compiles. -/
theorem S1_compiles : (compile {} Λc πz S1progSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S1. -/
theorem S1_checks : CheckerAccepts {} Λc πz S1progSrc S1_compiles :=
  compile_checks_get S1_compiles

/-! ## S2: a class with a capture set parameter

`mk` is bound by an ascription at its signature, with `any` in its result,
read as the platform set.  The caller's answer leaves scope at the upper bound
of the member, `{fs}`.  The judgment is DotMNF's `S2_typed`. -/

/-- S2. -/
def S2src : STm :=
  cc% let mk =
        (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in it
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {any}) ^ {fs}) in
      let un = (λ(y : ⊤). y : ⊤) in
      let it = mk un in let n = it.next in let r = n un in r

example : compiledTm Λc πz S2src = some (tmOfDeriv S2_typed) := by decide

/-- S2 is typed at DotMNF's judgment, from 138 units. -/
theorem S2_type : judgAt πz S2src =
    (some (usesOfDeriv S2_typed, .ty (tyOfDeriv S2_typed)), ⟨defaultFuel - 138, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz S2src)
  "S2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz S2src)
  "S2: the target checker rejects the use set evidence"

/-- S2 compiles. -/
theorem S2_compiles : (compile {} Λc πz S2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S2. -/
theorem S2_checks : CheckerAccepts {} Λc πz S2src S2_compiles :=
  compile_checks_get S2_compiles

/-! ## C5: the caller of `mk`, at DotMNF's own context

DotMNF types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  The
typer finds `{it, it.C}` and `⊤ ^ {it.C}`.  DotMNF's `{fs, k2}` and
`⊤ ^ {fs}` are reached by one `sub`. -/

/-- `let n = it.next in let r = n un in r`. -/
def C5src : STm := cc% let n = it.next in let r = n un in r

/-- The names of `S2Ctx3`: the platform, then `mk`, `un` and `it`. -/
def C5names : NameEnv ([],c,c,x,x,x) := ((πz.names.cons "mk").cons "un").cons "it"

/-- C5 as resolved. -/
def C5ann : ATm ([],c,c,x,x,x) := (resolveIn Λc C5names C5src).getD (.path (.var .here))

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc C5names C5src).map ATm.erase = some (tmOfDeriv C5_typed) := by decide

/-- C5 is typed at `{it, it.C}` and `⊤ ^ {it.C}`, from 16 units. -/
theorem C5_type : judgIn S2Ctx3 platSet3 C5ann =
    (some ([CapAtom.var .here, CapAtom.sel .here lC], .ty (Shape.top ^ [CapAtom.sel .here lC])),
      ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

example : reachesAt {} S2Ctx3 platSet3 C5ann (usesOfDeriv C5_typed)
    (.ty (tyOfDeriv C5_typed)) = true := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} S2Ctx3 platSet3 C5ann) == (true, true))
  "C5: the target checker rejects the translation or the use set evidence"

/-- C5 is typed at `S2Ctx3`. -/
theorem C5_compiles : (synthIn? {} S2Ctx3 platSet3 C5ann).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C5 at the translation of
`S2Ctx3`. -/
theorem C5_checks :
    FCdot.checkTmE S2Ctx3.translate ((synthIn? {} S2Ctx3 platSet3 C5ann).get C5_compiles).deriv.translate
      ((synthIn? {} S2Ctx3 platSet3 C5ann).get C5_compiles).ans.translate = true :=
  synthIn_checks_get S2Ctx3_wf C5_compiles

/-! ## Z1: `freshCell`

The signature writes `fresh` in the result.  The typer reads it as DotMNF's `Z1Ty`, an existential bounded by `{fs, u}`,
and the arrow rule packs the cell.  The term and the judgment are DotMNF's
`Z1_plat`. -/

/-- `freshCell`, bound by an ascription. -/
def Z1progSrc : STm :=
  cc% (λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs})

example : compiledTm Λc πz Z1progSrc = some (tmOfDeriv Z1_plat) := by decide

/-- `readAt` expands the `any`s, of which there are none, and reads `fresh` as
the existential.  This is DotMNF's W4. -/
example : readAt platCtx platSet (Z1TyF k1) = Z1Ty k1 := by decide

/-- Z1 is typed at DotMNF's judgment, from 12 units. -/
theorem Z1_type : judgAt πz Z1progSrc =
    (some (usesOfDeriv Z1_plat, .ty (tyOfDeriv Z1_plat)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz Z1progSrc)
  "Z1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz Z1progSrc)
  "Z1: the target checker rejects the use set evidence"

/-- Z1 compiles. -/
theorem Z1_compiles : (compile {} Λc πz Z1progSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z1. -/
theorem Z1_checks : CheckerAccepts {} Λc πz Z1progSrc Z1_compiles :=
  compile_checks_get Z1_compiles

/-! ## `freshCell` bound by a `let`

`Z1defSrc` of `Typer.lean`: the annotation of the `let` writes `fresh` in the
result, which reads as `Z1Ty`, and the closure reaches it by the arrow rule. -/

/-- `freshCell` bound by a `let` is typed at `Z1Ty`, from 31 units. -/
theorem Z1def_type : judgAt πz Z1defSrc =
    (pureAt πz (ccTy% (∀(u : ⊤) ∃[c ⊑ {fs, u}] μ(y. {read : (∀(v : ⊤) ⊤) ^ {y}}) ^ {c}) ^ {fs}),
      ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

example : judgAt πz Z1defSrc = (some ([], .ty (Z1Ty k1)), ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz Z1defSrc)
  "freshCell by a let: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz Z1defSrc)
  "freshCell by a let: the target checker rejects the use set evidence"

/-- `freshCell` bound by a `let` compiles. -/
theorem Z1def_compiles : (compile {} Λc πz Z1defSrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem Z1def_checks : CheckerAccepts {} Λc πz Z1defSrc Z1def_compiles :=
  compile_checks_get Z1def_compiles

/-! ## The caller of `freshCell`, at `Z1Ctx`

`Z1callerAnn` of `Resolve.lean`.  The `let` becomes a `letex`, and the
elaborated term erases to the term of DotMNF's `Z1_caller`.  The typer
finds `{fc, fs, un}`, and DotMNF's `Z1Use ∪ Z1Use` is reached by one
`sub`. -/

example : erasedOf (synthIn? {} Z1Ctx ps2z Z1callerAnn) = some (tmOfDeriv Z1_caller) := by
  decide +kernel

/-- The caller of `freshCell` is typed at `{fc, fs, un}` and the closure at
its own type, from 8 units. -/
theorem Z1caller_type : judgIn Z1Ctx ps2z Z1callerAnn =
    (some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here], .ty (arrowS ^ [])),
      ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

example : reachesAt {} Z1Ctx ps2z Z1callerAnn
    (usesOfDeriv Z1_caller) (.ty (tyOfDeriv Z1_caller)) = true := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} Z1Ctx ps2z Z1callerAnn) == (true, true))
  "the caller of freshCell: the target checker rejects the translation or the use set evidence"

/-- The caller of `freshCell` is typed at `Z1Ctx`. -/
theorem Z1caller_compiles : (synthIn? {} Z1Ctx ps2z Z1callerAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the caller of `freshCell`
at the translation of `Z1Ctx`. -/
theorem Z1caller_checks :
    FCdot.checkTmE Z1Ctx.translate
      ((synthIn? {} Z1Ctx ps2z Z1callerAnn).get Z1caller_compiles).deriv.translate
      ((synthIn? {} Z1Ctx ps2z Z1callerAnn).get Z1caller_compiles).ans.translate = true :=
  synthIn_checks_get Z1Ctx_wf Z1caller_compiles

/-! ## An unpacking whose answer is existential, at `Z1Ctx`

`let c1 = fc un in fc un`, `Z1TailAnn` of `Resolve.lean`.  The answer is the
second call's existential, moved past the witness and the payload of the
first. -/

/-- The unpacking is typed at an existential answer, from 5 units. -/
theorem Z1tail_type : judgIn Z1Ctx ps2z Z1TailAnn =
    (some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here],
      ∃ᶜ[Z1Use] (fileS ^ [CapAtom.cvar .here])), ⟨defaultFuel - 5, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} Z1Ctx ps2z Z1TailAnn) == (true, true))
  "the unpacking: the target checker rejects the translation or the use set evidence"

/-- The unpacking is typed at `Z1Ctx`. -/
theorem Z1tail_compiles : (synthIn? {} Z1Ctx ps2z Z1TailAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the unpacking at the
translation of `Z1Ctx`. -/
theorem Z1tail_checks :
    FCdot.checkTmE Z1Ctx.translate
      ((synthIn? {} Z1Ctx ps2z Z1TailAnn).get Z1tail_compiles).deriv.translate
      ((synthIn? {} Z1Ctx ps2z Z1TailAnn).get Z1tail_compiles).ans.translate = true :=
  synthIn_checks_get Z1Ctx_wf Z1tail_compiles

/-! ## Two calls of `freshCell`, at `Z1Ctx`

Each call is unpacked by a `letex` of its own, so the body runs under two
opened capture binders.  Neither is a root, and subcapturing relates neither to
the other.  This is DotMNF's `Z_two_calls_no_level`. -/

/-- `let c1 = fc un in let c2 = fc un in un`, as resolved. -/
def twoCallsAnn : ATm ([],c,c,x,x) :=
  (resolveIn Λc z1Names (cc% let c1 = fc un in let c2 = fc un in un)).getD (.path (.var .here))

example : erasedOf (synthIn? {} Z1Ctx ps2z twoCallsAnn) =
    some (.letex (.app (.there .here) .here)
      (.letex (.app (.there (.there (.there .here))) (.there (.there .here)))
        (.path (.var (.there (.there (.there (.there .here)))))))) := by
  decide +kernel

/-- The two calls are typed at `{fc, fs, un}` and `⊤`, from 6 units. -/
theorem twoCalls_type : judgIn Z1Ctx ps2z twoCallsAnn =
    (some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here], .ty unitTy),
      ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} Z1Ctx ps2z twoCallsAnn) == (true, true))
  "two calls: the target checker rejects the translation or the use set evidence"

/-- The two calls are typed at `Z1Ctx`. -/
theorem twoCalls_compiles : (synthIn? {} Z1Ctx ps2z twoCallsAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the two calls at the
translation of `Z1Ctx`. -/
theorem twoCalls_checks :
    FCdot.checkTmE Z1Ctx.translate
      ((synthIn? {} Z1Ctx ps2z twoCallsAnn).get twoCalls_compiles).deriv.translate
      ((synthIn? {} Z1Ctx ps2z twoCallsAnn).get twoCalls_compiles).ans.translate = true :=
  synthIn_checks_get Z1Ctx_wf twoCalls_compiles

example : subcapFound {} Z1BodyCtxSrc [CapAtom.cvar Zk1'] [CapAtom.cvar Zk2'] = false := by
  decide +kernel

example : subcapFound {} Z1BodyCtxSrc [CapAtom.cvar Zk2'] [CapAtom.cvar Zk1'] = false := by
  decide +kernel

/-! ## A payload that leaves by the level rule

`let x = fc un in x` in the body of a lambda at `Z1Ctx`.  The payload's type
leaves the unpacking as a file captured by that body's root, the compiler's
local root absorbing a `fresh`. -/

/-- The body of a lambda `λ(v : ⊤)` at `Z1Ctx`. -/
def absorbCtx : Ctx (Sig.body ([],c,c,x,x)) := Z1Ctx.body unitTy

/-- `absorbCtx` is well formed. -/
theorem absorbCtx_wf : absorbCtx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- `let x = fc un in x`, resolved in `absorbCtx`. -/
def absorbAnn : ATm (Sig.body ([],c,c,x,x)) :=
  (resolveIn Λc (((z1Names.consC "%").consC "%").cons "v") (cc% let x = fc un in x)).getD
    (.path (.var .here))

/-- The unpacking is typed at a file captured by the body's root, from 7
units. -/
theorem absorb_type : judgIn absorbCtx (psBody ps2z) absorbAnn =
    (some ([CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.cvar (up fs2),
        CapAtom.var (.there (.there (.there .here)))],
      .ty (fileS ^ [CapAtom.cvar (.there (.there .here))])), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} absorbCtx (psBody ps2z) absorbAnn) == (true, true))
  "the absorbed payload: the target checker rejects the translation or the use set evidence"

/-- The unpacking is typed at `absorbCtx`. -/
theorem absorb_compiles : (synthIn? {} absorbCtx (psBody ps2z) absorbAnn).isOk = true := by
  decide +kernel

/-- The target checker accepts its translation at the translation of
`absorbCtx`. -/
theorem absorb_checks :
    FCdot.checkTmE absorbCtx.translate
      ((synthIn? {} absorbCtx (psBody ps2z) absorbAnn).get absorb_compiles).deriv.translate
      ((synthIn? {} absorbCtx (psBody ps2z) absorbAnn).get absorb_compiles).ans.translate =
      true :=
  synthIn_checks_get absorbCtx_wf absorb_compiles

/-! ## Z2 and W3: `makeLogger`

The parameter is written `any`, which reads as the arrow's own binder, and the
result is `fresh`.  The written type resolves to DotMNF's `W3TyAny`, and
the typer reaches `Z2Ty`, whose witness is the parameter. -/

/-- `makeLogger`, bound by an ascription. -/
def Z2src : STm :=
  cc% (λ(l : (∀(u : ⊤) ⊤) ^ {any}).
          let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {})

example : resolveTy Λc πz.names
    (ccTy% (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {}) =
      some W3TyAny := by
  decide

example : elaboratedTm {} Λc πz Z2src = some (tmOfDeriv Z2_plat) := by decide +kernel

/-- Z2 is typed at DotMNF's judgment, from 12 units. -/
theorem Z2_type : judgAt πz Z2src =
    (some (usesOfDeriv Z2_plat, .ty (tyOfDeriv Z2_plat)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz Z2src)
  "Z2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz Z2src)
  "Z2: the target checker rejects the use set evidence"

/-- Z2 compiles. -/
theorem Z2_compiles : (compile {} Λc πz Z2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z2. -/
theorem Z2_checks : CheckerAccepts {} Λc πz Z2src Z2_compiles :=
  compile_checks_get Z2_compiles

/-! ## Z3: `mk` with a `fresh` result

S2's `mk` with the result written `fresh`.  The typer packs a payload at the
payload's own type, and the literal's precise type is not the iterator type.
So the body ascribes the literal's variable at the iterator type.  The term,
the use set and the type are DotMNF's `Z3_plat`. -/

/-- `mk` with a `fresh` result, its body ascribed. -/
def Z3src : STm :=
  cc% (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in
                 (it : μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fs})
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fresh})
             ^ {fs})

example : compiledTm Λc πz Z3src = some (tmOfDeriv Z3_plat) := by decide

/-- Z3 is typed at DotMNF's judgment, from 101 units. -/
theorem Z3_type : judgAt πz Z3src =
    (some (usesOfDeriv Z3_plat, .ty (tyOfDeriv Z3_plat)), ⟨defaultFuel - 101, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πz Z3src)
  "Z3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πz Z3src)
  "Z3: the target checker rejects the use set evidence"

/-- Z3 compiles. -/
theorem Z3_compiles : (compile {} Λc πz Z3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z3. -/
theorem Z3_checks : CheckerAccepts {} Λc πz Z3src Z3_compiles :=
  compile_checks_get Z3_compiles

/-! ## W2: `process` and its call

`W2defSrc` of `Typer.lean` writes the parameter `any`, which reads as the
arrow's own binder.  It elaborates to DotMNF's `W2Tm`.  Its least answer
has the inner closure at its own type, and `W2Ty` is reached by one `sub`.
The call `p f` is typed at DotMNF's `W2CallCtx` at the use set `{f}` and
the type `⊤`. -/

example : elaboratedTm {} Λc πc W2defSrc = some W2Tm := by decide +kernel

/-- `process` is typed with its parameter at its own capture binder, from 2
units. -/
theorem W2_type : judgAt πc W2defSrc =
    (pureAt πc (ccTy% ∀[c](x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c}) ∀(u : ⊤) ⊤),
      ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

example : topReaches {} πc (resolveTop Λc πc W2defSrc) [] (.ty W2Ty) = true := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc W2defSrc)
  "W2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc W2defSrc)
  "W2: the target checker rejects the use set evidence"

/-- `process` compiles. -/
theorem W2_compiles : (compile {} Λc πc W2defSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of `process`. -/
theorem W2_checks : CheckerAccepts {} Λc πc W2defSrc W2_compiles :=
  compile_checks_get W2_compiles

/-- The call of `process` is typed at DotMNF's judgment, from 2 units. -/
theorem W2call_type : judgIn W2CallCtx ps2c (.app (.there .here) .here) =
    (some (usesOfDeriv W2_call, .ty (tyOfDeriv W2_call)), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} W2CallCtx ps2c (.app (.there .here) .here)) ==
    (true, true))
  "the call of process: the target checker rejects the translation or the use set evidence"

/-- The call of `process` is typed at `W2CallCtx`. -/
theorem W2call_compiles :
    (synthIn? {} W2CallCtx ps2c (.app (.there .here) .here)).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the call of `process` at
the translation of `W2CallCtx`. -/
theorem W2call_checks :
    FCdot.checkTmE W2CallCtx.translate
      ((synthIn? {} W2CallCtx ps2c (.app (.there .here) .here)).get
        W2call_compiles).deriv.translate
      ((synthIn? {} W2CallCtx ps2c (.app (.there .here) .here)).get
        W2call_compiles).ans.translate = true :=
  synthIn_checks_get W2CallCtx_wf W2call_compiles

/-! ## W2 deep: `any` below a field of a domain

`deepSrc` of `Typer.lean`.  DotMNF's `W2_deep_rejected` says that the
written type is not one DotMNF reads.  The front end rejects it with that
reason, before any goal is asked. -/

/-- The typer rejects W2 deep from a full tank, with the tank unmarked. -/
theorem deep_verdict : judgAt πc deepSrc = (none, ⟨defaultFuel, false⟩) := by decide +kernel

/-- W2 deep does not compile at any budget. -/
theorem deep_rejected (b : Budget) : (compile b Λc πc deepSrc).isOk = false :=
  judgAt_rejects deep_verdict b

example : (compile {} Λc πc deepSrc).reason?.map Reason.name = some "anyNotOk" := by
  decide +kernel

/-! ## An existential answer at the top

`exTopSrc` of `Typer.lean`: a call of `freshCell` as the body of a `let`
outside every scope.  Its answer is an existential, and no root absorbs the
witness. -/

/-- The typer rejects the program after 19 units, with the tank unmarked. -/
theorem exTop_verdict : judgAt πz exTopSrc = (none, ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- The program does not compile at any budget. -/
theorem exTop_rejected (b : Budget) : (compile b Λc πz exTopSrc).isOk = false :=
  judgAt_rejects exTop_verdict b

example : topRejected {} πz exTopSrc = some "existentialAtTop" := by decide +kernel

/-! ## The existential annotations and a projection

cov2 packs a plain `let` into its existential annotation, with the payload's
own set `{f}` as witness.  cov4 writes the existential's binder below a field,
where the payload's own set is empty and is no witness, and the written bound
`{k1}` is.  cov3 is a closure that projects its parameter, charged its
receiver, which leaves with the parameter. -/

/-- cov2 is typed at its annotation, from 14 units. -/
theorem cov2_type : judgAt πc cov2Src =
    (pureAt πc (ccTy% ∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {k1})
        ∃[c ⊑ {f}] μ(y. {read : (∀(u : ⊤) ⊤) ^ {y}}) ^ {c}),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc cov2Src)
  "cov2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc cov2Src)
  "cov2: the target checker rejects the use set evidence"

/-- cov2 compiles. -/
theorem cov2_compiles : (compile {} Λc πc cov2Src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov2. -/
theorem cov2_checks : CheckerAccepts {} Λc πc cov2Src cov2_compiles :=
  compile_checks_get cov2_compiles

/-- cov4 is typed at its annotation, from 32 units. -/
theorem cov4_type : judgAt πc cov4Src =
    (pureAt πc (ccTy% ∀(p : {a : ⊤ ^ {k1}}) ∃[c ⊑ {k1}] {a : ⊤ ^ {c}}),
      ⟨defaultFuel - 32, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc cov4Src)
  "cov4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc cov4Src)
  "cov4: the target checker rejects the use set evidence"

/-- cov4 compiles. -/
theorem cov4_compiles : (compile {} Λc πc cov4Src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov4. -/
theorem cov4_checks : CheckerAccepts {} Λc πc cov4Src cov4_compiles :=
  compile_checks_get cov4_compiles

/-- cov3 is a pure closure, from 2 units. -/
theorem cov3_type : judgAt πc cov3Src =
    (pureAt πc (ccTy% ∀(o : {a : ⊤ ^ {k1}} ^ {k1}) ⊤ ^ {k1}), ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc cov3Src)
  "cov3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc cov3Src)
  "cov3: the target checker rejects the use set evidence"

/-- cov3 compiles. -/
theorem cov3_compiles : (compile {} Λc πc cov3Src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov3. -/
theorem cov3_checks : CheckerAccepts {} Λc πc cov3Src cov3_compiles :=
  compile_checks_get cov3_compiles

/-! ## A: a capture parameter that is called

`P1ann` of `Resolve.lean`, under `unit : ⊤`.  The call is charged to the
function and to the argument.  The closure is pure. -/

/-- The context of `P1ann`. -/
def P1Ctx : Ctx ([],c,c,x) := platCtx.cons unitTy

/-- `P1Ctx` is well formed. -/
theorem P1Ctx_wf : P1Ctx.Wf := ctxWf?_sound _ (by decide +kernel)

/-- The call of a capture parameter is typed at a pure closure whose domain
reads `any` as the arrow's own binder, from 4 units. -/
theorem P1_type : judgIn P1Ctx (CaptureSet.weaken πc.set) P1ann =
    (some ([], .ty ((Shape.all (arrowS ^ [CapAtom.cvar .here]) (.ty unitTy)) ^ [])),
      ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} P1Ctx (CaptureSet.weaken πc.set) P1ann) == (true, true))
  "A: the target checker rejects the translation or the use set evidence"

/-- The call of a capture parameter is typed. -/
theorem P1_compiles : (synthIn? {} P1Ctx (CaptureSet.weaken πc.set) P1ann).isOk = true := by
  decide +kernel

/-- The target checker accepts its translation. -/
theorem P1_checks :
    FCdot.checkTmE P1Ctx.translate
      ((synthIn? {} P1Ctx (CaptureSet.weaken πc.set) P1ann).get P1_compiles).deriv.translate
      ((synthIn? {} P1Ctx (CaptureSet.weaken πc.set) P1ann).get P1_compiles).ans.translate =
      true :=
  synthIn_checks_get P1Ctx_wf P1_compiles

/-! ## W1: the levels of two nested bodies

At `W1Ctx2`, the body of a lambda inside the body of another, subcapturing finds
the level steps DotMNF's `W1` derives: the outer root below the inner
one, and both parameters below the inner root.  It does not find the inner
root below the outer one.  The inner parameter is found below the outer root
by `sc-var`, since the parameter has the pure type `⊤`, and not by the level
rule, which `W1_outer_not_inner` denies. -/

example : subcapFound {} W1Ctx2 [CapAtom.cvar W1outRoot] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound {} W1Ctx2 [CapAtom.var W1outParam] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound {} W1Ctx2 [CapAtom.var W1inParam] [CapAtom.cvar W1inRoot] =
    true := by
  decide +kernel

example : subcapFound {} W1Ctx2 [CapAtom.cvar W1inRoot] [CapAtom.cvar W1outRoot] = false := by
  decide +kernel

/-! ## W5: the escape of a callback, at DotMNF's context

At `W5Ctx`, the body of a callback under an older root, subcapturing finds the
callback's parameter below its own body root, DotMNF's `W5_level_own`,
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

/-- **The certificate builder answers at W5's goal**, with the older root as
the root of the rejection.  The kernel computes the answer. -/
theorem W5_certify : certify? W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout] =
    some (.levelEscape W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout]
      (FCdot.CapAtom.cvar W5kout) W5_escape_rejected) := rfl

/-! ## The escape

`EscSrc` of `Notation.lean`: `λ(g : ⊤). let cb : A = λ(f : File ^ {any}).
λ(u : ⊤). f in cb`, where the annotation `A` reads its result `any`s as the
root of `g`'s body.  The callback is typed at its own type, bound to `cb`, and
moved to `A` by the arrow rule, which opens the callback's scope and reaches
`{f} <: {κ_g}`.  The certificate builder rejects that goal.  The goal sits in
`EscGoalCtx`, which binds `cb`.  The rejection leaves the tank unmarked, so it
holds at every budget. -/

/-- The typer rejects the escape after 31 units, with the tank unmarked. -/
theorem Esc_verdict : judgAt πc EscSrc = (none, ⟨defaultFuel - 31, false⟩) := by decide +kernel

/-- The escape does not compile at any budget. -/
theorem Esc_rejected (b : Budget) : (compile b Λc πc EscSrc).isOk = false :=
  judgAt_rejects Esc_verdict b

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

/-- **The certificate builder answers at the escape goal.**  At `EscGoalCtx`
and the goal `{f} <: {κ_g}`, `certify?` returns a rejection by a level escape
at that goal, whose root is the root of `g`'s body.  The kernel computes the
answer.  A certificate is a proof, so it is `Esc_rejected'`. -/
theorem Esc_certify : certify? EscGoalCtx [CapAtom.var .here] [CapAtom.cvar escRoot] =
    some (.levelEscape EscGoalCtx [CapAtom.var .here] [CapAtom.cvar escRoot]
      (FCdot.CapAtom.cvar escRoot) Esc_rejected') := rfl

set_option maxHeartbeats 4000000 in
/-- **The escape is rejected by a level escape.**  `compile` returns the
answer of `Esc_certify` as its rejection: the goal `{f} <: {κ_g}` in
`EscGoalCtx`, the root of `g`'s body, and the certificate. -/
theorem Esc_compile_rejected : compile {} Λc πc EscSrc =
    .rejected (.levelEscape EscGoalCtx [CapAtom.var .here] [CapAtom.cvar escRoot]
      (FCdot.CapAtom.cvar escRoot) Esc_rejected') := rfl

/-! ## The escape by an ascription

`AscEscSrc` of `Typer.lean` writes the same callback with an ascription in
place of the `let` annotation.  An ascription binds too, so the escape is
rejected at the callback's body. -/

/-- The typer rejects the escape by an ascription after 88 units, with the
tank unmarked. -/
theorem AscEsc_verdict : judgAt πc AscEscSrc = (none, ⟨defaultFuel - 88, false⟩) := by
  decide +kernel

/-- The escape by an ascription does not compile at any budget. -/
theorem AscEsc_rejected (b : Budget) : (compile b Λc πc AscEscSrc).isOk = false :=
  judgAt_rejects AscEsc_verdict b

#eval expect ((compile {} Λc πc AscEscSrc).reason?.map Reason.name == some "levelEscape")
  "the escape by an ascription: compile does not reject it"

/-- The escape by an ascription is rejected by a level escape. -/
theorem AscEsc_levelEscape :
    (compile {} Λc πc AscEscSrc).reason?.map Reason.name = some "levelEscape" := by
  decide +kernel

/-! ## The escape at the top of a program

`TopEscSrc` of `Typer.lean` binds the same callback at the top, where the
result `any` reads as the platform set and the source has no root.  The goal
is `{f} <: {fs, k2}` in `TopGoalCtx`, and the certificate's root is the
universal one, which the source cannot name. -/

/-- The typer rejects the escape at the top after 31 units, with the tank
unmarked. -/
theorem TopEsc_verdict : judgAt πc TopEscSrc = (none, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-- The escape at the top does not compile at any budget. -/
theorem TopEsc_rejected (b : Budget) : (compile b Λc πc TopEscSrc).isOk = false :=
  judgAt_rejects TopEsc_verdict b

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

set_option maxHeartbeats 4000000 in
/-- **The escape at the top is rejected by a level escape.**  `compile`
returns the rejection at the goal `{f} <: {fs, k2}` in `TopGoalCtx`, whose root
is the universal one, with the certificate `top_escape_rejected`. -/
theorem TopEsc_compile_rejected : compile {} Λc πc TopEscSrc =
    .rejected (.levelEscape TopGoalCtx [CapAtom.var .here] topPlat
      FCdot.CapAtom.top top_escape_rejected) := rfl

/-! ## A callback that keeps its capture inside its own scope

`EscOkSrc` of `Typer.lean`: the callback of the escape, annotated with its
result at its own parameter.  What it captures stays inside its own scope, so
it is accepted. -/

/-- The callback is typed at its annotation, from 4 units. -/
theorem EscOk_type : judgAt πc EscOkSrc =
    (pureAt πc (ccTy% ∀(g : ⊤) ∀[c](f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c})
        (∀(u : ⊤) μ(w. {read : (∀(u : ⊤) ⊤) ^ {w}}) ^ {f}) ^ {f}),
      ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc EscOkSrc)
  "EscOk: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc EscOkSrc)
  "EscOk: the target checker rejects the use set evidence"

/-- The callback at its own parameter compiles. -/
theorem EscOk_compiles : (compile {} Λc πc EscOkSrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem EscOk_checks : CheckerAccepts {} Λc πc EscOkSrc EscOk_compiles :=
  compile_checks_get EscOk_compiles

/-! ## PA1: a member selected through a recursive shape

`PA1src` of `Typer.lean`: `f : ∀(y : M) y.A` ascribed at `∀(y : M) {a : ⊤}`,
with `M = μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥..{a : ⊤}}))`.  The two `∀` are
compared under `y`, and the upper bound of `y.A` is read off `M` opened at
`y`, three steps down.  Scalac accepts the same program. -/

/-- PA1 is typed at the ascribed type, from 45 units. -/
theorem PA1_type : judgAt .empty PA1src =
    (pureAt .empty (ccTy% ∀(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) y.A)
        ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) {a : ⊤}),
      ⟨defaultFuel - 45, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty PA1src)
  "PA1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty PA1src)
  "PA1: the target checker rejects the use set evidence"

/-- PA1 compiles. -/
theorem PA1_compiles : (compile {} Λc .empty PA1src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of PA1. -/
theorem PA1_checks : CheckerAccepts {} Λc .empty PA1src PA1_compiles :=
  compile_checks_get PA1_compiles

/-! ## P4: a field four steps down an upper bound

`y : x.A`, and the field `a` is found by the lookup through `x.A`'s upper
bound, the recursive type opened at `y`, and the right operand twice.
Scalac accepts the same program. -/

/-- P4 is typed from 28 units. -/
theorem P4_type : judgAt .empty P4src =
    (pureAt .empty (ccTy% ∀(x : {A : ⊥ .. μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : ⊤}))}) ∀(y : x.A) ⊤),
      ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty P4src)
  "P4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty P4src)
  "P4: the target checker rejects the use set evidence"

/-- P4 compiles. -/
theorem P4_compiles : (compile {} Λc .empty P4src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of P4. -/
theorem P4_checks : CheckerAccepts {} Λc .empty P4src P4_compiles :=
  compile_checks_get P4_compiles

/-! ## P5: the second of two function types

`f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)` applied to `y : ⊤`.  The application
tries every function type the lookup finds, and the second accepts the
argument.  Scalac accepts the same program. -/

/-- P5 is typed from 13 units. -/
theorem P5_type : judgAt .empty P5src =
    (pureAt .empty (ccTy% ∀(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)) ∀(y : ⊤) ⊤),
      ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty P5src)
  "P5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty P5src)
  "P5: the target checker rejects the use set evidence"

/-- P5 compiles. -/
theorem P5_compiles : (compile {} Λc .empty P5src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of P5. -/
theorem P5_checks : CheckerAccepts {} Λc .empty P5src P5_compiles :=
  compile_checks_get P5_compiles

/-! ## R1 to R4: the field that lets the rest of the program type

In each program a projection finds two fields of one name, and only the
second has the member the rest of the program needs.  In R1 the first field
is found through `x.A`'s upper bound.  In R2 both are written.  R3 checks the
projection at an ascription, and R4 binds it under a written `let` type.
The typer keeps every candidate, so each compiles.  Scalac accepts R1 and
R2. -/

/-- R1 is typed from 17 units. -/
theorem R1_type : judgAt .empty R1src =
    (pureAt .empty (ccTy% ∀(x : {A : ⊥ .. {a : ⊤}}) ∀(y : x.A ∧ {a : {b : ⊤}}) ⊤),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R1src)
  "R1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty R1src)
  "R1: the target checker rejects the use set evidence"

/-- R1 compiles. -/
theorem R1_compiles : (compile {} Λc .empty R1src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R1. -/
theorem R1_checks : CheckerAccepts {} Λc .empty R1src R1_compiles :=
  compile_checks_get R1_compiles

/-- R2 is typed from 10 units. -/
theorem R2_type : judgAt .empty R2src =
    (pureAt .empty (ccTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) ⊤), ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R2src)
  "R2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty R2src)
  "R2: the target checker rejects the use set evidence"

/-- R2 compiles. -/
theorem R2_compiles : (compile {} Λc .empty R2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R2. -/
theorem R2_checks : CheckerAccepts {} Λc .empty R2src R2_compiles :=
  compile_checks_get R2_compiles

/-- R3 is typed at the ascribed field, from 11 units. -/
theorem R3_type : judgAt .empty R3src =
    (pureAt .empty (ccTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) {b : ⊤}),
      ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R3src)
  "R3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty R3src)
  "R3: the target checker rejects the use set evidence"

/-- R3 compiles. -/
theorem R3_compiles : (compile {} Λc .empty R3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R3. -/
theorem R3_checks : CheckerAccepts {} Λc .empty R3src R3_compiles :=
  compile_checks_get R3_compiles

/-- R4 is typed from 9 units. -/
theorem R4_type : judgAt .empty R4src =
    (pureAt .empty (ccTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) ⊤), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R4src)
  "R4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty R4src)
  "R4: the target checker rejects the use set evidence"

/-- R4 compiles. -/
theorem R4_compiles : (compile {} Λc .empty R4src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R4. -/
theorem R4_checks : CheckerAccepts {} Λc .empty R4src R4_compiles :=
  compile_checks_get R4_compiles

/-! ## Alias chains

`x0 : {A : ⊥..⊤}` and `xk : {A : x(k-1).A..x(k-1).A}` for `k = 1..n`, then
`y : xn.A` ascribed at `x0.A`.  The goal `xn.A <: x0.A` passes the lower bound
of every link, one goal per link, so the work grows with the length.  The
program and its type are built by structural recursion on the number of
links. -/

/-- `x` followed by a number. -/
def xName (i : Nat) : String := "x" ++ toString i

/-- `{A : xi.A..xi.A}`, the declared shape of the link after `xi`. -/
def linkShape (i : Nat) : SShape := .typ "A" (.sel (xName i) "A") (.sel (xName i) "A")

/-- The last `j` links of a chain of `n`, then `λ(y : xn.A). (y : x0.A)`. -/
def chainLams (n : Nat) : Nat → STm
  | 0 => .lam none "y" (.capt (.sel (xName n) "A") [])
      (.asc (.var "y") (.capt (.sel (xName 0) "A") []))
  | j + 1 => .lam none (xName (n - j)) (.capt (linkShape (n - j - 1)) []) (chainLams n j)
termination_by structural j => j

/-- The type of `chainLams n j`. -/
def chainAlls (n : Nat) : Nat → SType
  | 0 => .capt (.all none "y" (.capt (.sel (xName n) "A") [])
      (.ty (.capt (.sel (xName 0) "A") []))) []
  | j + 1 => .capt (.all none (xName (n - j)) (.capt (linkShape (n - j - 1)) [])
      (.ty (chainAlls n j))) []
termination_by structural j => j

/-- The alias chain of `n` links as a program. -/
def chainSrc (n : Nat) : STm := .lam none (xName 0) (.capt (.typ "A" .bot .top) []) (chainLams n n)

/-- The type the program `chainSrc n` writes. -/
def chainSTy (n : Nat) : SType :=
  .capt (.all none (xName 0) (.capt (.typ "A" .bot .top) []) (.ty (chainAlls n n))) []

/-- The chain of sixteen links is typed at its written type, from 203 units. -/
theorem chain16_type : judgAt .empty (chainSrc 16) =
    (pureAt .empty (chainSTy 16), ⟨defaultFuel - 203, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty (chainSrc 16))
  "the chain of sixteen links: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty (chainSrc 16))
  "the chain of sixteen links: the target checker rejects the use set evidence"

/-- The chain of sixteen links compiles. -/
theorem chain16_compiles : (compile {} Λc .empty (chainSrc 16)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem chain16_checks : CheckerAccepts {} Λc .empty (chainSrc 16) chain16_compiles :=
  compile_checks_get chain16_compiles

/-- The chain of thirty two links is typed at its written type, from 659
units. -/
theorem chain32_type : judgAt .empty (chainSrc 32) =
    (pureAt .empty (chainSTy 32), ⟨defaultFuel - 659, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty (chainSrc 32))
  "the chain of thirty two links: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty (chainSrc 32))
  "the chain of thirty two links: the target checker rejects the use set evidence"

/-- The chain of thirty two links compiles. -/
theorem chain32_compiles : (compile {} Λc .empty (chainSrc 32)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem chain32_checks : CheckerAccepts {} Λc .empty (chainSrc 32) chain32_compiles :=
  compile_checks_get chain32_compiles

/-! ## B1: a field through a middle the program does not write

`B1src` of `Typer.lean`: `n : {a : ⊤}`, `n.b` through
`x : {A : {a : ⊤}..{b : ⊤}}`.  The field `b` needs `n` below `x.A` and `x.A`
below `{b : ⊤}`, a middle the program does not write.  The lookup finds no
field `b` in `{a : ⊤}`, so no goal of the core is asked.  The judgment that
would give `n` the field, `n : {b : ⊤}`, has no `Alg` derivation. -/

/-- The body of the inner lambda: `x`, then `n : {a : ⊤}`. -/
def B1nCtx : Ctx (Sig.body (Sig.body ([] : Sig))) :=
  Ctx.body (Ctx.body .nil ((Shape.typ lA (.fld la unitTy) (.fld lb unitTy)) ^ []))
    ((Shape.fld la unitTy) ^ [])

/-- The typer rejects B1 after 2 units, with the tank unmarked. -/
theorem B1_verdict : judgAt .empty B1src = (none, ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- B1 does not compile at any budget. -/
theorem B1_rejected (b : Budget) : (compile b Λc .empty B1src).isOk = false :=
  judgAt_rejects B1_verdict b

/-- `n : {b : ⊤}` has no `Alg` derivation. -/
theorem B1_not_alg :
    ¬ Alg ⟨_, B1nCtx, .var .here ((Shape.fld la unitTy) ^ []) ((Shape.fld lb unitTy) ^ [])⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? B1nCtx .here ((Shape.fld lb unitTy) ^ [])) 5 = true))
  have hv : (varView B1nCtx .here).ty = (Shape.fld la unitTy) ^ [] := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## A1: a written `let` annotation the bound value does not meet

`A1src` of `Typer.lean`: `λ(x : ⊤). let y : {a : ⊤} = x in y`.  The
annotation binds, so the body `y` is checked against `{a : ⊤}`, and `y` has
the type `⊤` of `x`.  Scalac rejects the same program. -/

/-- The body of the lambda, then the `let` binder `y : ⊤`. -/
def A1yCtx : Ctx (Sig.body ([] : Sig),x) := (Ctx.body .nil unitTy).cons unitTy

/-- The typer rejects A1 after 11 units, with the tank unmarked. -/
theorem A1_verdict : judgAt .empty A1src = (none, ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-- A1 does not compile at any budget. -/
theorem A1_rejected (b : Budget) : (compile b Λc .empty A1src).isOk = false :=
  judgAt_rejects A1_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem A1_not_alg : ¬ Alg ⟨_, A1yCtx, .var .here unitTy ((Shape.fld la unitTy) ^ [])⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? A1yCtx .here ((Shape.fld la unitTy) ^ [])) 5 = true))
  have hv : (varView A1yCtx .here).ty = unitTy := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## BX2 and BX: box adaptation by the box status

`y` has the avoided type `□((∀(u : ⊤) ⊤) ^ {f}) ^ {}`, and the goal is a box
too: the domain `□(⊤ ^ {})` of `h` in BX2, an ascription in BX.  Both
statuses are boxed, so `y` is unboxed first, which fails, and then boxed,
which succeeds. -/

/-- BX2 is typed from 34 units.  The inner closure captures `f`. -/
theorem BX2_type : judgAt πc BX2src =
    (pureAt πc (ccTy% ∀(f : (∀(u : ⊤) ⊤) ^ {k1}) (∀(h : (∀(v : □(⊤ ^ {})) ⊤) ^ {}) ⊤) ^ {f}),
      ⟨defaultFuel - 34, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc BX2src)
  "BX2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc BX2src)
  "BX2: the target checker rejects the use set evidence"

/-- BX2 compiles. -/
theorem BX2_compiles : (compile {} Λc πc BX2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of BX2. -/
theorem BX2_checks : CheckerAccepts {} Λc πc BX2src BX2_compiles :=
  compile_checks_get BX2_compiles

/-- BX is typed at the ascribed box, from 29 units. -/
theorem BX_type : judgAt πc BXsrc =
    (pureAt πc (ccTy% ∀(f : (∀(u : ⊤) ⊤) ^ {k1}) □(⊤ ^ {})), ⟨defaultFuel - 29, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc BXsrc)
  "BX: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc BXsrc)
  "BX: the target checker rejects the use set evidence"

/-- BX compiles. -/
theorem BX_compiles : (compile {} Λc πc BXsrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of BX. -/
theorem BX_checks : CheckerAccepts {} Λc πc BXsrc BX_compiles :=
  compile_checks_get BX_compiles

/-! ## LP and PF: the recursion limit

LP checks `x : p.A` against `q.B`, through `∀` bodies, and reaches the same
goal under one more binder at every level.  PF is Pierce's divergence of
F<:.  Its goal comes back under a new binder that it names, so no cut ends
it.
Each run ends with the tank marked, the compiler's recursion limit.  Scalac
rejects LP at the declaration of its cyclic members, a check outside
subtyping. -/

/-- LP ends with the tank marked after 32737 units. -/
theorem LP_limit : judgAt .empty LPsrc = (none, ⟨defaultFuel - 32737, true⟩) := by
  decide +kernel

/-- PF ends with the tank marked after 32693 units. -/
theorem PF_limit : judgAt .empty PFsrc = (none, ⟨defaultFuel - 32693, true⟩) := by
  decide +kernel

/-! ## The effect theorem

`compile_effect_safety_get` at C2, for a run of DotMNF's term from the
platform's initial store and a variable `x` the reached state reads.  The
capability is `k1`.  The premise, that the use set the typer found does not
hold `k1`, is decided by the kernel.  The elaborated term equals DotMNF's
term, so the run transfers. -/

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, at a state that reads `x`, there is a typed target state with
the same erasure that the run of the translated derivation reaches, and in it
`x` is not rooted at `k1`. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc C2src).get C2_compiles).2.deriv.translate⟩ :
          FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile {} Λc πc C2src).get C2_compiles).2.tm.erase = C2tm := by
    decide +kernel
  exact compile_effect_safety_get C2_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-! ## The effect theorem at a variable declared at a platform capability

In C2 no variable the run reads is declared at a set that names `k1` or `k2`.
`ReadK2Src` binds `a` at `{k1}` and `f` at `{k2}`, by ascriptions, and calls
`f` on itself.  The typer boxes the argument, since `f` is tracked.  The run
reads `f`, never `a`.  The use set the typer finds is `{k2}`, so
`compile_effect_safety_get` applies at `k1`: the variable the run reads, which
is declared at `{k2}`, is not rooted at `k1`. -/

/-- `a` at `{k1}`, `f` at `{k2}`, then `f f`. -/
def ReadK2Src : STm :=
  cc% let a = ((λ(u : ⊤). u) : (∀(u : ⊤) ⊤) ^ {k1}) in
      let f = ((λ(u : ⊤). u) : (∀(u : ⊤) ⊤) ^ {k2}) in
      f f

/-- The term `a` is bound to. -/
def ReadK2aSrc : STm := cc% ((λ(u : ⊤). u) : (∀(u : ⊤) ⊤) ^ {k1})

/-- The term `f` is bound to. -/
def ReadK2fSrc : STm := cc% ((λ(u : ⊤). u) : (∀(u : ⊤) ⊤) ^ {k2})

/-- The capture set of the type the typer finds for a closed term, if it
finds a plain type. -/
def judgSet? (e : STm) : Option (CaptureSet πc.sig) :=
  match (judgAt πc e).1 with
  | some (_, .ty T) => some T.captureSet
  | _ => none

/-- The typer types the term bound to `a` at a set `{k1}`. -/
theorem ReadK2a_set : judgSet? ReadK2aSrc = some [CapAtom.cvar k1] := by decide +kernel

/-- The typer types the term bound to `f` at a set `{k2}`. -/
theorem ReadK2f_set : judgSet? ReadK2fSrc = some [CapAtom.cvar k2] := by decide +kernel

theorem ReadK2_compiles : (compile {} Λc πc ReadK2Src).isOk = true := by decide +kernel

/-- The use set is `{k2}`: the program uses `f`, and not `a`. -/
theorem ReadK2_uses :
    ((compile {} Λc πc ReadK2Src).get ReadK2_compiles).2.use = [CapAtom.cvar k2] := by
  decide +kernel

/-- The compiled term: `a`, `f`, the box of `f`, and the call. -/
example : ppTmWith Λc (namesOver ["k1", "k2"] _)
    ((compile {} Λc πc ReadK2Src).get ReadK2_compiles).2.tm.erase =
      "let x = λ(x : ⊤). x in let y = λ(y : ⊤). y in let z = □ y in y z" := by
  decide +kernel

/-- After six steps the run calls `x3`, the closure bound to `f`.  The store
holds `x2`, the closure bound to `a`, which the run does not read. -/
example : ppRunOver Λc ["k1", "k2"] (compileAndRun {} 6 Λc πc ReadK2Src) =
    "⟨k1, k2, x2 = λ(x : ⊤). x, x3 = λ(x : ⊤). x, x4 = □ x3 | · | x3 x4⟩" := by
  decide +kernel

/-- The state after six steps reads a variable. -/
theorem ReadK2_reads6 :
    ((run 6 πc.sig ⟨πc.plat.store, .nil,
      ((compile {} Λc πc ReadK2Src).get ReadK2_compiles).2.tm.erase⟩).2.inspects).isSome =
      true := by
  decide +kernel

/-- **`ReadK2Src` never reads `k1`.**  Along any run of the compiled term
from the platform's initial store, at a state that reads `x`, there is a typed
target state with the same erasure that the run of the translated derivation
reaches, and in it `x` is not rooted at `k1`. -/
theorem ReadK2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil,
      ((compile {} Λc πc ReadK2Src).get ReadK2_compiles).2.tm.erase⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc ReadK2Src).get ReadK2_compiles).2.deriv.translate⟩ :
          FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] :=
  compile_effect_safety_get ReadK2_compiles (κ := k1) (by decide +kernel) r hin

/-- The instance at the state that calls `f`, six steps in. -/
example := ReadK2_never_reads_k1 (run_steps 6 _) (Option.some_get ReadK2_reads6).symm

/-! ## The log of a compiled program

`compile_lvl_safety` speaks of each entry of the log `levelSteps` reads off the
derivation.  C2 has 121 entries and S1 has 92. -/

example : (compileLog {} Λc πc C2src).length = 121 := by decide +kernel

example : (compileLog {} Λc πz S1progSrc).length = 92 := by decide +kernel

/-! ## Level safety at two entries

`compile_lvl_safety_get` is applied to two entries `lo <: hi` and a root `ρ`
of the entry's context.  In both, `lo` as written is not confined to `ρ`, so
the conclusion, that the resolution of `lo` is confined to `ρ`, is not read
off `lo`.

Entry 6 of the log of C7 has `hi` a platform capability.  It is confined to
every capture binder of the entry's context, so the premise holds at every
root.

The first entry of the log of `CallbackSrc` separates the roots.  The program is
`λ(g : ⊤). λ(f : ⊤ ^ {any}). let h = ((λ(u : ⊤ ^ {f}). u) : A) in f`, where
the ascription `A` reads its `any`s as the root of `f`'s body.  The entry is
`{u} <: {κ_f}` under the scope of `u`, with `κ_f` that root.  The premise
holds at `κ_f`, and fails at the root of `g`'s body, which is older.  The
parameter `u` lives inside the scope of `u`, so it is not confined to `κ_f` as
written.  It resolves through `f` to the capture binder of `f`, which is. -/

/-- The capture binders of a signature, newest first. -/
def capVars : (s : Sig) → List (BVar s .cap)
  | [] => []
  | .cap :: s => .here :: (capVars s).map .there
  | .var :: s => (capVars s).map .there

/-- The capture binder at de Bruijn depth `d`, as an atom, or the universal
root when there is none. -/
def cvarAt (s : Sig) (d : Nat) : FCdot.CapAtom s :=
  match (capVars s).find? (fun κ => κ.depth == d) with
  | some κ => .cvar κ
  | none => .top

theorem C7_log_drop : (compileLog {} Λc πc C7src).drop 6 ≠ [] := by decide +kernel

/-- Entry 6 of the log of C7. -/
def C7entry : LevelStep := ((compileLog {} Λc πc C7src).drop 6).head C7_log_drop

theorem C7entry_mem : C7entry ∈ compileLog {} Λc πc C7src :=
  List.mem_of_mem_drop (List.head_mem _)

/-- The root the entry is read against: the capture binder at depth 7. -/
def C7root : FCdot.CapAtom C7entry.sig := cvarAt C7entry.sig 7

/-- It is a scope root, not the universal one. -/
theorem C7root_isRoot : C7entry.ctx.translate.IsRoot C7root ∧ C7root ≠ .top := by
  decide +kernel

/-- `hi` is confined to every capture binder of the context. -/
theorem C7entry_hi_all :
    ∀ κ ∈ capVars C7entry.sig, C7entry.ctx.translate.Confined C7entry.hi.translate (.cvar κ) := by
  decide +kernel

/-- `lo` as written is not confined to the root. -/
theorem C7entry_lo_not : ¬ C7entry.ctx.translate.Confined C7entry.lo.translate C7root := by
  decide +kernel

/-- The premise, at every depth. -/
theorem C7entry_premise :
    ∀ m, C7entry.ctx.translate.Confined
      (C7entry.ctx.translate.caps m C7entry.hi.translate) C7root := by
  intro m
  rw [caps_self _ (by decide +kernel) m]
  decide +kernel

/-- **Level safety at entry 6 of C7.** -/
theorem C7entry_lvl :
    ∀ n, C7entry.ctx.translate.Confined
      (C7entry.ctx.translate.caps n C7entry.lo.translate) C7root :=
  compile_lvl_safety_get C7_compiles C7entry C7entry_mem C7root C7entry_premise

/-- A callback ascribed at the root of an inner scope. -/
def CallbackSrc : STm :=
  cc% λ(g : ⊤). λ(f : ⊤ ^ {any}).
        let h = ((λ(u : ⊤ ^ {f}). u) : (∀(u : ⊤ ^ {f}) ⊤ ^ {any}) ^ {any}) in f

theorem Callback_compiles : (compile {} Λc πc CallbackSrc).isOk = true := by decide +kernel

theorem Callback_log_ne : compileLog {} Λc πc CallbackSrc ≠ [] := by decide +kernel

/-- The first entry of the log of `CallbackSrc`. -/
def CallbackEntry : LevelStep := (compileLog {} Λc πc CallbackSrc).head Callback_log_ne

theorem CallbackEntry_mem : CallbackEntry ∈ compileLog {} Λc πc CallbackSrc := List.head_mem _

/-- `lo` is the parameter `u` and `hi` is the root of `f`'s body, each a
single atom. -/
example : CallbackEntry.lo.length = 1 ∧ CallbackEntry.hi.length = 1 ∧
    CallbackEntry.hi.translate = [cvarAt CallbackEntry.sig 5] := by
  decide +kernel

/-- The root of `f`'s body, at depth 5. -/
def CallbackRoot : FCdot.CapAtom CallbackEntry.sig := cvarAt CallbackEntry.sig 5

/-- The root of `g`'s body, at depth 8. -/
def CallbackOuter : FCdot.CapAtom CallbackEntry.sig := cvarAt CallbackEntry.sig 8

/-- Both are scope roots, and neither is the universal one. -/
theorem Callback_roots :
    CallbackEntry.ctx.translate.IsRoot CallbackRoot ∧ CallbackRoot ≠ .top ∧
      CallbackEntry.ctx.translate.IsRoot CallbackOuter ∧ CallbackOuter ≠ .top := by
  decide +kernel

/-- The premise at the root of `f`'s body, at every depth. -/
theorem CallbackEntry_premise :
    ∀ m, CallbackEntry.ctx.translate.Confined
      (CallbackEntry.ctx.translate.caps m CallbackEntry.hi.translate) CallbackRoot := by
  intro m
  rw [caps_self _ (by decide +kernel) m]
  decide +kernel

/-- The premise fails at the root of `g`'s body. -/
theorem CallbackEntry_separates :
    ¬ ∀ m, CallbackEntry.ctx.translate.Confined
      (CallbackEntry.ctx.translate.caps m CallbackEntry.hi.translate) CallbackOuter := by
  intro h
  have h0 := h 0
  rw [← capsS_eq] at h0
  revert h0
  decide +kernel

/-- `lo` as written is not confined to the root of `f`'s body. -/
theorem CallbackEntry_lo_not :
    ¬ CallbackEntry.ctx.translate.Confined CallbackEntry.lo.translate CallbackRoot := by
  decide +kernel

/-- **Level safety at the first entry of `CallbackSrc`.** -/
theorem CallbackEntry_lvl :
    ∀ n, CallbackEntry.ctx.translate.Confined
      (CallbackEntry.ctx.translate.caps n CallbackEntry.lo.translate) CallbackRoot :=
  compile_lvl_safety_get Callback_compiles CallbackEntry CallbackEntry_mem CallbackRoot CallbackEntry_premise

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

#eval ppRunOver Λc ["fs", "k2"] (compileAndRun {} runBudget Λc πz S2src)

example : ppRunTmOver Λc ["fs", "k2"] (compileAndRun {} runBudget Λc πz S2src) = "x3" := by
  decide +kernel

example : (runFinal? {} 15 πz S2src && ! runFinal? {} 14 πz S2src) = true := by
  decide +kernel

#eval ppRunOver Λc ["k1", "k2"] (compileAndRun {} runBudget Λc πc C2src)

example : ppRunTmOver Λc ["k1", "k2"] (compileAndRun {} runBudget Λc πc C2src) = "x6" := by
  decide +kernel

example : (runFinal? {} 12 πc C2src && ! runFinal? {} 11 πc C2src) = true := by
  decide +kernel

#eval ppRun Λc (compileAndRun {} runBudget Λc .empty E2src)

example : ppRunTm Λc (compileAndRun {} runBudget Λc .empty E2src) = "x1" := by
  decide +kernel

example : (runFinal? {} 6 .empty E2src && ! runFinal? {} 5 .empty E2src) = true := by
  decide +kernel

end Examples

/-! ## Annotations erased

Each program below is written with every slot, then erased in five ways.  `D`
erases every lambda domain, `S` every self shape, and `A` the domain of every
lambda passed as an argument.  `C` erases the domain of every lambda in a
checked position, where the typer passes a goal: directly under an ascription,
an argument, the bound term of `let x : A = t in x`, the body of a `let` with a
written answer, a field of a literal whose self shape is written, and the body
of a lambda or a block in such a position.  `G` is `C` with every self shape
erased too.  `G` is the program a Scala programmer writes where an expected
type reaches.  The erasures act on the surface program, so `compile` applies
to the result, and each agrees with the erasure of the same name on the
resolved term (`Erasure.agrees`).

A cell is the verdict of `compileE` on an erased program at `defaultFuel`,
with the tank the elaborator leaves.  An erasure that changes nothing is
`noSlot`, whose verdict is the written one by `compile_full`.  A program that
compiles does so at the written term (`same`) or at another fill (`other`),
with its type.  The fill is the one `compile` returns.  A fill that fails the
agreement or the skeleton test of `compileE` is `shape`, and `compileE`
reports a mismatch there.  A rejected program has
its reason, with the typer's own reason named.  When the elaborator finds no
candidate and no reason of its own, the reason is the typer's verdict on the
fill, as `compileE` reports it.  The first cell of a row is the written
program itself.

A cell whose reason search reaches the certificate builder of a level escape
is one the kernel does not evaluate, since the builder reads the well-founded
`Ctx.caps`.  These are the escapes and CapPure.  Their rows are checked by
`#eval expect`, and their other cells by the kernel. -/

section Erasures

mutual
/-- Every lambda domain erased. -/
def STm.eraseDoms (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam κ x _ t => .lam κ x none (STm.eraseDoms t)
  | .obj x S d => .obj x S (SDefs.eraseDoms d)
  | .app t u => .app (STm.eraseDoms t) (STm.eraseDoms u)
  | .proj t a => .proj (STm.eraseDoms t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseDoms t) (STm.eraseDoms u)
  | .letex κ x t u => .letex κ x (STm.eraseDoms t) (STm.eraseDoms u)
  | .box t => .box (STm.eraseDoms t)
  | .unbox C t => .unbox C (STm.eraseDoms t)
  | .asc t T => .asc (STm.eraseDoms t) T
termination_by structural e
/-- Every lambda domain erased, in definitions. -/
def SDefs.eraseDoms (d : SDefs) : SDefs :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a T t => .trm a T (STm.eraseDoms t)
  | .and d e => .and (SDefs.eraseDoms d) (SDefs.eraseDoms e)
termination_by structural d
end

mutual
/-- Every self shape erased. -/
def STm.eraseSelf (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam κ x T t => .lam κ x T (STm.eraseSelf t)
  | .obj x _ d => .obj x none (SDefs.eraseSelf d)
  | .app t u => .app (STm.eraseSelf t) (STm.eraseSelf u)
  | .proj t a => .proj (STm.eraseSelf t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseSelf t) (STm.eraseSelf u)
  | .letex κ x t u => .letex κ x (STm.eraseSelf t) (STm.eraseSelf u)
  | .box t => .box (STm.eraseSelf t)
  | .unbox C t => .unbox C (STm.eraseSelf t)
  | .asc t T => .asc (STm.eraseSelf t) T
termination_by structural e
/-- Every self shape erased, in definitions. -/
def SDefs.eraseSelf (d : SDefs) : SDefs :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a T t => .trm a T (STm.eraseSelf t)
  | .and d e => .and (SDefs.eraseSelf d) (SDefs.eraseSelf e)
termination_by structural d
end

/-- A lambda's domain erased, at the head only. -/
def STm.dropDom : STm → STm
  | .lam κ x _ t => .lam κ x none t
  | e => e

mutual
/-- The domain of every lambda passed as an argument erased.  The resolver
binds such a lambda by an `arg` binding. -/
def STm.eraseArgs (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam κ x T t => .lam κ x T (STm.eraseArgs t)
  | .obj x S d => .obj x S (SDefs.eraseArgs d)
  | .app t u => .app (STm.eraseArgs t) (STm.dropDom (STm.eraseArgs u))
  | .proj t a => .proj (STm.eraseArgs t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseArgs t) (STm.eraseArgs u)
  | .letex κ x t u => .letex κ x (STm.eraseArgs t) (STm.eraseArgs u)
  | .box t => .box (STm.eraseArgs t)
  | .unbox C t => .unbox C (STm.eraseArgs t)
  | .asc t T => .asc (STm.eraseArgs t) T
termination_by structural e
/-- The domain of every lambda passed as an argument erased, in definitions. -/
def SDefs.eraseArgs (d : SDefs) : SDefs :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a T t => .trm a T (STm.eraseArgs t)
  | .and d e => .and (SDefs.eraseArgs d) (SDefs.eraseArgs e)
termination_by structural d
end

mutual
/-- The domain of every lambda in a checked position erased, and with `fS`
every self shape too.  A position is checked when the typer passes it a goal:
directly under an ascription, an argument of an application, the bound term
of `let x : A = t in x`, the body of a `let` with a written answer, a field of
a literal whose self shape is written, and the body of a lambda or a block in
a checked position.  `chk` says whether the term itself sits in one. -/
def STm.eraseChecked (fS chk : Bool) (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam κ x T t => .lam κ x (if chk then none else T) (STm.eraseChecked fS chk t)
  | .obj x S d => .obj x (if fS then none else S) (SDefs.eraseChecked fS (!fS && S.isSome) d)
  | .app t u => .app (STm.eraseChecked fS false t) (STm.eraseChecked fS true u)
  | .proj t a => .proj (STm.eraseChecked fS false t) a
  | .«let» x ann t u =>
      .«let» x ann (STm.eraseChecked fS (ann.isSome && decide (u = .var x)) t)
        (STm.eraseChecked fS (chk || ann.isSome) u)
  | .letex κ x t u => .letex κ x (STm.eraseChecked fS false t) (STm.eraseChecked fS chk u)
  | .box t => .box (STm.eraseChecked fS false t)
  | .unbox C t => .unbox C (STm.eraseChecked fS false t)
  | .asc t T => .asc (STm.eraseChecked fS true t) T
termination_by structural e
/-- The domain of every lambda in a checked position erased, in
definitions. -/
def SDefs.eraseChecked (fS chk : Bool) (d : SDefs) : SDefs :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a T t => .trm a T (STm.eraseChecked fS chk t)
  | .and d e => .and (SDefs.eraseChecked fS chk d) (SDefs.eraseChecked fS chk e)
termination_by structural d
end

/-- The five erasures of the tables. -/
inductive Erasure where
  /-- Every lambda domain. -/
  | D
  /-- Every self shape. -/
  | S
  /-- The domain of every lambda passed as an argument. -/
  | A
  /-- The domain of every lambda in a checked position. -/
  | C
  /-- Every self shape, and the domain of every lambda in a checked
  position. -/
  | G
deriving DecidableEq

/-- An erasure on the surface program. -/
def Erasure.surface : Erasure → STm → STm
  | .D, e => STm.eraseDoms e
  | .S, e => STm.eraseSelf e
  | .A, e => STm.eraseArgs e
  | .C, e => STm.eraseChecked false false e
  | .G, e => STm.eraseChecked true false e

/-- The same erasure on the resolved term. -/
def Erasure.resolved {s : Sig} : Erasure → PTm s → PTm s
  | .D, p => p.eraseDoms
  | .S, p => p.eraseSelf
  | .A, p => p.eraseArgs
  | .C, p => p.eraseChecked false false
  | .G, p => p.eraseG

/-- The erased surface program resolves to the resolved program erased. -/
def Erasure.agrees (k : Erasure) (π : PlatformNames) (e : STm) : Bool :=
  decide (resolvePTop Λc π (k.surface e) = (resolvePTop Λc π e).map k.resolved)

/-- A reason with the typer's own reason replaced by its name. -/
abbrev RView := Frontend.Reason.Reason Label String

/-- The verdict on one erased program. -/
inductive Cell (s : Sig) where
  /-- The erasure changes nothing. -/
  | noSlot
  /-- Compiled at the written term, with its type and the tank left. -/
  | same (T : Ty s) (t : Tank)
  /-- Compiled at another fill, with its type and the tank left. -/
  | other (T : Ty s) (t : Tank)
  /-- Rejected, with the reason and the tank left. -/
  | no (r : RView) (t : Tank)
  /-- The erased program is not the written one with some slots empty, or
  its fill does not agree with it. -/
  | shape
deriving DecidableEq

/-- The elaborator's verdict on a resolved program `p` at `defaultFuel`, read
as `compileE` reads it.  `a?` is the written term, when there is one: a fill
equal to it is `same`, any other fill `other`. -/
def cellOf (π : PlatformNames) (p : PTm π.sig) (a? : Option (ATm π.sig)) : Cell π.sig :=
  match elabTopF defaultFuel π p with
  | (.ok c, t) =>
      match c.e.split with
      | .inl q =>
          if p.fills c.fill = true ∧ ATm.skel q.tm = ATm.skel c.fill then
            if some c.fill = a? then .same q.ty t else .other q.ty t
          else .shape
      | .inr q => .no (EReason.view (.landed (existentialAt π.plat.ctx q))) t
  | (.error .mismatch, t) => .no (fillReason {} π p).view t
  | (.error r, t) => .no r.view t

/-- The verdict on `e`, the written program `w` with some slots empty.
`PTm.fills` checks that `e` is such a program. -/
def erasedCell (π : PlatformNames) (w e : STm) : Cell π.sig :=
  match resolveTop Λc π w, resolvePTop Λc π e with
  | some a, some p => if p.fills a then cellOf π p (some a) else .shape
  | _, _ => .shape

/-- The verdict on a program with no written form. -/
def openCell (π : PlatformNames) (e : STm) : Cell π.sig :=
  match resolvePTop Λc π e with
  | some p => cellOf π p none
  | none => .shape

/-- The verdict on the program `w` erased by `k`. -/
def cell (k : Erasure) (π : PlatformNames) (w : STm) : Cell π.sig :=
  if k.surface w = w then .noSlot else erasedCell π w (k.surface w)

/-- A row of the table: the written program, then its five erasures. -/
def row (π : PlatformNames) (w : STm) : List (Cell π.sig) :=
  [erasedCell π w w, cell .D π w, cell .S π w, cell .A π w, cell .C π w, cell .G π w]

/-- The written program, then another erasure of it. -/
def pair (π : PlatformNames) (w e : STm) : List (Cell π.sig) :=
  [erasedCell π w w, erasedCell π w e]

/-- The type the typer gives a written program, `⊤` when it gives no plain
type. -/
def tyOf (π : PlatformNames) (w : STm) : Ty π.sig :=
  match (judgAt π w).1 with
  | some (_, .ty T) => T
  | _ => Shape.top ^ []


/-- The tank left after `n` units of `defaultFuel`, unmarked. -/
def spent (n : Nat) : Tank := ⟨defaultFuel - n, false⟩

/-- The tank left after `n` units of `defaultFuel`, marked. -/
def marked (n : Nat) : Tank := ⟨defaultFuel - n, true⟩

/-- A missing parameter type after `n` units. -/
def missing {s : Sig} (n : Nat) : Cell s := .no (.missingParamType none) (spent n)

/-- The written verdict, a missing parameter type under `D` from a full tank,
and no slot for the other erasures: a program whose outermost term is a
lambda, with no self shape and no domain in a checked position. -/
abbrev LambdaRow (π : PlatformNames) (w : STm) (c : Cell π.sig) : Prop :=
  row π w = [c, missing 0, .noSlot, .noSlot, .noSlot, .noSlot]


/-! ### What a cell says about `compile`

A cell is computed from `elabTopF` and the fill, as `compileE` is, so a cell
fact is a fact about `compile`.  A rejection that ends unmarked is a rejection
at every budget, by `elabTop?_stable` above `defaultFuel` and `elabTop?_mono`
below it.  The reason is the one `compileE` reports at the default budget.  A
reason of inference comes from the elaborator alone, so it is also the reason
at every budget from `defaultFuel` up.  A reason of the typer may come from
the fill of a failed elaboration, whose own tank no theorem follows. -/

/-- The reason of a result, with the typer's own reason replaced by its
name. -/
def errView {α : Type} : Except EReason α → Option RView
  | .ok _ => none
  | .error r => some r.view

/-- The reason `compileE` reports at the budget `b`, if it reports one. -/
def reasonAt (b : Budget) (π : PlatformNames) (e : STm) : Option RView :=
  errView (compileE b Λc π e)

/-- A program rejected at every budget, with the reason `compileE` reports
at the default budget. -/
def RejectedWith (π : PlatformNames) (e : STm) (r : RView) : Prop :=
  (∀ b, (compile b Λc π e).isOk = false) ∧ reasonAt {} π e = some r

/-- A program rejected at every budget, with the same reason at every budget
from `defaultFuel` up. -/
def RejectedAbove (π : PlatformNames) (e : STm) (r : RView) : Prop :=
  RejectedWith π e r ∧ ∀ b : Budget, defaultFuel ≤ b.fuel → reasonAt b π e = some r

/-- A result that is an error is no success. -/
theorem verdictOf_error {α : Type} {x : Except EReason α} {r : EReason} (h : x = .error r) :
    (verdictOf x).isOk = false := by
  subst h
  cases r <;> rfl

/-- An elaboration that ends in a reason with the tank unmarked fails at
every budget. -/
theorem elabTopF_error_all {π : PlatformNames} {p : PTm π.sig} {r : EReason} {n : Nat}
    (het : elabTopF defaultFuel π p = (.error r, ⟨n, false⟩)) (m : Nat) :
    ∃ r', (elabTopF m π p).1 = .error r' := by
  cases hm : (elabTopF m π p).1 with
  | error r' => exact ⟨r', rfl⟩
  | ok c =>
    exfalso
    rcases Nat.le_total defaultFuel m with hle | hle
    · have hs := elabTop?_stable het (m - defaultFuel)
      rw [Nat.add_sub_cancel' hle, hm] at hs
      cases hs
    · have hd := elabTop?_mono hm hle
      rw [het] at hd
      cases hd

/-- `compileE` after resolution reads the elaborator's first answer. -/
theorem compileE_error_of {b : Budget} {π : PlatformNames} {e : STm} {p : PTm π.sig}
    {r : EReason} (hp : resolvePTop Λc π e = some p) (het : (elabTopF b.fuel π p).1 = .error r) :
    ∃ r', compileE b Λc π e = .error r' := by
  unfold compileE
  rw [hp]
  simp only [het]
  cases r <;> exact ⟨_, rfl⟩

/-- An existential answer is an error of `compileE`. -/
theorem compileE_ex_of {b : Budget} {π : PlatformNames} {e : STm} {p : PTm π.sig}
    {c : ECand π.plat.ctx} {q : XElab π.plat.ctx} (hp : resolvePTop Λc π e = some p)
    (het : (elabTopF b.fuel π p).1 = .ok c) (hs : c.e.split = .inr q) :
    compileE b Λc π e = .error (.landed (existentialAt π.plat.ctx q)) := by
  unfold compileE
  rw [hp]
  simp only [het, hs]

/-- **An elaboration that fails unmarked rejects at every budget.** -/
theorem rejects_of_error {π : PlatformNames} {e : STm} {p : PTm π.sig} {r : EReason} {n : Nat}
    (hp : resolvePTop Λc π e = some p) (het : elabTopF defaultFuel π p = (.error r, ⟨n, false⟩))
    (b : Budget) : (compile b Λc π e).isOk = false := by
  obtain ⟨r', hr'⟩ := elabTopF_error_all het b.fuel
  obtain ⟨r'', h⟩ := compileE_error_of hp hr'
  exact verdictOf_error h

/-- An elaboration whose first answer is existential rejects at every
budget. -/
theorem rejects_of_ex {π : PlatformNames} {e : STm} {p : PTm π.sig} {c : ECand π.plat.ctx}
    {q : XElab π.plat.ctx} (hp : resolvePTop Λc π e = some p)
    (het : (elabTopF defaultFuel π p).1 = .ok c) (hs : c.e.split = .inr q) (b : Budget) :
    (compile b Λc π e).isOk = false := by
  cases hb : (elabTopF b.fuel π p).1 with
  | error r =>
    obtain ⟨r', h⟩ := compileE_error_of hp hb
    exact verdictOf_error h
  | ok c' =>
    have hc' : c' = c := by
      rcases Nat.le_total defaultFuel b.fuel with hle | hle
      · have hm := elabTop?_mono het hle
        rw [hb] at hm
        cases hm
        rfl
      · have hm := elabTop?_mono hb hle
        rw [het] at hm
        cases hm
        rfl
    subst hc'
    exact verdictOf_error (compileE_ex_of hp hb hs)

/-- The elaborator's tank on a rejected cell, and the reason `compileE` gives
at the default budget. -/
theorem cellOf_no {π : PlatformNames} {e : STm} {p : PTm π.sig} {a? : Option (ATm π.sig)}
    {r : RView} {n : Nat} (hp : resolvePTop Λc π e = some p)
    (h : cellOf π p a? = .no r ⟨n, false⟩) :
    RejectedWith π e r ∧
      ((∃ r0, elabTopF defaultFuel π p = (.error r0, ⟨n, false⟩) ∧
          (r0 ≠ .mismatch → r0.view = r)) ∨
        ∃ c q, elabTopF defaultFuel π p = (.ok c, ⟨n, false⟩) ∧ c.e.split = .inr q) := by
  unfold cellOf at h
  split at h
  · rename_i c t het
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · rename_i q hs
      cases h
      have het1 : (elabTopF defaultFuel π p).1 = .ok c := by rw [het]
      refine ⟨⟨rejects_of_ex hp het1 hs, ?_⟩, .inr ⟨c, q, het, hs⟩⟩
      unfold reasonAt
      rw [compileE_ex_of (b := {}) hp het1 hs]
      rfl
  · rename_i t het
    cases h
    refine ⟨⟨rejects_of_error hp het, ?_⟩, .inl ⟨.mismatch, het, fun h => absurd rfl h⟩⟩
    unfold reasonAt compileE
    rw [hp]
    have h1 : (elabTopF ({} : Budget).fuel π p).1 = .error .mismatch := by rw [het]
    simp only [h1]
    rfl
  · rename_i r0 t hne het
    cases h
    refine ⟨⟨rejects_of_error hp het, ?_⟩, .inl ⟨r0, het, fun _ => rfl⟩⟩
    unfold reasonAt compileE
    rw [hp]
    have h1 : (elabTopF ({} : Budget).fuel π p).1 = .error r0 := by rw [het]
    simp only [h1]
    cases r0 with
    | mismatch => exact absurd rfl hne
    | _ => rfl

/-- **A rejected cell with the tank unmarked is a rejection at every
budget.** -/
theorem erasedCell_rejected {π : PlatformNames} {w e : STm} {r : RView} {n : Nat}
    (h : erasedCell π w e = .no r ⟨n, false⟩) : RejectedWith π e r := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · exact (cellOf_no hp h).1
    · cases h
  · cases h

/-- **A program with no written form, rejected with the tank unmarked, is
rejected at every budget.** -/
theorem openCell_rejected {π : PlatformNames} {e : STm} {r : RView} {n : Nat}
    (h : openCell π e = .no r ⟨n, false⟩) : RejectedWith π e r := by
  unfold openCell at h
  split at h
  · rename_i p hp
    exact (cellOf_no hp h).1
  · cases h

/-- A slot reason comes from the elaborator, never from the fill. -/
theorem view_slot {r : EReason} : r.view.isSlotReason = r.isSlotReason := by
  cases r <;> rfl

/-- The reason of an elaboration that fails unmarked is `compileE`'s reason at
every budget from `defaultFuel` up, when it is not a mismatch. -/
theorem reasonAt_above {π : PlatformNames} {e : STm} {p : PTm π.sig} {r0 : EReason} {n : Nat}
    (hp : resolvePTop Λc π e = some p) (het : elabTopF defaultFuel π p = (.error r0, ⟨n, false⟩))
    (hne : r0 ≠ .mismatch) (b : Budget) (hb : defaultFuel ≤ b.fuel) :
    reasonAt b π e = some r0.view := by
  have hs := elabTop?_stable het (b.fuel - defaultFuel)
  rw [Nat.add_sub_cancel' hb] at hs
  unfold reasonAt compileE
  rw [hp]
  simp only [hs]
  cases r0 with
  | mismatch => exact absurd rfl hne
  | _ => rfl

/-- **A slot reason holds at every budget.**  A rejected cell whose reason is
a reason of inference, with the tank unmarked, is the reason of `compileE` at
every budget from `defaultFuel` up. -/
theorem cellOf_slot {π : PlatformNames} {e : STm} {p : PTm π.sig} {a? : Option (ATm π.sig)}
    {r : RView} {n : Nat} (hp : resolvePTop Λc π e = some p)
    (h : cellOf π p a? = .no r ⟨n, false⟩) (hr : r.isSlotReason = true) :
    RejectedAbove π e r := by
  obtain ⟨hw, hc⟩ := cellOf_no hp h
  refine ⟨hw, fun b hb => ?_⟩
  rcases hc with ⟨r0, het, hv⟩ | ⟨c, q, het, hs⟩
  · have hne : r0 ≠ .mismatch := by
      intro h0
      subst h0
      unfold cellOf at h
      rw [het] at h
      simp only at h
      cases h
      rw [view_slot, fillReason_not_slot] at hr
      cases hr
    rw [reasonAt_above hp het hne b hb, hv hne]
  · exfalso
    unfold cellOf at h
    rw [het] at h
    simp only [hs] at h
    cases h
    cases hr

/-- **A slot reason of an erased program holds at every budget.** -/
theorem erasedCell_slot {π : PlatformNames} {w e : STm} {r : RView} {n : Nat}
    (h : erasedCell π w e = .no r ⟨n, false⟩) (hr : r.isSlotReason = true) :
    RejectedAbove π e r := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · exact cellOf_slot hp h hr
    · cases h
  · cases h

/-- **A slot reason of a program with no written form holds at every
budget.** -/
theorem openCell_slot {π : PlatformNames} {e : STm} {r : RView} {n : Nat}
    (h : openCell π e = .no r ⟨n, false⟩) (hr : r.isSlotReason = true) : RejectedAbove π e r := by
  unfold openCell at h
  split at h
  · rename_i p hp
    exact cellOf_slot hp h hr
  · cases h

/-- An elaboration whose fill passes the two tests is `compile`: the fill, at
the candidate's type. -/
theorem compile_of_fill {b : Budget} {π : PlatformNames} {e : STm} {p : PTm π.sig}
    {c : ECand π.plat.ctx} {q : PElab π.plat.ctx} (hp : resolvePTop Λc π e = some p)
    (het : (elabTopF b.fuel π p).1 = .ok c) (hs : c.e.split = .inl q)
    (hc : p.fills c.fill = true ∧ ATm.skel q.tm = ATm.skel c.fill) :
    (compile b Λc π e).toOption.map (fun r => (r.1, r.2.ty)) = some (c.fill, q.ty) := by
  show (verdictOf (compileE b Λc π e)).toOption.map _ = _
  unfold compileE
  rw [hp]
  simp only [het, hs, hc.1, if_true, dif_pos hc.2]
  rfl

/-- A compiled cell is `compile` at every budget from `defaultFuel` up: the
fill and the type. -/
theorem cellOf_ok {π : PlatformNames} {e : STm} {p : PTm π.sig} {a? : Option (ATm π.sig)}
    {c' : Cell π.sig} (hp : resolvePTop Λc π e = some p) (h : cellOf π p a? = c')
    (hc' : ∀ T t, c' ≠ .no T t) (hc'' : c' ≠ .shape) :
    ∃ c q, (elabTopF defaultFuel π p).1 = .ok c ∧ c.e.split = .inl q ∧
      (∀ b : Budget, defaultFuel ≤ b.fuel →
        (compile b Λc π e).toOption.map (fun r => (r.1, r.2.ty)) = some (c.fill, q.ty)) ∧
      c' = (if some c.fill = a? then .same q.ty (elabTopF defaultFuel π p).2
        else .other q.ty (elabTopF defaultFuel π p).2) := by
  unfold cellOf at h
  split at h
  · rename_i c t het
    split at h
    · rename_i q hs
      split at h
      · rename_i hc
        have het1 : (elabTopF defaultFuel π p).1 = .ok c := by rw [het]
        refine ⟨c, q, het1, hs, fun b hb => compile_of_fill hp (elabTop?_mono het1 hb) hs hc, ?_⟩
        rw [← h, het]
      · exact absurd h.symm hc''
    · exact absurd h.symm (hc' _ _)
  · exact absurd h.symm (hc' _ _)
  · exact absurd h.symm (hc' _ _)

/-- **A cell at the written term is `compile` at the written term.**  At every
budget from `defaultFuel` up, the erased program compiles to the term the
written program resolves to, at the cell's type. -/
theorem erasedCell_same {π : PlatformNames} {w e : STm} {T : Ty π.sig} {t : Tank}
    (h : erasedCell π w e = .same T t) (b : Budget) (hb : defaultFuel ≤ b.fuel) :
    (compile b Λc π e).toOption.map (fun r => (r.1, r.2.ty)) =
      (resolveTop Λc π w).map (fun a => (a, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · obtain ⟨c, q, _, _, hcomp, heq⟩ :=
        cellOf_ok hp h (fun _ _ => by simp) (by simp)
      rw [hcomp b hb, hw]
      split at heq
      · rename_i hfa
        cases heq
        cases hfa
        rfl
      · cases heq
    · cases h
  · cases h

/-- **A cell at another fill is `compile` at the cell's type**, at every
budget from `defaultFuel` up. -/
theorem erasedCell_other {π : PlatformNames} {w e : STm} {T : Ty π.sig} {t : Tank}
    (h : erasedCell π w e = .other T t) (b : Budget) (hb : defaultFuel ≤ b.fuel) :
    (compile b Λc π e).toOption.map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · obtain ⟨c, q, _, _, hcomp, heq⟩ :=
        cellOf_ok hp h (fun _ _ => by simp) (by simp)
      have h2 := congrArg (Option.map Prod.snd) (hcomp b hb)
      simp only [Option.map_map] at h2
      split at heq
      · cases heq
      · cases heq
        exact h2
    · cases h
  · cases h

/-- A cell of an erasure that changes the program is the erased program's
cell. -/
theorem cell_erased {k : Erasure} {π : PlatformNames} {w : STm} (h : cell k π w ≠ .noSlot) :
    cell k π w = erasedCell π w (k.surface w) := by
  unfold cell at h ⊢
  split
  · rename_i he
    rw [if_pos he] at h
    exact absurd rfl h
  · rfl

/-- A program the elaborator rejects with the tank unmarked, as `elabOut`
reports it, is rejected at every budget. -/
theorem elabOut_rejects {π : PlatformNames} {e : STm} {r : RView} {n : Nat}
    (h : elabOut π e = (.no r, ⟨n, false⟩)) (b : Budget) : (compile b Λc π e).isOk = false := by
  unfold elabOut at h
  split at h
  · rename_i p hp
    split at h
    · cases h
    · rename_i r0 t het
      cases h
      exact rejects_of_error hp het b
  · cases h


/-! ### Written forms of programs given with empty slots

`Elab.lean` checks programs written with an empty slot.  Here each gets a
written form, and its erasure is checked to be the program there.  Where an
erased program compiles at a self shape other than the written one, a written
form at the formed shape states its type: `E5srcR`, `E6srcR`, `C7srcF`,
`SelfProjSrcF` and `BareCapSrcF` of `Elab.lean`, and `NestSrcW` here. -/

/-- E6 closed over its parameter, with its self shape written as in
`DotMNF/Examples.lean`. -/
def E6srcW : STm :=
  cc% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

/-- A lambda bound with no type, the domain written. -/
def Id0Src : STm := cc% let i = λ(x : ⊤). x in i

/-- A lambda ascribed at `⊤`, the domain written. -/
def IdTopSrc : STm := cc% (λ(x : ⊤). x : ⊤)

/-- Two function sides with incomparable domains, and a lambda at `⊤` below
both. -/
def AndIncSrc : STm := cc% (λ(y : ⊤). y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤))

/-- One function side and a field the lambda does not have. -/
def AndOneSrc : STm := cc% (λ(y : ⊤). y : (∀(x : ⊤) ⊤) ∧ {a : ⊤})

/-- An abstract type with a function upper bound as the goal. -/
def UpperSrc : STm := cc% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). (λ(x : ⊤). x : y.A)

/-- An abstract type with a function lower bound as the goal. -/
def LowerSrc : STm := cc% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). (λ(x : ⊤). x : y.A)

/-- A lambda bound by a written `let` and then passed, the domain written. -/
def LetArgSrc : STm := cc% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λ(x : ⊤). x in g i

/-- A callee whose two formals are incomparable, applied to a lambda at `⊤`. -/
def IncSrc : STm :=
  cc% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- A callee with no function type, applied to a lambda. -/
def NoFnSrc : STm := cc% λ(g : ⊤). g (λ(x : ⊤). x)

/-- A body that calls `g` on another variable. -/
def CalleeOtherSrc : STm := cc% λ(g : ∀(y : ⊤) ⊤). λ(z : ⊤). let h = λ(x : ⊤). g z in h

/-- A callee at incomparable domains. -/
def CalleeIncSrc : STm :=
  cc% λ(g : (∀(y : {a : ⊤}) ⊤) ∧ (∀(y : {b : ⊤}) ⊤)). let h = λ(x : {a : ⊤}). g x in h

/-- Two fields that read each other, the self shape written. -/
def CycSrc : STm := cc% ν(z : {a : ⊤} ∧ {b : ⊤}. {a = z.b} ∧ {b = z.a})

/-- A field that reads a cycle between two later fields, the self shape
written. -/
def Cyc3Src : STm :=
  cc% ν(z : {a : ⊤} ∧ {b : ⊤} ∧ {v : ⊤}. {a = z.b} ∧ {b = z.v} ∧ {v = z.b})

/-- A recursive field that reads itself through an alias of the self, the
self shape written. -/
def AliasRecSrc : STm :=
  cc% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = z in let u = w.a in u y})

/-- A field whose right-hand side has two incomparable types, the self shape
written at one of them. -/
def AmbSrc : STm := cc% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s : {a : {b : ⊤}}. {a = y.a})

/-- A field that is a lambda, the self shape and the domain written. -/
def NoDomSrc : STm := cc% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). y})

/-- A lambda ascribed at a type that puts `any` below a field of its domain,
the domain written. -/
def DeepAscSrc : STm := cc% (λ(x : {read : ⊤ ^ {any}}). x : ∀(x : {read : ⊤ ^ {any}}) ⊤)

/-- Nest with both self shapes written at the shapes its definitions form:
the inner field at the type of `y`. -/
def NestSrcW : STm :=
  cc% λ(y : {b : ⊤} ∧ {elem : ⊤}).
        ν(o : {a : μ(z. {b : {b : ⊤} ∧ {elem : ⊤}})}.
           {a = ν(z : {b : {b : ⊤} ∧ {elem : ⊤}}. {b = y})})

-- The erasures give the programs of `Resolve.lean` and `Elab.lean`.
example : Erasure.D.surface E2src = E2srcD ∧ Erasure.S.surface E2src = E2srcS ∧
    Erasure.S.surface E5src = E5srcS ∧ Erasure.S.surface E7src = E7srcS ∧
    Erasure.D.surface E8src = E8srcD ∧ Erasure.S.surface S3src = S3srcS ∧
    Erasure.S.surface C2src = C2srcS ∧ Erasure.C.surface C2src = C2srcG ∧
    Erasure.G.surface S1progSrc = S1srcG ∧ Erasure.G.surface S2src = S2srcG ∧
    Erasure.D.surface Z1progSrc = Z1srcD ∧ Erasure.S.surface Z3src = Z3srcS ∧
    Erasure.G.surface EscSrc = EscSrcG ∧ Erasure.A.surface K1src = K1srcA ∧
    Erasure.S.surface E6srcW = E6srcS := by
  and_intros <;> rfl
example : Erasure.D.surface W2ascSrc = W2ascSrcD ∧ Erasure.C.surface AndSameSrc = AndSameSrcD ∧
    Erasure.C.surface X3Src = X3SrcD ∧ Erasure.C.surface AndTwoSrc = AndTwoSrcD ∧
    Erasure.C.surface AndResSrc = AndResSrcD ∧ Erasure.C.surface AndIncSrc = AndIncSrcD ∧
    Erasure.C.surface AndOneSrc = AndOneSrcD ∧ Erasure.C.surface AndTopSrc = AndTopSrcD ∧
    Erasure.C.surface AscSrc = AscSrcD ∧ Erasure.C.surface AliasSrc = AliasSrcD ∧
    Erasure.C.surface Alias2Src = Alias2SrcD ∧ Erasure.C.surface UpperSrc = UpperSrcD ∧
    Erasure.C.surface LowerSrc = LowerSrcD ∧ Erasure.C.surface LoopSrc = LoopSrcD ∧
    Erasure.D.surface Id0Src = Id0SrcD ∧ Erasure.C.surface IdTopSrc = IdTopSrcD ∧
    Erasure.C.surface CurrySrc = CurrySrcD ∧ Erasure.C.surface SideCurrySrc = SideCurrySrcD ∧
    Erasure.C.surface LetBodySrc = LetBodySrcD ∧ Erasure.C.surface BlockSrc = BlockSrcD ∧
    Erasure.C.surface CapSrc = CapSrcD ∧ Erasure.C.surface CapPureSrc = CapPureSrcD ∧
    Erasure.C.surface FldSrc = FldSrcD ∧ Erasure.S.surface AscObjSrc = AscObjSrcS ∧
    Erasure.S.surface AscWideSrc = AscWideSrcS ∧ Erasure.D.surface DeepAscSrc = DeepSrcD := by
  and_intros <;> rfl
example : Erasure.A.surface S1callSrc = S1callSrcA ∧ Erasure.C.surface S1callSrc = S1callSrcG ∧
    Erasure.A.surface KcapSrc = KcapSrcA ∧ Erasure.A.surface X1Src = X1SrcA ∧
    Erasure.A.surface DomSrc = DomSrcA ∧ Erasure.A.surface IncSrc = IncSrcA ∧
    Erasure.A.surface NoFnSrc = NoFnSrcA ∧ Erasure.C.surface BlockArgSrc = BlockArgSrcG ∧
    Erasure.C.surface CurriedSrc = CurriedSrcG ∧ Erasure.A.surface BoxCalleeSrc = BoxCalleeSrcA ∧
    Erasure.A.surface BoxFSrc = BoxFSrcA ∧ Erasure.A.surface AnyAscSrc = AnyAscSrcA ∧
    Erasure.A.surface FitsSrc = FitsSrcA ∧ Erasure.A.surface TooBigSrc = TooBigSrcA ∧
    Erasure.C.surface CalleeTopSrc = CalleeTopSrcD ∧
    Erasure.A.surface CalleeArgSrc = CalleeArgSrcA ∧ Erasure.C.surface ValSrc = ValSrcD ∧
    Erasure.C.surface Z1defSrc = Z1defSrcD ∧ Erasure.C.surface EscOkSrc = EscOkSrcG ∧
    Erasure.C.surface TopEscSrc = TopEscSrcG ∧ Erasure.D.surface TopEscSrc = TopEscSrcG ∧
    Erasure.C.surface Z2src = Z2srcD ∧ Erasure.D.surface Z2src = Z2srcD ∧
    Erasure.C.surface S2src = S2srcChecked ∧ Erasure.C.surface exTopSrc = exTopSrcG ∧
    Erasure.D.surface exTopSrc = exTopSrcD ∧ Erasure.C.surface EscSrc = EscSrcG ∧
    Erasure.C.surface AscEscSrc = AscEscSrcG ∧ Erasure.D.surface W2defSrc = W2defSrcD ∧
    Erasure.D.surface C7src = C7srcD ∧ Erasure.D.surface Z3src = Z3srcD := by
  and_intros <;> rfl
example : Erasure.S.surface RecObjSrc = RecSrcS ∧ Erasure.S.surface CycSrc = CycSrcS ∧
    Erasure.S.surface Cyc3Src = Cyc3SrcS ∧ Erasure.S.surface AliasRecSrc = AliasRecSrcS ∧
    Erasure.S.surface BareSrc = BareSrcS ∧ Erasure.S.surface FwdSelfSrc = FwdSelfSrcS ∧
    Erasure.S.surface BareProjSrc = BareProjSrcS ∧ Erasure.S.surface AmbSrc = AmbSrcS ∧
    Erasure.S.surface AmbUseSrc = AmbUseSrcS ∧ Erasure.S.surface AmbUse2Src = AmbUse2SrcS ∧
    Erasure.S.surface (NestKSrc true 2) = NestKSrc false 2 ∧ Erasure.S.surface Z1litF = Z1litS ∧
    Erasure.S.surface FldTySrc = NoShapeSrcS := by
  and_intros <;> rfl

/-- The programs of the tables, each over its platform. -/
def tablePrograms : List (PlatformNames × STm) :=
  [(.empty, E1src), (.empty, E2src), (.empty, E3src), (.empty, E4src), (.empty, E5src),
   (.empty, E6srcW), (.empty, E7src), (.empty, E8src), (.empty, E1ssrc), (.empty, E3ssrc),
   (.empty, PA1src), (.empty, P4src), (.empty, P5src), (.empty, R1src), (.empty, R2src),
   (.empty, R3src), (.empty, R4src), (.empty, B1src), (.empty, A1src), (.empty, chainSrc 16),
   (.empty, LPsrc), (.empty, PFsrc),
   (πc, C7boxSrc), (πc, C7src), (πc, S3src), (πc, C2src), (πz, S1progSrc), (πz, S2src),
   (πz, Z1progSrc), (πz, Z1defSrc), (πz, Z2src), (πz, Z3src), (πc, W2defSrc), (πc, cov2Src),
   (πc, cov3Src), (πc, cov4Src), (πc, accountedSrc), (πc, deepSrc), (πz, exTopSrc),
   (πc, EscSrc), (πc, AscEscSrc), (πc, TopEscSrc), (πc, EscOkSrc), (πc, BX2src), (πc, BXsrc),
   (πz, LetExSrc),
   (πz, S1callSrc), (.empty, K1src), (πc, KcapSrc), (.empty, X1Src), (.empty, DomSrc),
   (.empty, IncSrc), (.empty, NoFnSrc), (.empty, BlockArgSrc), (.empty, CurriedSrc),
   (.empty, BoxCalleeSrc), (.empty, BoxFSrc), (πc, AnyAscSrc), (πc, FitsSrc), (πc, TooBigSrc),
   (.empty, CalleeSrc), (.empty, CalleeAnySrc), (.empty, CalleeTopSrc), (.empty, CalleeArgSrc),
   (.empty, CalleeOtherSrc), (.empty, CalleeIncSrc), (.empty, LetArgSrc), (.empty, Id0Src),
   (.empty, ValSrc),
   (πc, W2ascSrc), (.empty, AndSameSrc), (.empty, X3Src), (.empty, AndTwoSrc),
   (.empty, AndResSrc), (.empty, AndIncSrc), (.empty, AndOneSrc), (.empty, AndTopSrc),
   (.empty, AscSrc), (.empty, AliasSrc), (.empty, Alias2Src), (.empty, UpperSrc),
   (.empty, LowerSrc), (.empty, LoopSrc), (.empty, IdTopSrc), (.empty, CurrySrc),
   (.empty, SideCurrySrc), (.empty, LetBodySrc), (.empty, BlockSrc), (πc, CapSrc),
   (πc, CapPureSrc), (.empty, DeepAscSrc),
   (πc, FldSrc), (.empty, FldTySrc), (.empty, AscObjSrc), (.empty, AscWideSrc), (.empty, NestSrc),
   (.empty, FwdObjSrc), (πc, Cap1Src), (πc, SelfProjSrc), (.empty, RecObjSrc), (.empty, BareSrc),
   (πc, BareCapSrc), (πc, LamCapSrc), (.empty, FwdSelfSrc), (.empty, BareProjSrc),
   (.empty, AmbUseSrc), (.empty, AmbUse2Src), (.empty, AmbSrc), (.empty, E2objSrc),
   (.empty, CycSrc), (πc, Cyc3Src), (.empty, AliasRecSrc), (.empty, NoDomSrc), (πz, Z1litF)]

-- Every erasure of every program agrees with the erasure of the resolved term.
example : tablePrograms.all (fun (π, w) => [Erasure.D, .S, .A, .C, .G].all (·.agrees π w)) =
    true := by
  decide +kernel

/-! ### The programs of the typer

Every closed program of `Notation.lean`, `Typer.lean` and the sections above.
Each one whose outermost term is a lambda is a missing parameter type under
`D`, since nothing gives the lambda a goal, as in Scala.  E2, Z1, Z1def, Z2 and
Z3 keep compiling under `D`, since their lambdas take their domains from a
written self shape, a written `let` type or an ascription.  S1 and S2 are
rejected under `D` at a lambda bound by a `let` with no type, after the fuel
their first steps take.

Under `S` and `G` a literal forms its self shape from its definitions.  E2, E7
and accounted compile at the written term.  E5, E6 and C7 compile at the types
of their right-hand sides, which `E5srcR`, `E6srcR` and `C7srcF` write.  S3, C2,
S1, S2 and Z3 compile at the written type, with a self shape other than the
written one, which names a member or its set.  The literal of `freshCell` forms
`read` pure, and the version has no subtyping between two `μ` shapes, so Z1,
Z1def, Z2 and exTop do not meet the written `μ` and are a type mismatch.  C7
with its boxes written boxes each capability at its own set, where its written
unboxing names `{k1}`, so it is a type mismatch too.  The recursion limit of LP
and PF stays at its fuel. -/

/-- E1 under each erasure.  The written program is rejected, with no reason
of the typer. -/
theorem E1_erased : LambdaRow .empty E1src (.no .mismatch (spent 11)) := by
  decide +kernel

/-- E2 under each erasure.  Its one lambda is a field of a literal, so `D`
and `C` take its domain from the written self shape, and `S` and `G` form
the written self shape. -/
theorem E2_erased : row .empty E2src =
    [.same (tyOf .empty E2src) (spent 60), .same (tyOf .empty E2src) (spent 62),
     .same (tyOf .empty E2src) (spent 61), .noSlot, .same (tyOf .empty E2src) (spent 62),
     .same (tyOf .empty E2src) (spent 61)] := by
  decide +kernel

/-- E3 under each erasure. -/
theorem E3_erased : LambdaRow .empty E3src (.no .mismatch (spent 11)) := by
  decide +kernel

/-- E4 under each erasure. -/
theorem E4_erased : LambdaRow .empty E4src (.no .mismatch (spent 16)) := by
  decide +kernel

/-- E5 under each erasure.  `S` and `G` compile at the type of the
right-hand side. -/
theorem E5_erased : row .empty E5src =
    [.same (tyOf .empty E5src) (spent 20), missing 0,
     .other (tyOf .empty E5srcR) (spent 11), .noSlot, .noSlot,
     .other (tyOf .empty E5srcR) (spent 11)] := by
  decide +kernel

/-- E6 under each erasure.  `S` and `G` compile at the type of the
right-hand side. -/
theorem E6_erased : row .empty E6srcW =
    [.same (tyOf .empty E6srcW) (spent 14), missing 0,
     .other (tyOf .empty E6srcR) (spent 3), .noSlot, .noSlot,
     .other (tyOf .empty E6srcR) (spent 3)] := by
  decide +kernel

/-- E7 under each erasure.  `S` and `G` form the written self shape. -/
theorem E7_erased : row .empty E7src =
    [.same (tyOf .empty E7src) (spent 1), .noSlot, .same (tyOf .empty E7src) (spent 1),
     .noSlot, .noSlot, .same (tyOf .empty E7src) (spent 1)] := by
  decide +kernel

/-- E8 under each erasure. -/
theorem E8_erased : LambdaRow .empty E8src (.same (tyOf .empty E8src) (spent 13)) := by
  decide +kernel

/-- E1s under each erasure. -/
theorem E1s_erased : LambdaRow .empty E1ssrc (.same (tyOf .empty E1ssrc) (spent 20)) := by
  decide +kernel

/-- E3s under each erasure. -/
theorem E3s_erased : LambdaRow .empty E3ssrc (.same (tyOf .empty E3ssrc) (spent 18)) := by
  decide +kernel

/-- PA1 under each erasure. -/
theorem PA1_erased : LambdaRow .empty PA1src (.same (tyOf .empty PA1src) (spent 45)) := by
  decide +kernel

/-- P4 under each erasure. -/
theorem P4_erased : LambdaRow .empty P4src (.same (tyOf .empty P4src) (spent 28)) := by
  decide +kernel

/-- P5 under each erasure. -/
theorem P5_erased : LambdaRow .empty P5src (.same (tyOf .empty P5src) (spent 13)) := by
  decide +kernel

/-- R1 under each erasure. -/
theorem R1_erased : LambdaRow .empty R1src (.same (tyOf .empty R1src) (spent 17)) := by
  decide +kernel

/-- R2 under each erasure. -/
theorem R2_erased : LambdaRow .empty R2src (.same (tyOf .empty R2src) (spent 10)) := by
  decide +kernel

/-- R3 under each erasure. -/
theorem R3_erased : LambdaRow .empty R3src (.same (tyOf .empty R3src) (spent 11)) := by
  decide +kernel

/-- R4 under each erasure. -/
theorem R4_erased : LambdaRow .empty R4src (.same (tyOf .empty R4src) (spent 9)) := by
  decide +kernel

/-- B1 under each erasure. -/
theorem B1_erased : LambdaRow .empty B1src (.no .mismatch (spent 2)) := by
  decide +kernel

/-- A1 under each erasure. -/
theorem A1_erased : LambdaRow .empty A1src (.no .mismatch (spent 11)) := by
  decide +kernel

/-- chain16 under each erasure. -/
theorem chain16_erased :
    LambdaRow .empty (chainSrc 16) (.same (tyOf .empty (chainSrc 16)) (spent 203)) := by
  decide +kernel

/-- LP under each erasure.  The written program is at the recursion limit. -/
theorem LP_erased : LambdaRow .empty LPsrc (.no .limit (marked 32737)) := by
  decide +kernel

/-- PF under each erasure.  The written program is at the recursion limit. -/
theorem PF_erased : LambdaRow .empty PFsrc (.no .limit (marked 32693)) := by
  decide +kernel

/-- C7 with its boxes written, under each erasure.  `S` and `G` box each
capability at its own set, where the written unboxing names `{k1}`. -/
theorem C7box_erased : row πc C7boxSrc =
    [.same (tyOf πc C7boxSrc) (spent 31), missing 0, .no .mismatch (spent 13), .noSlot,
     .noSlot, .no .mismatch (spent 13)] := by
  decide +kernel

/-- C7 with no box written, under each erasure.  `S` and `G` compile at the
self shape the definitions form, the fields at the capabilities they hold. -/
theorem C7_erased : row πc C7src =
    [.same (tyOf πc C7src) (spent 80), missing 0, .other (tyOf πc C7srcF) (spent 44),
     .noSlot, .noSlot, .other (tyOf πc C7srcF) (spent 44)] := by
  decide +kernel

/-- S3 under each erasure.  `S` and `G` compile at the written type, the
field at the boxed capability where the written shape names `z.A`. -/
theorem S3_erased : row πc S3src =
    [.same (tyOf πc S3src) (spent 46), missing 0, .other (tyOf πc S3src) (spent 15),
     .noSlot, .noSlot, .other (tyOf πc S3src) (spent 15)] := by
  decide +kernel

/-- C2 under each erasure.  `C` takes the domains of the fields from the
written self shapes.  `S` and `G` compile at the written type, with `run`
pure. -/
theorem C2_erased : row πc C2src =
    [.same (tyOf πc C2src) (spent 214), missing 0, .other (tyOf πc C2src) (spent 244),
     .noSlot, .same (tyOf πc C2src) (spent 218), .other (tyOf πc C2src) (spent 244)] := by
  decide +kernel

/-- S1 under each erasure.  `D` erases the domain of `op`, bound by a `let`
with no type.  `C` takes the domains from the ascription and the self shape. -/
theorem S1_erased : row πz S1progSrc =
    [.same (tyOf πz S1progSrc) (spent 86), missing 28,
     .other (tyOf πz S1progSrc) (spent 97), .noSlot, .same (tyOf πz S1progSrc) (spent 88),
     .other (tyOf πz S1progSrc) (spent 97)] := by
  decide +kernel

/-- S2 under each erasure.  `C` and `G` erase the domain of `(λy. y : ⊤)`,
whose goal has no function part, so they are a missing parameter type. -/
theorem S2_erased : row πz S2src =
    [.same (tyOf πz S2src) (spent 138), missing 96, .other (tyOf πz S2src) (spent 191),
     .noSlot, missing 96, missing 143] := by
  decide +kernel

/-- Z1 under each erasure.  `D` and `C` take the domains from the ascription
and the self shape.  `S` and `G` form `read` pure, which does not meet the
written `μ`. -/
theorem Z1_erased : row πz Z1progSrc =
    [.same (tyOf πz Z1progSrc) (spent 12), .same (tyOf πz Z1progSrc) (spent 14),
     .no .mismatch (spent 62), .noSlot, .same (tyOf πz Z1progSrc) (spent 14),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z1def under each erasure.  `D` and `C` take the domains from the written
`let` type and the self shape.  `S` and `G` form `read` pure. -/
theorem Z1def_erased : row πz Z1defSrc =
    [.same (tyOf πz Z1defSrc) (spent 31), .same (tyOf πz Z1defSrc) (spent 45),
     .no .mismatch (spent 112), .noSlot, .same (tyOf πz Z1defSrc) (spent 45),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z2 under each erasure.  `D` and `C` fill the domain with the goal's, its
`any` read at the arrow's binder, where the written program holds `any`.
`S` and `G` form `read` pure. -/
theorem Z2_erased : row πz Z2src =
    [.same (tyOf πz Z2src) (spent 12), .other (tyOf πz Z2src) (spent 14),
     .no .mismatch (spent 62), .noSlot, .other (tyOf πz Z2src) (spent 14),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z3 under each erasure.  Every erasure compiles, `S` and `G` with a self
shape other than the written one. -/
theorem Z3_erased : row πz Z3src =
    [.same (tyOf πz Z3src) (spent 101), .same (tyOf πz Z3src) (spent 107),
     .other (tyOf πz Z3src) (spent 154), .noSlot, .same (tyOf πz Z3src) (spent 107),
     .other (tyOf πz Z3src) (spent 154)] := by
  decide +kernel

/-- W2def under each erasure. -/
theorem W2def_erased : LambdaRow πc W2defSrc (.same (tyOf πc W2defSrc) (spent 2)) := by
  decide +kernel

/-- cov2 under each erasure. -/
theorem cov2_erased : LambdaRow πc cov2Src (.same (tyOf πc cov2Src) (spent 14)) := by
  decide +kernel

/-- cov3 under each erasure. -/
theorem cov3_erased : LambdaRow πc cov3Src (.same (tyOf πc cov3Src) (spent 2)) := by
  decide +kernel

/-- cov4 under each erasure. -/
theorem cov4_erased : LambdaRow πc cov4Src (.same (tyOf πc cov4Src) (spent 32)) := by
  decide +kernel

/-- accounted under each erasure.  `S` and `G` form the written self shape. -/
theorem accounted_erased : row πc accountedSrc =
    [.same (tyOf πc accountedSrc) (spent 36), missing 0,
     .same (tyOf πc accountedSrc) (spent 36), .noSlot, .noSlot,
     .same (tyOf πc accountedSrc) (spent 36)] := by
  decide +kernel

/-- W2 deep under each erasure.  The typer rejects the written domain with
`anyNotOk`. -/
theorem deep_erased : LambdaRow πc deepSrc (.no (.landed "anyNotOk") (spent 0)) := by
  decide +kernel

/-- exTop under each erasure.  The written program and `C` are rejected by
the typer with `existentialAtTop`.  `D` erases the domain of the lambda
bound to `un` by a written `let`.  `S` and `G` form `read` pure. -/
theorem exTop_erased : row πz exTopSrc =
    [.no (.landed "existentialAtTop") (spent 19), missing 14, .no .mismatch (spent 62),
     .noSlot, .no (.landed "existentialAtTop") (spent 21), .no .mismatch (spent 62)] := by
  decide +kernel

/-- The escape under each erasure.  `C` and `G` take the callback's domains
from the written answer of its `let`, and the typer rejects the fill with the
escape the written program has.  The kernel checks the cells of `D`, `S` and
`A`, and `#eval expect` the whole row. -/
theorem Esc_erased : cell .D πc EscSrc = missing 0 ∧ cell .S πc EscSrc = .noSlot ∧
    cell .A πc EscSrc = .noSlot := by
  decide +kernel
#eval expect (row πc EscSrc == [.no (.landed "levelEscape") (spent 31), missing 0, .noSlot,
    .noSlot, .no (.landed "levelEscape") (spent 63), .no (.landed "levelEscape") (spent 63)])
  "Esc: the row differs"

/-- The escape by an ascription under each erasure.  The kernel checks the
cells of `D`, `S` and `A`, and `#eval expect` the whole row. -/
theorem AscEsc_erased : cell .D πc AscEscSrc = missing 0 ∧ cell .S πc AscEscSrc = .noSlot ∧
    cell .A πc AscEscSrc = .noSlot := by
  decide +kernel
#eval expect (row πc AscEscSrc == [.no (.landed "levelEscape") (spent 88), missing 0, .noSlot,
    .noSlot, .no (.landed "levelEscape") (spent 63), .no (.landed "levelEscape") (spent 63)])
  "AscEsc: the row differs"

/-- The escape at the top under each erasure.  Every domain is in a checked
position, so `D`, `C` and `G` give one program, rejected with the escape.  The
kernel checks the cells of `S` and `A`, and `#eval expect` the whole row. -/
theorem TopEsc_erased : cell .S πc TopEscSrc = .noSlot ∧ cell .A πc TopEscSrc = .noSlot ∧
    Erasure.D.surface TopEscSrc = Erasure.C.surface TopEscSrc ∧
    Erasure.G.surface TopEscSrc = Erasure.C.surface TopEscSrc := by
  decide +kernel
#eval expect (row πc TopEscSrc == [.no (.landed "levelEscape") (spent 31),
    .no (.landed "levelEscape") (spent 63), .noSlot, .noSlot,
    .no (.landed "levelEscape") (spent 63), .no (.landed "levelEscape") (spent 63)])
  "TopEsc: the row differs"

/-- EscOk under each erasure.  `C` and `G` fill the callback's domain with
the goal's, its `any` read, so the fill is another one at the written type. -/
theorem EscOk_erased : row πc EscOkSrc =
    [.same (tyOf πc EscOkSrc) (spent 4), missing 0, .noSlot, .noSlot,
     .other (tyOf πc EscOkSrc) (spent 7), .other (tyOf πc EscOkSrc) (spent 7)] := by
  decide +kernel

/-- BX2 under each erasure. -/
theorem BX2_erased : LambdaRow πc BX2src (.same (tyOf πc BX2src) (spent 34)) := by
  decide +kernel

/-- BX under each erasure. -/
theorem BX_erased : LambdaRow πc BXsrc (.same (tyOf πc BXsrc) (spent 29)) := by
  decide +kernel

/-- A `let` whose bound term has an existential answer, under each erasure.
`C` fills the body under the unpacking, so the fill is an unpacking, which
`PTm.fills` does not relate to the written `let`.  The cell is `shape`, and
`compileE` reports a mismatch.  `S` and `G` form `read` pure. -/
theorem LetEx_erased : row πz LetExSrc =
    [.same (tyOf πz LetExSrc) (spent 20), missing 0, .no .mismatch (spent 62), .noSlot,
     .shape, .no .mismatch (spent 62)] := by
  decide +kernel

/-! ### Call arguments, callee bodies and `val` definitions

A lambda passed as an argument takes the dominant formal of its callee, whole,
so a block and a curried lambda get their inner domains too.  Under `A` every
such program compiles at the written term but Inc, whose formals are
incomparable, NoFn, whose callee has no function type, and TooBig, whose
closure is too large for its formal, as when written.  A callee body `λx. g x`
takes `g`'s formal, and a `val` definition its written type.  The rows of the
callee bodies and of a lambda bound by a written `let` leave their own slots
to the pairs below, since `D` erases the outer domain as well. -/

/-- `withFile` applied to its callback, under each erasure.  `A` takes the
callback's domain from the formal.  `C` and `G` erase the inner domain too,
whose goal is the formal's result `⊤`, so they are a missing parameter type.
`S` compiles at the written type with `read` pure. -/
theorem S1call_erased : row πz S1callSrc =
    [.same (tyOf πz S1callSrc) (spent 83), missing 54,
     .other (tyOf πz S1callSrc) (spent 94), .same (tyOf πz S1callSrc) (spent 91),
     missing 54, missing 63] := by
  decide +kernel

/-- K1 under each erasure.  The argument takes the formal. -/
theorem K1_erased : row .empty K1src =
    [.same (tyOf .empty K1src) (spent 26), missing 0, .noSlot,
     .same (tyOf .empty K1src) (spent 33), .same (tyOf .empty K1src) (spent 33),
     .same (tyOf .empty K1src) (spent 33)] := by
  decide +kernel

/-- A callback whose parameter captures a platform capability, under each
erasure. -/
theorem Kcap_erased : row πc KcapSrc =
    [.same (tyOf πc KcapSrc) (spent 31), missing 0, .noSlot,
     .same (tyOf πc KcapSrc) (spent 41), .same (tyOf πc KcapSrc) (spent 41),
     .same (tyOf πc KcapSrc) (spent 41)] := by
  decide +kernel

/-- X1 under each erasure.  The dominant formal is the one with the result
`⊤`. -/
theorem X1_erased : row .empty X1Src =
    [.same (tyOf .empty X1Src) (spent 31), missing 0, .noSlot,
     .same (tyOf .empty X1Src) (spent 52), .same (tyOf .empty X1Src) (spent 52),
     .same (tyOf .empty X1Src) (spent 52)] := by
  decide +kernel

/-- Dom under each erasure.  The dominant formal is the one with the smaller
domain. -/
theorem Dom_erased : row .empty DomSrc =
    [.same (tyOf .empty DomSrc) (spent 41), missing 0, .noSlot,
     .same (tyOf .empty DomSrc) (spent 66), .same (tyOf .empty DomSrc) (spent 66),
     .same (tyOf .empty DomSrc) (spent 66)] := by
  decide +kernel

/-- Inc under each erasure.  The formals are incomparable, so there is no
dominant one. -/
theorem Inc_erased : row .empty IncSrc =
    [.same (tyOf .empty IncSrc) (spent 52), missing 0, .noSlot, missing 17, missing 17,
     missing 17] := by
  decide +kernel

/-- NoFn under each erasure.  The callee has no function type. -/
theorem NoFn_erased : row .empty NoFnSrc =
    [.no .mismatch (spent 3), missing 0, .noSlot, missing 2, missing 2, missing 2] := by
  decide +kernel

/-- A block passed as an argument, under each erasure.  `A` erases no lambda
directly passed.  `C` and `G` erase the block's result lambda, which takes
the formal. -/
theorem BlockArg_erased : row .empty BlockArgSrc =
    [.same (tyOf .empty BlockArgSrc) (spent 7), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty BlockArgSrc) (spent 10),
     .same (tyOf .empty BlockArgSrc) (spent 10)] := by
  decide +kernel

/-- A curried callback, under each erasure.  `A` erases the outer domain,
`C` and `G` both. -/
theorem Curried_erased : row .empty CurriedSrc =
    [.same (tyOf .empty CurriedSrc) (spent 6), missing 0, .noSlot,
     .same (tyOf .empty CurriedSrc) (spent 10), .same (tyOf .empty CurriedSrc) (spent 10),
     .same (tyOf .empty CurriedSrc) (spent 10)] := by
  decide +kernel

/-- BoxCallee under each erasure. -/
theorem BoxCallee_erased : row .empty BoxCalleeSrc =
    [.same (tyOf .empty BoxCalleeSrc) (spent 8), missing 0, .noSlot,
     .same (tyOf .empty BoxCalleeSrc) (spent 12),
     .same (tyOf .empty BoxCalleeSrc) (spent 12),
     .same (tyOf .empty BoxCalleeSrc) (spent 12)] := by
  decide +kernel

/-- BoxF under each erasure. -/
theorem BoxF_erased : row .empty BoxFSrc =
    [.same (tyOf .empty BoxFSrc) (spent 14), missing 0, .noSlot,
     .same (tyOf .empty BoxFSrc) (spent 17), .same (tyOf .empty BoxFSrc) (spent 17),
     .same (tyOf .empty BoxFSrc) (spent 17)] := by
  decide +kernel

/-- AnyAsc under each erasure.  `C` and `G` also erase the domain of `g`'s
lambda, which reads the written `any`, so the fill is another one. -/
theorem AnyAsc_erased : row πc AnyAscSrc =
    [.same (tyOf πc AnyAscSrc) (spent 22), missing 0, .noSlot,
     .same (tyOf πc AnyAscSrc) (spent 26), .other (tyOf πc AnyAscSrc) (spent 26),
     .other (tyOf πc AnyAscSrc) (spent 26)] := by
  decide +kernel

/-- Fits under each erasure. -/
theorem Fits_erased : row πc FitsSrc =
    [.same (tyOf πc FitsSrc) (spent 16), missing 0, .noSlot,
     .same (tyOf πc FitsSrc) (spent 20), .same (tyOf πc FitsSrc) (spent 20),
     .same (tyOf πc FitsSrc) (spent 20)] := by
  decide +kernel

/-- TooBig under each erasure.  The closure is too large for the pure
formal, written or not. -/
theorem TooBig_erased : row πc TooBigSrc =
    [.no .mismatch (spent 20), missing 0, .noSlot, .no .mismatch (spent 36),
     .no .mismatch (spent 36), .no .mismatch (spent 36)] := by
  decide +kernel

/-- A callee body under each erasure.  `D` erases the outer domain too. -/
theorem Callee_erased : LambdaRow .empty CalleeSrc (.same (tyOf .empty CalleeSrc) (spent 5)) := by
  decide +kernel

/-- A callee body at a formal written at `{any}`, under each erasure.  The
fill reads `any`, so it is another one at the written type. -/
theorem CalleeAny_erased : row .empty CalleeAnySrc =
    [.same (tyOf .empty CalleeAnySrc) (spent 18),
     .other (tyOf .empty CalleeAnySrc) (spent 19), .noSlot, .noSlot,
     .other (tyOf .empty CalleeAnySrc) (spent 18),
     .other (tyOf .empty CalleeAnySrc) (spent 18)] := by
  decide +kernel

/-- A callee body ascribed at `⊤`, under each erasure.  `C` and `G` take
`g`'s formal. -/
theorem CalleeTop_erased : row .empty CalleeTopSrc =
    [.same (tyOf .empty CalleeTopSrc) (spent 9), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty CalleeTopSrc) (spent 10),
     .same (tyOf .empty CalleeTopSrc) (spent 10)] := by
  decide +kernel

/-- A callee body passed as an argument, under each erasure. -/
theorem CalleeArg_erased : row .empty CalleeArgSrc =
    [.same (tyOf .empty CalleeArgSrc) (spent 12), missing 0, .noSlot,
     .same (tyOf .empty CalleeArgSrc) (spent 22),
     .same (tyOf .empty CalleeArgSrc) (spent 22),
     .same (tyOf .empty CalleeArgSrc) (spent 22)] := by
  decide +kernel

/-- CalleeOther under each erasure. -/
theorem CalleeOther_erased :
    LambdaRow .empty CalleeOtherSrc (.same (tyOf .empty CalleeOtherSrc) (spent 6)) := by
  decide +kernel

/-- CalleeInc under each erasure. -/
theorem CalleeInc_erased :
    LambdaRow .empty CalleeIncSrc (.same (tyOf .empty CalleeIncSrc) (spent 14)) := by
  decide +kernel

/-- LetArg under each erasure. -/
theorem LetArg_erased : LambdaRow .empty LetArgSrc (.same (tyOf .empty LetArgSrc) (spent 5)) := by
  decide +kernel

/-- Id0 under each erasure. -/
theorem Id0_erased : LambdaRow .empty Id0Src (.same (tyOf .empty Id0Src) (spent 2)) := by
  decide +kernel

/-- A `val` definition under each erasure.  The written type is the goal. -/
theorem Val_erased : row .empty ValSrc =
    [.same (tyOf .empty ValSrc) (spent 2), .same (tyOf .empty ValSrc) (spent 4), .noSlot,
     .noSlot, .same (tyOf .empty ValSrc) (spent 4), .same (tyOf .empty ValSrc) (spent 4)] := by
  decide +kernel

/-! ### Lambdas under an ascription

The ascription's type is the goal of the lambda.  Two function sides meet,
the larger domain being the one taken, and an alias is followed to its
function type.  A goal with no function part is a missing parameter type, a
goal that only bounds a function type from above a type mismatch.  Two sides
with incomparable domains are a type mismatch, where the compiler forms a
union the version does not have. -/

/-- `process` ascribed at its own type, under each erasure.  The fill holds
the goal's domain, its `any` read at the arrow's binder, where the written
program holds `any`. -/
theorem W2asc_erased : row πc W2ascSrc =
    [.same (tyOf πc W2ascSrc) (spent 3), .other (tyOf πc W2ascSrc) (spent 3), .noSlot,
     .noSlot, .other (tyOf πc W2ascSrc) (spent 3), .other (tyOf πc W2ascSrc) (spent 3)] := by
  decide +kernel

/-- Two function sides of one domain, under each erasure. -/
theorem AndSame_erased : row .empty AndSameSrc =
    [.same (tyOf .empty AndSameSrc) (spent 34), .same (tyOf .empty AndSameSrc) (spent 34),
     .noSlot, .noSlot, .same (tyOf .empty AndSameSrc) (spent 34),
     .same (tyOf .empty AndSameSrc) (spent 34)] := by
  decide +kernel

/-- X3 under each erasure.  `C` and `G` compile, where Scala rejects. -/
theorem X3_erased : row .empty X3Src =
    [.same (tyOf .empty X3Src) (spent 40), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty X3Src) (spent 41), .same (tyOf .empty X3Src) (spent 41)] := by
  decide +kernel

/-- Two function sides with comparable domains, under each erasure.  The
larger domain is taken. -/
theorem AndTwo_erased : row .empty AndTwoSrc =
    [.same (tyOf .empty AndTwoSrc) (spent 34), .same (tyOf .empty AndTwoSrc) (spent 38),
     .noSlot, .noSlot, .same (tyOf .empty AndTwoSrc) (spent 38),
     .same (tyOf .empty AndTwoSrc) (spent 38)] := by
  decide +kernel

/-- Two function sides whose results the lambda does not meet, under each
erasure. -/
theorem AndRes_erased : row .empty AndResSrc =
    [.no .mismatch (spent 31), .no .mismatch (spent 35), .noSlot, .noSlot,
     .no .mismatch (spent 35), .no .mismatch (spent 35)] := by
  decide +kernel

/-- Two function sides with incomparable domains, under each erasure.  The
sides do not meet, a type mismatch. -/
theorem AndInc_erased : row .empty AndIncSrc =
    [.same (tyOf .empty AndIncSrc) (spent 56), .no .mismatch (spent 4), .noSlot, .noSlot,
     .no .mismatch (spent 4), .no .mismatch (spent 4)] := by
  decide +kernel

/-- One function side and a field the lambda lacks, under each erasure. -/
theorem AndOne_erased : row .empty AndOneSrc =
    [.no .mismatch (spent 12), .no .mismatch (spent 12), .noSlot, .noSlot,
     .no .mismatch (spent 12), .no .mismatch (spent 12)] := by
  decide +kernel

/-- AndTop under each erasure. -/
theorem AndTop_erased : row .empty AndTopSrc =
    [.same (tyOf .empty AndTopSrc) (spent 12), .same (tyOf .empty AndTopSrc) (spent 12),
     .noSlot, .noSlot, .same (tyOf .empty AndTopSrc) (spent 12),
     .same (tyOf .empty AndTopSrc) (spent 12)] := by
  decide +kernel

/-- Asc under each erasure. -/
theorem Asc_erased : row .empty AscSrc =
    [.same (tyOf .empty AscSrc) (spent 2), .same (tyOf .empty AscSrc) (spent 2), .noSlot,
     .noSlot, .same (tyOf .empty AscSrc) (spent 2), .same (tyOf .empty AscSrc) (spent 2)] := by
  decide +kernel

/-- Alias under each erasure. -/
theorem Alias_erased : row .empty AliasSrc =
    [.same (tyOf .empty AliasSrc) (spent 11), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty AliasSrc) (spent 12), .same (tyOf .empty AliasSrc) (spent 12)] := by
  decide +kernel

/-- Alias2 under each erasure. -/
theorem Alias2_erased : row .empty Alias2Src =
    [.same (tyOf .empty Alias2Src) (spent 17), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty Alias2Src) (spent 19), .same (tyOf .empty Alias2Src) (spent 19)] := by
  decide +kernel

/-- A goal with a function upper bound only, under each erasure.  The lambda
is not below it. -/
theorem Upper_erased : row .empty UpperSrc =
    [.no .mismatch (spent 7), missing 0, .noSlot, .noSlot, .no .mismatch (spent 1),
     .no .mismatch (spent 1)] := by
  decide +kernel

/-- A goal with a function lower bound only, under each erasure.  It has no
function part. -/
theorem Lower_erased : row .empty LowerSrc =
    [.same (tyOf .empty LowerSrc) (spent 11), missing 0, .noSlot, .noSlot, missing 1,
     missing 1] := by
  decide +kernel

/-- A goal whose alias comes back to itself, under each erasure. -/
theorem Loop_erased : row .empty LoopSrc =
    [.no .mismatch (spent 12), missing 0, .noSlot, .noSlot, missing 3, missing 3] := by
  decide +kernel

/-- A lambda ascribed at `⊤`, under each erasure. -/
theorem IdTop_erased : row .empty IdTopSrc =
    [.same (tyOf .empty IdTopSrc) (spent 6), missing 0, .noSlot, .noSlot, missing 0,
     missing 0] := by
  decide +kernel

/-- Curry under each erasure. -/
theorem Curry_erased : row .empty CurrySrc =
    [.same (tyOf .empty CurrySrc) (spent 3), .same (tyOf .empty CurrySrc) (spent 3),
     .noSlot, .noSlot, .same (tyOf .empty CurrySrc) (spent 3),
     .same (tyOf .empty CurrySrc) (spent 3)] := by
  decide +kernel

/-- SideCurry under each erasure. -/
theorem SideCurry_erased : row .empty SideCurrySrc =
    [.same (tyOf .empty SideCurrySrc) (spent 13),
     .same (tyOf .empty SideCurrySrc) (spent 14), .noSlot, .noSlot,
     .same (tyOf .empty SideCurrySrc) (spent 14),
     .same (tyOf .empty SideCurrySrc) (spent 14)] := by
  decide +kernel

/-- LetBody under each erasure. -/
theorem LetBody_erased : row .empty LetBodySrc =
    [.same (tyOf .empty LetBodySrc) (spent 3), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty LetBodySrc) (spent 3), .same (tyOf .empty LetBodySrc) (spent 3)] := by
  decide +kernel

/-- Block under each erasure. -/
theorem Block_erased : row .empty BlockSrc =
    [.same (tyOf .empty BlockSrc) (spent 3), missing 0, .noSlot, .noSlot,
     .same (tyOf .empty BlockSrc) (spent 3), .same (tyOf .empty BlockSrc) (spent 3)] := by
  decide +kernel

/-- Cap under each erasure. -/
theorem Cap_erased : row πc CapSrc =
    [.same (tyOf πc CapSrc) (spent 4), missing 0, .noSlot, .noSlot,
     .same (tyOf πc CapSrc) (spent 4), .same (tyOf πc CapSrc) (spent 4)] := by
  decide +kernel

/-- A closure over `f` ascribed at a pure type, under each erasure.  The typer
rejects the fill with no reason of its own.  Its reason search reaches the
certificate builder, which reads the well-founded `Ctx.caps`, so the kernel
checks the cells of `D`, `S` and `A`, and `#eval expect` the whole row. -/
theorem CapPure_erased : cell .D πc CapPureSrc = missing 0 ∧ cell .S πc CapPureSrc = .noSlot ∧
    cell .A πc CapPureSrc = .noSlot := by
  decide +kernel
#eval expect (row πc CapPureSrc == [.no .mismatch (spent 14), missing 0, .noSlot, .noSlot,
    .no .mismatch (spent 14), .no .mismatch (spent 14)])
  "CapPure: the row differs"

/-- A lambda ascribed at a type with `any` below a field of its domain,
under each erasure.  Every cell is the typer's `anyNotOk`. -/
theorem DeepAsc_erased : row .empty DeepAscSrc =
    [.no (.landed "anyNotOk") (spent 0), .no (.landed "anyNotOk") (spent 0), .noSlot,
     .noSlot, .no (.landed "anyNotOk") (spent 0), .no (.landed "anyNotOk") (spent 0)] := by
  decide +kernel

/-! ### Literals

A literal without a self shape at a `μ` goal takes the goal's shape, and
otherwise forms its self shape from its definitions in rounds.  A field reached
again while it is typed is a cyclic reference, and a field whose types have no
least one is ambiguous. -/

/-- A field closure under a written self shape, under each erasure. -/
theorem Fld_erased : row πc FldSrc =
    [.same (tyOf πc FldSrc) (spent 5), missing 0, .same (tyOf πc FldSrc) (spent 8),
     .noSlot, .same (tyOf πc FldSrc) (spent 8), .same (tyOf πc FldSrc) (spent 8)] := by
  decide +kernel

/-- A literal whose field has no written type, under each erasure.  `S` and
`G` give `NoShapeSrcS` of `Elab.lean`, a literal with no self shape and no
goal, which forms the written shape. -/
theorem FldTy_erased : row .empty FldTySrc =
    [.same (tyOf .empty FldTySrc) (spent 3), .same (tyOf .empty FldTySrc) (spent 5),
     .same (tyOf .empty FldTySrc) (spent 4), .noSlot,
     .same (tyOf .empty FldTySrc) (spent 5), .same (tyOf .empty FldTySrc) (spent 4)] := by
  decide +kernel

/-- A literal ascribed at a `μ`, under each erasure.  `S` and `G` take the
`μ` as the self shape. -/
theorem AscObj_erased : row .empty AscObjSrc =
    [.same (tyOf .empty AscObjSrc) (spent 3), missing 0,
     .same (tyOf .empty AscObjSrc) (spent 3), .noSlot, .noSlot,
     .same (tyOf .empty AscObjSrc) (spent 3)] := by
  decide +kernel

/-- A literal ascribed at a `μ` whose field is larger than the right-hand
side's type, under each erasure. -/
theorem AscWide_erased : row .empty AscWideSrc =
    [.same (tyOf .empty AscWideSrc) (spent 5), missing 0,
     .same (tyOf .empty AscWideSrc) (spent 5), .noSlot, .noSlot,
     .same (tyOf .empty AscWideSrc) (spent 5)] := by
  decide +kernel

/-- Nest under each erasure.  `S` and `G` erase both self shapes, so the
inner literal has no `μ` goal and forms its shape, which `NestSrcW` writes. -/
theorem Nest_erased : row .empty NestSrc =
    [.same (tyOf .empty NestSrc) (spent 6), missing 0,
     .other (tyOf .empty NestSrcW) (spent 6), .noSlot, .noSlot,
     .other (tyOf .empty NestSrcW) (spent 6)] := by
  decide +kernel

/-- A field that reads a later field, under each erasure. -/
theorem Fwd_erased : row .empty FwdObjSrc =
    [.same (tyOf .empty FwdObjSrc) (spent 12), .same (tyOf .empty FwdObjSrc) (spent 14),
     .same (tyOf .empty FwdObjSrc) (spent 16), .noSlot,
     .same (tyOf .empty FwdObjSrc) (spent 14), .same (tyOf .empty FwdObjSrc) (spent 16)] := by
  decide +kernel

/-- A field that holds a capability, under each erasure. -/
theorem Cap1_erased : row πc Cap1Src =
    [.same (tyOf πc Cap1Src) (spent 10), missing 0, .same (tyOf πc Cap1Src) (spent 10),
     .noSlot, .noSlot, .same (tyOf πc Cap1Src) (spent 10)] := by
  decide +kernel

/-- SelfProj under each erasure.  The written self shape charges `a` at
`{z}`, which the typer rejects.  `S` and `G` form `{z, f}` and compile.  `C`
keeps the written shape and is rejected with it. -/
theorem SelfProj_erased : row πc SelfProjSrc =
    [.no .mismatch (spent 36), missing 0, .other (tyOf πc SelfProjSrcF) (spent 44),
     .noSlot, .no .mismatch (spent 47), .other (tyOf πc SelfProjSrcF) (spent 44)] := by
  decide +kernel

/-- A recursive field, under each erasure.  `S` and `G` are a cyclic
reference at `a`. -/
theorem Rec_erased : row .empty RecObjSrc =
    [.same (tyOf .empty RecObjSrc) (spent 7), .same (tyOf .empty RecObjSrc) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0), .noSlot,
     .same (tyOf .empty RecObjSrc) (spent 13), .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that is the self, under each erasure. -/
theorem Bare_erased : row .empty BareSrc =
    [.same (tyOf .empty BareSrc) (spent 15), .noSlot,
     .same (tyOf .empty BareSrc) (spent 15), .noSlot, .noSlot,
     .same (tyOf .empty BareSrc) (spent 15)] := by
  decide +kernel

/-- BareCap under each erasure.  `S` and `G` form `b` at the snapshot that
knows `a`. -/
theorem BareCap_erased : row πc BareCapSrc =
    [.same (tyOf πc BareCapSrc) (spent 38), missing 0,
     .other (tyOf πc BareCapSrcF) (spent 40), .noSlot, .noSlot,
     .other (tyOf πc BareCapSrcF) (spent 40)] := by
  decide +kernel

/-- LamCap under each erasure.  `S` and `G` form the written self shape. -/
theorem LamCap_erased : row πc LamCapSrc =
    [.same (tyOf πc LamCapSrc) (spent 54), missing 0,
     .same (tyOf πc LamCapSrc) (spent 68), .noSlot, .same (tyOf πc LamCapSrc) (spent 76),
     .same (tyOf πc LamCapSrc) (spent 68)] := by
  decide +kernel

/-- A field that reads a later field that is the self, under each erasure. -/
theorem FwdSelf_erased : row .empty FwdSelfSrc =
    [.same (tyOf .empty FwdSelfSrc) (spent 30), .noSlot,
     .same (tyOf .empty FwdSelfSrc) (spent 33), .noSlot, .noSlot,
     .same (tyOf .empty FwdSelfSrc) (spent 33)] := by
  decide +kernel

/-- A field that is the self and a later one that reads it, under each
erasure. -/
theorem BareProj_erased : row .empty BareProjSrc =
    [.same (tyOf .empty BareProjSrc) (spent 30), .noSlot,
     .same (tyOf .empty BareProjSrc) (spent 33), .noSlot, .noSlot,
     .same (tyOf .empty BareProjSrc) (spent 33)] := by
  decide +kernel

/-- A field with two types, one below the other, under each erasure.  `S`
and `G` take the least. -/
theorem AmbUse_erased : row .empty AmbUseSrc =
    [.same (tyOf .empty AmbUseSrc) (spent 18), missing 0,
     .same (tyOf .empty AmbUseSrc) (spent 33), .noSlot, .noSlot,
     .same (tyOf .empty AmbUseSrc) (spent 33)] := by
  decide +kernel

/-- The same two types in the other order, under each erasure. -/
theorem AmbUse2_erased : row .empty AmbUse2Src =
    [.same (tyOf .empty AmbUse2Src) (spent 18), missing 0,
     .same (tyOf .empty AmbUse2Src) (spent 28), .noSlot, .noSlot,
     .same (tyOf .empty AmbUse2Src) (spent 28)] := by
  decide +kernel

/-- A field with two incomparable types, under each erasure.  `S` and `G`
are ambiguous at `a`. -/
theorem Amb_erased : row .empty AmbSrc =
    [.same (tyOf .empty AmbSrc) (spent 12), missing 0,
     .no (.ambiguous (.trm 0)) (spent 15), .noSlot, .noSlot,
     .no (.ambiguous (.trm 0)) (spent 15)] := by
  decide +kernel

/-- The literal of E2 on its own, under each erasure. -/
theorem E2obj_erased : row .empty E2objSrc =
    [.same (tyOf .empty E2objSrc) (spent 3), .same (tyOf .empty E2objSrc) (spent 5),
     .same (tyOf .empty E2objSrc) (spent 4), .noSlot,
     .same (tyOf .empty E2objSrc) (spent 5), .same (tyOf .empty E2objSrc) (spent 4)] := by
  decide +kernel

/-- Two fields that read each other, under each erasure.  `S` and `G` are a
cyclic reference at `a`. -/
theorem Cyc_erased : row .empty CycSrc =
    [.same (tyOf .empty CycSrc) (spent 19), .noSlot, .no (.cyclicRef (.trm 0)) (spent 0),
     .noSlot, .noSlot, .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that reads a cycle of two later fields, under each erasure.  `S`
and `G` are a cyclic reference at `b`. -/
theorem Cyc3_erased : row πc Cyc3Src =
    [.same (tyOf πc Cyc3Src) (spent 52), .noSlot, .no (.cyclicRef (.trm 1)) (spent 0),
     .noSlot, .noSlot, .no (.cyclicRef (.trm 1)) (spent 0)] := by
  decide +kernel

/-- A recursive field read through an alias of the self, under each erasure.
`S` and `G` are a cyclic reference at `a`. -/
theorem AliasRec_erased : row .empty AliasRecSrc =
    [.same (tyOf .empty AliasRecSrc) (spent 7),
     .same (tyOf .empty AliasRecSrc) (spent 13), .no (.cyclicRef (.trm 0)) (spent 0),
     .noSlot, .same (tyOf .empty AliasRecSrc) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that is a lambda, under each erasure. -/
theorem NoDom_erased : row .empty NoDomSrc =
    [.same (tyOf .empty NoDomSrc) (spent 3), .same (tyOf .empty NoDomSrc) (spent 5),
     .same (tyOf .empty NoDomSrc) (spent 4), .noSlot,
     .same (tyOf .empty NoDomSrc) (spent 5), .same (tyOf .empty NoDomSrc) (spent 4)] := by
  decide +kernel

/-- The literal of `freshCell` on its own, written at the shape its
definitions form, under each erasure. -/
theorem Z1lit_erased : row πz Z1litF =
    [.same (tyOf πz Z1litF) (spent 3), .same (tyOf πz Z1litF) (spent 5),
     .same (tyOf πz Z1litF) (spent 4), .noSlot, .same (tyOf πz Z1litF) (spent 5),
     .same (tyOf πz Z1litF) (spent 4)] := by
  decide +kernel


/-! ### Erasures no column makes

Each pair is a written program and one erased form of it: the inner domain of
a callback written, the body of a callee or of a `let` with the outer domain
written, the inner self shape of Nest, a field type written in place of the
self shape, and the body of a `let` whose bound term has an existential
answer. -/

/-- `withFile` applied to its callback with the inner domain written.  The
callback's outer domain comes from the formal. -/
theorem S1callGu_pair : pair πz S1callSrc S1callSrcGu =
    [.same (tyOf πz S1callSrc) (spent 83), .same (tyOf πz S1callSrc) (spent 93)] := by
  decide +kernel

/-- A callee body with the outer domain written.  The body takes `g`'s
formal. -/
theorem Callee_pair : pair .empty CalleeSrc CalleeSrcD =
    [.same (tyOf .empty CalleeSrc) (spent 5), .same (tyOf .empty CalleeSrc) (spent 6)] := by
  decide +kernel

/-- A callee body at a formal written at `{any}`, `g`'s domain written.  The
fill reads `any`. -/
theorem CalleeAny_pair : pair .empty CalleeAnySrc CalleeAnySrcD =
    [.same (tyOf .empty CalleeAnySrc) (spent 18),
     .other (tyOf .empty CalleeAnySrc) (spent 19)] := by
  decide +kernel

/-- A body that calls `g` on another variable is no callee body. -/
theorem CalleeOther_pair : pair .empty CalleeOtherSrc CalleeOtherSrcD =
    [.same (tyOf .empty CalleeOtherSrc) (spent 6), missing 0] := by
  decide +kernel

/-- A callee at incomparable domains has no dominant formal. -/
theorem CalleeInc_pair : pair .empty CalleeIncSrc CalleeIncSrcD =
    [.same (tyOf .empty CalleeIncSrc) (spent 14), missing 9] := by
  decide +kernel

/-- A lambda bound by a written `let` and then passed has no goal, as Scala's
`val i = x => x`. -/
theorem LetArg_pair : pair .empty LetArgSrc LetArgSrcD =
    [.same (tyOf .empty LetArgSrc) (spent 5), missing 0] := by
  decide +kernel

/-- The inner self shape of Nest erased.  The field's written `μ` is the
goal. -/
theorem Nest_pair : pair .empty NestSrc NestSrcS =
    [.same (tyOf .empty NestSrc) (spent 6), .same (tyOf .empty NestSrc) (spent 10)] := by
  decide +kernel

/-- Seventeen literals nested, every self shape erased.  Each field is
elaborated once and checked once more at each enclosing literal. -/
theorem Nest16_pair : pair .empty (NestKSrc true 16) (NestKSrc false 16) =
    [.same (tyOf .empty (NestKSrc true 16)) (spent 19),
     .same (tyOf .empty (NestKSrc true 16)) (spent 171)] := by
  decide +kernel

/-- A recursive field with its type written in place of the self shape, the
domain erased and written. -/
theorem RecW_pair : pair .empty RecObjSrc RecWSrcS =
      [.same (tyOf .empty RecObjSrc) (spent 7), .same (tyOf .empty RecObjSrc) (spent 13)] ∧
    pair .empty RecObjSrc RecWdSrcS =
      [.same (tyOf .empty RecObjSrc) (spent 7), .same (tyOf .empty RecObjSrc) (spent 7)] := by
  decide +kernel

/-- A field type written under the written self shape, the domain erased. -/
theorem FldTyD_pair : pair .empty FldTySrc FldTySrcD =
    [.same (tyOf .empty FldTySrc) (spent 3), .same (tyOf .empty FldTySrc) (spent 5)] := by
  decide +kernel

/-- A field that is a lambda, with its self shape and its domain erased: no
goal reaches the lambda. -/
theorem NoDomDS_pair : pair .empty NoDomSrc NoDomSrcS =
    [.same (tyOf .empty NoDomSrc) (spent 3), missing 0] := by
  decide +kernel

/-- The body of a `let` whose bound term has an existential answer, its domain
erased.  The fill is an unpacking, which `PTm.fills` does not relate to the
written `let`, so `compileE` reports a mismatch where the elaborator types the
program. -/
theorem LetEx_pair : pair πz LetExSrc LetExSrcD = [.same (tyOf πz LetExSrc) (spent 20), .shape] ∧
    (elabOut πz LetExSrcD).1.isOk = true ∧ reasonAt {} πz LetExSrcD = some .mismatch := by
  decide +kernel

/-- The two programs with no written form: a field whose type names the class
root, and a field whose right-hand side unpacks a `fresh` result.  Each needs
a written type, which no written form can give. -/
theorem NE_open : openCell .empty NESrcS = .no (.needsExplicitType (.trm 0)) (spent 2) ∧
    openCell πz NEfreshSrcS = .no (.needsExplicitType (.trm 0)) (spent 24) := by
  decide +kernel


/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at every distinct erased program whose cell is `same` or
`other`, and at every pair that compiles.  The success is the premise, by
`decide +kernel`.  A program two erasures give alike is listed once, under
every erasure that gives it. -/

/-- The target checker accepts E2 under `D` and `C`. -/
theorem E2_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface E2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2 under `S` and `G`. -/
theorem E2_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface E2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E5 under `S` and `G`. -/
theorem E5_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface E5src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E6 under `S` and `G`. -/
theorem E6_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface E6srcW) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E7 under `S` and `G`. -/
theorem E7_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface E7src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C7 under `S` and `G`. -/
theorem C7_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface C7src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S3 under `S` and `G`. -/
theorem S3_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface S3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C2 under `S` and `G`. -/
theorem C2_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface C2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C2 under `C`. -/
theorem C2_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface C2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `S`. -/
theorem S1_S_checks :
    CheckerAccepts {} Λc πz (Erasure.S.surface S1progSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `C`. -/
theorem S1_C_checks :
    CheckerAccepts {} Λc πz (Erasure.C.surface S1progSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `G`. -/
theorem S1_G_checks :
    CheckerAccepts {} Λc πz (Erasure.G.surface S1progSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S2 under `S`. -/
theorem S2_S_checks :
    CheckerAccepts {} Λc πz (Erasure.S.surface S2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1 under `D` and `C`. -/
theorem Z1_D_checks :
    CheckerAccepts {} Λc πz (Erasure.D.surface Z1progSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1def under `D` and `C`. -/
theorem Z1def_D_checks :
    CheckerAccepts {} Λc πz (Erasure.D.surface Z1defSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z2 under `D` and `C`. -/
theorem Z2_D_checks :
    CheckerAccepts {} Λc πz (Erasure.D.surface Z2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `D` and `C`. -/
theorem Z3_D_checks :
    CheckerAccepts {} Λc πz (Erasure.D.surface Z3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `S`. -/
theorem Z3_S_checks :
    CheckerAccepts {} Λc πz (Erasure.S.surface Z3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `G`. -/
theorem Z3_G_checks :
    CheckerAccepts {} Λc πz (Erasure.G.surface Z3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts accounted under `S` and `G`. -/
theorem accounted_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface accountedSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts EscOk under `C` and `G`. -/
theorem EscOk_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface EscOkSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1call under `S`. -/
theorem S1call_S_checks :
    CheckerAccepts {} Λc πz (Erasure.S.surface S1callSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1call under `A`. -/
theorem S1call_A_checks :
    CheckerAccepts {} Λc πz (Erasure.A.surface S1callSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts K1 under `A`, `C` and `G`. -/
theorem K1_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface K1src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Kcap under `A`, `C` and `G`. -/
theorem Kcap_A_checks :
    CheckerAccepts {} Λc πc (Erasure.A.surface KcapSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X1 under `A`, `C` and `G`. -/
theorem X1_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface X1Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Dom under `A`, `C` and `G`. -/
theorem Dom_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface DomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BlockArg under `C` and `G`. -/
theorem BlockArg_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface BlockArgSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curried under `A`. -/
theorem Curried_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface CurriedSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curried under `C` and `G`. -/
theorem Curried_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface CurriedSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BoxCallee under `A`, `C` and `G`. -/
theorem BoxCallee_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface BoxCalleeSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BoxF under `A`, `C` and `G`. -/
theorem BoxF_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface BoxFSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AnyAsc under `A`. -/
theorem AnyAsc_A_checks :
    CheckerAccepts {} Λc πc (Erasure.A.surface AnyAscSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AnyAsc under `C` and `G`. -/
theorem AnyAsc_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface AnyAscSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fits under `A`, `C` and `G`. -/
theorem Fits_A_checks :
    CheckerAccepts {} Λc πc (Erasure.A.surface FitsSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeAny under `D`. -/
theorem CalleeAny_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface CalleeAnySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeAny under `C` and `G`. -/
theorem CalleeAny_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface CalleeAnySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeTop under `C` and `G`. -/
theorem CalleeTop_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface CalleeTopSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeArg under `A`, `C` and `G`. -/
theorem CalleeArg_A_checks :
    CheckerAccepts {} Λc .empty (Erasure.A.surface CalleeArgSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Val under `D`, `C` and `G`. -/
theorem Val_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface ValSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts W2asc under `D`, `C` and `G`. -/
theorem W2asc_D_checks :
    CheckerAccepts {} Λc πc (Erasure.D.surface W2ascSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndSame under `D`, `C` and `G`. -/
theorem AndSame_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AndSameSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X3 under `C` and `G`. -/
theorem X3_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface X3Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndTwo under `D`, `C` and `G`. -/
theorem AndTwo_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AndTwoSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndTop under `D`, `C` and `G`. -/
theorem AndTop_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AndTopSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Asc under `D`, `C` and `G`. -/
theorem Asc_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AscSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Alias under `C` and `G`. -/
theorem Alias_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface AliasSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Alias2 under `C` and `G`. -/
theorem Alias2_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface Alias2Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curry under `D`, `C` and `G`. -/
theorem Curry_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface CurrySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts SideCurry under `D`, `C` and `G`. -/
theorem SideCurry_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface SideCurrySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LetBody under `C` and `G`. -/
theorem LetBody_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface LetBodySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Block under `C` and `G`. -/
theorem Block_C_checks :
    CheckerAccepts {} Λc .empty (Erasure.C.surface BlockSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Cap under `C` and `G`. -/
theorem Cap_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface CapSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fld under `S` and `G`. -/
theorem Fld_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface FldSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fld under `C`. -/
theorem Fld_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface FldSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FldTy under `D` and `C`. -/
theorem FldTy_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface FldTySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FldTy under `S` and `G`. -/
theorem FldTy_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface FldTySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AscObj under `S` and `G`. -/
theorem AscObj_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface AscObjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AscWide under `S` and `G`. -/
theorem AscWide_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface AscWideSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Nest under `S` and `G`. -/
theorem Nest_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface NestSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fwd under `D` and `C`. -/
theorem Fwd_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface FwdObjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fwd under `S` and `G`. -/
theorem Fwd_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface FwdObjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Cap1 under `S` and `G`. -/
theorem Cap1_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface Cap1Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts SelfProj under `S` and `G`. -/
theorem SelfProj_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface SelfProjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Rec under `D` and `C`. -/
theorem Rec_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface RecObjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Bare under `S` and `G`. -/
theorem Bare_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface BareSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BareCap under `S` and `G`. -/
theorem BareCap_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface BareCapSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LamCap under `S` and `G`. -/
theorem LamCap_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface LamCapSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LamCap under `C`. -/
theorem LamCap_C_checks :
    CheckerAccepts {} Λc πc (Erasure.C.surface LamCapSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FwdSelf under `S` and `G`. -/
theorem FwdSelf_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface FwdSelfSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BareProj under `S` and `G`. -/
theorem BareProj_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface BareProjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AmbUse under `S` and `G`. -/
theorem AmbUse_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface AmbUseSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AmbUse2 under `S` and `G`. -/
theorem AmbUse2_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface AmbUse2Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2obj under `D` and `C`. -/
theorem E2obj_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface E2objSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2obj under `S` and `G`. -/
theorem E2obj_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface E2objSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AliasRec under `D` and `C`. -/
theorem AliasRec_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AliasRecSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts NoDom under `D` and `C`. -/
theorem NoDom_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts NoDom under `S` and `G`. -/
theorem NoDom_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1lit under `D` and `C`. -/
theorem Z1lit_D_checks :
    CheckerAccepts {} Λc πz (Erasure.D.surface Z1litF) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1lit under `S` and `G`. -/
theorem Z1lit_S_checks :
    CheckerAccepts {} Λc πz (Erasure.S.surface Z1litF) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts `withFile` applied to its callback with the
inner domain written. -/
theorem S1callGu_pair_checks : CheckerAccepts {} Λc πz S1callSrcGu (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts a callee body with the outer domain written. -/
theorem Callee_pair_checks : CheckerAccepts {} Λc .empty CalleeSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts a callee body at a formal written at
`{any}`. -/
theorem CalleeAny_pair_checks : CheckerAccepts {} Λc .empty CalleeAnySrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Nest with the inner self shape erased. -/
theorem Nest_pair_checks : CheckerAccepts {} Λc .empty NestSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts seventeen nested literals with no self
shape. -/
theorem Nest16_pair_checks :
    CheckerAccepts {} Λc .empty (NestKSrc false 16) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the recursive field with its type written in
place of the self shape. -/
theorem RecW_pair_checks : CheckerAccepts {} Λc .empty RecWSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The same with the domain written. -/
theorem RecWd_pair_checks : CheckerAccepts {} Λc .empty RecWdSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts a field type written under the written self
shape. -/
theorem FldTyD_pair_checks : CheckerAccepts {} Λc .empty FldTySrcD (by decide +kernel) :=
  compile_checks_get _


/-! ### Rejections with the compiler's reason

Each states `RejectedWith` at a cell the kernel computes: no result at any
budget, and the reason `compileE` reports.  A reason of inference is the
reason at every budget from `defaultFuel` up (`RejectedAbove`).  The escapes
fail at every budget by the elaborator's own verdict, and their reason, the
typer's level escape on the fill, is checked by `#eval expect` at the goal the
typer reached. -/

/-- E1 with its domains erased: no goal reaches the outer lambda, as for
every program whose outermost term is a lambda. -/
theorem E1_D_rejected : RejectedAbove .empty (Erasure.D.surface E1src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty E1src (Erasure.D.surface E1src) = missing 0) rfl

/-- S1 with every domain erased: the lambda bound to `op` by a `let` with no
type has no goal. -/
theorem S1_D_rejected : RejectedAbove πz (Erasure.D.surface S1progSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S1progSrc (Erasure.D.surface S1progSrc) = missing 28) rfl

/-- S2 with every domain erased. -/
theorem S2_D_rejected : RejectedAbove πz (Erasure.D.surface S2src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S2src (Erasure.D.surface S2src) = missing 96) rfl

/-- S2 with the domains in checked positions erased: `(λy. y : ⊤)` has a
goal with no function part. -/
theorem S2_C_rejected : RejectedAbove πz (Erasure.C.surface S2src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S2src (Erasure.C.surface S2src) = missing 96) rfl

/-- S2 as a Scala programmer writes it, rejected at the same lambda. -/
theorem S2_G_rejected : RejectedAbove πz (Erasure.G.surface S2src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S2src (Erasure.G.surface S2src) = missing 143) rfl

/-- exTop with every domain erased: the argument bound to `un` by a written
`let` has no goal. -/
theorem exTop_D_rejected : RejectedAbove πz (Erasure.D.surface exTopSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz exTopSrc (Erasure.D.surface exTopSrc) = missing 14) rfl

/-- `withFile` applied to its callback with both domains erased: the inner
lambda's goal is the formal's result `⊤`. -/
theorem S1call_C_rejected :
    RejectedAbove πz (Erasure.C.surface S1callSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S1callSrc (Erasure.C.surface S1callSrc) = missing 54) rfl

/-- The same with every self shape erased too. -/
theorem S1call_G_rejected :
    RejectedAbove πz (Erasure.G.surface S1callSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πz S1callSrc (Erasure.G.surface S1callSrc) = missing 63) rfl

/-- A callee whose two formals are incomparable: no formal dominates. -/
theorem Inc_A_rejected : RejectedAbove .empty (Erasure.A.surface IncSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty IncSrc (Erasure.A.surface IncSrc) = missing 17) rfl

/-- A callee with no function type. -/
theorem NoFn_A_rejected :
    RejectedAbove .empty (Erasure.A.surface NoFnSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty NoFnSrc (Erasure.A.surface NoFnSrc) = missing 2) rfl

/-- A lambda bound by a `let` with no type. -/
theorem Id0_D_rejected : RejectedAbove .empty (Erasure.D.surface Id0Src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty Id0Src (Erasure.D.surface Id0Src) = missing 0) rfl

/-- A lambda ascribed at `⊤`, which has no function part. -/
theorem IdTop_C_rejected :
    RejectedAbove .empty (Erasure.C.surface IdTopSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty IdTopSrc (Erasure.C.surface IdTopSrc) = missing 0) rfl

/-- A goal that bounds a function type from below only. -/
theorem Lower_C_rejected :
    RejectedAbove .empty (Erasure.C.surface LowerSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty LowerSrc (Erasure.C.surface LowerSrc) = missing 1) rfl

/-- A goal whose alias comes back to itself. -/
theorem Loop_C_rejected :
    RejectedAbove .empty (Erasure.C.surface LoopSrc) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty LoopSrc (Erasure.C.surface LoopSrc) = missing 3) rfl

/-- A lambda bound by a written `let` and then passed: the `let` is no call
argument. -/
theorem LetArg_pair_rejected : RejectedAbove .empty LetArgSrcD (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty LetArgSrc LetArgSrcD = missing 0) rfl

/-- A body that calls `g` on another variable. -/
theorem CalleeOther_pair_rejected : RejectedAbove .empty CalleeOtherSrcD (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty CalleeOtherSrc CalleeOtherSrcD = missing 0) rfl

/-- A callee body at incomparable domains. -/
theorem CalleeInc_pair_rejected : RejectedAbove .empty CalleeIncSrcD (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty CalleeIncSrc CalleeIncSrcD = missing 9) rfl

/-- A field that is a lambda, in a literal without a self shape and with no
goal. -/
theorem NoDomDS_pair_rejected : RejectedAbove .empty NoDomSrcS (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty NoDomSrc NoDomSrcS = missing 0) rfl

/-- Two fields that read each other: a cyclic reference at `a`. -/
theorem Cyc_S_rejected : RejectedAbove .empty (Erasure.S.surface CycSrc) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty CycSrc (Erasure.S.surface CycSrc) = .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A recursive field without a written type: a cyclic reference at `a`. -/
theorem Rec_S_rejected : RejectedAbove .empty (Erasure.S.surface RecObjSrc) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty RecObjSrc (Erasure.S.surface RecObjSrc) =
      .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A recursive field read through an alias of the self: a cyclic reference
at `a`. -/
theorem AliasRec_S_rejected :
    RejectedAbove .empty (Erasure.S.surface AliasRecSrc) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty AliasRecSrc (Erasure.S.surface AliasRecSrc) =
      .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A field that reads a cycle of two later fields: a cyclic reference at
`b`, the member the walk from `a` reaches twice. -/
theorem Cyc3_S_rejected : RejectedAbove πc (Erasure.S.surface Cyc3Src) (.cyclicRef (.trm 1)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell πc Cyc3Src (Erasure.S.surface Cyc3Src) = .no (.cyclicRef (.trm 1)) (spent 0)) rfl

/-- A field whose two types are incomparable: no least one. -/
theorem Amb_S_rejected : RejectedAbove .empty (Erasure.S.surface AmbSrc) (.ambiguous (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell .empty AmbSrc (Erasure.S.surface AmbSrc) = .no (.ambiguous (.trm 0)) (spent 15)) rfl

/-- A field whose type names the class root needs a written type. -/
theorem NE_rejected :
    RejectedAbove .empty NESrcS (.needsExplicitType (.trm 0)) :=
  openCell_slot (by decide +kernel :
    openCell .empty NESrcS = .no (.needsExplicitType (.trm 0)) (spent 2)) rfl

/-- A field whose right-hand side unpacks a `fresh` result needs a written
type. -/
theorem NEfresh_rejected :
    RejectedAbove πz NEfreshSrcS (.needsExplicitType (.trm 0)) :=
  openCell_slot (by decide +kernel :
    openCell πz NEfreshSrcS = .no (.needsExplicitType (.trm 0)) (spent 24)) rfl

/-- Two function sides with incomparable domains: a type mismatch, where the
compiler forms the union of the domains. -/
theorem AndInc_D_rejected : RejectedWith .empty (Erasure.D.surface AndIncSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell .empty AndIncSrc (Erasure.D.surface AndIncSrc) = .no .mismatch (spent 4))

/-- One function side and a field the lambda lacks. -/
theorem AndOne_D_rejected : RejectedWith .empty (Erasure.D.surface AndOneSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell .empty AndOneSrc (Erasure.D.surface AndOneSrc) = .no .mismatch (spent 12))

/-- Two function sides whose results the lambda does not meet. -/
theorem AndRes_D_rejected : RejectedWith .empty (Erasure.D.surface AndResSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell .empty AndResSrc (Erasure.D.surface AndResSrc) = .no .mismatch (spent 35))

/-- A goal that bounds a function type from above only. -/
theorem Upper_C_rejected : RejectedWith .empty (Erasure.C.surface UpperSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell .empty UpperSrc (Erasure.C.surface UpperSrc) = .no .mismatch (spent 1))

/-- A closure over `f` at a pure formal. -/
theorem TooBig_A_rejected : RejectedWith πc (Erasure.A.surface TooBigSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πc TooBigSrc (Erasure.A.surface TooBigSrc) = .no .mismatch (spent 36))

/-- A closure over `f` ascribed at a pure type.  The elaborator fails with the
tank unmarked, so no budget compiles it.  The reason, a mismatch, is checked
with the row. -/
theorem CapPure_C_rejected (b : Budget) :
    (compile b Λc πc (Erasure.C.surface CapPureSrc)).isOk = false :=
  elabOut_rejects (by decide +kernel :
    elabOut πc (Erasure.C.surface CapPureSrc) = (.no .mismatch, spent 14)) b

/-- C7 with its boxes written and its self shape erased: the formed box
holds `{f1}` where the written unboxing names `{k1}`. -/
theorem C7box_S_rejected : RejectedWith πc (Erasure.S.surface C7boxSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πc C7boxSrc (Erasure.S.surface C7boxSrc) = .no .mismatch (spent 13))

/-- `freshCell` with its self shape erased: the formed `read` is pure, and
no rule relates the formed `μ` to the written one. -/
theorem Z1_S_rejected : RejectedWith πz (Erasure.S.surface Z1progSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz Z1progSrc (Erasure.S.surface Z1progSrc) = .no .mismatch (spent 62))

/-- The same in a `let` with a written type. -/
theorem Z1def_S_rejected : RejectedWith πz (Erasure.S.surface Z1defSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz Z1defSrc (Erasure.S.surface Z1defSrc) = .no .mismatch (spent 112))

/-- The same in `makeLogger`. -/
theorem Z2_S_rejected : RejectedWith πz (Erasure.S.surface Z2src) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz Z2src (Erasure.S.surface Z2src) = .no .mismatch (spent 62))

/-- The same in exTop. -/
theorem exTop_S_rejected : RejectedWith πz (Erasure.S.surface exTopSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz exTopSrc (Erasure.S.surface exTopSrc) = .no .mismatch (spent 62))

/-- The same in the `let` whose bound term has an existential answer. -/
theorem LetEx_S_rejected : RejectedWith πz (Erasure.S.surface LetExSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz LetExSrc (Erasure.S.surface LetExSrc) = .no .mismatch (spent 62))

/-- SelfProj with the field's domain erased: the written self shape charges
`a` at `{z}`, as the written program, which the typer rejects. -/
theorem SelfProj_C_rejected : RejectedWith πc (Erasure.C.surface SelfProjSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πc SelfProjSrc (Erasure.C.surface SelfProjSrc) = .no .mismatch (spent 47))

/-- exTop with the domains in checked positions erased: the typer rejects
the existential answer outside every scope, as on the written program. -/
theorem exTop_C_rejected :
    RejectedWith πz (Erasure.C.surface exTopSrc) (.landed "existentialAtTop") :=
  erasedCell_rejected (by decide +kernel :
    erasedCell πz exTopSrc (Erasure.C.surface exTopSrc) =
      .no (.landed "existentialAtTop") (spent 21))

/-- A lambda ascribed at a type with `any` below a field of its domain: the
typer's `anyNotOk`. -/
theorem DeepAsc_D_rejected :
    RejectedWith .empty (Erasure.D.surface DeepAscSrc) (.landed "anyNotOk") :=
  erasedCell_rejected (by decide +kernel :
    erasedCell .empty DeepAscSrc (Erasure.D.surface DeepAscSrc) =
      .no (.landed "anyNotOk") (spent 0))

/-- The escape with its callback's domains erased, under `C` and `G`, which
give one program.  The elaborator fails with the tank unmarked, so no budget
compiles it. -/
theorem Esc_C_rejected (b : Budget) : (compile b Λc πc (Erasure.C.surface EscSrc)).isOk = false :=
  elabOut_rejects (by decide +kernel :
    elabOut πc (Erasure.C.surface EscSrc) = (.no .mismatch, spent 63)) b

/-- The escape by an ascription with its callback's domains erased, under `C`
and `G`. -/
theorem AscEsc_C_rejected (b : Budget) :
    (compile b Λc πc (Erasure.C.surface AscEscSrc)).isOk = false :=
  elabOut_rejects (by decide +kernel :
    elabOut πc (Erasure.C.surface AscEscSrc) = (.no .mismatch, spent 63)) b

/-- The escape at the top with its callback's domains erased, under `D`, `C`
and `G`. -/
theorem TopEsc_C_rejected (b : Budget) :
    (compile b Λc πc (Erasure.C.surface TopEscSrc)).isOk = false :=
  elabOut_rejects (by decide +kernel :
    elabOut πc (Erasure.C.surface TopEscSrc) = (.no .mismatch, spent 63)) b

-- The reason is the typer's escape on the fill, at the goal the typer reaches
-- on the written program, with the same certificate.
#eval expect (escapesAt (compile {} Λc πc (Erasure.C.surface EscSrc)) EscGoalCtx
    [CapAtom.var .here] [CapAtom.cvar escRoot])
  "the escape under C: not rejected at the goal in EscGoalCtx"

#eval expect ((compile {} Λc πc (Erasure.C.surface AscEscSrc)).reason?.map Reason.name ==
    some "levelEscape")
  "the escape by an ascription under C: not rejected with the escape"

#eval expect (escapesAt (compile {} Λc πc (Erasure.C.surface TopEscSrc)) TopGoalCtx
    [CapAtom.var .here] topPlat)
  "the escape at the top under C: not rejected at the goal in TopGoalCtx"

end Erasures

/-! ## Completeness at the direct sites

`compile_complete_canonAt` at the erased programs of the tables whose empty
slots sit at direct sites.  Each theorem says that the erased program compiles
as the written one does, fill, term, use set, type and derivation, at every
budget from some fuel on.  `canonAt` decides its premises, with every reading
of a goal and every run of the typer taken at `defaultFuel`, and the kernel
checks it.  The fill is the written program in every case.  A theorem is named
after the first erasure that gives its program, and its docstring names every
erasure that gives the same program.

The erased programs that compile and are no such case are a lambda whose body
has an empty slot at an intersection with a function side, a literal whose
self shape the rounds form, a literal written in a field whose outer literal
has no self shape either, and a program whose fill reads the `any` of its goal,
which is no written program.  A program at a call argument closes the section.
The elaborator rejects it, though the typer accepts its fill, which is the
written program. -/

section Complete

/-- The erased program `e` compiles as the written program `w` does, at every
budget from some fuel on. -/
def CompilesAs (π : PlatformNames) (e w : STm) : Prop :=
  ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λc π e = compile b Λc π w

/-! ### Call arguments

The dominant formal of the callee gives the domain. -/

/-- S1 with the domain of its callback erased. -/
theorem S1call_A_complete : CompilesAs πz (Erasure.A.surface S1callSrc) S1callSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda passed to a callee whose parameter type is written, under `A`, `C`
and `G`. -/
theorem K1_A_complete : CompilesAs .empty (Erasure.A.surface K1src) K1src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callback whose parameter captures a platform capability, under `A`, `C`
and `G`. -/
theorem Kcap_A_complete : CompilesAs πc (Erasure.A.surface KcapSrc) KcapSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An intersection callee whose formals agree on their domain, under `A`, `C`
and `G`. -/
theorem X1_A_complete : CompilesAs .empty (Erasure.A.surface X1Src) X1Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An intersection callee whose formals have comparable domains, under `A`,
`C` and `G`. -/
theorem Dom_A_complete : CompilesAs .empty (Erasure.A.surface DomSrc) DomSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda passed as an argument, its outer domain erased. -/
theorem Curried_A_complete : CompilesAs .empty (Erasure.A.surface CurriedSrc) CurriedSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with both domains erased, under `C` and `G`. -/
theorem Curried_C_complete : CompilesAs .empty (Erasure.C.surface CurriedSrc) CurriedSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A boxed callee, under `A`, `C` and `G`. -/
theorem BoxCallee_A_complete : CompilesAs .empty (Erasure.A.surface BoxCalleeSrc) BoxCalleeSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A boxed formal, under `A`, `C` and `G`. -/
theorem BoxF_A_complete : CompilesAs .empty (Erasure.A.surface BoxFSrc) BoxFSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee whose formal captures anything, and a closure over `f` as its
argument. -/
theorem AnyAsc_A_complete : CompilesAs πc (Erasure.A.surface AnyAscSrc) AnyAscSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over `f` at a formal that captures `f`, under `A`, `C` and `G`. -/
theorem Fits_A_complete : CompilesAs πc (Erasure.A.surface FitsSrc) FitsSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee body as a call argument at a formal with no function part, so
the callee of the body gives the domain, under `A`, `C` and `G`. -/
theorem CalleeArg_A_complete : CompilesAs .empty (Erasure.A.surface CalleeArgSrc) CalleeArgSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block as a call argument whose result is a lambda, under `C` and `G`. -/
theorem BlockArg_C_complete : CompilesAs .empty (Erasure.C.surface BlockArgSrc) BlockArgSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Ascriptions and written types

The written type gives the domain through its function part.  A written type
with no function part leaves it to the callee of a body `g x`. -/

/-- `let x : A = λy. y in x`, under `D`, `C` and `G`. -/
theorem Val_D_complete : CompilesAs .empty (Erasure.D.surface ValSrc) ValSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two function sides of one domain, under `D`, `C` and `G`. -/
theorem AndSame_D_complete : CompilesAs .empty (Erasure.D.surface AndSameSrc) AndSameSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two function sides with comparable domains, under `D`, `C` and `G`. -/
theorem AndTwo_D_complete : CompilesAs .empty (Erasure.D.surface AndTwoSrc) AndTwoSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A function side beside `⊤`, under `D`, `C` and `G`. -/
theorem AndTop_D_complete : CompilesAs .empty (Erasure.D.surface AndTopSrc) AndTopSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The identity ascribed `∀(x : ⊤) ⊤`, under `D`, `C` and `G`. -/
theorem Asc_D_complete : CompilesAs .empty (Erasure.D.surface AscSrc) AscSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda ascribed a curried function type, both domains erased,
under `D`, `C` and `G`. -/
theorem Curry_D_complete : CompilesAs .empty (Erasure.D.surface CurrySrc) CurrySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An ascription whose second side is a selection with a function lower
bound, under `C` and `G`. -/
theorem X3_C_complete : CompilesAs .empty (Erasure.C.surface X3Src) X3Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of a function type, under `C` and `G`. -/
theorem Alias_C_complete : CompilesAs .empty (Erasure.C.surface AliasSrc) AliasSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of an alias, under `C` and `G`. -/
theorem Alias2_C_complete : CompilesAs .empty (Erasure.C.surface Alias2Src) Alias2Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee body ascribed at `⊤`, which has no function part, so the callee
gives the domain, under `C` and `G`. -/
theorem CalleeTop_C_complete : CompilesAs .empty (Erasure.C.surface CalleeTopSrc) CalleeTopSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda as the body of a `let` with a written function type, under `C`
and `G`. -/
theorem LetBody_C_complete : CompilesAs .empty (Erasure.C.surface LetBodySrc) LetBodySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block ascribed at a function type, under `C` and `G`. -/
theorem Block_C_complete : CompilesAs .empty (Erasure.C.surface BlockSrc) BlockSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over a capability ascribed a function type that captures it,
under `C` and `G`. -/
theorem Cap_C_complete : CompilesAs πc (Erasure.C.surface CapSrc) CapSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals with a written self shape

A field takes the domain of its lambda from its type in the shape. -/

/-- E2: a literal whose field is a lambda, projected and applied, under `D` and
`C`. -/
theorem E2_D_complete : CompilesAs .empty (Erasure.D.surface E2src) E2src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- C2, its domains in checked positions erased. -/
theorem C2_C_complete : CompilesAs πc (Erasure.C.surface C2src) C2src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- S1, its domains in checked positions erased. -/
theorem S1_C_complete : CompilesAs πz (Erasure.C.surface S1progSrc) S1progSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z1, under `D` and `C`. -/
theorem Z1_D_complete : CompilesAs πz (Erasure.D.surface Z1progSrc) Z1progSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z1 with `freshCell` defined, under `D` and `C`. -/
theorem Z1def_D_complete : CompilesAs πz (Erasure.D.surface Z1defSrc) Z1defSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z3, under `D` and `C`. -/
theorem Z3_D_complete : CompilesAs πz (Erasure.D.surface Z3src) Z3src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The literal of `freshCell` with the self shape its definitions form, under
`D` and `C`. -/
theorem Z1lit_D_complete : CompilesAs πz (Erasure.D.surface Z1litF) Z1litF :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field closure of a literal with a written self shape, under `C`. -/
theorem Fld_C_complete : CompilesAs πc (Erasure.C.surface FldSrc) FldSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal with a written self shape and a field without its type, under `D`
and `C`. -/
theorem FldTy_D_complete : CompilesAs .empty (Erasure.D.surface FldTySrc) FldTySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal whose first field reads the second, under `D` and `C`. -/
theorem Fwd_D_complete : CompilesAs .empty (Erasure.D.surface FwdObjSrc) FwdObjSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field with its type written in the self shape, under `D` and
`C`. -/
theorem Rec_D_complete : CompilesAs .empty (Erasure.D.surface RecObjSrc) RecObjSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field that reads itself through an alias of the self, under `D`
and `C`. -/
theorem AliasRec_D_complete : CompilesAs .empty (Erasure.D.surface AliasRecSrc) AliasRecSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure that reads a sibling through the self, beside a field that holds
a capability, under `C`. -/
theorem LamCap_C_complete : CompilesAs πc (Erasure.C.surface LamCapSrc) LamCapSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The literal of E2 on its own, under `D` and `C`. -/
theorem E2obj_D_complete : CompilesAs .empty (Erasure.D.surface E2objSrc) E2objSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field that is a lambda, under `D` and `C`. -/
theorem NoDom_D_complete : CompilesAs .empty (Erasure.D.surface NoDomSrc) NoDomSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals at a `μ` goal

A literal without a self shape takes the body of the `μ` its goal dealiases
to. -/

/-- A literal ascribed at `μ` of its shape, under `S` and `G`. -/
theorem AscObj_S_complete : CompilesAs .empty (Erasure.S.surface AscObjSrc) AscObjSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal whose field is below the goal's field, under `S` and `G`. -/
theorem AscWide_S_complete : CompilesAs .empty (Erasure.S.surface AscWideSrc) AscWideSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Erasures no column makes -/

/-- S1's call with the outer domain of its callback erased and the inner one
written. -/
theorem S1callGu_pair_complete : CompilesAs πz S1callSrcGu S1callSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body `λx. g x` bound by a `let`. -/
theorem Callee_pair_complete : CompilesAs .empty CalleeSrcD CalleeSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal nested in a field of a written self shape, its own self shape
erased. -/
theorem Nest_pair_complete : CompilesAs .empty NestSrcS NestSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field with a written type equal to the shape's, the domain of its
lambda erased. -/
theorem FldTyD_pair_complete : CompilesAs .empty FldTySrcD FldTySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

-- Erased programs that compile with no canonical fill: a lambda whose body
-- has an empty slot at an intersection, a literal whose shape the rounds form,
-- the same seventeen deep, a fill that reads the `any` of its goal, and a field
-- type written in place of the self shape.
example : canonAt Λc .empty (Erasure.D.surface SideCurrySrc) SideCurrySrc = false := by
  decide +kernel
example : canonAt Λc .empty (Erasure.S.surface E2src) E2src = false := by decide +kernel
example : canonAt Λc .empty (NestKSrc false 16) (NestKSrc true 16) = false := by decide +kernel
example : canonAt Λc .empty CalleeAnySrcD CalleeAnySrc = false := by decide +kernel
example : canonAt Λc .empty RecWSrcS RecObjSrc = false := by decide +kernel

/-! ### Where the elaborator checks at another formal

A call argument.  The context has `y : {A : {a : ⊤} .. {b : ⊤}}` and
`n : {a : ⊤}`, and the callee `f` has two function types.  Their formals are
`∀(x : ⊤) y.A` and `∀(x : ⊤) {b : ⊤}`, and the second is dominant, since
`y.A` is below `{b : ⊤}` through its upper bound.  Its domain `⊤` is the fill,
so the fill is the written program.  The typer types the written program at
the first formal: `{a : ⊤}` is below `y.A` through its lower bound.  The
elaborator checks the filled argument at the dominant formal, which needs
`{a : ⊤}` below `{b : ⊤}`, a middle type the program does not write, and
rejects.  So the typer's check of the fill at the dominant formal is a premise
of the call argument site. -/

/-- A call argument whose fill the typer accepts at a formal that is not the
dominant one. -/
def MidSrc : STm :=
  cc% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λ(x : ⊤). n)

/-- The same with the argument's domain erased. -/
def MidSrcA : STm :=
  cc% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λx. n)

-- The erased program is the written one with the argument's domain erased.
example : Erasure.A.surface MidSrc = MidSrcA := rfl

/-- The written program compiles, and the erased one is a mismatch. -/
theorem Mid_erased : pair .empty MidSrc MidSrcA =
    [.same (tyOf .empty MidSrc) (spent 60), .no .mismatch (spent 77)] := by decide +kernel

/-- The erased program is rejected at every budget. -/
theorem Mid_rejected : RejectedWith .empty MidSrcA .mismatch :=
  erasedCell_rejected (w := MidSrc) (n := defaultFuel - 77) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem Mid_checks : CheckerAccepts {} Λc .empty MidSrc (by decide +kernel) :=
  compile_checks_get _

-- The erased program does not have the written one as its canonical fill.
example : canonAt Λc .empty MidSrcA MidSrc = false := by decide +kernel

end Complete

end CapturesCCFrontend
