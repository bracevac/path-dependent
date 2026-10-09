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
the log of `NestSrc`, whose premise holds at one root and fails at another.  S2 and C2 are run from the platform's initial store,
printed with the platform's own names, and pinned at the step count at which
they become final.  E2 is run beside them over the empty platform.
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
Above the fuel of the check this is `synthTop?_stable`.  Below it, an answer
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
    simp only [compile, hr]
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

The first entry of the log of `NestSrc` separates the roots.  The program is
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
def NestSrc : STm :=
  cc% λ(g : ⊤). λ(f : ⊤ ^ {any}).
        let h = ((λ(u : ⊤ ^ {f}). u) : (∀(u : ⊤ ^ {f}) ⊤ ^ {any}) ^ {any}) in f

theorem Nest_compiles : (compile {} Λc πc NestSrc).isOk = true := by decide +kernel

theorem Nest_log_ne : compileLog {} Λc πc NestSrc ≠ [] := by decide +kernel

/-- The first entry of the log of `NestSrc`. -/
def NestEntry : LevelStep := (compileLog {} Λc πc NestSrc).head Nest_log_ne

theorem NestEntry_mem : NestEntry ∈ compileLog {} Λc πc NestSrc := List.head_mem _

/-- `lo` is the parameter `u` and `hi` is the root of `f`'s body, each a
single atom. -/
example : NestEntry.lo.length = 1 ∧ NestEntry.hi.length = 1 ∧
    NestEntry.hi.translate = [cvarAt NestEntry.sig 5] := by
  decide +kernel

/-- The root of `f`'s body, at depth 5. -/
def NestRoot : FCdot.CapAtom NestEntry.sig := cvarAt NestEntry.sig 5

/-- The root of `g`'s body, at depth 8. -/
def NestOuter : FCdot.CapAtom NestEntry.sig := cvarAt NestEntry.sig 8

/-- Both are scope roots, and neither is the universal one. -/
theorem Nest_roots :
    NestEntry.ctx.translate.IsRoot NestRoot ∧ NestRoot ≠ .top ∧
      NestEntry.ctx.translate.IsRoot NestOuter ∧ NestOuter ≠ .top := by
  decide +kernel

/-- The premise at the root of `f`'s body, at every depth. -/
theorem NestEntry_premise :
    ∀ m, NestEntry.ctx.translate.Confined
      (NestEntry.ctx.translate.caps m NestEntry.hi.translate) NestRoot := by
  intro m
  rw [caps_self _ (by decide +kernel) m]
  decide +kernel

/-- The premise fails at the root of `g`'s body. -/
theorem NestEntry_separates :
    ¬ ∀ m, NestEntry.ctx.translate.Confined
      (NestEntry.ctx.translate.caps m NestEntry.hi.translate) NestOuter := by
  intro h
  have h0 := h 0
  rw [← capsS_eq] at h0
  revert h0
  decide +kernel

/-- `lo` as written is not confined to the root of `f`'s body. -/
theorem NestEntry_lo_not :
    ¬ NestEntry.ctx.translate.Confined NestEntry.lo.translate NestRoot := by
  decide +kernel

/-- **Level safety at the first entry of `NestSrc`.** -/
theorem NestEntry_lvl :
    ∀ n, NestEntry.ctx.translate.Confined
      (NestEntry.ctx.translate.caps n NestEntry.lo.translate) NestRoot :=
  compile_lvl_safety_get Nest_compiles NestEntry NestEntry_mem NestRoot NestEntry_premise

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

end CapturesCCFrontend
