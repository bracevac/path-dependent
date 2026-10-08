import Coercions.Classifiers.Frontend.Pipeline
import Coercions.Classifiers.Frontend.Pretty

/-!
# The examples end to end

The programs of the version's `DotMNF/Examples.lean`, the programs of
`Notation.lean` and `Typer.lean`, and the programs written here are taken
through the whole front end.  Where the hand written derivations of the
version exist, the term and the judgment are compared with them.

The capture programs come first.  They declare no classifier, so each is a
whole program over plain platform binders, built by `SProg.plain`.  The pure
programs run over the empty platform.  The others run over the platform
`k1, k2`, the version's `platCtx`, or over `fs, k2`, the same two binders, for
the programs whose capability is a file system.

The classifier programs follow.  CE1 to CE3 are E1, E2 and E3 of the version's
classifier examples: `Try.apply`, `Future.apply`, and a client against a
member bounded by a kind.  Each declares its classifiers, a platform whose
binders carry them, a use set and a kind.  CE3 is run again over three
capabilities.  CE4 reads a closure off a kind-bounded member and hands it to a
filtered domain.  CE5 passes a thread-local body to `Future.apply`, which the
calculus refuses.  W ascribes a restricted variable at its restricted set.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer, the kinding goal and the machine.  Every check runs at
`defaultFuel`, the one field of the default budget `{}`.  No program has a
budget of its own.

For a program that compiles:

- The term, by `decide`.  This is the resolved term, or the erasure of the
  elaborated term when the typer inserted a box, an unboxing or an unpacking
  (by `decide +kernel`, since it runs the typer).
- `Ek_type`: the use set and the answer the typer finds and the tank it
  leaves, by `decide +kernel` (`judgProg`).  The tank left is `defaultFuel`
  minus the units the typing used, and it is unmarked.  A program that
  declares a use set is moved to it by `compile`, and the judgment `compile`
  returns is checked too.
- The target checker's verdict on the translation of the derivation and on
  the use set evidence, through `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program.  So `Ek_checks` has no hypothesis.

A program the version types under a context is typed there.  Its `Ek_type`
is a fact about `judgIn`, its `Ek_compiles` about `synthIn?`, and its
`Ek_checks` is `synthIn_checks_get`, the open twin of `compile_checks_get`.

For a program the typer rejects:

- `Ek_verdict`: no answer, and the tank left unmarked, by `decide +kernel`.
- `Ek_rejected`: `compile` returns no result at every budget
  (`judgProg_rejects`).  Above `defaultFuel` this is `synthInF_stable`, and
  below it `synthInF_mono`.
- `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive that goal (`var?_reject`, `cap?_reject`,
  `kind?_reject`).  So no fuel and no other order of the alternatives would
  find it.

For a program at the recursion limit, `Ek_limit`: no answer, and the tank
marked, by `decide +kernel`.  The verdict is the compiler's recursion limit,
not a rejection by the rules.

Derivations are not compared, since `DotMNF.HasTy` is data with no decidable
equality and the typer may reach a judgment by another route.  No term, use
set or type is copied from the version: `tmOfDeriv`, `usesOfDeriv` and
`tyOfDeriv` read them off its derivations.  A judgment written here is a set
and a type in the notation, resolved over the program's platform
(`writtenAt`, `pureAt`).  Kindings and subcapturings are compared on their
translations, since `FCdot.KindCo` and `FCdot.CapCo` have decidable equality.

## The programs by verdict

Accepted at the version's judgment: E5, E6 at `E6Ctx1`, E7, E8, C7 with its
boxes written and with no box written, S3, S1, S2, Z1, Z2, Z3, the call of
`process` at `W2CallCtx`, the unpacking at `Z1Ctx` whose answer is
existential, CE1, CE2, and the retypings of CE3's literals at the kind bound.

Accepted at a least judgment, from which the version's judgment is reached
by one `sub`: C2 at `{k2}`, C5 at `{it, it.C}`, the caller of `freshCell` at
`{fc, fs, un}`, and `process`.  E2 is typed at the type avoidance gives,
`∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`, where the version's derivation concludes `⊤`.
CE3 and CE4 are typed at the empty set and moved to their declared sets.

Accepted at a judgment written here: `freshCell` bound by a `let` whose
answer is written with `fresh`, the existential annotations cov2 and cov4,
the projection cov3, a callback that keeps what it captures inside its own
scope, a capture parameter that is called, two calls of `freshCell`, an
unpacking whose payload leaves by the level rule, CE3 over three
capabilities and CE5 with an input-output body.

Accepted, and found by no search over the declared types of the context:
QP1, a function at a member selected through a recursive shape.  QP4, a
field four steps down the upper bound of a selection.  QP5, an intersection
of two function types applied to an argument only the second accepts.  R1
to R4, a projection with two fields of which only the second lets the rest of
the program type.  E1s and E3s, which are E1 and E3 with the middle type
written.  The alias chains of sixteen and thirty two links.  BX2 and BX,
where a boxed variable meets a boxed goal, unboxing fails and boxing
succeeds.  X1 and X2, a variable at its own abstract type, which the typer
widens whole.  W, a restricted variable widened to its restricted set.  The
goals M1, M2 and M5 of a mixed or filtered set, and R2, a selection off a
set-bounded member kinded through its upper bound.

Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
program does not write, and the typer chooses none.  A1 has a written `let`
annotation the bound value does not meet, and a written annotation binds.
CE4 with its member bounded by an unrelated classifier has no kinding of the
closure's set.  W without the restriction on its variable reaches `io`,
which is not `Control`.  CE5 has no kinding of its thread-local argument.
Each has its `¬ Alg` fact.  Rejected with a reason: `any` below a field of a
domain, an existential answer outside every scope, and the three escapes of
a callback.  The escape and the escape at the top carry a certificate at the
goal the typer reached.

At the recursion limit: LP, a check through `∀` bodies that reaches the same
goal under one more binder at every level.  PF, Pierce's divergence of F<:,
whose goal comes back under a new binder that it names.  LQ2, whose goal
compares two arrows with a codomain at the fresh parameter at every level.

## Kindings, levels, effects and runs

The kinding goal tries `kproj` first, so it kinds a restricted use set atom
by atom with `kproj`, where the version's kindings of E1 and E2 use `kcls`.
It kinds the last atom of a set alone, where the version's kindings add
`nil`.  The rules it takes are pinned, and the target checker accepts each.

The checks W1 and W5 ask subcapturing for the steps of the level order at
the version's contexts.  `C2_never_reads_k1` is the plain effect theorem at
C2.  `CE1_reads_only_control`, `CE2_no_thread_local` and
`CE3_reads_only_control` are the classified ones: every root of a variable a
run reads carries a classifier the declared kind admits.  The logs of C2, S1,
CE1, CE2 and CE3 are pinned.  S2, C2, E2, CE1, CE2 and CE3 are run from their
platform's initial store, printed with the platform's own names, and pinned
at the step count at which they become final.
-/

namespace ClassifiersFrontend

open Classifiers
open Frontend.Fuel ClassifiersFrontend.Core
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (CapAtom CaptureSet Shape Ty ETy Tm Ctx HasTy HasTyP Subcap CapKind State
  Steps Platform)
open scoped Classifiers.DotMNF

section Examples

open Classifiers.DotMNF.Examples

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

/-! ## Programs with no classifier

A program of the capture fragment declares no classifier, no use set and
no kind.  It runs over plain platform binders. -/

/-- A program over the empty platform. -/
def onE (e : STm) : SProg := SProg.plain [] e

/-- A program over the platform `k1, k2`, `platCtx`. -/
def onC (e : STm) : SProg := SProg.plain ["k1", "k2"] e

/-- A program over the platform `fs, k2`, the same two binders. -/
def onZ (e : STm) : SProg := SProg.plain ["fs", "k2"] e

/-! ## The decidable things -/

/-- The resolved body, erased into the version's syntax. -/
def compiledTm (Λ : LabelTable) (p : SProg) : Option (Tm p.platNames.sig) :=
  (resolveProg Λ p).map fun r => r.body.erase

/-- The elaborated term, erased.  It differs from the resolved one when the
typer inserted a box, an unboxing or an unpacking. -/
def elaboratedTm (b : Budget) (Λ : LabelTable) (p : SProg) : Option (Tm p.platNames.sig) :=
  (compile b Λ p).toOption.map fun r => r.2.tm.erase

/-- The use set and the type `compile` returns.  For a program that declares
a use set, this is the judgment at the declared set. -/
def compiledJudgment (b : Budget) (Λ : LabelTable) (p : SProg) :
    Option (CaptureSet p.platNames.sig × Ty p.platNames.sig) :=
  (compile b Λ p).toOption.map fun r => (r.2.use, r.2.ty)

/-- The use set and answer the typer finds for a whole program, from a full
tank of `n` units, with the tank left.  The body is typed at its platform's
context, as `compile` types it. -/
def judgProg (Λ : LabelTable) (p : SProg) (n : Nat := defaultFuel) :
    Option (CaptureSet p.platNames.sig × ETy p.platNames.sig) × Tank :=
  match resolveProg Λ p with
  | some r => ((synthInF r.plat.ctx p.platNames.set r.body n).1.map fun c => (c.uses, c.ans),
      (synthInF r.plat.ctx p.platNames.set r.body n).2)
  | none => (none, ⟨n, true⟩)

/-- A use set and a type written in the notation, resolved over the platform
of the program `p`. -/
def writtenAt (Λ : LabelTable) (κt : ClsTable) (p : SProg) (C : SCap) (T : SType) :
    Option (CaptureSet p.platNames.sig × ETy p.platNames.sig) := do
  let U ← resolveCap Λ κt p.platNames.names C
  let T' ← resolveTy Λ κt p.platNames.names T
  pure (U, .ty T')

/-- The judgment at the empty use set and a type written in the notation, for
a program with no classifier. -/
def pureAt (p : SProg) (T : SType) : Option (CaptureSet p.platNames.sig × ETy p.platNames.sig) :=
  writtenAt Λc [] p [] T

/-- The target checker's verdict on the translation of the derivation.  It is
`false` when the front end returns no derivation. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (p : SProg) : Bool :=
  match compile b Λ p with
  | .ok r => FCdot.checkTm r.1.plat.ctx.translate r.2.deriv.translate r.2.ty.translate
  | _ => false

/-- The target checker's verdict on the use set evidence the translation
emits. -/
def compiledUsesVerdict (b : Budget) (Λ : LabelTable) (p : SProg) : Bool :=
  match compile b Λ p with
  | .ok r =>
      FCdot.checkCap r.1.plat.ctx.translate r.2.deriv.translateUses r.2.deriv.translate.uses
        r.2.use.translate
  | _ => false

/-- What `compile_checks_get` concludes at a program that compiles: the
target checker accepts the translation of its derivation. -/
def CheckerAccepts (b : Budget) (Λ : LabelTable) (p : SProg)
    (h : (compile b Λ p).isOk = true) : Prop :=
  FCdot.checkTm ((compile b Λ p).get h).1.plat.ctx.translate
    ((compile b Λ p).get h).2.deriv.translate ((compile b Λ p).get h).2.ty.translate = true

/-- The two checker verdicts at a typing found at an open context. -/
def openVerdicts {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Bool × Bool :=
  match v with
  | .ok r =>
      (FCdot.checkTmE Γ.translate r.deriv.translate r.ans.translate,
        FCdot.checkCap Γ.translate r.deriv.translateUses r.deriv.translate.uses r.uses.translate)
  | _ => (false, false)

/-- **The target checker accepts a typing found at an open context.**  The open
twin of `compile_checks_get`: `FCdot.checkTm_complete` at
`HasTy.translate_typed`, at a well formed context. -/
theorem synthIn_checks_get {s : Sig} {Γ : Ctx s} {b : Budget} {ps : CaptureSet s} {a : ATm s}
    (hwf : Γ.Wf) (h : (synthIn? b Γ ps a).isOk = true) :
    FCdot.checkTmE Γ.translate ((synthIn? b Γ ps a).get h).deriv.translate
      ((synthIn? b Γ ps a).get h).ans.translate = true :=
  FCdot.checkTmE_complete (DotMNF.HasTy.translate_typed _ hwf)

/-- A sequence whose first step is not a success is not a success. -/
theorem Verdict.isOk_bind_false {α β : Type} {v : Verdict α} {f : α → Verdict β}
    (h : v.isOk = false) : (v.bind f).isOk = false := by
  cases v with
  | ok a => simp [Verdict.isOk] at h
  | rejected r => rfl
  | unknown => rfl

/-- A verdict that is not a success stays one under `map`. -/
theorem Verdict.isOk_map_false {α β : Type} {v : Verdict α} {f : α → β}
    (h : v.isOk = false) : (v.map f).isOk = false := by
  cases v with
  | ok a => simp [Verdict.isOk] at h
  | rejected r => rfl
  | unknown => rfl

/-- **A rejection that leaves the tank unmarked is a rejection at every
budget.**  Above the fuel of the check this is `synthInF_stable`.  Below it,
an answer would be kept by `synthInF_mono` and contradict the check.  With no
candidate, `synthIn?` is `rejected` or `unknown`, and `compile` passes either
on.  A program that does not resolve gives a marked tank in `judgProg`, so it
cannot meet the premise. -/
theorem judgProg_rejects {Λ : LabelTable} {p : SProg} {n k : Nat}
    (h : judgProg Λ p n = (none, ⟨k, false⟩)) (b : Budget) : (compile b Λ p).isOk = false := by
  unfold judgProg at h
  cases hr : resolveProg Λ p with
  | none =>
    rw [hr] at h
    cases h
  | some r =>
    rw [hr] at h
    simp only [Prod.mk.injEq, Option.map_eq_none_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hs : synthInF r.plat.ctx p.platNames.set r.body n = (none, ⟨k, false⟩) := by
      rw [← h1, ← h2]
    have hnone : (synthInF r.plat.ctx p.platNames.set r.body b.fuel).1 = none := by
      rcases Nat.le_total n b.fuel with hle | hle
      · have := synthInF_stable hs (b.fuel - n)
        rwa [Nat.add_sub_cancel' hle] at this
      · cases hc : (synthInF r.plat.ctx p.platNames.set r.body b.fuel).1 with
        | none => rfl
        | some c =>
          have := synthInF_mono hc hle
          rw [h1] at this
          cases this
    have hin : (synthIn? b r.plat.ctx p.platNames.set r.body).isOk = false := by
      unfold synthIn?
      cases hq : synthInF r.plat.ctx p.platNames.set r.body b.fuel with
      | mk o t =>
        rw [hq] at hnone
        cases hnone
        simp only
        split
        · rfl
        · split <;> rfl
    have ht : (typeAt b p.platNames r.plat r.body).isOk = false := by
      unfold typeAt synthPlat?
      exact Verdict.isOk_bind_false (Verdict.isOk_bind_false hin)
    simp only [compile, hr]
    exact Verdict.isOk_map_false (Verdict.isOk_bind_false ht)

/-- A run that answers with the tank unmarked gives a derivation. -/
theorem found_nonempty {α : Type} {r : Option α × Tank} {k : Nat} (h : answers r k = true) :
    Nonempty α :=
  ⟨r.1.get (answers_isSome h).1⟩

/-- Subcapturing at a context, from a full tank of the budget's fuel. -/
def subcapFound {s : Sig} (b : Budget) (Γ : Ctx s) (C D : CaptureSet s) : Bool :=
  (Core.cap? Γ C D b.fuel).1.isSome

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
  | .consCls Γ' k, .consCls Δ' k' => decide (k = k') && ctxEq Γ' Δ'
  | _, _ => false
termination_by structural Γ

/-- Two platforms are equal binder by binder. -/
def platEq {s : Sig} (P Q : Platform s) : Bool :=
  match P, Q with
  | .nil, .nil => true
  | .cons P', .cons Q' => platEq P' Q'
  | .consCls P' k, .consCls Q' k' => decide (k = k') && platEq P' Q'
  | _, _ => false
termination_by structural P

/-- `platEq` decides equality. -/
theorem platEq_sound : ∀ {s : Sig} (P Q : Platform s), platEq P Q = true → P = Q
  | _, .nil, .nil, _ => rfl
  | _, .cons P', .cons Q', h => by
      rw [platEq_sound P' Q' (by simpa [platEq] using h)]
  | _, .consCls P' k, .consCls Q' k', h => by
      simp only [platEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, platEq_sound P' Q' h.2]
  | _, .cons _, .consCls _ _, h => by simp [platEq] at h
  | _, .consCls _ _, .cons _, h => by simp [platEq] at h

/-- A verdict that rejects by a level escape at the goal `C <: D` in the
context `Γ`. -/
def escapesAt {α : Type} {s : Sig} (v : Verdict α) (Γ : Ctx s) (C D : CaptureSet s) : Bool :=
  match v with
  | .rejected (.levelEscape (s := s') Γ' C' D' _ _) =>
      if h : s' = s then ctxEq (h ▸ Γ') Γ && decide (h ▸ C' = C) && decide (h ▸ D' = D)
      else false
  | _ => false

/-! ## E1: bad bounds under a lambda

The annotated `let` is typed through the bad bounds chain in the version's
derivation `E1`.  The chain passes the middle `x.A`, which the program does
not write, so the typer rejects the program, as the Scala compiler does.  The
goal it rejects is the check of the body `y` against the annotation. -/

/-- `λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤}..{a : ⊤}} = x in y`. -/
def E1src : STm := cls% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

example : compiledTm Λc (onE E1src) = some (tmOfDeriv E1) := by decide

/-- The body of E1's lambda, then the `let` binder `y` at the type of `x`. -/
def E1yCtx : Ctx (Sig.body ([] : Sig),x) := E1Ctx.cons E1Dom

/-- The typer rejects E1 after 11 units, with the tank unmarked. -/
theorem E1_verdict : judgProg Λc (onE E1src) = (none, ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- E1 does not compile at any budget. -/
theorem E1_rejected (b : Budget) : (compile b Λc (onE E1src)).isOk = false :=
  judgProg_rejects E1_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation. -/
theorem E1_not_alg : ¬ Alg ⟨_, E1yCtx, .var .here E1Dom E1Res⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E1yCtx .here E1Res) 5 = true))
  have hv : (varView E1yCtx .here).ty = E1Dom := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## E2: a recursive object with a self referential member

The outer `let` has no annotation, and its body's type mentions the bound
variable.  Avoidance replaces `x.A` by its upper bound with `x` avoided,
`∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`, as the compiler's `avoid` does.  The version's
derivation `E2` gives `⊤`.  The term is the version's. -/

/-- `let x = ν(s : {A : E2A..E2A} ∧ {a : E2A}. {type A = E2A} ∧ {a = λ(y : s.A). y})
in let f = x.a in f f`, with `E2A` the shape `∀(y : s.A) s.A`. -/
def E2src : STm :=
  cls% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

example : compiledTm Λc (onE E2src) = some (tmOfDeriv E2) := by decide

/-- E2 is typed at the avoided type, from 60 units. -/
theorem E2_type : judgProg Λc (onE E2src) =
    (some (usesOfDeriv E2, .ty Core.E2AvoidedTy), ⟨defaultFuel - 60, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E2src))
  "E2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E2src))
  "E2: the target checker rejects the use set evidence"

/-- E2 compiles. -/
theorem E2_compiles : (compile {} Λc (onE E2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts {} Λc (onE E2src) E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation `E3`
passes the middle `x.A`, which the program does not write, so the typer
rejects the program, as the Scala compiler does.  The goal it rejects is the
check of the body `y` against the annotation. -/

/-- `λ(x : {A : ⊥..{a : ⊤}} ∧ {A : {b : ⊤}..⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y`. -/
def E3src : STm :=
  cls% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

example : compiledTm Λc (onE E3src) = some (tmOfDeriv E3) := by decide

/-- The body of the inner lambda, then the `let` binder `y : {b : ⊤}`. -/
def E3yCtx : Ctx (Sig.body (Sig.body ([] : Sig)),x) := E3Ctx2.cons E3T2

/-- The typer rejects E3 after 11 units, with the tank unmarked. -/
theorem E3_verdict : judgProg Λc (onE E3src) = (none, ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- E3 does not compile at any budget. -/
theorem E3_rejected (b : Budget) : (compile b Λc (onE E3src)).isOk = false :=
  judgProg_rejects E3_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3_not_alg : ¬ Alg ⟨_, E3yCtx, .var .here E3T2 E3T1⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E3yCtx .here E3T1) 5 = true))
  have hv : (varView E3yCtx .here).ty = E3T2 := by decide +kernel
  rw [hv] at hr
  exact hr

/-! ## E4: typing with no realizer

The version's derivation `E4` widens `w` to `x.B`, a subsumption through a
middle the program does not write, so the typer rejects the program, as the
Scala compiler does.  The goal it rejects is the argument `n` of `g n`
against the domain `w.A`, in `E4Ctx4`, where `g` has the type the typer gives
it. -/

/-- `λ(x : {B : {A : ⊥..⊤}..{A : {a : ⊤}..⊤}}). λ(w : {A : ⊥..⊤}). λ(n : {a : ⊤}).
let g = λ(y : w.A). y in g n`. -/
def E4src : STm :=
  cls% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
         λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

example : compiledTm Λc (onE E4src) = some (tmOfDeriv E4) := by decide

/-- The typer gives `g` the type `E4G` of the version, so the goal of `g n`
sits in `E4Ctx4`. -/
example : judgIn E4Ctx3 [] (.lam ((Shape.sel (.var (.there (up .here))) lA) ^ [])
    (.path (.var .here))) = (some ([], .ty (E4G (up .here))), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The typer rejects E4 after 16 units, with the tank unmarked. -/
theorem E4_verdict : judgProg Λc (onE E4src) = (none, ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

/-- E4 does not compile at any budget. -/
theorem E4_rejected (b : Budget) : (compile b Λc (onE E4src)).isOk = false :=
  judgProg_rejects E4_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4_not_alg :
    ¬ Alg ⟨_, E4Ctx4,
      .var (.there .here) E4Int ((Shape.sel (.var (.there (up .here))) lA) ^ [])⟩ :=
  E4_var_not_alg

/-! ## E5: an object returned from a function

The application renames the result's member to `w`, and the outer `let`
keeps `w.A`.  The version's derivation is `E5`. -/

/-- `λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
in let o = f w in o.a`. -/
def E5src : STm :=
  cls% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
         in let o = f w in o.a

example : compiledTm Λc (onE E5src) = some (tmOfDeriv E5) := by decide

/-- E5 is typed at the version's judgment, from 20 units. -/
theorem E5_type : judgProg Λc (onE E5src) =
    (some (usesOfDeriv E5, .ty (tyOfDeriv E5)), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E5src))
  "E5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E5src))
  "E5: the target checker rejects the use set evidence"

/-- E5 compiles. -/
theorem E5_compiles : (compile {} Λc (onE E5src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts {} Λc (onE E5src) E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The version types E6 at `E6Ctx1`, which binds `n : {a : ⊤}`.  So the literal
is resolved under the name `n` and typed at that context. -/

/-- `ν(x : {T : {a : ⊤}..{a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})`. -/
def E6src : STm :=
  cls% ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

/-- The names of `E6Ctx1`. -/
def E6names : NameEnv ([],x) := PlatformNames.empty.names.cons "n"

/-- E6 as resolved. -/
def E6ann : ATm ([],x) := (resolveIn Λc [] E6names E6src).getD (.path (.var .here))

/-- `E6Ctx1` is well formed. -/
theorem E6Ctx1_wf : E6Ctx1.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc [] E6names E6src).map ATm.erase = some (tmOfDeriv E6) := by decide

/-- E6 is typed at `E6Ctx1` at the version's judgment, from 13 units. -/
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

The version's derivation is `E7`.  No subtyping goal is asked. -/

/-- `ν(x : {A : x.B..x.B} ∧ {B : x.A..x.A}. {type A = x.B} ∧ {type B = x.A})`. -/
def E7src : STm :=
  cls% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})

example : compiledTm Λc (onE E7src) = some (tmOfDeriv E7) := by decide

/-- E7 is typed at the version's judgment, from 1 unit. -/
theorem E7_type : judgProg Λc (onE E7src) =
    (some (usesOfDeriv E7, .ty (tyOfDeriv E7)), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E7src))
  "E7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E7src))
  "E7: the target checker rejects the use set evidence"

/-- E7 compiles. -/
theorem E7_compiles : (compile {} Λc (onE E7src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts {} Λc (onE E7src) E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: refining an abstract type

The version gives one term two derivations, `E8` and `E8b`, at one
judgment.  The typer finds that judgment. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`. -/
def E8src : STm := cls% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

example : compiledTm Λc (onE E8src) = some (tmOfDeriv E8) := by decide

example : tmOfDeriv E8b = tmOfDeriv E8 := rfl

example : (usesOfDeriv E8b, tyOfDeriv E8b) = (usesOfDeriv E8, tyOfDeriv E8) := by decide

/-- E8 is typed at the version's judgment, from 13 units. -/
theorem E8_type : judgProg Λc (onE E8src) =
    (some (usesOfDeriv E8, .ty (tyOfDeriv E8)), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E8src))
  "E8: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E8src))
  "E8: the target checker rejects the use set evidence"

/-- E8 compiles. -/
theorem E8_compiles : (compile {} Λc (onE E8src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts {} Λc (onE E8src) E8_compiles :=
  compile_checks_get E8_compiles

/-! ## E1s and E3s: the middle written

E1 and E3 with the middle type `x.A` written.  A `let` annotation types the
whole `let`, so `let u : x.A = t in u` ascribes `x.A` to `t`.  Each step is
then one goal the typer asks, and both programs compile at the version's
types. -/

/-- E1 with the middle written is typed at `∀(x : E1Dom) E1Res`, from 20 units. -/
theorem E1s_type : judgProg Λc (onE E1ssrc) =
    (some ([], .ty ((Shape.all E1Dom (.ty E1Res)) ^ [])), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E1ssrc))
  "E1s: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E1ssrc))
  "E1s: the target checker rejects the use set evidence"

/-- E1 with the middle written compiles. -/
theorem E1s_compiles : (compile {} Λc (onE E1ssrc)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem E1s_checks : CheckerAccepts {} Λc (onE E1ssrc) E1s_compiles :=
  compile_checks_get E1s_compiles

/-- E3 with the middle written is typed at `∀(x : E3Dom) ∀(z : E3T2) E3T1`,
from 18 units. -/
theorem E3s_type : judgProg Λc (onE E3ssrc) =
    (some ([], .ty ((Shape.all E3Dom (.ty ((Shape.all E3T2 (.ty E3T1)) ^ []))) ^ [])),
      ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE E3ssrc))
  "E3s: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE E3ssrc))
  "E3s: the target checker rejects the use set evidence"

/-- E3 with the middle written compiles. -/
theorem E3s_compiles : (compile {} Λc (onE E3ssrc)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem E3s_checks : CheckerAccepts {} Λc (onE E3ssrc) E3s_compiles :=
  compile_checks_get E3s_compiles

/-! ## C7: a container of boxed capabilities, boxes written

The fields check by the box rule, and the client unboxes at `{k1}`.  The
version's derivation is `C7_typed`. -/

/-- C7 with its boxes and its unboxing written. -/
def C7boxSrc : STm :=
  cls% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

example : compiledTm Λc (onC C7boxSrc) = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc (onC C7boxSrc) = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with its boxes written is typed at the version's judgment, from 31
units. -/
theorem C7box_type : judgProg Λc (onC C7boxSrc) =
    (some (usesOfDeriv C7_typed, .ty (tyOfDeriv C7_typed)), ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC C7boxSrc))
  "C7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC C7boxSrc))
  "C7: the target checker rejects the use set evidence"

/-- C7 with its boxes written compiles. -/
theorem C7box_compiles : (compile {} Λc (onC C7boxSrc)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with its boxes
written. -/
theorem C7box_checks : CheckerAccepts {} Λc (onC C7boxSrc) C7box_compiles :=
  compile_checks_get C7box_compiles

/-! ## C7 with no box in any term

`C7src` of `Typer.lean`.  The typer inserts `□ f1` and `□ f2` at the fields
and `{k1} ⊸ e` at the ascription, in two passes of the object rule.  The
elaborated term is the version's. -/

example : compiledTm Λc (onC C7src) ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc (onC C7src) = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with no box written is typed at the version's judgment, from 80 units. -/
theorem C7_type : judgProg Λc (onC C7src) =
    (some (usesOfDeriv C7_typed, .ty (tyOfDeriv C7_typed)), ⟨defaultFuel - 80, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC C7src))
  "C7 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC C7src))
  "C7 with no box: the target checker rejects the use set evidence"

/-- C7 with no box in any term compiles. -/
theorem C7_compiles : (compile {} Λc (onC C7src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C7 with no box in any
term. -/
theorem C7_checks : CheckerAccepts {} Λc (onC C7src) C7_compiles :=
  compile_checks_get C7_compiles

/-! ## S3: a type member at a boxed capturing type

The bounds of a type member are shapes, so the program writes the box in the
member.  The client unboxes through the upper bound of `o.A`.  The version's
derivation is `S3_typed`. -/

/-- S3, its box and its unboxing written. -/
def S3src : STm :=
  cls% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : □((∀(u : ⊤) ⊤) ^ {f}) .. □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem : z.A}.
                   {type A = □((∀(u : ⊤) ⊤) ^ {f})} ∧ {elem = □ f})
        in let e = o.elem in {f} ⊸ e

example : compiledTm Λc (onC S3src) = some (tmOfDeriv S3_typed) := by decide

/-- S3 is typed at the version's judgment, from 46 units. -/
theorem S3_type : judgProg Λc (onC S3src) =
    (some (usesOfDeriv S3_typed, .ty (tyOfDeriv S3_typed)), ⟨defaultFuel - 46, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC S3src))
  "S3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC S3src))
  "S3: the target checker rejects the use set evidence"

/-- S3 compiles. -/
theorem S3_compiles : (compile {} Λc (onC S3src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S3. -/
theorem S3_checks : CheckerAccepts {} Λc (onC S3src) S3_compiles :=
  compile_checks_get S3_compiles

/-! ## C2: capture polymorphism by a capture member

The client reads `x.run`, whose set is `{x.C}`.  The typer finds the judgment
`{k2}` and `(⊤ → ⊤) ^ {k2}`, since the answer is the client at `b`, whose
member is `{k2}`.  The version's `{k1, k2}` is reached by one `sub`. -/

/-- C2, with the call `x.run u` in direct style. -/
def C2src : STm :=
  cls% let c = λ(x : μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

example : compiledTm Λc (onC C2src) = some (tmOfDeriv C2_typed) := by decide

example : elaboratedTm {} Λc (onC C2src) = some (tmOfDeriv C2_typed) := by decide +kernel

/-- C2 is typed at `{k2}` and `(⊤ → ⊤) ^ {k2}`, from 214 units. -/
theorem C2_type : judgProg Λc (onC C2src) =
    (some ([CapAtom.cvar k2], .ty ((Shape.all unitTy (.ty unitTy)) ^ [CapAtom.cvar k2])),
      ⟨defaultFuel - 214, false⟩) := by
  decide +kernel

example : topReaches {} πc (resolveTop Λc [] πc C2src) (usesOfDeriv C2_typed)
    (.ty (tyOfDeriv C2_typed)) = true := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC C2src))
  "C2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC C2src))
  "C2: the target checker rejects the use set evidence"

/-- C2 compiles. -/
theorem C2_compiles : (compile {} Λc (onC C2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of C2. -/
theorem C2_checks : CheckerAccepts {} Λc (onC C2src) C2_compiles :=
  compile_checks_get C2_compiles

/-! ## S1: `withFile` with an explicit capture parameter

`withFile` is bound by an ascription at its signature.  Its result `any` is
read at the top of the program as the platform set.  The judgment is the
version's `S1_typed`, `{fs, k2}` and `⊤ ^ {fs, k2}`.  The program runs over
`fs, k2`. -/

/-- S1. -/
def S1progSrc : STm :=
  cls% let withFile =
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

example : compiledTm Λc (onZ S1progSrc) = some (tmOfDeriv S1_typed) := by decide

/-- S1 is typed at the version's judgment, from 86 units. -/
theorem S1_type : judgProg Λc (onZ S1progSrc) =
    (some (usesOfDeriv S1_typed, .ty (tyOfDeriv S1_typed)), ⟨defaultFuel - 86, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ S1progSrc))
  "S1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ S1progSrc))
  "S1: the target checker rejects the use set evidence"

/-- S1 compiles. -/
theorem S1_compiles : (compile {} Λc (onZ S1progSrc)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S1. -/
theorem S1_checks : CheckerAccepts {} Λc (onZ S1progSrc) S1_compiles :=
  compile_checks_get S1_compiles

/-! ## S2: a class with a capture set parameter

`mk` is bound by an ascription at its signature, with `any` in its result,
read as the platform set.  The caller's answer leaves scope at the upper bound
of the member, `{fs}`.  The judgment is the version's `S2_typed`. -/

/-- S2. -/
def S2src : STm :=
  cls% let mk =
        (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in it
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {any}) ^ {fs}) in
      let un = (λ(y : ⊤). y : ⊤) in
      let it = mk un in let n = it.next in let r = n un in r

example : compiledTm Λc (onZ S2src) = some (tmOfDeriv S2_typed) := by decide

/-- S2 is typed at the version's judgment, from 138 units. -/
theorem S2_type : judgProg Λc (onZ S2src) =
    (some (usesOfDeriv S2_typed, .ty (tyOfDeriv S2_typed)), ⟨defaultFuel - 138, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ S2src))
  "S2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ S2src))
  "S2: the target checker rejects the use set evidence"

/-- S2 compiles. -/
theorem S2_compiles : (compile {} Λc (onZ S2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of S2. -/
theorem S2_checks : CheckerAccepts {} Λc (onZ S2src) S2_compiles :=
  compile_checks_get S2_compiles

/-! ## C5: the caller of `mk`, at the version's own context

The version types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  The
typer finds `{it, it.C}` and `⊤ ^ {it.C}`.  The version's `{fs, k2}` and
`⊤ ^ {fs}` are reached by one `sub`. -/

/-- `let n = it.next in let r = n un in r`. -/
def C5src : STm := cls% let n = it.next in let r = n un in r

/-- The names of `S2Ctx3`: the platform, then `mk`, `un` and `it`. -/
def C5names : NameEnv ([],c,c,x,x,x) := ((πz.names.cons "mk").cons "un").cons "it"

/-- C5 as resolved. -/
def C5ann : ATm ([],c,c,x,x,x) := (resolveIn Λc [] C5names C5src).getD (.path (.var .here))

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := ctxWf?_sound _ (by decide +kernel)

example : (resolveIn Λc [] C5names C5src).map ATm.erase = some (tmOfDeriv C5_typed) := by decide

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

The signature writes `fresh` in the result.  The typer reads it as the
version's `Z1Ty`, an existential bounded by `{fs, u}`, and the arrow rule packs
the cell.  The term and the judgment are the version's `Z1_plat`. -/

/-- `freshCell`, bound by an ascription. -/
def Z1progSrc : STm :=
  cls% (λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs})

example : compiledTm Λc (onZ Z1progSrc) = some (tmOfDeriv Z1_plat) := by decide

/-- `readAt` expands the `any`s, of which there are none, and reads `fresh` as
the existential.  This is the version's W4. -/
example : readAt platCtx platSet (Z1TyF k1) = Z1Ty k1 := by decide

/-- Z1 is typed at the version's judgment, from 12 units. -/
theorem Z1_type : judgProg Λc (onZ Z1progSrc) =
    (some (usesOfDeriv Z1_plat, .ty (tyOfDeriv Z1_plat)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ Z1progSrc))
  "Z1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ Z1progSrc))
  "Z1: the target checker rejects the use set evidence"

/-- Z1 compiles. -/
theorem Z1_compiles : (compile {} Λc (onZ Z1progSrc)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z1. -/
theorem Z1_checks : CheckerAccepts {} Λc (onZ Z1progSrc) Z1_compiles :=
  compile_checks_get Z1_compiles

/-! ## `freshCell` bound by a `let`

`Z1defSrc` of `Typer.lean`: the annotation of the `let` writes `fresh` in the
result, which reads as `Z1Ty`, and the closure reaches it by the arrow rule. -/

/-- `freshCell` bound by a `let` is typed at `Z1Ty`, from 31 units. -/
theorem Z1def_type : judgProg Λc (onZ Z1defSrc) =
    (pureAt (onZ Z1defSrc)
      (clsTy% (∀(u : ⊤) ∃[c ⊑ {fs, u}] μ(y. {read : (∀(v : ⊤) ⊤) ^ {y}}) ^ {c}) ^ {fs}),
      ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

example : judgProg Λc (onZ Z1defSrc) = (some ([], .ty (Z1Ty k1)), ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ Z1defSrc))
  "freshCell by a let: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ Z1defSrc))
  "freshCell by a let: the target checker rejects the use set evidence"

/-- `freshCell` bound by a `let` compiles. -/
theorem Z1def_compiles : (compile {} Λc (onZ Z1defSrc)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem Z1def_checks : CheckerAccepts {} Λc (onZ Z1defSrc) Z1def_compiles :=
  compile_checks_get Z1def_compiles

/-! ## The caller of `freshCell`, at `Z1Ctx`

`Z1callerAnn` of `Resolve.lean`.  The `let` becomes a `letex`, and the
elaborated term erases to the term of the version's `Z1_caller`.  The typer
finds `{fc, fs, un}`, and the version's `Z1Use ∪ Z1Use` is reached by one
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
the other.  This is the version's `Z_two_calls_no_level`. -/

/-- `let c1 = fc un in let c2 = fc un in un`, as resolved. -/
def twoCallsAnn : ATm ([],c,c,x,x) :=
  (resolveIn Λc [] z1Names (cls% let c1 = fc un in let c2 = fc un in un)).getD (.path (.var .here))

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
  (resolveIn Λc [] (((z1Names.consC "%").consC "%").cons "v") (cls% let x = fc un in x)).getD
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
result is `fresh`.  The written type resolves to the version's `W3TyAny`, and
the typer reaches `Z2Ty`, whose witness is the parameter. -/

/-- `makeLogger`, bound by an ascription. -/
def Z2src : STm :=
  cls% (λ(l : (∀(u : ⊤) ⊤) ^ {any}).
          let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
        : (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {})

example : resolveTy Λc [] πz.names
    (clsTy% (∀(l : (∀(u : ⊤) ⊤) ^ {any}) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {}) =
      some W3TyAny := by
  decide

example : elaboratedTm {} Λc (onZ Z2src) = some (tmOfDeriv Z2_plat) := by decide +kernel

/-- Z2 is typed at the version's judgment, from 12 units. -/
theorem Z2_type : judgProg Λc (onZ Z2src) =
    (some (usesOfDeriv Z2_plat, .ty (tyOfDeriv Z2_plat)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ Z2src))
  "Z2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ Z2src))
  "Z2: the target checker rejects the use set evidence"

/-- Z2 compiles. -/
theorem Z2_compiles : (compile {} Λc (onZ Z2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z2. -/
theorem Z2_checks : CheckerAccepts {} Λc (onZ Z2src) Z2_compiles :=
  compile_checks_get Z2_compiles

/-! ## Z3: `mk` with a `fresh` result

S2's `mk` with the result written `fresh`.  The typer packs a payload at the
payload's own type, and the literal's precise type is not the iterator type.
So the body ascribes the literal's variable at the iterator type.  The term,
the use set and the type are the version's `Z3_plat`. -/

/-- `mk` with a `fresh` result, its body ascribed. -/
def Z3src : STm :=
  cls% (λ(u : ⊤). let it = ν(i : {C^ : {fs}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {fs}} ∧ {next = λ(v : ⊤). v}) in
                 (it : μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fs})
         : (∀(u : ⊤) μ(i. {C^ : {}..{fs}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}) ^ {fresh})
             ^ {fs})

example : compiledTm Λc (onZ Z3src) = some (tmOfDeriv Z3_plat) := by decide

/-- Z3 is typed at the version's judgment, from 101 units. -/
theorem Z3_type : judgProg Λc (onZ Z3src) =
    (some (usesOfDeriv Z3_plat, .ty (tyOfDeriv Z3_plat)), ⟨defaultFuel - 101, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onZ Z3src))
  "Z3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onZ Z3src))
  "Z3: the target checker rejects the use set evidence"

/-- Z3 compiles. -/
theorem Z3_compiles : (compile {} Λc (onZ Z3src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of Z3. -/
theorem Z3_checks : CheckerAccepts {} Λc (onZ Z3src) Z3_compiles :=
  compile_checks_get Z3_compiles

/-! ## W2: `process` and its call

`W2defSrc` of `Typer.lean` writes the parameter `any`, which reads as the
arrow's own binder.  It elaborates to the version's `W2Tm`.  Its least answer
has the inner closure at its own type, and `W2Ty` is reached by one `sub`.
The call `p f` is typed at the version's `W2CallCtx` at the use set `{f}` and
the type `⊤`. -/

example : elaboratedTm {} Λc (onC W2defSrc) = some W2Tm := by decide +kernel

/-- `process` is typed with its parameter at its own capture binder, from 2
units. -/
theorem W2_type : judgProg Λc (onC W2defSrc) =
    (pureAt (onC W2defSrc) (clsTy% ∀[c](x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c}) ∀(u : ⊤) ⊤),
      ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

example : topReaches {} πc (resolveTop Λc [] πc W2defSrc) [] (.ty W2Ty) = true := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC W2defSrc))
  "W2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC W2defSrc))
  "W2: the target checker rejects the use set evidence"

/-- `process` compiles. -/
theorem W2_compiles : (compile {} Λc (onC W2defSrc)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of `process`. -/
theorem W2_checks : CheckerAccepts {} Λc (onC W2defSrc) W2_compiles :=
  compile_checks_get W2_compiles

/-- The call of `process` is typed at the version's judgment, from 2 units. -/
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

`deepSrc` of `Typer.lean`.  The version's `W2_deep_rejected` says that the
written type is not one the version reads.  The front end rejects it with that
reason, before any goal is asked. -/

/-- The typer rejects W2 deep from a full tank, with the tank unmarked. -/
theorem deep_verdict : judgProg Λc (onC deepSrc) = (none, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- W2 deep does not compile at any budget. -/
theorem deep_rejected (b : Budget) : (compile b Λc (onC deepSrc)).isOk = false :=
  judgProg_rejects deep_verdict b

example : (compile {} Λc (onC deepSrc)).reason?.map Reason.name = some "anyNotOk" := by
  decide +kernel

/-! ## An existential answer at the top

`exTopSrc` of `Typer.lean`: a call of `freshCell` as the body of a `let`
outside every scope.  Its answer is an existential, and no root absorbs the
witness. -/

/-- The typer rejects the program after 19 units, with the tank unmarked. -/
theorem exTop_verdict : judgProg Λc (onZ exTopSrc) = (none, ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- The program does not compile at any budget. -/
theorem exTop_rejected (b : Budget) : (compile b Λc (onZ exTopSrc)).isOk = false :=
  judgProg_rejects exTop_verdict b

example : topRejected {} πz exTopSrc = some "existentialAtTop" := by decide +kernel

/-! ## The existential annotations and a projection

cov2 packs a plain `let` into its existential annotation, with the payload's
own set `{f}` as witness.  cov4 writes the existential's binder below a field,
where the payload's own set is empty and is no witness, and the written bound
`{k1}` is.  cov3 is a closure that projects its parameter, charged its
receiver, which leaves with the parameter. -/

/-- cov2 is typed at its annotation, from 14 units. -/
theorem cov2_type : judgProg Λc (onC cov2Src) =
    (pureAt (onC cov2Src) (clsTy% ∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {k1})
        ∃[c ⊑ {f}] μ(y. {read : (∀(u : ⊤) ⊤) ^ {y}}) ^ {c}),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC cov2Src))
  "cov2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC cov2Src))
  "cov2: the target checker rejects the use set evidence"

/-- cov2 compiles. -/
theorem cov2_compiles : (compile {} Λc (onC cov2Src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov2. -/
theorem cov2_checks : CheckerAccepts {} Λc (onC cov2Src) cov2_compiles :=
  compile_checks_get cov2_compiles

/-- cov4 is typed at its annotation, from 32 units. -/
theorem cov4_type : judgProg Λc (onC cov4Src) =
    (pureAt (onC cov4Src) (clsTy% ∀(p : {a : ⊤ ^ {k1}}) ∃[c ⊑ {k1}] {a : ⊤ ^ {c}}),
      ⟨defaultFuel - 32, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC cov4Src))
  "cov4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC cov4Src))
  "cov4: the target checker rejects the use set evidence"

/-- cov4 compiles. -/
theorem cov4_compiles : (compile {} Λc (onC cov4Src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov4. -/
theorem cov4_checks : CheckerAccepts {} Λc (onC cov4Src) cov4_compiles :=
  compile_checks_get cov4_compiles

/-- cov3 is a pure closure, from 2 units. -/
theorem cov3_type : judgProg Λc (onC cov3Src) =
    (pureAt (onC cov3Src) (clsTy% ∀(o : {a : ⊤ ^ {k1}} ^ {k1}) ⊤ ^ {k1}),
      ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC cov3Src))
  "cov3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC cov3Src))
  "cov3: the target checker rejects the use set evidence"

/-- cov3 compiles. -/
theorem cov3_compiles : (compile {} Λc (onC cov3Src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of cov3. -/
theorem cov3_checks : CheckerAccepts {} Λc (onC cov3Src) cov3_compiles :=
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
the level steps the version's `W1` derives: the outer root below the inner
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

/-! ## W5: the escape of a callback, at the version's context

At `W5Ctx`, the body of a callback under an older root, subcapturing finds the
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
`EscGoalCtx`, which binds `cb`.  The rejection leaves the tank unmarked, so it
holds at every budget. -/

/-- The typer rejects the escape after 31 units, with the tank unmarked. -/
theorem Esc_verdict : judgProg Λc (onC EscSrc) = (none, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-- The escape does not compile at any budget. -/
theorem Esc_rejected (b : Budget) : (compile b Λc (onC EscSrc)).isOk = false :=
  judgProg_rejects Esc_verdict b

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

#eval expect ((resolveTop Λc [] πc EscSrc).map (fun a => escapesAt (synthTop? {} πc a) EscGoalCtx
    [CapAtom.var .here] [CapAtom.cvar escRoot]) == some true)
  "the escape: not rejected at the goal in EscGoalCtx"

#eval expect ((compile {} Λc (onC EscSrc)).reason?.map Reason.name == some "levelEscape")
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

/-! ## The escape by an ascription

`AscEscSrc` of `Typer.lean` writes the same callback with an ascription in
place of the `let` annotation.  An ascription binds too, so the escape is
rejected at the callback's body. -/

/-- The typer rejects the escape by an ascription after 88 units, with the
tank unmarked. -/
theorem AscEsc_verdict : judgProg Λc (onC AscEscSrc) = (none, ⟨defaultFuel - 88, false⟩) := by
  decide +kernel

/-- The escape by an ascription does not compile at any budget. -/
theorem AscEsc_rejected (b : Budget) : (compile b Λc (onC AscEscSrc)).isOk = false :=
  judgProg_rejects AscEsc_verdict b

#eval expect ((compile {} Λc (onC AscEscSrc)).reason?.map Reason.name == some "levelEscape")
  "the escape by an ascription: compile does not reject it"

/-! ## The escape at the top of a program

`TopEscSrc` of `Typer.lean` binds the same callback at the top, where the
result `any` reads as the platform set and the source has no root.  The goal
is `{f} <: {k1, k2}` in `TopGoalCtx`, and the certificate's root is the
universal one, which the source cannot name. -/

/-- The typer rejects the escape at the top after 31 units, with the tank
unmarked. -/
theorem TopEsc_verdict : judgProg Λc (onC TopEscSrc) = (none, ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-- The escape at the top does not compile at any budget. -/
theorem TopEsc_rejected (b : Budget) : (compile b Λc (onC TopEscSrc)).isOk = false :=
  judgProg_rejects TopEsc_verdict b

/-- The context of the goal at the top. -/
def TopGoalCtx : Ctx (Sig.body ([],c,c,x)) :=
  (platCtx.cons cbTy).body (fileS ^ [CapAtom.cvar .here])

/-- The platform set, read in `TopGoalCtx`. -/
def topPlat : CaptureSet (Sig.body ([],c,c,x)) :=
  [CapAtom.cvar (.there (.there (.there (.there (.there .here))))),
    CapAtom.cvar (.there (.there (.there (.there .here))))]

#eval expect ((resolveTop Λc [] πc TopEscSrc).map (fun a => escapesAt (synthTop? {} πc a) TopGoalCtx
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

/-! ## A callback that keeps its capture inside its own scope

`EscOkSrc` of `Typer.lean`: the callback of the escape, annotated with its
result at its own parameter.  What it captures stays inside its own scope, so
it is accepted. -/

/-- The callback is typed at its annotation, from 4 units. -/
theorem EscOk_type : judgProg Λc (onC EscOkSrc) =
    (pureAt (onC EscOkSrc) (clsTy% ∀(g : ⊤) ∀[c](f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c})
        (∀(u : ⊤) μ(w. {read : (∀(u : ⊤) ⊤) ^ {w}}) ^ {f}) ^ {f}),
      ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC EscOkSrc))
  "EscOk: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC EscOkSrc))
  "EscOk: the target checker rejects the use set evidence"

/-- The callback at its own parameter compiles. -/
theorem EscOk_compiles : (compile {} Λc (onC EscOkSrc)).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem EscOk_checks : CheckerAccepts {} Λc (onC EscOkSrc) EscOk_compiles :=
  compile_checks_get EscOk_compiles

/-! ## QP1: a member selected through a recursive shape

`PA1src` of `Typer.lean`: `f : ∀(y : M) y.A` ascribed at `∀(y : M) {a : ⊤}`,
with `M = μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥..{a : ⊤}}))`.  The two `∀` are
compared under `y`, and the upper bound of `y.A` is read off `M` opened at
`y`, three steps down.  Scalac accepts the same program. -/

/-- QP1 is typed at the ascribed type, from 45 units. -/
theorem QP1_type : judgProg Λc (onE PA1src) =
    (pureAt (onE PA1src) (clsTy% ∀(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) y.A)
        ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) {a : ⊤}),
      ⟨defaultFuel - 45, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE PA1src))
  "QP1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE PA1src))
  "QP1: the target checker rejects the use set evidence"

/-- QP1 compiles. -/
theorem QP1_compiles : (compile {} Λc (onE PA1src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of QP1. -/
theorem QP1_checks : CheckerAccepts {} Λc (onE PA1src) QP1_compiles :=
  compile_checks_get QP1_compiles

/-! ## QP4: a field four steps down an upper bound

`y : x.A`, and the field `a` is found by the lookup through `x.A`'s upper
bound, the recursive type opened at `y`, and the right operand twice.
Scalac accepts the same program. -/

/-- QP4 is typed from 28 units. -/
theorem QP4_type : judgProg Λc (onE P4src) =
    (pureAt (onE P4src)
      (clsTy% ∀(x : {A : ⊥ .. μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : ⊤}))}) ∀(y : x.A) ⊤),
      ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE P4src))
  "QP4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE P4src))
  "QP4: the target checker rejects the use set evidence"

/-- QP4 compiles. -/
theorem QP4_compiles : (compile {} Λc (onE P4src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of QP4. -/
theorem QP4_checks : CheckerAccepts {} Λc (onE P4src) QP4_compiles :=
  compile_checks_get QP4_compiles

/-! ## QP5: the second of two function types

`f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)` applied to `y : ⊤`.  The application
tries every function type the lookup finds, and the second accepts the
argument.  Scalac accepts the same program. -/

/-- QP5 is typed from 13 units. -/
theorem QP5_type : judgProg Λc (onE P5src) =
    (pureAt (onE P5src) (clsTy% ∀(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)) ∀(y : ⊤) ⊤),
      ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE P5src))
  "QP5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE P5src))
  "QP5: the target checker rejects the use set evidence"

/-- QP5 compiles. -/
theorem QP5_compiles : (compile {} Λc (onE P5src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of QP5. -/
theorem QP5_checks : CheckerAccepts {} Λc (onE P5src) QP5_compiles :=
  compile_checks_get QP5_compiles

/-! ## R1 to R4: the field that lets the rest of the program type

In each program a projection finds two fields of one name, and only the
second has the member the rest of the program needs.  In R1 the first field
is found through `x.A`'s upper bound.  In R2 both are written.  R3 checks the
projection at an ascription, and R4 binds it under a written `let` type.
The typer keeps every candidate, so each compiles.  Scalac accepts R1 and
R2. -/

/-- R1 is typed from 17 units. -/
theorem R1_type : judgProg Λc (onE R1src) =
    (pureAt (onE R1src) (clsTy% ∀(x : {A : ⊥ .. {a : ⊤}}) ∀(y : x.A ∧ {a : {b : ⊤}}) ⊤),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE R1src))
  "R1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE R1src))
  "R1: the target checker rejects the use set evidence"

/-- R1 compiles. -/
theorem R1_compiles : (compile {} Λc (onE R1src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R1. -/
theorem R1_checks : CheckerAccepts {} Λc (onE R1src) R1_compiles :=
  compile_checks_get R1_compiles

/-- R2 is typed from 10 units. -/
theorem R2_type : judgProg Λc (onE R2src) =
    (pureAt (onE R2src) (clsTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) ⊤), ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE R2src))
  "R2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE R2src))
  "R2: the target checker rejects the use set evidence"

/-- R2 compiles. -/
theorem R2_compiles : (compile {} Λc (onE R2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R2. -/
theorem R2_checks : CheckerAccepts {} Λc (onE R2src) R2_compiles :=
  compile_checks_get R2_compiles

/-- R3 is typed at the ascribed field, from 11 units. -/
theorem R3_type : judgProg Λc (onE R3src) =
    (pureAt (onE R3src) (clsTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) {b : ⊤}),
      ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE R3src))
  "R3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE R3src))
  "R3: the target checker rejects the use set evidence"

/-- R3 compiles. -/
theorem R3_compiles : (compile {} Λc (onE R3src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R3. -/
theorem R3_checks : CheckerAccepts {} Λc (onE R3src) R3_compiles :=
  compile_checks_get R3_compiles

/-- R4 is typed from 9 units. -/
theorem R4_type : judgProg Λc (onE R4src) =
    (pureAt (onE R4src) (clsTy% ∀(y : {a : ⊤} ∧ {a : {b : ⊤}}) ⊤), ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE R4src))
  "R4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE R4src))
  "R4: the target checker rejects the use set evidence"

/-- R4 compiles. -/
theorem R4_compiles : (compile {} Λc (onE R4src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of R4. -/
theorem R4_checks : CheckerAccepts {} Λc (onE R4src) R4_compiles :=
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
theorem chain16_type : judgProg Λc (onE (chainSrc 16)) =
    (pureAt (onE (chainSrc 16)) (chainSTy 16), ⟨defaultFuel - 203, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE (chainSrc 16)))
  "the chain of sixteen links: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE (chainSrc 16)))
  "the chain of sixteen links: the target checker rejects the use set evidence"

/-- The chain of sixteen links compiles. -/
theorem chain16_compiles : (compile {} Λc (onE (chainSrc 16))).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem chain16_checks : CheckerAccepts {} Λc (onE (chainSrc 16)) chain16_compiles :=
  compile_checks_get chain16_compiles

/-- The chain of thirty two links is typed at its written type, from 659
units. -/
theorem chain32_type : judgProg Λc (onE (chainSrc 32)) =
    (pureAt (onE (chainSrc 32)) (chainSTy 32), ⟨defaultFuel - 659, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE (chainSrc 32)))
  "the chain of thirty two links: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE (chainSrc 32)))
  "the chain of thirty two links: the target checker rejects the use set evidence"

/-- The chain of thirty two links compiles. -/
theorem chain32_compiles : (compile {} Λc (onE (chainSrc 32))).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem chain32_checks : CheckerAccepts {} Λc (onE (chainSrc 32)) chain32_compiles :=
  compile_checks_get chain32_compiles

/-! ## X1 and X2: a variable at its own abstract type

X1 is `λ(q : {A : ⊥..⊤}). λ(x : q.A). λ(f : ∀(y : q.A) ⊤). f x`.  The argument
`x` is seen at `q.A ^ {x}`, and the domain is `q.A ^ {}`.  The typer widens the
view whole, the selection included, so `{x}` goes to the empty set and
`q.A <: q.A` holds by identity.  X2 reaches `q.A` through the upper bound of
`p.A`.  Scalac accepts X1. -/

/-- X1. -/
def X1src : STm := cls% λ(q : {A : ⊥ .. ⊤}). λ(x : q.A). λ(f : ∀(y : q.A) ⊤). f x

/-- X2, the argument at `p.A` with `p.A` bounded by `q.A`. -/
def X2src : STm :=
  cls% λ(q : {A : ⊥ .. ⊤}). λ(p : {A : ⊥ .. q.A}). λ(x : p.A). λ(f : ∀(y : q.A) ⊤). f x

/-- X1 is typed from 5 units. -/
theorem X1_type : judgProg Λc (onE X1src) =
    (pureAt (onE X1src)
      (clsTy% ∀(q : {A : ⊥ .. ⊤}) ∀(x : q.A) ∀(f : ∀(y : q.A) ⊤) ⊤),
      ⟨defaultFuel - 5, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE X1src))
  "X1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE X1src))
  "X1: the target checker rejects the use set evidence"

/-- X1 compiles. -/
theorem X1_compiles : (compile {} Λc (onE X1src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of X1. -/
theorem X1_checks : CheckerAccepts {} Λc (onE X1src) X1_compiles :=
  compile_checks_get X1_compiles

/-- X2 is typed from 10 units. -/
theorem X2_type : judgProg Λc (onE X2src) =
    (pureAt (onE X2src)
      (clsTy% ∀(q : {A : ⊥ .. ⊤}) ∀(p : {A : ⊥ .. q.A}) ∀(x : p.A) ∀(f : ∀(y : q.A) ⊤) ⊤),
      ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onE X2src))
  "X2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onE X2src))
  "X2: the target checker rejects the use set evidence"

/-- X2 compiles. -/
theorem X2_compiles : (compile {} Λc (onE X2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of X2. -/
theorem X2_checks : CheckerAccepts {} Λc (onE X2src) X2_compiles :=
  compile_checks_get X2_compiles

/-- The goals of X1 and X2 at the contexts of `Sub.lean`: the variable at its
own abstract type, declared at `{}`, declared at `{κ₁}`, and through an upper
bound.  Each holds in the version. -/
theorem X1_var_empty : Nonempty ((U : CaptureSet ([],x,x)) × HasTy U XCtx (.path (.var .here)) (.ty XT)) :=
  found_nonempty (by decide +kernel : answers (var? XCtx .here XT) 1 = true)

theorem X1_var_cap :
    Nonempty ((U : CaptureSet ([],c,c,x,x)) × HasTy U XkCtx (.path (.var .here)) (.ty XkT)) :=
  found_nonempty (by decide +kernel : answers (var? XkCtx .here XkT) 24 = true)

theorem X2_var :
    Nonempty ((U : CaptureSet ([],x,x,x)) × HasTy U X2Ctx (.path (.var .here)) (.ty X2T)) :=
  found_nonempty (by decide +kernel : answers (var? X2Ctx .here X2T) 5 = true)

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
theorem B1_verdict : judgProg Λc (onE B1src) = (none, ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-- B1 does not compile at any budget. -/
theorem B1_rejected (b : Budget) : (compile b Λc (onE B1src)).isOk = false :=
  judgProg_rejects B1_verdict b

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
theorem A1_verdict : judgProg Λc (onE A1src) = (none, ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- A1 does not compile at any budget. -/
theorem A1_rejected (b : Budget) : (compile b Λc (onE A1src)).isOk = false :=
  judgProg_rejects A1_verdict b

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
theorem BX2_type : judgProg Λc (onC BX2src) =
    (pureAt (onC BX2src)
      (clsTy% ∀(f : (∀(u : ⊤) ⊤) ^ {k1}) (∀(h : (∀(v : □(⊤ ^ {})) ⊤) ^ {}) ⊤) ^ {f}),
      ⟨defaultFuel - 34, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC BX2src))
  "BX2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC BX2src))
  "BX2: the target checker rejects the use set evidence"

/-- BX2 compiles. -/
theorem BX2_compiles : (compile {} Λc (onC BX2src)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of BX2. -/
theorem BX2_checks : CheckerAccepts {} Λc (onC BX2src) BX2_compiles :=
  compile_checks_get BX2_compiles

/-- BX is typed at the ascribed box, from 29 units. -/
theorem BX_type : judgProg Λc (onC BXsrc) =
    (pureAt (onC BXsrc) (clsTy% ∀(f : (∀(u : ⊤) ⊤) ^ {k1}) □(⊤ ^ {})),
      ⟨defaultFuel - 29, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc (onC BXsrc))
  "BX: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc (onC BXsrc))
  "BX: the target checker rejects the use set evidence"

/-- BX compiles. -/
theorem BX_compiles : (compile {} Λc (onC BXsrc)).isOk = true := by decide +kernel

/-- The target checker accepts the translation of BX. -/
theorem BX_checks : CheckerAccepts {} Λc (onC BXsrc) BX_compiles :=
  compile_checks_get BX_compiles

/-! ## LP, PF and LQ2: the recursion limit

LP checks `x : p.A` against `q.B`, through `∀` bodies, and reaches the same
goal under one more binder at every level.  PF is Pierce's divergence of
F<:.  Its goal comes back under a new binder that it names, so no cut ends
it.  LQ2 checks `v : y.B` against `y.A`, two arrows whose codomain goal
mentions the fresh parameter at every level.  Each run ends with the tank
marked, the compiler's recursion limit.  Scalac rejects LP at the declaration
of its cyclic members, a check outside subtyping, and stops on LQ2 with a
cyclic reference and a recursion limit in member lookup. -/

/-- LQ2: `y : μ(s. {T : ⊥..μ(r. {T : ⊥..s.T} ∧ M(r))} ∧ M(s))` with
`M(r) = {B : ⊥..∀(z : r.T) z.B} ∧ {A : ∀(w : r.T) w.A..⊤}`, then `v : y.B`
ascribed at `y.A`. -/
def LQ2src : STm :=
  cls% λ(y : μ(s. {T : ⊥ .. μ(r. {T : ⊥ .. s.T} ∧ ({B : ⊥ .. ∀(z : r.T) z.B} ∧ {A : ∀(w : r.T) w.A .. ⊤}))}
                 ∧ ({B : ⊥ .. ∀(z : s.T) z.B} ∧ {A : ∀(w : s.T) w.A .. ⊤}))).
        λ(v : y.B). (v : y.A)

/-- LP ends with the tank marked after 32737 units. -/
theorem LP_limit : judgProg Λc (onE LPsrc) = (none, ⟨defaultFuel - 32737, true⟩) := by
  decide +kernel

/-- PF ends with the tank marked after 32693 units. -/
theorem PF_limit : judgProg Λc (onE PFsrc) = (none, ⟨defaultFuel - 32693, true⟩) := by
  decide +kernel

/-- LQ2 ends with the tank marked after 32763 units. -/
theorem LQ2_limit : judgProg Λc (onE LQ2src) = (none, ⟨defaultFuel - 32763, true⟩) := by
  decide +kernel

/-! ## The effect theorem

`compile_effect_safety_get` at C2.  The subject is a run `r` of the version's
term from the platform's initial store, and a variable `x` the reached state
reads.  The capability is `k1`.  Its two premises, that the use set the typer
found writes no projection and does not hold `k1`, are decided by the
kernel.  The run is moved onto the compiled program by two decided
equations: the elaborated term is the version's, and the platform the
program resolves to is `πc.plat`. -/

/-- **Effect safety at a named platform and term.**  `compile_effect_safety_get`
with the compiled program's platform and erased term replaced by two that
are equal to them.  For a concrete program both equations are decided, so a
run can be stated over the platform and the term written out. -/
theorem compile_effect_safety_at {b : Budget} {Λ : LabelTable} {p : SProg}
    (h : (compile b Λ p).isOk = true) {P : Platform p.platNames.sig} {t : Tm p.platNames.sig}
    (hP : ((compile b Λ p).get h).1.plat = P) (ht : ((compile b Λ p).get h).2.tm.erase = t)
    {κ : BVar p.platNames.sig .cap} (hp : noProj? ((compile b Λ p).get h).2.use = true)
    (hκ : ((compile b Λ p).get h).2.use.elem (.cvar κ) = false)
    {s : Sig} {st : State s} (run' : Steps (⟨P.store, .nil, t⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] := by
  subst hP ht
  exact compile_effect_safety_get h hp hκ run' hin

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, a variable the reached state reads is not rooted at `k1` in
the matched target state. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] :=
  compile_effect_safety_at C2_compiles (platEq_sound _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r hin

/-! ## The log of a compiled program

`compile_lvl_safety` speaks of each entry of the log `levelSteps` reads off
the derivation.  C2 has 121 entries and S1 has 92. -/

example : (compileLog {} Λc (onC C2src)).length = 121 := by decide +kernel

example : (compileLog {} Λc (onZ S1progSrc)).length = 92 := by decide +kernel

/-! ## The classifier programs

The programs below declare classifiers, a platform whose binders carry
them, and a use set and a kind for the whole program.  They are the
E1, E2 and E3 of `DotMNF/Examples.lean`, written CE1 to CE3 in
`Notation.lean`, the E3 program over three capabilities, and more written
here.  `Λk` is the label table of the classifier examples and `exCls` its
classifier table.

A program declares a use set and a kind.  The use set is binding, and
`compile` moves the derivation to it.  The kind is what the two classified
entry points are asked for: `compileFiltered` when the declared set is a
projection, `compileKinded` otherwise. -/

/-- The rules of a kinding derivation, outermost first. -/
def kindRules {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (g : CapKind Γ C φ) : List String :=
  match g with
  | .nil => ["nil"]
  | .cons g h => "cons" :: (kindRules g ++ kindRules h)
  | .kproj _ => ["kproj"]
  | .kcls _ _ => ["kcls"]
  | .kvar _ g => "kvar" :: kindRules g
  | .kcvar _ _ g => "kcvar" :: kindRules g
  | .ksel _ => ["ksel"]
  | .kprojS g => "kprojS" :: kindRules g
  | .ksub g _ => "ksub" :: kindRules g
  | .kle _ g => "kle" :: kindRules g
termination_by structural g

/-- The rules of the kinding `compileKinded` found. -/
def kindedRules (b : Budget) (Λ : LabelTable) (p : SProg) (φ : Cls.Kind) :
    Option (List String) :=
  (compileKinded b Λ p φ).toOption.map fun r => kindRules r.2.2.kind

/-- The kinding `compileKinded` found and a kinding of the version at the
same judgment have the same translation. -/
def kindedAgrees (b : Budget) (Λ : LabelTable) (p : SProg) (φ : Cls.Kind)
    {s : Sig} {Γ : Ctx s} {C : CaptureSet s} (g : CapKind Γ C φ) : Bool :=
  match compileKinded b Λ p φ with
  | .ok r =>
      if h : p.platNames.sig = s then decide (h ▸ r.2.2.kind.translate = g.translate) else false
  | _ => false

/-- The target checker's verdict on the translation of the kinding
`compileKinded` found. -/
def kindedVerdict (b : Budget) (Λ : LabelTable) (p : SProg) (φ : Cls.Kind) : Bool :=
  match compileKinded b Λ p φ with
  | .ok r => FCdot.checkKindCo r.1.plat.ctx.translate r.2.2.kind.translate r.2.1.use.translate φ
  | _ => false

/-- **The target checker accepts the kinding of a program that kinds.**
`compile_kind_checks` at the record `compileKinded` returns, for a program
whose kinded compile succeeds by a decided test. -/
theorem compile_kind_checks_get {b : Budget} {Λ : LabelTable} {p : SProg} {φ : Cls.Kind}
    (h : (compileKinded b Λ p φ).isOk = true) :
    FCdot.checkKindCo ((compileKinded b Λ p φ).get h).1.plat.ctx.translate
      ((compileKinded b Λ p φ).get h).2.2.kind.translate
      ((compileKinded b Λ p φ).get h).2.1.use.translate φ = true :=
  compile_kind_checks (Verdict.get_eq _ h)

/-- **Filtered effect safety at a named platform and term.**
`compile_filtered_effect_safety` with the compiled program's platform and
erased term replaced by two that are equal to them, for a program whose
filtered compile succeeds by a decided test. -/
theorem compile_filtered_effect_safety_at {b : Budget} {Λ : LabelTable} {p : SProg}
    {φ : Cls.Kind} (h : (compileFiltered b Λ p φ).isOk = true)
    {P : Platform p.platNames.sig} {t : Tm p.platNames.sig}
    (hP : ((compileFiltered b Λ p φ).get h).1.plat = P)
    (ht : ((compileFiltered b Λ p φ).get h).2.1.tm.erase = t)
    {s : Sig} {st : State s} (run' : Steps (⟨P.store, .nil, t⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] → φ.Contains (Γ'.classOf a) := by
  subst hP ht
  exact compile_filtered_effect_safety (Verdict.get_eq _ h) run' hin

/-- **Kinded effect safety at a named platform and term.**
`compile_classified_effect_safety` with the compiled program's platform and
erased term replaced by two that are equal to them, for a program whose
kinded compile succeeds by a decided test. -/
theorem compile_classified_effect_safety_at {b : Budget} {Λ : LabelTable} {p : SProg}
    {φ : Cls.Kind} (h : (compileKinded b Λ p φ).isOk = true)
    {P : Platform p.platNames.sig} {t : Tm p.platNames.sig}
    (hP : ((compileKinded b Λ p φ).get h).1.plat = P)
    (ht : ((compileKinded b Λ p φ).get h).2.1.tm.erase = t)
    {s : Sig} {st : State s} (run' : Steps (⟨P.store, .nil, t⟩ : State p.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename p.platNames.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] → φ.Contains (Γ'.classOf a) := by
  subst hP ht
  exact compile_classified_effect_safety (Verdict.get_eq _ h) run' hin

/-! ## CE1: `Try.apply`, filtered at `only[Control]`

The platform is `ctl : Control, io : IO`.  The program declares the use set
`{ctl, io}.only[Control]` and the kind `only[Control]`.  The typer
synthesizes exactly that set, so `compile` keeps it, and the filtered entry
point reads it as a projection.  The call `f b` returns at
`{b ↾ only[Control]}`, and the `let` of `b` avoids `b` by replacing the
projected atom with the set `b` is declared at.  The term, the use set and
the type are the version's `E1_typed`.

The kinding goal kinds the use set at `only[Control]` too.  It takes `kproj`
at both atoms, where the version's `E1_kind` takes `kcls`.  The two
derivations differ, and the target checker accepts the one found. -/

example : compiledTm Λk CE1src = some (tmOfDeriv E1_typed) := by decide

example : elaboratedTm {} Λk CE1src = some (tmOfDeriv E1_typed) := by decide +kernel

/-- CE1 is typed at the version's judgment, from 45 units. -/
theorem CE1_type : judgProg Λk CE1src =
    (some (usesOfDeriv E1_typed, .ty (tyOfDeriv E1_typed)), ⟨defaultFuel - 45, false⟩) := by
  decide +kernel

example : compiledJudgment {} Λk CE1src = some (usesOfDeriv E1_typed, tyOfDeriv E1_typed) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk CE1src)
  "CE1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE1src)
  "CE1: the target checker rejects the use set evidence"

/-- CE1 compiles. -/
theorem CE1_compiles : (compile {} Λk CE1src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of CE1. -/
theorem CE1_checks : CheckerAccepts {} Λk CE1src CE1_compiles :=
  compile_checks_get CE1_compiles

/-- CE1's use set is the projection at `only[Control]`. -/
theorem CE1_filtered : (compileFiltered {} Λk CE1src (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-- CE1 is kinded at `only[Control]`. -/
theorem CE1_kinded : (compileKinded {} Λk CE1src (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

example : kindedRules {} Λk CE1src (Cls.only Cls.Control) =
    some ["cons", "kproj", "kproj"] := by
  decide +kernel

example : kindedAgrees {} Λk CE1src (Cls.only Cls.Control) E1_kind = false := by
  decide +kernel

example : kindedVerdict {} Λk CE1src (Cls.only Cls.Control) = true := by decide +kernel

/-- The target checker accepts the translation of the kinding of CE1's use
set. -/
theorem CE1_kind_checks :
    FCdot.checkKindCo ((compileKinded {} Λk CE1src (Cls.only Cls.Control)).get CE1_kinded).1.plat.ctx.translate
      ((compileKinded {} Λk CE1src (Cls.only Cls.Control)).get CE1_kinded).2.2.kind.translate
      ((compileKinded {} Λk CE1src (Cls.only Cls.Control)).get CE1_kinded).2.1.use.translate
      (Cls.only Cls.Control) = true :=
  compile_kind_checks_get CE1_kinded

/-- **CE1 reads only `Control` capabilities.**  Along any run of the
version's `E1tm` from the initial store of `E1Plat`, every root of a
variable the reached state reads, in the matched target state, carries a
classifier `only[Control]` admits.  So the run never reads `io`.  This is
`compile_filtered_effect_safety` at CE1, with the platform and the term
compared by the kernel. -/
theorem CE1_reads_only_control {s : Sig} {st : State s}
    (r : Steps (⟨E1Plat.store, .nil, E1tm⟩ : State ([],c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename ([],c,c) s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext E1Plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] →
            (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  compile_filtered_effect_safety_at CE1_filtered (platEq_sound _ _ (by decide +kernel))
    (by decide +kernel) r hin

/-- The log of CE1's derivation has fifty two entries. -/
example : (compileLog {} Λk CE1src).length = 52 := by decide +kernel

/-! ## M1 and M5: mixed and filtered sets on the left

M1 is `{b ↾ only[Control], f}` below the filtered platform set, in `E1Ctx2`,
where `b` is at that set and `f` at `{}`.  M5 is `{ctl}` below the filtered
platform set, the goal a program meets that charges only `ctl` and declares
`{ctl, io}.only[Control]`.  `M5src` is such a program: the typer charges
`{ctl}` and `compile` moves it to the declared set by that goal. -/

/-- M1 holds in the version, found from 172 units. -/
theorem M1_subcap : Nonempty (Subcap E1Ctx2
    [CapAtom.proj (.var (.there .here)) (Cls.only Cls.Control), CapAtom.var .here]
    (CaptureSet.weaken (CaptureSet.weaken E1Filt))) :=
  found_nonempty (by decide +kernel : answers (cap? E1Ctx2
    [CapAtom.proj (.var (.there .here)) (Cls.only Cls.Control), CapAtom.var .here]
    (CaptureSet.weaken (CaptureSet.weaken E1Filt))) 172 = true)

/-- M5 holds in the version, found from 5 units. -/
theorem M5_subcap : Nonempty (Subcap E1PlatCtx [CapAtom.cvar E1ctl] E1Filt) :=
  found_nonempty (by decide +kernel : answers (cap? E1PlatCtx [CapAtom.cvar E1ctl] E1Filt) 5 = true)

/-- A program that charges only `ctl` and declares the filtered set. -/
def M5src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    uses {ctl, io}.only[Control]
    kind only[Control]
    let g = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl}) in
    let r = g g in r

/-- The typer charges `M5src` the set `{ctl}`, from 21 units. -/
theorem M5_type : judgProg Λk M5src =
    (writtenAt Λk exCls M5src (clsSet% {ctl}) (clsTy% ⊤), ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

example : compiledJudgment {} Λk M5src = some (E1Filt, unitTy) := by decide +kernel

#eval expect (compiledVerdict {} Λk M5src)
  "M5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk M5src)
  "M5: the target checker rejects the use set evidence"

/-- `M5src` compiles at its declared set. -/
theorem M5_compiles : (compile {} Λk M5src).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem M5_checks : CheckerAccepts {} Λk M5src M5_compiles :=
  compile_checks_get M5_compiles

/-- Its use set is the projection at `only[Control]`. -/
theorem M5_filtered : (compileFiltered {} Λk M5src (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-! ## W: a restricted variable widened to its restricted set

`f : {ctl, io}` and `g : {f ↾ only[Control]}`, then `g` ascribed at
`{ctl, io}.only[Control]`.  The goal `{f ↾ only[Control]} <: {ctl ↾ only[Control],
io ↾ only[Control]}` widens the restricted atom to `f`'s declared set
restricted to the same kind.  No route through the atoms of the right set
holds, since `io` is not `Control`.  Scalac accepts the same program.  With
`g : {f}` the restriction is gone, `{f}` reaches `io`, and the program is
rejected, as scalac rejects it. -/

/-- W. -/
def WSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    λ(f : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
      λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {f.only[Control]}).
        (g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control])

/-- W with `g` at `{f}`. -/
def WnegSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    λ(f : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
      λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {f}).
        (g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control])

/-- W is typed at its written type, from 393 units. -/
theorem W_type : judgProg Λk WSrc =
    (writtenAt Λk exCls WSrc (clsSet% {})
      (clsTy% ∀(f : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
        ∀(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {f.only[Control]})
          (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]),
      ⟨defaultFuel - 393, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk WSrc)
  "W: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk WSrc)
  "W: the target checker rejects the use set evidence"

/-- W compiles. -/
theorem W_compiles : (compile {} Λk WSrc).isOk = true := by decide +kernel

/-- The target checker accepts the translation of W. -/
theorem W_checks : CheckerAccepts {} Λk WSrc W_compiles :=
  compile_checks_get W_compiles

/-- The goals of W at the contexts of `Sub.lean`, found by the widening of a
restricted atom: the sets from 174 units, the variable from 391. -/
theorem W_subcap : Nonempty (Subcap WCtx1 WL WR) :=
  found_nonempty (by decide +kernel : answers (cap? WCtx1 WL WR) 174 = true)

theorem W_var : Nonempty ((U : CaptureSet ([],c,c,x,x)) × HasTy U WCtx2 (.path (.var .here)) (.ty WT2)) :=
  found_nonempty (by decide +kernel : answers (var? WCtx2 .here WT2) 391 = true)

/-- The typer rejects W with `g : {f}` after 234 units, with the tank
unmarked. -/
theorem Wneg_verdict : judgProg Λk WnegSrc = (none, ⟨defaultFuel - 234, false⟩) := by
  decide +kernel

/-- W with `g : {f}` does not compile at any budget. -/
theorem Wneg_rejected (b : Budget) : (compile b Λk WnegSrc).isOk = false :=
  judgProg_rejects Wneg_verdict b

/-- `f` and then `g : (Unit → Unit) ^ {f}`. -/
def WnegCtx : Ctx ([],c,c,x,x) := WCtx1.cons (arrowS ^ [CapAtom.var .here])

/-- The written type, `(Unit → Unit) ^ {ctl ↾ only[Control], io ↾ only[Control]}`,
seen from `WnegCtx`. -/
def WnegT : Ty ([],c,c,x,x) :=
  arrowS ^ CaptureSet.proj (WnegCtx.lookup (.there .here)).captureSet ctlK

/-- `g` at the written type has no `Alg` derivation. -/
theorem Wneg_not_alg : ¬ Alg ⟨_, WnegCtx, .var .here (varView WnegCtx .here).ty WnegT⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? WnegCtx .here WnegT) 228 = true))

/-- And the reason: `io` is not of kind `only[Control]`. -/
theorem Wneg_io_not_alg : ¬ Alg ⟨_, WCtx1, .kind [CapAtom.cvar (.there E1io)] ctlK⟩ :=
  W_io_kind_not_alg

/-! ## CE2: `Future.apply`, filtered at `except[ThreadLocal]`

The platform is `tl : ThreadLocal, ctl : Control, io : IO`.  The domain of
`f` writes `{any.except[ThreadLocal]}`, which reads as the arrow's own
binder under the filter.  The call asks for `{b}` below
`{b ↾ except[ThreadLocal]}`, which subcapturing finds by `proj` over a
kinding of `{b}`.  The elaborated term, the use set and the type are the
version's `E2_typed`.  The kinding goal kinds the use set by `kproj` at each
of its three atoms, where the version's `E2_kind` takes `kcls`. -/

example : (compiledTm Λk CE2src).map Tm.expand = some (tmOfDeriv E2_typed) := by decide

example : elaboratedTm {} Λk CE2src = some (tmOfDeriv E2_typed) := by decide +kernel

/-- CE2 is typed at the version's judgment, from 56 units. -/
theorem CE2_type : judgProg Λk CE2src =
    (some (usesOfDeriv E2_typed, .ty (tyOfDeriv E2_typed)), ⟨defaultFuel - 56, false⟩) := by
  decide +kernel

example : compiledJudgment {} Λk CE2src = some (usesOfDeriv E2_typed, tyOfDeriv E2_typed) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk CE2src)
  "CE2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE2src)
  "CE2: the target checker rejects the use set evidence"

/-- CE2 compiles. -/
theorem CE2_compiles : (compile {} Λk CE2src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of CE2. -/
theorem CE2_checks : CheckerAccepts {} Λk CE2src CE2_compiles :=
  compile_checks_get CE2_compiles

/-- CE2's use set is the projection at `except[ThreadLocal]`. -/
theorem CE2_filtered :
    (compileFiltered {} Λk CE2src (Cls.except Cls.ThreadLocal)).isOk = true := by
  decide +kernel

example : kindedRules {} Λk CE2src (Cls.except Cls.ThreadLocal) =
    some ["cons", "kproj", "cons", "kproj", "kproj"] := by
  decide +kernel

example : kindedAgrees {} Λk CE2src (Cls.except Cls.ThreadLocal) E2_kind = false := by
  decide +kernel

example : kindedVerdict {} Λk CE2src (Cls.except Cls.ThreadLocal) = true := by decide +kernel

/-- The subcapturing of the call, at `E2IoCtx`, where the argument is charged
to `io`.  The derivation found is another one than the version's
`E2_io_arg`, and the target checker accepts it. -/
example : (Core.cap? E2IoCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))).1.isSome = true := by
  decide +kernel

example : (match (Core.cap? E2IoCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))).1 with
    | some e => decide (e.translate = E2_io_arg.translate)
    | none => true) = false := by
  decide +kernel

#eval expect (match (Core.cap? E2IoCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))).1 with
    | some e => FCdot.checkCap E2IoCtx.translate e.translate
        (CaptureSet.translate [CapAtom.var .here])
        (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal)).translate
    | none => false)
  "CE2: the target checker rejects the subcapturing of the call"

/-- M2: a mixed set on the right.  At `E2IoCtx` a domain
`{ctl, any.except[ThreadLocal]}` reads, after the call substitutes `y`, as
`{κ_ctl, y ↾ except[ThreadLocal]}`.  `{y}` is below it, found from 8 units. -/
theorem M2_subcap : Nonempty (Subcap E2IoCtx [CapAtom.var .here]
    [CapAtom.cvar (.there (.there .here)), CapAtom.proj (.var .here) (Cls.except Cls.ThreadLocal)]) :=
  found_nonempty (by decide +kernel : answers (cap? E2IoCtx [CapAtom.var .here]
    [CapAtom.cvar (.there (.there .here)),
      CapAtom.proj (.var .here) (Cls.except Cls.ThreadLocal)]) 8 = true)

/-- **CE2 never reads a thread-local capability.**  Along any run of the
version's `E2tm` from the initial store of `E2PlatIO`, every root of a
variable the reached state reads carries a classifier `except[ThreadLocal]`
admits.  `compile_filtered_effect_safety` at CE2. -/
theorem CE2_no_thread_local {s : Sig} {st : State s}
    (r : Steps (⟨E2PlatIO.store, .nil, E2tm⟩ : State ([],c,c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename ([],c,c,c) s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext E2PlatIO.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] →
            (Cls.except Cls.ThreadLocal).Contains (Γ'.classOf a) :=
  compile_filtered_effect_safety_at CE2_filtered (platEq_sound _ _ (by decide +kernel))
    (by decide +kernel) r hin

/-- The log of CE2's derivation has fifty two entries. -/
example : (compileLog {} Λk CE2src).length = 52 := by decide +kernel

/-! ## CE3: a client against a kind-bounded member, kinded

The platform is `k1 : Control, k2 : Control`.  The client `c` takes an
object whose member `C` is bounded by the kind `only[Control]` alone.  Two
literals define `C` as `{k1}` and as `{k2}`, and each is retyped at the
client's domain through `capkI`.  The typer types the body `c` at the empty
set, and `compile` moves it to the declared use set `{k1, k2}`.  That set is
not a projection, so the filtered entry point does not apply, and the
kinding goal kinds it by `kcls` twice, the rules of `E3_kind`, with the last
atom kinded alone where `E3_kind` adds `nil`.

The retyping of a literal is compared at the version's judgment.  At
`E3CtxB`, where `a` is bound, the ascription `(a : E3AbsTy ..)` is typed at
the judgment of `E3_abstract_a`. -/

example : compiledTm Λk CE3src = some (tmOfDeriv E3_typed) := by decide

example : elaboratedTm {} Λk CE3src = some (tmOfDeriv E3_typed) := by decide +kernel

/-- CE3 is typed at the empty set and the client's type, from 174 units. -/
theorem CE3_type : judgProg Λk CE3src =
    (some ([], .ty (tyOfDeriv E3_typed)), ⟨defaultFuel - 174, false⟩) := by
  decide +kernel

example : compiledJudgment {} Λk CE3src = some (usesOfDeriv E3_typed, tyOfDeriv E3_typed) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk CE3src)
  "CE3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE3src)
  "CE3: the target checker rejects the use set evidence"

/-- CE3 compiles. -/
theorem CE3_compiles : (compile {} Λk CE3src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of CE3. -/
theorem CE3_checks : CheckerAccepts {} Λk CE3src CE3_compiles :=
  compile_checks_get CE3_compiles

/-- CE3 is kinded at `only[Control]`. -/
theorem CE3_kinded : (compileKinded {} Λk CE3src (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

example : kindedRules {} Λk CE3src (Cls.only Cls.Control) = some ["cons", "kcls", "kcls"] := by
  decide +kernel

example : kindedAgrees {} Λk CE3src (Cls.only Cls.Control) E3_kind = false := by decide +kernel

example : kindedVerdict {} Λk CE3src (Cls.only Cls.Control) = true := by decide +kernel

example : (compileFiltered {} Λk CE3src (Cls.only Cls.Control)).isOk = false := by
  decide +kernel

/-- **CE3 reads only `Control` capabilities.**  Along any run of the
version's `E3tm` from the initial store of `E3Plat`, every root of a
variable the reached state reads carries a classifier `only[Control]`
admits.  `compile_classified_effect_safety` at the kinding the kinding
goal found. -/
theorem CE3_reads_only_control {s : Sig} {st : State s}
    (r : Steps (⟨E3Plat.store, .nil, E3tm⟩ : State ([],c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename ([],c,c) s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext E3Plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] →
            (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  compile_classified_effect_safety_at CE3_kinded (platEq_sound _ _ (by decide +kernel))
    (by decide +kernel) r hin

/-- The platform set at `E3CtxB`. -/
def psE3B : CaptureSet ([],c,c,x,x,x) :=
  CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken [CapAtom.cvar E3k1, CapAtom.cvar E3k2]))

/-- The literal `a` ascribed at the client's domain, at `E3CtxB`. -/
def E3aAsc : ATm ([],c,c,x,x,x) :=
  .asc (.path (.var (.there .here))) (tyOfDeriv (E3_abstract_a (U := [])))

/-- `E3CtxB` is well formed. -/
theorem E3CtxB_wf : E3CtxB.Wf := ctxWf?_sound _ (by decide +kernel)

example : erasedOf (synthIn? {} E3CtxB psE3B E3aAsc) =
    some (tmOfDeriv (E3_abstract_a (U := []))) := by
  decide +kernel

/-- The retyping of `a` is typed at the version's judgment, from 75 units. -/
theorem E3retype_type : judgIn E3CtxB psE3B E3aAsc =
    (some ([], .ty (tyOfDeriv (E3_abstract_a (U := [])))), ⟨defaultFuel - 75, false⟩) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} E3CtxB psE3B E3aAsc) == (true, true))
  "CE3, the retyping of a: the target checker rejects the translation or the use set evidence"

/-- The retyping of `a` is typed at `E3CtxB`. -/
theorem E3retype_compiles : (synthIn? {} E3CtxB psE3B E3aAsc).isOk = true := by
  decide +kernel

/-- The target checker accepts the translation of the retyping of `a` at
the translation of `E3CtxB`. -/
theorem E3retype_checks :
    FCdot.checkTmE E3CtxB.translate
      ((synthIn? {} E3CtxB psE3B E3aAsc).get E3retype_compiles).deriv.translate
      ((synthIn? {} E3CtxB psE3B E3aAsc).get E3retype_compiles).ans.translate = true :=
  synthIn_checks_get E3CtxB_wf E3retype_compiles

/-- The log of CE3's derivation has ninety eight entries. -/
example : (compileLog {} Λk CE3src).length = 98 := by decide +kernel

/-- R2: over E3's platform, C2's client has `x` with `{C : {}..{κ₁, κ₂}}`.
`{x.C}` is kinded at `only[Control]` through the member's upper bound, whose
two binders are `Control`, from 27 units. -/
theorem R2_kind : Nonempty (CapKind (C2CtxG E3PlatCtx E3k1 E3k2)
    [CapAtom.sel (.there (up .here)) lC] (Cls.only Cls.Control)) :=
  found_nonempty (by decide +kernel : answers (kind? (C2CtxG E3PlatCtx E3k1 E3k2)
    [CapAtom.sel (.there (up .here)) lC] (Cls.only Cls.Control)) 27 = true)

/-! ## CE3 over three `Control` capabilities

A third `Control` capability changes no bound.  The program gains `k3`, a
third literal `d` with `C` defined as `{k3}`, and its call.  The client's
domain is read at `{k1, k2, k3}`, and the kinding of the use set takes the
rules of `E3_kind3`.  At `E3CtxD`, where `d` is bound, the ascription of `d`
at the client's domain is typed at the judgment of `E3_abstract_c`. -/

/-- CE3 over the platform `k1, k2, k3`, all `Control`. -/
def CE3sSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [k1 : Control, k2 : Control, k3 : Control]
    uses {k1, k2, k3}
    kind only[Control]
    let c : (∀(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2, k3})
               (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {x, x.C}) ^ {} =
              λ(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2, k3}).
                λ(u : ⊤ ^ {}). let g = x.run in g u in
    let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k1}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k2}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let d = ν(z : {C^ : {k3}..{k3}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k3}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let ga = c a in
    let gb = c b in
    let gd = c d in
    c

example : resolvePlatform exCls CE3sSrc.platform = some E3Plat3 := rfl

/-- CE3 over three capabilities is typed at the empty set and the written
type of `c`, from 253 units. -/
theorem CE3s_type : judgProg Λk CE3sSrc =
    (writtenAt Λk exCls CE3sSrc (clsSet% {})
      (clsTy% (∀(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2, k3})
               (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {x, x.C}) ^ {}),
      ⟨defaultFuel - 253, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk CE3sSrc)
  "CE3 over three capabilities: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE3sSrc)
  "CE3 over three capabilities: the target checker rejects the use set evidence"

/-- CE3 over three capabilities compiles. -/
theorem CE3s_compiles : (compile {} Λk CE3sSrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem CE3s_checks : CheckerAccepts {} Λk CE3sSrc CE3s_compiles :=
  compile_checks_get CE3s_compiles

example : kindedRules {} Λk CE3sSrc (Cls.only Cls.Control) =
    some ["cons", "kcls", "cons", "kcls", "kcls"] := by
  decide +kernel

/-- The platform set at `E3CtxD`. -/
def psE3D : CaptureSet ([],c,c,c,x) :=
  CaptureSet.weaken [CapAtom.cvar E3k1', CapAtom.cvar E3k2', CapAtom.cvar E3k3]

/-- The literal `d` ascribed at the client's domain, at `E3CtxD`. -/
def E3dAsc : ATm ([],c,c,c,x) := .asc (.path (.var .here)) (tyOfDeriv E3_abstract_c)

/-- The retyping of `d` is typed at the version's judgment, from 75 units. -/
theorem E3retypeD_type : judgIn E3CtxD psE3D E3dAsc =
    (some (usesOfDeriv E3_abstract_c, .ty (tyOfDeriv E3_abstract_c)),
      ⟨defaultFuel - 75, false⟩) := by
  decide +kernel

example : erasedOf (synthIn? {} E3CtxD psE3D E3dAsc) = some (tmOfDeriv E3_abstract_c) := by
  decide +kernel

#eval expect (openVerdicts (synthIn? {} E3CtxD psE3D E3dAsc) == (true, true))
  "CE3, the retyping of d: the target checker rejects the translation or the use set evidence"

/-! ## CE4: a closure read off a kind-bounded member, handed to a filtered domain

CE3's client with one more step.  `h` takes a closure at the domain
`{any.only[Control]}`, and the client hands it `g`, the closure it read off
`x.run` at `{x.C}`.  The call asks for `{g}` below `{g ↾ only[Control]}`.
Subcapturing finds it by `proj` over a kinding of `{g}`: `kvar` to
`{x.C}`, then `ksel` at the member of `x` the lookup finds.  The version
writes that kinding, at the client's context, as `E3_client_kind`. -/

/-- CE4. -/
def CE4src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [k1 : Control, k2 : Control]
    uses {k1, k2}
    kind only[Control]
    let h = λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.only[Control]}). g in
    let c = λ(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤ ^ {}). let g = x.run in let g2 = h g in g2 u in
    let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k1}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k2}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let ga = c a in
    let gb = c b in
    c

example : (compiledTm Λk CE4src).map Tm.expand = elaboratedTm {} Λk CE4src := by decide +kernel

/-- CE4 is typed at the empty set and the client's type of CE3, from 212
units. -/
theorem CE4_type : judgProg Λk CE4src =
    (some ([], .ty (tyOfDeriv E3_typed)), ⟨defaultFuel - 212, false⟩) := by
  decide +kernel

example : (compiledJudgment {} Λk CE4src).map (·.1) = some E3Uses := by decide +kernel

#eval expect (compiledVerdict {} Λk CE4src)
  "CE4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE4src)
  "CE4: the target checker rejects the use set evidence"

/-- CE4 compiles. -/
theorem CE4_compiles : (compile {} Λk CE4src).isOk = true := by decide +kernel

/-- The target checker accepts the translation of CE4. -/
theorem CE4_checks : CheckerAccepts {} Λk CE4src CE4_compiles :=
  compile_checks_get CE4_compiles

example : kindedRules {} Λk CE4src (Cls.only Cls.Control) = some ["cons", "kcls", "kcls"] := by
  decide +kernel

/-- At `E3ClientCtx` the kinding goal kinds `{x.C}` at `only[Control]` by
`ksel`, the rule of `E3_client_kind`, at the member the lookup finds. -/
example : (Core.kind? E3ClientCtx E3ClosureSet (Cls.only Cls.Control)).1.map kindRules =
    some ["ksel"] := by
  decide +kernel

#eval expect (match (Core.kind? E3ClientCtx E3ClosureSet (Cls.only Cls.Control)).1 with
    | some g => decide (g.translate = E3_client_kind_plat.translate)
    | none => false)
  "CE4: the kinding found is not E3_client_kind"

/-- And `{g}` below `{g ↾ only[Control]}` there, the goal of the call. -/
example : subcapFound {} E3ClientCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.Control)) = true := by
  decide +kernel

/-! ## CE4 with the member bounded by an unrelated classifier

The client of CE4 alone, with the member `C` bounded by `only[IO]`.  The call
`h g` asks for `{g}` below `{g ↾ only[Control]}`, so for a kinding of `{x.C}`
at `only[Control]`.  `ksel` gives `only[IO]`, which is no subkind of
`only[Control]`, and no other rule kinds `{x.C}`.  The program is rejected
with the tank unmarked, as scalac rejects it.  The same client with the
member bounded by `only[Control]` compiles. -/

/-- CE4's client with the member bounded by `only[IO]`. -/
def CE4negSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [k1 : Control, k2 : Control]
    let h = λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.only[Control]}). g in
    let c = λ(x : μ(z. {C^ : only[IO]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤ ^ {}). let g = x.run in let g2 = h g in g2 u in
    c

/-- CE4's client with the member bounded by `only[Control]`. -/
def CE4posSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [k1 : Control, k2 : Control]
    let h = λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.only[Control]}). g in
    let c = λ(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤ ^ {}). let g = x.run in let g2 = h g in g2 u in
    c

/-- The typer rejects the client at `only[IO]` after 84 units, with the tank
unmarked. -/
theorem CE4neg_verdict : judgProg Λk CE4negSrc = (none, ⟨defaultFuel - 84, false⟩) := by
  decide +kernel

/-- The client at `only[IO]` does not compile at any budget. -/
theorem CE4neg_rejected (b : Budget) : (compile b Λk CE4negSrc).isOk = false :=
  judgProg_rejects CE4neg_verdict b

/-- The member shape of the client at `only[IO]`, with the self at `z`. -/
def CE4negAbs {s : Sig} (z : BVar s .var) : Shape s :=
  .and (.capk lC (Cls.only Cls.IO)) (.fld lrun (arrowS ^ [CapAtom.sel z lC]))

/-- The client's context over E3's platform, `E3ClientCtx` with the member
bounded by `only[IO]`: `x`, the unit argument, then `g : (Unit → Unit) ^ {x.C}`. -/
def CE4negCtx : Ctx (Sig.body (Sig.body ([],c,c)),x) :=
  (Ctx.body (Ctx.body E3PlatCtx ((Shape.mu (CE4negAbs .here)) ^
    [CapAtom.cvar (.there E3k1), CapAtom.cvar (.there E3k2)])) unitTy).cons
    (arrowS ^ [CapAtom.sel (up .here) lC])

/-- `{x.C}` at `only[Control]` has no `Alg` derivation. -/
theorem CE4neg_not_alg :
    ¬ Alg ⟨_, CE4negCtx, .kind [CapAtom.sel (.there (up .here)) lC] (Cls.only Cls.Control)⟩ :=
  kind?_reject (rejects_eq (by decide +kernel :
    rejects (kind? CE4negCtx [CapAtom.sel (.there (up .here)) lC] (Cls.only Cls.Control)) 19 = true))

/-- The goal of the call, `{g} <: {g ↾ only[Control]}`, has no `Alg`
derivation. -/
theorem CE4neg_call_not_alg :
    ¬ Alg ⟨_, CE4negCtx, .cap [CapAtom.var .here]
      (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.Control))⟩ :=
  cap?_reject (rejects_eq (by decide +kernel : rejects (cap? CE4negCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.Control))) 60 = true))

/-- The client at `only[Control]` is typed from 50 units. -/
theorem CE4pos_type : judgProg Λk CE4posSrc =
    (some ([], .ty (tyOfDeriv E3_typed)), ⟨defaultFuel - 50, false⟩) := by
  decide +kernel

/-- The client at `only[Control]` compiles. -/
theorem CE4pos_compiles : (compile {} Λk CE4posSrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem CE4pos_checks : CheckerAccepts {} Λk CE4posSrc CE4pos_compiles :=
  compile_checks_get CE4pos_compiles

/-! ## CE5: a thread-local body passed to `Future.apply`

CE2's `f` applied to a body at `{tl}`.  The call asks for `{b}` below
`{b ↾ except[ThreadLocal]}`, which needs `{tl}` kinded at
`except[ThreadLocal]`.  It is proved that the set `kvar` descends to from
`{b}` is kinded at `except[ThreadLocal]` by no derivation
(`FCdot.Examples.E2_tl_descent_not_capKind`), and the front end finds no
derivation, with the tank unmarked.  The same program with the body at
`{io}` compiles. -/

/-- CE5. -/
def CE5src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [tl : ThreadLocal, ctl : Control, io : IO]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {tl}) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body}) ^ {}) in
    let r = f b in
    r

/-- CE5 with the body at `{io}`. -/
def CE5ioSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [tl : ThreadLocal, ctl : Control, io : IO]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {io}) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body}) ^ {}) in
    let r = f b in
    r

/-- The typer rejects CE5 after 40 units, with the tank unmarked. -/
theorem CE5_verdict : judgProg Λk CE5src = (none, ⟨defaultFuel - 40, false⟩) := by
  decide +kernel

/-- CE5 does not compile at any budget. -/
theorem CE5_rejected (b : Budget) : (compile b Λk CE5src).isOk = false :=
  judgProg_rejects CE5_verdict b

/-- At CE5's platform with an argument at `{tl}`, the goal of the call has no
`Alg` derivation. -/
theorem CE5_not_alg : ¬ Alg ⟨_, E2TlCtx, .cap [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))⟩ :=
  CE5_cap_not_alg

/-- CE5 with an input-output body is typed at `{io}` and the object at
`{io}`, from 34 units. -/
theorem CE5io_type : judgProg Λk CE5ioSrc =
    (writtenAt Λk exCls CE5ioSrc (clsSet% {io})
      (clsTy% μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {io}),
      ⟨defaultFuel - 34, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λk CE5ioSrc)
  "CE5 with an IO body: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λk CE5ioSrc)
  "CE5 with an IO body: the target checker rejects the use set evidence"

/-- CE5 with an input-output body compiles. -/
theorem CE5io_compiles : (compile {} Λk CE5ioSrc).isOk = true := by decide +kernel

/-- The target checker accepts its translation. -/
theorem CE5io_checks : CheckerAccepts {} Λk CE5ioSrc CE5io_compiles :=
  compile_checks_get CE5io_compiles

/-! ## The run tests

`compileAndRun` at a step budget of 40, printed with the platform's own
names.  Each run is pinned at the step count at which it becomes final.

S2 answers with `un`, the identity it passed to the iterator, in fifteen
steps.  C2 answers with the client at `b` in twelve.  E2 answers with the
identity at the literal's member in six.  The classifier programs run over
their classified platforms, whose classifiers leave no trace in the store.
CE1 answers with the object `Try.apply` built, in seven steps, and so does
CE2.  CE3 answers with the client, in twelve. -/

/-- The step budget of the runs. -/
def runBudget : Nat := 40

/-- Whether the driver's answer is a final state.  It is `false` when the
program does not compile. -/
def runFinal? (b : Budget) (m : Nat) (Λ : LabelTable) (p : SProg) : Bool :=
  match compileAndRun b m Λ p with
  | .ok r => final? r.2
  | _ => false

#eval ppRunOver Λc [] ["fs", "k2"] (compileAndRun {} runBudget Λc (onZ S2src))

example : ppRunTmOver Λc [] ["fs", "k2"] (compileAndRun {} runBudget Λc (onZ S2src)) = "x3" := by
  decide +kernel

example : (runFinal? {} 15 Λc (onZ S2src) && ! runFinal? {} 14 Λc (onZ S2src)) = true := by
  decide +kernel

#eval ppRunOver Λc [] ["k1", "k2"] (compileAndRun {} runBudget Λc (onC C2src))

example : ppRunTmOver Λc [] ["k1", "k2"] (compileAndRun {} runBudget Λc (onC C2src)) = "x6" := by
  decide +kernel

example : (runFinal? {} 12 Λc (onC C2src) && ! runFinal? {} 11 Λc (onC C2src)) = true := by
  decide +kernel

#eval ppRun Λc [] (compileAndRun {} runBudget Λc (onE E2src))

example : ppRunTm Λc [] (compileAndRun {} runBudget Λc (onE E2src)) = "x1" := by
  decide +kernel

example : (runFinal? {} 6 Λc (onE E2src) && ! runFinal? {} 5 Λc (onE E2src)) = true := by
  decide +kernel

#eval ppRunOver Λk exCls ["ctl", "io"] (compileAndRun {} runBudget Λk CE1src)

example : ppRunTmOver Λk exCls ["ctl", "io"] (compileAndRun {} runBudget Λk CE1src) = "x4" := by
  decide +kernel

example : (runFinal? {} 7 Λk CE1src && ! runFinal? {} 6 Λk CE1src) = true := by
  decide +kernel

#eval ppRunOver Λk exCls ["tl", "ctl", "io"] (compileAndRun {} runBudget Λk CE2src)

example : ppRunTmOver Λk exCls ["tl", "ctl", "io"] (compileAndRun {} runBudget Λk CE2src) =
    "x5" := by
  decide +kernel

example : (runFinal? {} 7 Λk CE2src && ! runFinal? {} 6 Λk CE2src) = true := by
  decide +kernel

#eval ppRunOver Λk exCls ["k1", "k2"] (compileAndRun {} runBudget Λk CE3src)

example : ppRunTmOver Λk exCls ["k1", "k2"] (compileAndRun {} runBudget Λk CE3src) = "x2" := by
  decide +kernel

example : (runFinal? {} 12 Λk CE3src && ! runFinal? {} 11 Λk CE3src) = true := by
  decide +kernel

end Examples

end ClassifiersFrontend
