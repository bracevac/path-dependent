import Coercions.Classifiers.Frontend.Pipeline
import Coercions.Classifiers.Frontend.Pretty

/-!
# The examples end to end

This module takes example programs through the whole front end and checks the
verdicts in the kernel.  The programs come from `DotMNF/Examples.lean`,
`Notation.lean` and `Typer.lean`, and some are written here.  "The version"
below is the calculus `Classifiers.DotMNF`.  Where it has a hand written
derivation of a program, the term and the judgment are compared with it.

The capture programs come first.  They declare no classifier, so each is a
whole program over plain platform binders, built by `SProg.plain`.  The pure
programs run over the empty platform.  The others run over the platform
`k1, k2` (the version's `platCtx`), or over `fs, k2` when the capability is a
file system.

The classifier programs follow.  CE1 to CE3 are E1, E2 and E3 of the version's
classifier examples: `Try.apply`, `Future.apply`, and a client against a member
bounded by a kind.  Each declares its classifiers, a platform whose binders
carry them, a use set and a kind.  CE3 is also run over three capabilities.
CE4 reads a closure off a kind-bounded member and hands it to a filtered
domain.  CE5 passes a thread-local body to `Future.apply`, which the calculus
refuses.  W ascribes a restricted variable at its restricted set.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer, the kinding goal and the machine.  A level escape is
included.  `certify?` reads the resolution `FCdot.Ctx.caps`, which is well
founded, through its structural twin `capsK`, so the kernel checks those
verdicts too (`compile_rejected_goal`, `TopEsc_compile_rejected`).  The
certificate at the goal is also proved by hand (`Esc_rejected'`,
`top_escape_rejected`).  Every check runs at `defaultFuel`, the one field of
the default budget `{}`.

For a program that compiles:

- The term, by `decide`.  This is the resolved term, or the erasure of the
  elaborated term when the typer inserted a box, an unboxing or an unpacking
  (then by `decide +kernel`, since it runs the typer).
- `Ek_type`: the use set and the answer the typer finds and the tank it leaves,
  by `decide +kernel` (`judgProg`).  The tank left is `defaultFuel` minus the
  units the typing used, and it is unmarked.  A program that declares a use set
  is moved to it by `compile`, and the judgment `compile` returns is checked
  too.
- The target checker's verdict on the translation of the derivation and on the
  use set evidence, through `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program and has no hypothesis.

A program the version types under a context is typed there.  Its `Ek_type` is
a fact about `judgIn`, its `Ek_compiles` about `synthIn?`, and its `Ek_checks`
is `synthIn_checks_get`, the open twin of `compile_checks_get`.

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
equality and the typer may reach a judgment by another route.  The terms, use
sets and types of the version are read off its derivations by `tmOfDeriv`,
`usesOfDeriv` and `tyOfDeriv`.  A judgment written here is a set and a type in
the notation, resolved over the program's platform (`writtenAt`, `pureAt`).
Kindings and subcapturings are compared on their translations, since
`FCdot.KindCo` and `FCdot.CapCo` have decidable equality.

## The programs by verdict

Accepted at the version's judgment: E5, E6 at `E6Ctx1`, E7, E8, C7 with its
boxes written and with no box written, S3, S1, S2, Z1, Z2, Z3, the call of
`process` at `W2CallCtx`, the unpacking at `Z1Ctx` whose answer is existential,
CE1, CE2, and the retypings of CE3's literals at the kind bound.

Accepted at a least judgment, from which the version's judgment is reached by
one `sub`: C2 at `{k2}`, C5 at `{it, it.C}`, the caller of `freshCell` at
`{fc, fs, un}`, and `process`.  E2 is typed at the type avoidance gives,
`∀(y : (∀(w : ⊤) ⊥) ^ {}) ⊤`, where the version's derivation concludes `⊤`.
CE3 and CE4 are typed at the empty set and moved to their declared sets.

Accepted at a judgment written here: `freshCell` bound by a `let` whose answer
is written with `fresh`, the existential annotations cov2 and cov4, the
projection cov3, a callback that keeps what it captures inside its own scope, a
capture parameter that is called, two calls of `freshCell`, an unpacking whose
payload leaves by the level rule, CE3 over three capabilities and CE5 with an
input-output body.  CE1b, CE1 with its filtered closure called, at the
filtered set it declares.

Accepted although no search over the declared types of the context finds it:
QP1, a function at a member selected through a recursive shape.  QP4, a field
four steps down the upper bound of a selection.  QP5, an intersection of two
function types applied to an argument only the second accepts.  R1 to R4, a
projection with two fields of which only the second lets the rest of the
program type.  E1s and E3s, which are E1 and E3 with the middle type written.
The alias chains of sixteen and thirty two links.  BX2 and BX, where a boxed
variable meets a boxed goal, unboxing fails and boxing succeeds.  X1 and X2, a
variable at its own abstract type, which the typer widens whole.  W, a
restricted variable widened to its restricted set.  The goals M1, M2 and M5 of
a mixed or filtered set, and R2, a selection off a set-bounded member kinded
through its upper bound.

Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
program does not write, and the typer chooses none.  A1 has a written `let`
annotation the bound value does not meet, and a written annotation binds.  CE4
with its member bounded by an unrelated classifier has no kinding of the
closure's set.  W without the restriction on its variable reaches `io`, which
is not `Control`.  CE5 has no kinding of its thread-local argument.  Each has
its `¬ Alg` fact.  Rejected with a reason: `any` below a field of a domain, an
existential answer outside every scope, and the three escapes of a callback.
The escape and the escape at the top carry a certificate at the goal the typer
reached, and the kernel checks the verdict of `compile` on both.

At the recursion limit: LP, a check through `∀` bodies that reaches the same
goal under one more binder at every level.  PF, Pierce's divergence of F<:,
whose goal comes back under a new binder that it names.  LQ2, whose goal
compares two arrows with a codomain at the fresh parameter at every level.

## Kindings, levels, effects and runs

The kinding goal tries `kproj` first, so it kinds a restricted use set atom by
atom with `kproj`, where the version's kindings of E1 and E2 use `kcls`.  It
kinds the last atom of a set alone, where the version's kindings add `nil`.
The rules it takes are pinned, and the target checker accepts each.

The checks W1 and W5 ask subcapturing for the steps of the level order at the
version's contexts.  `C2_never_reads_k1` is the plain effect theorem at C2.
`CE1_reads_only_control`, `CE2_no_thread_local` and `CE3_reads_only_control`
are the classified ones: every root of a variable a run reads carries a
classifier the declared kind admits.  Their runs read only closures declared at
the empty set.  `CE1b_reads_only_control` is the instance whose run reads a
closure declared at a filtered set that names `io`.  The logs of C2, S1, CE1, CE2 and CE3 are
pinned.  S2, C2, E2, CE1, CE2 and CE3 are run from their platform's initial
store, printed with the platform's own names, and pinned at the step count at
which they become final.

## Annotations erased

The closed programs above, the programs of `Elab.lean` with their written
forms, and the classifier programs are taken through the front end again with
the annotations of their bodies erased, in five ways: every lambda domain (`D`),
every self shape (`S`), the domain of every lambda passed as an argument
(`A`), the domain of every lambda in a checked position (`C`), and `C` with
every self shape erased too (`G`).  The classifier declarations, the platform,
the declared use set and the declared kind stay as written.  `row` gives the
verdict on each, by `decide +kernel`.  `RejectedWith`, `erasedCell_same` and
`erasedCell_other` read a cell as a fact about `compile`.  Each erased program
that compiles has its `_checks` theorem.

## Completeness at the direct sites

Each erased program whose empty slots sit at direct sites, as `Canon` of
`Pipeline.lean` names them, has a `_complete` theorem: it compiles as its
written form does, header, fill, term, use set, type and derivation, at every
budget from some fuel on (`CompilesAs`, `compile_complete_canonAt`).  These
are the erased programs of the tables that compile at the written body but
those whose self shapes the rounds form, and SideCurry, whose inner lambda
takes its domain through an intersection.  Mid is a call argument the typer
accepts at a formal other than the dominant one, which the elaborator
rejects.
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
cannot meet the premise.  So the program resolves with every slot of its body
written, and `compile_full` makes its compile the typer's verdict. -/
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
    rw [compile_full hr]
    unfold compileLanded
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

/-- `ctxEq` decides equality. -/
theorem ctxEq_sound : ∀ {s : Sig} (Γ Δ : Ctx s), ctxEq Γ Δ = true → Γ = Δ
  | _, .nil, .nil, _ => rfl
  | _, .cons Γ' T, .cons Δ' U, h => by
      simp only [ctxEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, ctxEq_sound Γ' Δ' h.2]
  | _, .consSelf Γ' d S U, .consSelf Δ' d' S' U', h => by
      simp only [ctxEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, ctxEq_sound Γ' Δ' h.2]
  | _, .consC Γ', .consC Δ', h => by
      rw [ctxEq_sound Γ' Δ' (by simpa [ctxEq] using h)]
  | _, .consRoot Γ', .consRoot Δ', h => by
      rw [ctxEq_sound Γ' Δ' (by simpa [ctxEq] using h)]
  | _, .consInst Γ' C, .consInst Δ' D, h => by
      simp only [ctxEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, ctxEq_sound Γ' Δ' h.2]
  | _, .consCls Γ' k, .consCls Δ' k', h => by
      simp only [ctxEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, ctxEq_sound Γ' Δ' h.2]
  | _, .cons _ _, .consSelf _ _ _ _, h => by simp [ctxEq] at h
  | _, .consSelf _ _ _ _, .cons _ _, h => by simp [ctxEq] at h
  | _, .consC _, .consRoot _, h => by simp [ctxEq] at h
  | _, .consC _, .consInst _ _, h => by simp [ctxEq] at h
  | _, .consC _, .consCls _ _, h => by simp [ctxEq] at h
  | _, .consRoot _, .consC _, h => by simp [ctxEq] at h
  | _, .consRoot _, .consInst _ _, h => by simp [ctxEq] at h
  | _, .consRoot _, .consCls _ _, h => by simp [ctxEq] at h
  | _, .consInst _ _, .consC _, h => by simp [ctxEq] at h
  | _, .consInst _ _, .consRoot _, h => by simp [ctxEq] at h
  | _, .consInst _ _, .consCls _ _, h => by simp [ctxEq] at h
  | _, .consCls _ _, .consC _, h => by simp [ctxEq] at h
  | _, .consCls _ _, .consRoot _, h => by simp [ctxEq] at h
  | _, .consCls _ _, .consInst _ _, h => by simp [ctxEq] at h

/-- A verdict that rejects by a level escape at the goal `C <: D` in the
context `Γ`, with the certificate's root `r`. -/
def rejectsAt {α : Type} {s : Sig} (v : Verdict α) (Γ : Ctx s) (C D : CaptureSet s)
    (r : FCdot.CapAtom s) : Bool :=
  match v with
  | .rejected (.levelEscape (s := s') Γ' C' D' r' _) =>
      if h : s' = s then
        ctxEq (h ▸ Γ') Γ && decide (h ▸ C' = C) && decide (h ▸ D' = D) && decide (h ▸ r' = r)
      else false
  | _ => false

/-- `rejectsAt` decides that the verdict is that rejection.  The certificate
says that no member-free subcapturing proves the goal. -/
theorem rejectsAt_sound {α : Type} {s : Sig} {v : Verdict α} {Γ : Ctx s}
    {C D : CaptureSet s} {r : FCdot.CapAtom s} (h : rejectsAt v Γ C D r = true) :
    ∃ cert : ¬ ∃ d : Subcap Γ C D, d.MemberFree,
      v = .rejected (.levelEscape Γ C D r cert) := by
  match v, h with
  | .rejected (.levelEscape (s := s') Γ' C' D' r' cert), h =>
      simp only [rejectsAt] at h
      split at h
      · rename_i hs
        subst hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hΓ, hC⟩, hD⟩, hr⟩ := h
        cases ctxEq_sound _ _ hΓ
        subst hC hD hr
        exact ⟨cert, rfl⟩
      · exact absurd h (by simp)

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

/-- The typer rejects E1, with the tank unmarked. -/
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

/-- E2 is typed at the avoided type. -/
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

/-- The typer rejects E3, with the tank unmarked. -/
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

/-- The typer rejects E4, with the tank unmarked. -/
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

/-- E5 is typed at the version's judgment. -/
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

/-- E6 is typed at `E6Ctx1` at the version's judgment. -/
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

/-- E7 is typed at the version's judgment. -/
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

/-- E8 is typed at the version's judgment. -/
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

/-- E1 with the middle written is typed at `∀(x : E1Dom) E1Res`. -/
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

/-- E3 with the middle written is typed at `∀(x : E3Dom) ∀(z : E3T2) E3T1`. -/
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

/-- C7 with its boxes written is typed at the version's judgment. -/
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

/-- C7 with no box written is typed at the version's judgment. -/
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

/-- **C7 is compiled faithfully, and not to its resolved body.**  The
elaborated term differs from the resolved body, since the typer inserted
`□ f1`, `□ f2` and `{k1} ⊸ e`.  The two have the same skeleton, by
`compile_faithful_get`. -/
theorem C7_faithful :
    ((compile {} Λc (onC C7src)).get C7_compiles).2.tm ≠
        ((compile {} Λc (onC C7src)).get C7_compiles).1.body ∧
      ATm.skel ((compile {} Λc (onC C7src)).get C7_compiles).2.tm =
        ATm.skel ((compile {} Λc (onC C7src)).get C7_compiles).1.body :=
  ⟨by decide +kernel, (compile_faithful_get C7_compiles).2.2⟩

/-- C7 with its boxes written and C7 with none have the same skeleton. -/
example : ATm.skel ((compile {} Λc (onC C7boxSrc)).get C7box_compiles).1.body =
    ATm.skel ((compile {} Λc (onC C7src)).get C7_compiles).1.body := by
  decide +kernel

/-- Skeletons tell programs apart: those of C7 and E2 differ. -/
example : ATm.skel ((compile {} Λc (onC C7src)).get C7_compiles).2.tm ≠
    ATm.skel ((compile {} Λc (onE E2src)).get E2_compiles).2.tm := by
  decide +kernel

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

/-- S3 is typed at the version's judgment. -/
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

/-- C2 is typed at `{k2}` and `(⊤ → ⊤) ^ {k2}`. -/
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

/-- S1 is typed at the version's judgment. -/
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

/-- S2 is typed at the version's judgment. -/
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

/-- C5 is typed at `{it, it.C}` and `⊤ ^ {it.C}`. -/
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

/-- Z1 is typed at the version's judgment. -/
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

/-- `freshCell` bound by a `let` is typed at `Z1Ty`. -/
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
its own type. -/
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

/-- The unpacking is typed at an existential answer. -/
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

/-- The two calls are typed at `{fc, fs, un}` and `⊤`. -/
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

/-- The unpacking is typed at a file captured by the body's root. -/
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

/-- Z2 is typed at the version's judgment. -/
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

/-- Z3 is typed at the version's judgment. -/
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

/-- `process` is typed with its parameter at its own capture binder. -/
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

/-- The call of `process` is typed at the version's judgment. -/
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

/-- The typer rejects the program, with the tank unmarked. -/
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

/-- cov2 is typed at its annotation. -/
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

/-- cov4 is typed at its annotation. -/
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

/-- cov3 is a pure closure. -/
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
reads `any` as the arrow's own binder. -/
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

/-- The certificate builder certifies the escape goal. -/
example : (certify? W5Ctx [CapAtom.var W5f] [CapAtom.cvar W5kout]).map Reason.name =
    some "levelEscape" := by
  decide +kernel

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

/-- The typer rejects the escape, with the tank unmarked. -/
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

/-- The typer rejects the escape at the goal in `EscGoalCtx`. -/
example : (resolveTop Λc [] πc EscSrc).map (fun a => escapesAt (synthTop? {} πc a) EscGoalCtx
    [CapAtom.var .here] [CapAtom.cvar escRoot]) = some true := by
  decide +kernel

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

/-- **What the compile of the escape returns.**  At the default budget,
`compile` rejects the escape for a level escape at the goal `{f} <: {κ_g}` in
`EscGoalCtx`, with the root `κ_g`.  The certificate it carries says that no
member-free subcapturing proves that goal, as `Esc_rejected'` does.  The kernel
computes the verdict. -/
theorem compile_rejected_goal :
    ∃ cert : ¬ ∃ d : Subcap EscGoalCtx [CapAtom.var .here] [CapAtom.cvar escRoot], d.MemberFree,
      compile {} Λc (onC EscSrc) = .rejected (.levelEscape EscGoalCtx [CapAtom.var .here]
        [CapAtom.cvar escRoot] (FCdot.CapAtom.cvar escRoot) cert) :=
  rejectsAt_sound (by decide +kernel)

/-! ## The escape by an ascription

`AscEscSrc` of `Typer.lean` writes the same callback with an ascription in
place of the `let` annotation.  An ascription binds too, so the escape is
rejected at the callback's body. -/

/-- The typer rejects the escape by an ascription, with the tank
unmarked. -/
theorem AscEsc_verdict : judgProg Λc (onC AscEscSrc) = (none, ⟨defaultFuel - 88, false⟩) := by
  decide +kernel

/-- The escape by an ascription does not compile at any budget. -/
theorem AscEsc_rejected (b : Budget) : (compile b Λc (onC AscEscSrc)).isOk = false :=
  judgProg_rejects AscEsc_verdict b

/-- `compile` rejects the escape by an ascription for a level escape. -/
example : (compile {} Λc (onC AscEscSrc)).reason?.map Reason.name = some "levelEscape" := by
  decide +kernel

/-! ## The escape at the top of a program

`TopEscSrc` of `Typer.lean` binds the same callback at the top, where the
result `any` reads as the platform set and the source has no root.  The goal
is `{f} <: {k1, k2}` in `TopGoalCtx`, and the certificate's root is the
universal one, which the source cannot name. -/

/-- The typer rejects the escape at the top, with the tank
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

/-- The typer rejects the escape at the top at the goal in `TopGoalCtx`. -/
example : (resolveTop Λc [] πc TopEscSrc).map (fun a => escapesAt (synthTop? {} πc a) TopGoalCtx
    [CapAtom.var .here] topPlat) = some true := by
  decide +kernel

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

/-- **What the compile of the escape at the top returns.**  At the default
budget, `compile` rejects it for a level escape at the goal `{f} <: {k1, k2}`
in `TopGoalCtx`, with the universal root.  The kernel computes the verdict. -/
theorem TopEsc_compile_rejected :
    ∃ cert : ¬ ∃ d : Subcap TopGoalCtx [CapAtom.var .here] topPlat, d.MemberFree,
      compile {} Λc (onC TopEscSrc) = .rejected (.levelEscape TopGoalCtx [CapAtom.var .here]
        topPlat FCdot.CapAtom.top cert) :=
  rejectsAt_sound (by decide +kernel)

/-! ## A callback that keeps its capture inside its own scope

`EscOkSrc` of `Typer.lean`: the callback of the escape, annotated with its
result at its own parameter.  What it captures stays inside its own scope, so
it is accepted. -/

/-- The callback is typed at its annotation. -/
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

/-- QP1 is typed at the ascribed type. -/
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

/-- QP4 is typed. -/
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

/-- QP5 is typed. -/
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

/-- R1 is typed. -/
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

/-- R2 is typed. -/
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

/-- R3 is typed at the ascribed field. -/
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

/-- R4 is typed. -/
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

/-- The chain of sixteen links is typed at its written type. -/
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

/-- The chain of thirty two links is typed at its written type. -/
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

/-- X1 is typed. -/
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

/-- X2 is typed. -/
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

/-- The typer rejects B1, with the tank unmarked. -/
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

/-- The typer rejects A1, with the tank unmarked. -/
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

/-- BX2 is typed.  The inner closure captures `f`. -/
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

/-- BX is typed at the ascribed box. -/
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

/-- LP ends with the tank marked. -/
theorem LP_limit : judgProg Λc (onE LPsrc) = (none, ⟨defaultFuel - 32737, true⟩) := by
  decide +kernel

/-- PF ends with the tank marked. -/
theorem PF_limit : judgProg Λc (onE PFsrc) = (none, ⟨defaultFuel - 32693, true⟩) := by
  decide +kernel

/-- LQ2 ends with the tank marked. -/
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
      FCdot.Steps (⟨P.targetStore, .nil, ((compile b Λ p).get h).2.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] := by
  subst hP ht
  exact compile_effect_safety_get h hp hκ run' hin

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, a variable the reached state reads is not rooted at `k1` in
the matched target state.  The run reads only `c`, which the program declares
at the empty capture set, so no root exists and the statement holds trivially
here. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil, ((compile {} Λc (onC C2src)).get C2_compiles).2.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
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
      FCdot.Steps (⟨P.targetStore, .nil, ((compileFiltered b Λ p φ).get h).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
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
      FCdot.Steps (⟨P.targetStore, .nil, ((compileKinded b Λ p φ).get h).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
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

/-- CE1 is typed at the version's judgment. -/
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
classifier `only[Control]` admits.  This is `compile_filtered_effect_safety`
at CE1, with the platform and the term compared by the kernel.  The run reads
only `f`, which the program declares at the empty capture set, so no root
exists and the statement holds trivially here.  The program never calls
`r.body`, so the filter is not exercised.  `CE1b_reads_only_control` is the
instance where the run reads a filtered closure. -/
theorem CE1_reads_only_control {s : Sig} {st : State s}
    (r : Steps (⟨E1Plat.store, .nil, E1tm⟩ : State ([],c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename ([],c,c) s),
      FCdot.Steps (⟨E1Plat.targetStore, .nil,
        ((compileFiltered {} Λk CE1src (Cls.only Cls.Control)).get CE1_filtered).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext E1Plat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] →
            (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  compile_filtered_effect_safety_at CE1_filtered (platEq_sound _ _ (by decide +kernel))
    (by decide +kernel) r hin

/-- The log of CE1's derivation has fifty two entries. -/
example : (compileLog {} Λk CE1src).length = 52 := by decide +kernel

/-! ## CE1b: the filtered closure, called

CE1 with the closure `b` called.  `b` is declared at the filtered platform set
`{ctl, io}.only[Control]`, which names `io`, and the program applies it to a
pure closure `t`.  So the run reads `b`, a variable whose declared set is not
empty, and the effect theorem speaks of a filtered set at that read. -/

/-- `let b = λu.u at {ctl, io}.only[Control] in let t = λu.u in let r = b t in
r`. -/
def CE1bSrc : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    uses {ctl, io}.only[Control]
    kind only[Control]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]) in
    let t = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {}) in
    let r = b t in
    r

/-- CE1b's use set is the projection at `only[Control]`. -/
theorem CE1b_filtered : (compileFiltered {} Λk CE1bSrc (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-- CE1b is kinded at `only[Control]`. -/
theorem CE1b_kinded : (compileKinded {} Λk CE1bSrc (Cls.only Cls.Control)).isOk = true := by
  decide +kernel

/-- The sizes of the capture sets the written types give to the binders of a
`let` spine, outermost first. -/
def declaredLens : {s : Sig} → ATm s → List Nat
  | _, .let (some (.ty T)) _ u => T.captureSet.length :: declaredLens u
  | _, .let _ (.asc _ T) u => T.captureSet.length :: declaredLens u
  | _, .let _ _ u => 0 :: declaredLens u
  | _, _ => []

/-- The position of a binder, counted from the innermost. -/
def bvarIdx {s : Sig} {k : Kind} : BVar s k → Nat
  | .here => 0
  | .there x => bvarIdx x + 1

/-- The platform of the filtered compile of CE1b. -/
def CE1bPlat : Platform CE1bSrc.platNames.sig :=
  ((compileFiltered {} Λk CE1bSrc (Cls.only Cls.Control)).get CE1b_filtered).1.plat

/-- The erased term of the filtered compile of CE1b. -/
def CE1bTm : Tm CE1bSrc.platNames.sig :=
  ((compileFiltered {} Λk CE1bSrc (Cls.only Cls.Control)).get CE1b_filtered).2.1.tm.erase

/-- `b` is declared at the two atoms of the filtered platform set, `t` and
`r` at none. -/
theorem CE1b_declared :
    declaredLens ((compileFiltered {} Λk CE1bSrc (Cls.only Cls.Control)).get CE1b_filtered).2.1.tm
      = [2, 0, 0] := by
  decide +kernel

/-- The state of the run after five steps reads a variable. -/
theorem CE1b_reads :
    ((run 5 CE1bSrc.platNames.sig ⟨CE1bPlat.store, .nil, CE1bTm⟩).2.inspects).isSome = true := by
  decide +kernel

/-- That variable is `b`, the second binder from the innermost. -/
theorem CE1b_reads_b :
    ((run 5 CE1bSrc.platNames.sig ⟨CE1bPlat.store, .nil, CE1bTm⟩).2.inspects).map bvarIdx =
      some 1 := by
  decide +kernel

/-- **CE1b reads only `Control` capabilities.**  Along any run of CE1b from the
platform's initial store, every root of a variable the reached state reads, in
the matched target state, carries a classifier `only[Control]` admits.  This
is `compile_filtered_effect_safety` at CE1b.  The run reads `b` at step five
(`CE1b_reads_b`), and `b` is declared at the filtered set (`CE1b_declared`),
whose base names `io`. -/
theorem CE1b_reads_only_control {s : Sig} {st : State s}
    (r : Steps (⟨CE1bPlat.store, .nil, CE1bTm⟩ : State CE1bSrc.platNames.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename CE1bSrc.platNames.sig s),
      FCdot.Steps (⟨CE1bPlat.targetStore, .nil,
        ((compileFiltered {} Λk CE1bSrc (Cls.only Cls.Control)).get
          CE1b_filtered).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext CE1bPlat.targetStore stt.σ ρ ∧
          ∀ a : FCdot.CapAtom s, Γ'.Root a [FCdot.CapAtom.var x] →
            (Cls.only Cls.Control).Contains (Γ'.classOf a) :=
  compile_filtered_effect_safety_at CE1b_filtered rfl rfl r hin

/-- The theorem at the read of `b`, after five steps. -/
example := CE1b_reads_only_control (run_steps 5 _) (Option.some_get CE1b_reads).symm

/-- The platform of the kinded compile of CE1b. -/
def CE1bkPlat : Platform CE1bSrc.platNames.sig :=
  ((compileKinded {} Λk CE1bSrc (Cls.only Cls.Control)).get CE1b_kinded).1.plat

/-- The erased term of the kinded compile of CE1b. -/
def CE1bkTm : Tm CE1bSrc.platNames.sig :=
  ((compileKinded {} Λk CE1bSrc (Cls.only Cls.Control)).get CE1b_kinded).2.1.tm.erase

/-- The run of the kinded compile reads a variable after five steps too. -/
theorem CE1bk_reads :
    ((run 5 CE1bSrc.platNames.sig ⟨CE1bkPlat.store, .nil, CE1bkTm⟩).2.inspects).isSome = true := by
  decide +kernel

/-- `compile_classified_effect_safety` at the read of `b`. -/
example := compile_classified_effect_safety_at CE1b_kinded (P := CE1bkPlat) (t := CE1bkTm) rfl rfl
  (run_steps 5 (⟨CE1bkPlat.store, .nil, CE1bkTm⟩ : State CE1bSrc.platNames.sig))
  (Option.some_get CE1bk_reads).symm

/-! ## M1 and M5: mixed and filtered sets on the left

M1 is `{b ↾ only[Control], f}` below the filtered platform set, in `E1Ctx2`,
where `b` is at that set and `f` at `{}`.  M5 is `{ctl}` below the filtered
platform set, the goal a program meets that charges only `ctl` and declares
`{ctl, io}.only[Control]`.  `M5src` is such a program: the typer charges
`{ctl}` and `compile` moves it to the declared set by that goal. -/

/-- M1 holds in the version, and the search finds it. -/
theorem M1_subcap : Nonempty (Subcap E1Ctx2
    [CapAtom.proj (.var (.there .here)) (Cls.only Cls.Control), CapAtom.var .here]
    (CaptureSet.weaken (CaptureSet.weaken E1Filt))) :=
  found_nonempty (by decide +kernel : answers (cap? E1Ctx2
    [CapAtom.proj (.var (.there .here)) (Cls.only Cls.Control), CapAtom.var .here]
    (CaptureSet.weaken (CaptureSet.weaken E1Filt))) 172 = true)

/-- M5 holds in the version, and the search finds it. -/
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

/-- The typer charges `M5src` the set `{ctl}`. -/
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

/-- W is typed at its written type. -/
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
restricted atom. -/
theorem W_subcap : Nonempty (Subcap WCtx1 WL WR) :=
  found_nonempty (by decide +kernel : answers (cap? WCtx1 WL WR) 174 = true)

theorem W_var : Nonempty ((U : CaptureSet ([],c,c,x,x)) × HasTy U WCtx2 (.path (.var .here)) (.ty WT2)) :=
  found_nonempty (by decide +kernel : answers (var? WCtx2 .here WT2) 391 = true)

/-- The typer rejects W with `g : {f}`, with the tank
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

/-- CE2 is typed at the version's judgment. -/
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
`{κ_ctl, y ↾ except[ThreadLocal]}`.  `{y}` is below it. -/
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
      FCdot.Steps (⟨E2PlatIO.targetStore, .nil,
        ((compileFiltered {} Λk CE2src (Cls.except Cls.ThreadLocal)).get CE2_filtered).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
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

/-- CE3 is typed at the empty set and the client's type. -/
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
goal found.  The run reads only `c`, which the program declares at the empty
capture set, so no root exists and the statement holds trivially here. -/
theorem CE3_reads_only_control {s : Sig} {st : State s}
    (r : Steps (⟨E3Plat.store, .nil, E3tm⟩ : State ([],c,c)) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename ([],c,c) s),
      FCdot.Steps (⟨E3Plat.targetStore, .nil,
        ((compileKinded {} Λk CE3src (Cls.only Cls.Control)).get CE3_kinded).2.1.deriv.translate⟩ : FCdot.State _) stt ∧
      (∃ V, FCdot.State.Typed stt V) ∧ stt.inspects = some x ∧
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

/-- The retyping of `a` is typed at the version's judgment. -/
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
two binders are `Control`. -/
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
type of `c`. -/
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

/-- The retyping of `d` is typed at the version's judgment. -/
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

/-- CE4 is typed at the empty set and the client's type of CE3. -/
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

/-- The typer rejects the client at `only[IO]`, with the tank
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

/-- The client at `only[Control]` is typed. -/
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

/-- The typer rejects CE5, with the tank unmarked. -/
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
`{io}`. -/
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

/-! ## Annotations erased

Each program below is written with every slot, then its body is erased in
five ways.  `D` erases every lambda domain, `S` every self shape, and `A` the
domain of every lambda passed as an argument.  `C` erases the domain of every
lambda in a checked position, where the typer passes a goal: directly under an
ascription, an argument, the bound term of `let x : A = t in x`, the body of a
`let` with a written answer, a field of a literal whose self shape is written,
and the body of a lambda or a block in such a position.  `G` is `C` with every
self shape erased too.  `G` is the program a Scala programmer writes where an
expected type reaches.  The erasures act on the body of the surface program,
so `compile` applies to the result, and each agrees with the erasure of the
same name on the resolved body (`Erasure.agrees`).  The classifier
declarations, the platform, the declared use set and the declared kind stay as
written: a kind is no slot.

A cell is the verdict of `compileE` on an erased program at `defaultFuel`,
with the tank the elaborator leaves.  An erasure that changes nothing is
`noSlot`, whose verdict is the written one by `compile_full`.  A program that
compiles does so at the written body (`same`) or at another fill (`other`),
with the type `compile` returns.  The fill is the body `compile` returns.  A
fill that fails the agreement or the skeleton test of `compileE` is `shape`,
and `compileE` reports a mismatch there.  A fill the elaborator types whose
record does not reach the declared use set is `undeclared`.  A rejected
program has its reason, with the typer's own reason named.  When the
elaborator finds no candidate and no reason of its own, the reason is the
typer's verdict on the fill, as `compileE` reports it.  The first cell of a
row is the written program itself.

A cell whose reason search reaches the certificate builder of a level escape
is one the kernel does not evaluate, since the builder reads the well-founded
`Ctx.caps`.  These are the escapes and CapPure.  Their rows are checked by
`#eval expect`, and their other cells by the kernel.  No cell of the tables
is `undeclared`. -/

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

/-- An erasure on the surface body. -/
def Erasure.surface : Erasure → STm → STm
  | .D, e => STm.eraseDoms e
  | .S, e => STm.eraseSelf e
  | .A, e => STm.eraseArgs e
  | .C, e => STm.eraseChecked false false e
  | .G, e => STm.eraseChecked true false e

/-- The same erasure on the resolved body. -/
def Erasure.resolved {s : Sig} : Erasure → PTm s → PTm s
  | .D, p => p.eraseDoms
  | .S, p => p.eraseSelf
  | .A, p => p.eraseArgs
  | .C, p => p.eraseChecked false false
  | .G, p => p.eraseG

/-- A whole program with another body, its header as written. -/
def SProg.withSBody (p : SProg) (b : STm) : SProg := { p with body := b }

/-- A whole program with its body erased. -/
def Erasure.prog (k : Erasure) (p : SProg) : SProg := p.withSBody (k.surface p.body)

/-- The erased surface program resolves to the resolved body erased, under
the same header. -/
def Erasure.agrees (k : Erasure) (Λ : LabelTable) (p : SProg) : Bool :=
  decide ((resolvePProg Λ (k.prog p)).map Prod.snd =
    (resolvePProg Λ p).map fun r => k.resolved r.2)

/-- A reason with the typer's own reason replaced by its name. -/
abbrev RView := Frontend.Reason.Reason Label String

/-- The verdict on one erased program. -/
inductive Cell (s : Sig) where
  /-- The erasure changes nothing. -/
  | noSlot
  /-- Compiled at the written body, with its type and the tank left. -/
  | same (T : Ty s) (t : Tank)
  /-- Compiled at another fill, with its type and the tank left. -/
  | other (T : Ty s) (t : Tank)
  /-- Rejected, with the reason and the tank left. -/
  | no (r : RView) (t : Tank)
  /-- The erased program is not the written one with some slots empty, or
  its fill does not agree with it. -/
  | shape
  /-- Elaborated, but the record does not reach the declared use set: the
  reason `atDeclared` gives. -/
  | undeclared (r : RView)
deriving DecidableEq

/-- The elaborator's verdict on the resolved body `q` of a program `p` with
header `h` at `defaultFuel`, read as `compileE` reads it.  `a?` is the written
body, when there is one: a fill equal to it is `same`, any other fill
`other`. -/
def cellOf (p : SProg) (h : ProgHeader p.platNames.sig) (q : PTm p.platNames.sig)
    (a? : Option (ATm p.platNames.sig)) : Cell p.platNames.sig :=
  match elabProgF defaultFuel p h q with
  | (.ok c, t) =>
      match c.e.split with
      | .inl e =>
          if q.fills c.fill = true then
            if hs : ATm.skel e.tm = ATm.skel c.fill then
              match atDeclared {} h.plat ⟨e.tm, e.uses, e.ty, e.deriv, hs⟩ h.uses with
              | .ok c' => if some c.fill = a? then .same c'.ty t else .other c'.ty t
              | .rejected r => .undeclared (.landed r.name)
              | .unknown => .undeclared .mismatch
            else .shape
          else .shape
      | .inr x => .no (EReason.view (.landed (existentialAt h.plat.ctx x))) t
  | (.error .mismatch, t) => .no (fillReason {} p h q).view t
  | (.error r, t) => .no r.view t

/-- The verdict on `w` with the body `b`, the written body with some slots
empty.  `PTm.fills` checks that `b` is such a body. -/
def erasedCell (Λ : LabelTable) (w : SProg) (b : STm) : Cell w.platNames.sig :=
  match resolveProg Λ w, resolvePProg Λ (w.withSBody b) with
  | some r, some (h, q) => if q.fills r.body then cellOf (w.withSBody b) h q (some r.body) else .shape
  | _, _ => .shape

/-- The verdict on a program with no written form. -/
def openCell (Λ : LabelTable) (e : SProg) : Cell e.platNames.sig :=
  match resolvePProg Λ e with
  | some (h, q) => cellOf e h q none
  | none => .shape

/-- The verdict on the program `w` erased by `k`. -/
def cell (k : Erasure) (Λ : LabelTable) (w : SProg) : Cell w.platNames.sig :=
  if k.surface w.body = w.body then .noSlot else erasedCell Λ w (k.surface w.body)

/-- A row of the table: the written program, then its five erasures. -/
def row (Λ : LabelTable) (w : SProg) : List (Cell w.platNames.sig) :=
  [erasedCell Λ w w.body, cell .D Λ w, cell .S Λ w, cell .A Λ w, cell .C Λ w, cell .G Λ w]

/-- The written program, then the same program with another body. -/
def pair (Λ : LabelTable) (w : SProg) (b : STm) : List (Cell w.platNames.sig) :=
  [erasedCell Λ w w.body, erasedCell Λ w b]

/-- The type `compile` gives a written program, `⊤` when it gives none. -/
def tyOf (Λ : LabelTable) (w : SProg) : Ty w.platNames.sig :=
  match compile {} Λ w with
  | .ok r => r.2.ty
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
abbrev LambdaRow (Λ : LabelTable) (w : SProg) (c : Cell w.platNames.sig) : Prop :=
  row Λ w = [c, missing 0, .noSlot, .noSlot, .noSlot, .noSlot]

/-! ### What a cell says about `compile`

A cell is computed from `elabProgF`, the fill and `atDeclared`, as `compileE`
is, so a cell fact is a fact about `compile`.  A rejection that ends unmarked
is a rejection at every budget, by `elabProg?_stable` above `defaultFuel` and
`elabProg?_mono` below it.  The reason is the one `compileE` reports at the
default budget.  A reason of inference comes from the elaborator alone, so it
is also the reason at every budget from `defaultFuel` up.  A reason of the
typer may come from the fill of a failed elaboration, whose own tank no
theorem follows. -/

/-- The reason of a result, with the typer's own reason replaced by its
name. -/
def errView {α : Type} : Except EReason α → Option RView
  | .ok _ => none
  | .error r => some r.view

/-- The reason `compileE` reports at the budget `b`, if it reports one. -/
def reasonAt (b : Budget) (Λ : LabelTable) (e : SProg) : Option RView :=
  errView (compileE b Λ e)

/-- A program rejected at every budget, with the reason `compileE` reports
at the default budget. -/
def RejectedWith (Λ : LabelTable) (e : SProg) (r : RView) : Prop :=
  (∀ b, (compile b Λ e).isOk = false) ∧ reasonAt {} Λ e = some r

/-- A program rejected at every budget, with the same reason at every budget
from `defaultFuel` up. -/
def RejectedAbove (Λ : LabelTable) (e : SProg) (r : RView) : Prop :=
  RejectedWith Λ e r ∧ ∀ b : Budget, defaultFuel ≤ b.fuel → reasonAt b Λ e = some r

/-- A result that is an error is no success. -/
theorem verdictOf_error {α : Type} {x : Except EReason α} {r : EReason} (h : x = .error r) :
    (verdictOf x).isOk = false := by
  subst h
  cases r <;> rfl

/-- More fuel keeps a record that reaches the declared use set. -/
theorem atDeclared_mono {b b' : Budget} {s₀ : Sig} {P : Platform s₀} {a : ATm s₀}
    {c c' : Compiled P a} {U : Option (CaptureSet s₀)} (h : atDeclared b P c U = .ok c')
    (hb : b.fuel ≤ b'.fuel) : atDeclared b' P c U = .ok c' := by
  cases U with
  | none => exact h
  | some U =>
    unfold atDeclared at h ⊢
    dsimp only at h ⊢
    by_cases hu : c.use = U
    · rw [if_pos hu] at h ⊢
      exact h
    · rw [if_neg hu] at h ⊢
      cases he : (cap? P.ctx c.use U b.fuel).1 with
      | some e =>
        rw [he] at h
        rw [cap?_mono he hb]
        exact h
      | none =>
        rw [he] at h
        exfalso
        revert h
        cases certify? P.ctx c.use U <;> intro h <;> cases h

/-- An elaboration that ends in a reason with the tank unmarked fails at
every budget. -/
theorem elabProgF_error_all {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {r : EReason} {n : Nat}
    (het : elabProgF defaultFuel p h q = (.error r, ⟨n, false⟩)) (m : Nat) :
    ∃ r', (elabProgF m p h q).1 = .error r' := by
  cases hm : (elabProgF m p h q).1 with
  | error r' => exact ⟨r', rfl⟩
  | ok c =>
    exfalso
    rcases Nat.le_total defaultFuel m with hle | hle
    · have hs := elabProg?_stable het (m - defaultFuel)
      rw [Nat.add_sub_cancel' hle, hm] at hs
      cases hs
    · have hd := elabProg?_mono hm hle
      rw [het] at hd
      cases hd

/-- `compileE` after resolution reads the elaborator's first answer. -/
theorem compileE_error_of {b : Budget} {Λ : LabelTable} {p : SProg}
    {h : ProgHeader p.platNames.sig} {q : PTm p.platNames.sig} {r : EReason}
    (hp : resolvePProg Λ p = some (h, q)) (het : (elabProgF b.fuel p h q).1 = .error r) :
    ∃ r', compileE b Λ p = .error r' := by
  unfold compileE
  rw [hp]
  simp only [het]
  cases r <;> exact ⟨_, rfl⟩

/-- An existential answer is an error of `compileE`. -/
theorem compileE_ex_of {b : Budget} {Λ : LabelTable} {p : SProg}
    {h : ProgHeader p.platNames.sig} {q : PTm p.platNames.sig} {c : ECand h.plat.ctx}
    {x : XElab h.plat.ctx} (hp : resolvePProg Λ p = some (h, q))
    (het : (elabProgF b.fuel p h q).1 = .ok c) (hs : c.e.split = .inr x) :
    compileE b Λ p = .error (.landed (existentialAt h.plat.ctx x)) := by
  unfold compileE
  rw [hp]
  simp only [het, hs]

/-- **An elaboration that fails unmarked rejects at every budget.** -/
theorem rejects_of_error {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {r : EReason} {n : Nat}
    (hp : resolvePProg Λ p = some (h, q))
    (het : elabProgF defaultFuel p h q = (.error r, ⟨n, false⟩)) (b : Budget) :
    (compile b Λ p).isOk = false := by
  obtain ⟨r', hr'⟩ := elabProgF_error_all het b.fuel
  obtain ⟨r'', h⟩ := compileE_error_of hp hr'
  exact verdictOf_error h

/-- An elaboration whose first answer is existential rejects at every
budget. -/
theorem rejects_of_ex {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {c : ECand h.plat.ctx} {x : XElab h.plat.ctx}
    (hp : resolvePProg Λ p = some (h, q))
    (het : (elabProgF defaultFuel p h q).1 = .ok c) (hs : c.e.split = .inr x) (b : Budget) :
    (compile b Λ p).isOk = false := by
  cases hb : (elabProgF b.fuel p h q).1 with
  | error r =>
    obtain ⟨r', h⟩ := compileE_error_of hp hb
    exact verdictOf_error h
  | ok c' =>
    have hc' : c' = c := by
      rcases Nat.le_total defaultFuel b.fuel with hle | hle
      · have hm := elabProg?_mono het hle
        rw [hb] at hm
        cases hm
        rfl
      · have hm := elabProg?_mono hb hle
        rw [het] at hm
        cases hm
        rfl
    subst hc'
    exact verdictOf_error (compileE_ex_of hp hb hs)

/-- The elaborator's tank on a rejected cell, and the reason `compileE` gives
at the default budget. -/
theorem cellOf_no {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a? : Option (ATm p.platNames.sig)} {r : RView} {n : Nat}
    (hp : resolvePProg Λ p = some (h, q)) (hc : cellOf p h q a? = .no r ⟨n, false⟩) :
    RejectedWith Λ p r ∧
      ((∃ r0, elabProgF defaultFuel p h q = (.error r0, ⟨n, false⟩) ∧
          (r0 ≠ .mismatch → r0.view = r)) ∨
        ∃ c x, elabProgF defaultFuel p h q = (.ok c, ⟨n, false⟩) ∧ c.e.split = .inr x) := by
  unfold cellOf at hc
  split at hc
  · rename_i c t het
    split at hc
    · split at hc
      · split at hc
        · split at hc
          · split at hc <;> cases hc
          · cases hc
          · cases hc
        · cases hc
      · cases hc
    · rename_i x hs
      cases hc
      have het1 : (elabProgF defaultFuel p h q).1 = .ok c := by rw [het]
      refine ⟨⟨rejects_of_ex hp het1 hs, ?_⟩, .inr ⟨c, x, het, hs⟩⟩
      unfold reasonAt
      rw [compileE_ex_of (b := {}) hp het1 hs]
      rfl
  · rename_i t het
    cases hc
    refine ⟨⟨rejects_of_error hp het, ?_⟩, .inl ⟨.mismatch, het, fun h => absurd rfl h⟩⟩
    unfold reasonAt compileE
    rw [hp]
    have h1 : (elabProgF ({} : Budget).fuel p h q).1 = .error .mismatch := by rw [het]
    simp only [h1]
    rfl
  · rename_i r0 t hne het
    cases hc
    refine ⟨⟨rejects_of_error hp het, ?_⟩, .inl ⟨r0, het, fun _ => rfl⟩⟩
    unfold reasonAt compileE
    rw [hp]
    have h1 : (elabProgF ({} : Budget).fuel p h q).1 = .error r0 := by rw [het]
    simp only [h1]
    cases r0 with
    | mismatch => exact absurd rfl hne
    | _ => rfl

/-- **A rejected cell with the tank unmarked is a rejection at every
budget.** -/
theorem erasedCell_rejected {Λ : LabelTable} {w : SProg} {b : STm} {r : RView} {n : Nat}
    (h : erasedCell Λ w b = .no r ⟨n, false⟩) : RejectedWith Λ (w.withSBody b) r := by
  unfold erasedCell at h
  split at h
  · rename_i a hd q _ hp
    split at h
    · exact (cellOf_no hp h).1
    · cases h
  · cases h

/-- **A program with no written form, rejected with the tank unmarked, is
rejected at every budget.** -/
theorem openCell_rejected {Λ : LabelTable} {e : SProg} {r : RView} {n : Nat}
    (h : openCell Λ e = .no r ⟨n, false⟩) : RejectedWith Λ e r := by
  unfold openCell at h
  split at h
  · rename_i hd q hp
    exact (cellOf_no hp h).1
  · cases h

/-- A slot reason comes from the elaborator, never from the fill. -/
theorem view_slot {r : EReason} : r.view.isSlotReason = r.isSlotReason := by
  cases r <;> rfl

/-- The reason of an elaboration that fails unmarked is `compileE`'s reason at
every budget from `defaultFuel` up, when it is not a mismatch. -/
theorem reasonAt_above {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {r0 : EReason} {n : Nat} (hp : resolvePProg Λ p = some (h, q))
    (het : elabProgF defaultFuel p h q = (.error r0, ⟨n, false⟩)) (hne : r0 ≠ .mismatch)
    (b : Budget) (hb : defaultFuel ≤ b.fuel) : reasonAt b Λ p = some r0.view := by
  have hs := elabProg?_stable het (b.fuel - defaultFuel)
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
theorem cellOf_slot {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a? : Option (ATm p.platNames.sig)} {r : RView} {n : Nat}
    (hp : resolvePProg Λ p = some (h, q)) (hc : cellOf p h q a? = .no r ⟨n, false⟩)
    (hr : r.isSlotReason = true) : RejectedAbove Λ p r := by
  obtain ⟨hw, hcase⟩ := cellOf_no hp hc
  refine ⟨hw, fun b hb => ?_⟩
  rcases hcase with ⟨r0, het, hv⟩ | ⟨c, x, het, hs⟩
  · have hne : r0 ≠ .mismatch := by
      intro h0
      subst h0
      unfold cellOf at hc
      rw [het] at hc
      simp only at hc
      cases hc
      rw [view_slot, fillReason_not_slot] at hr
      cases hr
    rw [reasonAt_above hp het hne b hb, hv hne]
  · exfalso
    unfold cellOf at hc
    rw [het] at hc
    simp only [hs] at hc
    cases hc
    cases hr

/-- **A slot reason of an erased program holds at every budget.** -/
theorem erasedCell_slot {Λ : LabelTable} {w : SProg} {b : STm} {r : RView} {n : Nat}
    (h : erasedCell Λ w b = .no r ⟨n, false⟩) (hr : r.isSlotReason = true) :
    RejectedAbove Λ (w.withSBody b) r := by
  unfold erasedCell at h
  split at h
  · rename_i a hd q _ hp
    split at h
    · exact cellOf_slot hp h hr
    · cases h
  · cases h

/-- **A slot reason of a program with no written form holds at every
budget.** -/
theorem openCell_slot {Λ : LabelTable} {e : SProg} {r : RView} {n : Nat}
    (h : openCell Λ e = .no r ⟨n, false⟩) (hr : r.isSlotReason = true) :
    RejectedAbove Λ e r := by
  unfold openCell at h
  split at h
  · rename_i hd q hp
    exact cellOf_slot hp h hr
  · cases h

/-- An elaboration whose fill passes the two tests and whose record reaches
the declared use set is `compile`: the fill, at the record's type. -/
theorem compile_of_fill {b : Budget} {Λ : LabelTable} {p : SProg}
    {h : ProgHeader p.platNames.sig} {q : PTm p.platNames.sig} {c : ECand h.plat.ctx}
    {e : PElab h.plat.ctx} {c' : Compiled h.plat c.fill} (hp : resolvePProg Λ p = some (h, q))
    (het : (elabProgF b.fuel p h q).1 = .ok c) (hs : c.e.split = .inl e)
    (hf : q.fills c.fill = true) (hk : ATm.skel e.tm = ATm.skel c.fill)
    (hd : atDeclared b h.plat ⟨e.tm, e.uses, e.ty, e.deriv, hk⟩ h.uses = .ok c') :
    (compile b Λ p).toOption.map (fun r => (r.1.body, r.2.ty)) = some (c.fill, c'.ty) := by
  show (verdictOf (compileE b Λ p)).toOption.map _ = _
  unfold compileE
  rw [hp]
  simp only [het, hs, hf, if_true, dif_pos hk, hd]
  rfl

/-- A compiled cell is `compile` at every budget from `defaultFuel` up: the
fill and the type. -/
theorem cellOf_ok {Λ : LabelTable} {p : SProg} {h : ProgHeader p.platNames.sig}
    {q : PTm p.platNames.sig} {a? : Option (ATm p.platNames.sig)} {d : Cell p.platNames.sig}
    (hp : resolvePProg Λ p = some (h, q)) (hc : cellOf p h q a? = d)
    (hd : ∃ T t, d = .same T t ∨ d = .other T t) :
    ∃ (c : ECand h.plat.ctx) (T : Ty p.platNames.sig),
      (elabProgF defaultFuel p h q).1 = .ok c ∧
      (∀ b : Budget, defaultFuel ≤ b.fuel →
        (compile b Λ p).toOption.map (fun r => (r.1.body, r.2.ty)) = some (c.fill, T)) ∧
      d = (if some c.fill = a? then .same T (elabProgF defaultFuel p h q).2
        else .other T (elabProgF defaultFuel p h q).2) := by
  obtain ⟨T0, t0, hd⟩ := hd
  unfold cellOf at hc
  split at hc
  · rename_i c t het
    have het1 : (elabProgF defaultFuel p h q).1 = .ok c := by rw [het]
    split at hc
    · rename_i e hs
      split at hc
      · rename_i hf
        split at hc
        · rename_i hk
          split at hc
          · rename_i c' hdc
            refine ⟨c, c'.ty, het1,
              fun b hb => compile_of_fill hp (elabProg?_mono het1 hb) hs hf hk
                (atDeclared_mono hdc hb), ?_⟩
            rw [← hc, het]
          · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
          · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
        · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
      · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
    · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
  · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc
  · rcases hd with hd | hd <;> rw [hd] at hc <;> cases hc

/-- **A cell at the written body is `compile` at the written body.**  At every
budget from `defaultFuel` up, the erased program compiles to the body the
written program resolves to, at the cell's type. -/
theorem erasedCell_same {Λ : LabelTable} {w : SProg} {b : STm} {T : Ty w.platNames.sig}
    {t : Tank} (h : erasedCell Λ w b = .same T t) (bud : Budget) (hb : defaultFuel ≤ bud.fuel) :
    (compile bud Λ (w.withSBody b)).toOption.map (fun r => (r.1.body, r.2.ty)) =
      (resolveProg Λ w).map (fun r => (r.body, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i r hd q hw hp
    split at h
    · obtain ⟨c, T', _, hcomp, heq⟩ := cellOf_ok hp h ⟨T, t, .inl rfl⟩
      rw [hcomp bud hb, hw]
      split at heq
      · rename_i hfa
        cases heq
        simp only [Option.map_some, Option.some.injEq] at hfa ⊢
        rw [hfa]
        rfl
      · cases heq
    · cases h
  · cases h

/-- **A cell at another fill is `compile` at the cell's type**, at every
budget from `defaultFuel` up. -/
theorem erasedCell_other {Λ : LabelTable} {w : SProg} {b : STm} {T : Ty w.platNames.sig}
    {t : Tank} (h : erasedCell Λ w b = .other T t) (bud : Budget) (hb : defaultFuel ≤ bud.fuel) :
    (compile bud Λ (w.withSBody b)).toOption.map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i r hd q hw hp
    split at h
    · obtain ⟨c, T', _, hcomp, heq⟩ := cellOf_ok hp h ⟨T, t, .inr rfl⟩
      have h2 := congrArg (Option.map Prod.snd) (hcomp bud hb)
      simp only [Option.map_map] at h2
      split at heq
      · cases heq
      · cases heq
        exact h2
    · cases h
  · cases h

/-- A cell of an erasure that changes the body is the erased program's
cell. -/
theorem cell_erased {k : Erasure} {Λ : LabelTable} {w : SProg} (h : cell k Λ w ≠ .noSlot) :
    cell k Λ w = erasedCell Λ w (k.surface w.body) := by
  unfold cell at h ⊢
  split
  · rename_i he
    rw [if_pos he] at h
    exact absurd rfl h
  · rfl

/-- A program the elaborator rejects with the tank unmarked, as
`elabProgOut` reports it, is rejected at every budget. -/
theorem elabProgOut_rejects {Λ : LabelTable} {e : SProg} {r : RView} {n : Nat}
    (h : elabProgOut Λ e = (.no r, ⟨n, false⟩)) (b : Budget) : (compile b Λ e).isOk = false := by
  unfold elabProgOut at h
  split at h
  · rename_i hd q hp
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
`SelfProjSrcF`, `BareCapSrcF` and `KSelfSrcF` of `Elab.lean`, and `NestSrcW`
here. -/

/-- E6 closed over its parameter, with its self shape written as in the
version's derivation. -/
def E6srcW : STm :=
  cls% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

/-- A lambda bound with no type, the domain written. -/
def Id0Src : STm := cls% let i = λ(x : ⊤). x in i

/-- A lambda ascribed at `⊤`, the domain written. -/
def IdTopSrc : STm := cls% (λ(x : ⊤). x : ⊤)

/-- Two function sides with incomparable domains, and a lambda at `⊤` below
both. -/
def AndIncSrc : STm := cls% (λ(y : ⊤). y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤))

/-- One function side and a field the lambda does not have. -/
def AndOneSrc : STm := cls% (λ(y : ⊤). y : (∀(x : ⊤) ⊤) ∧ {a : ⊤})

/-- An abstract type with a function upper bound as the goal. -/
def UpperSrc : STm := cls% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). (λ(x : ⊤). x : y.A)

/-- An abstract type with a function lower bound as the goal. -/
def LowerSrc : STm := cls% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). (λ(x : ⊤). x : y.A)

/-- A lambda bound by a written `let` and then passed, the domain written. -/
def LetArgSrc : STm := cls% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λ(x : ⊤). x in g i

/-- A callee whose two formals are incomparable, applied to a lambda at `⊤`. -/
def IncSrc : STm :=
  cls% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- A callee with no function type, applied to a lambda. -/
def NoFnSrc : STm := cls% λ(g : ⊤). g (λ(x : ⊤). x)

/-- A body that calls `g` on another variable. -/
def CalleeOtherSrc : STm := cls% λ(g : ∀(y : ⊤) ⊤). λ(z : ⊤). let h = λ(x : ⊤). g z in h

/-- A callee at incomparable domains. -/
def CalleeIncSrc : STm :=
  cls% λ(g : (∀(y : {a : ⊤}) ⊤) ∧ (∀(y : {b : ⊤}) ⊤)). let h = λ(x : {a : ⊤}). g x in h

/-- Two fields that read each other, the self shape written. -/
def CycSrc : STm := cls% ν(z : {a : ⊤} ∧ {b : ⊤}. {a = z.b} ∧ {b = z.a})

/-- A field that reads a cycle between two later fields, the self shape
written. -/
def Cyc3Src : STm :=
  cls% ν(z : {a : ⊤} ∧ {b : ⊤} ∧ {v : ⊤}. {a = z.b} ∧ {b = z.v} ∧ {v = z.b})

/-- A recursive field that reads itself through an alias of the self, the
self shape written. -/
def AliasRecSrc : STm :=
  cls% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = z in let u = w.a in u y})

/-- A field whose right-hand side has two incomparable types, the self shape
written at one of them. -/
def AmbSrc : STm := cls% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s : {a : {b : ⊤}}. {a = y.a})

/-- A field that is a lambda, the self shape and the domain written. -/
def NoDomSrc : STm := cls% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). y})

/-- A lambda ascribed at a type that puts `any` below a field of its domain,
the domain written. -/
def DeepAscSrc : STm := cls% (λ(x : {read : ⊤ ^ {any}}). x : ∀(x : {read : ⊤ ^ {any}}) ⊤)

/-- Nest with both self shapes written at the shapes its definitions form:
the inner field at the type of `y`. -/
def NestSrcW : STm :=
  cls% λ(y : {b : ⊤} ∧ {elem : ⊤}).
        ν(o : {a : μ(z. {b : {b : ⊤} ∧ {elem : ⊤}})}.
           {a = ν(z : {b : {b : ⊤} ∧ {elem : ⊤}}. {b = y})})

/-- A literal ascribed at an alias of a `μ`: the alias is followed to the
self shape. -/
def AliasMuSrc : STm :=
  cls% λ(y : {A : μ(z. {run : ∀(u : ⊤) ⊤}) .. μ(z. {run : ∀(u : ⊤) ⊤})}).
        (ν(z : {run : ∀(u : ⊤) ⊤}. {run = λ(u : ⊤). u}) : y.A)

/-- A written lambda ascribed at an intersection with one function side and an
abstract side, whose body holds a literal with a written self shape. -/
def X4Src : STm :=
  cls% λ(y : {A : (∀(x : {a : ⊤}) {a : ⊤}) .. ⊤}).
        (λ(x : {a : ⊤}). let o = ν(z : {B : ⊤ .. ⊤}. {type B = ⊤}) in x :
          (∀(x : {a : ⊤}) ⊤) ∧ y.A)

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
    Erasure.A.surface KcapSrc = KcapSrcA ∧ Erasure.A.surface E11aSrc = E11aSrcA ∧
    Erasure.A.surface X1Src = X1SrcA ∧ Erasure.A.surface DomFSrc = DomFSrcA ∧
    Erasure.A.surface DomSrc = DomSrcA ∧ Erasure.A.surface TwoFSrc = TwoFSrcA ∧
    Erasure.A.surface IncSrc = IncSrcA ∧ Erasure.A.surface NoFnSrc = NoFnSrcA ∧
    Erasure.A.surface AliasArgSrc = AliasArgSrcA ∧ Erasure.C.surface BlockArgSrc = BlockArgSrcG ∧
    Erasure.C.surface CurriedSrc = CurriedSrcG ∧ Erasure.A.surface BoxCalleeSrc = BoxCalleeSrcA ∧
    Erasure.A.surface BoxFSrc = BoxFSrcA ∧ Erasure.A.surface AnyAscSrc = AnyAscSrcA ∧
    Erasure.A.surface FitsSrc = FitsSrcA ∧ Erasure.A.surface TooBigSrc = TooBigSrcA ∧
    Erasure.C.surface CalleeTopSrc = CalleeTopSrcD ∧
    Erasure.A.surface CalleeArgSrc = CalleeArgSrcA ∧ Erasure.C.surface ValSrc = ValSrcD ∧
    Erasure.C.surface Z1defSrc = Z1defSrcD ∧ Erasure.C.surface EscOkSrc = EscOkSrcG ∧
    Erasure.C.surface TopEscSrc = TopEscSrcG ∧ Erasure.D.surface TopEscSrc = TopEscSrcG ∧
    Erasure.C.surface EscSrc = EscSrcG ∧ Erasure.C.surface AscEscSrc = AscEscSrcG := by
  and_intros <;> rfl
example : Erasure.S.surface RecObjSrc = RecSrcS ∧ Erasure.S.surface CycSrc = CycSrcS ∧
    Erasure.S.surface Cyc3Src = Cyc3SrcS ∧ Erasure.S.surface AliasRecSrc = AliasRecSrcS ∧
    Erasure.S.surface BareSrc = BareSrcS ∧ Erasure.S.surface FwdSelfSrc = FwdSelfSrcS ∧
    Erasure.S.surface BareProjSrc = BareProjSrcS ∧ Erasure.S.surface AmbSrc = AmbSrcS ∧
    Erasure.S.surface AmbUseSrc = AmbUseSrcS ∧ Erasure.S.surface AmbUse2Src = AmbUse2SrcS ∧
    Erasure.S.surface (NestKSrc true 2) = NestKSrc false 2 ∧ Erasure.S.surface Z1litF = Z1litS ∧
    Erasure.S.surface FldTySrc = NoShapeSrcS := by
  and_intros <;> rfl
example : Erasure.D.surface CE1src.body = CE1BodyD ∧ Erasure.S.surface CE3src.body = CE3BodyS ∧
    Erasure.D.surface CE3src.body = CE3BodyD := by
  and_intros <;> rfl

/-- The programs of the tables, each with its label table. -/
def tablePrograms : List (LabelTable × SProg) :=
  [(Λc, onE E1src), (Λc, onE E2src), (Λc, onE E3src), (Λc, onE E4src), (Λc, onE E5src),
   (Λc, onE E6srcW), (Λc, onE E7src), (Λc, onE E8src), (Λc, onE E1ssrc), (Λc, onE E3ssrc),
   (Λc, onE PA1src), (Λc, onE P4src), (Λc, onE P5src), (Λc, onE R1src), (Λc, onE R2src),
   (Λc, onE R3src), (Λc, onE R4src), (Λc, onE B1src), (Λc, onE A1src), (Λc, onE (chainSrc 16)),
   (Λc, onE X1src), (Λc, onE X2src), (Λc, onE LPsrc), (Λc, onE PFsrc), (Λc, onE LQ2src),
   (Λc, onC C7boxSrc), (Λc, onC C7src), (Λc, onC S3src), (Λc, onC C2src), (Λc, onZ S1progSrc),
   (Λc, onZ S2src), (Λc, onZ Z1progSrc), (Λc, onZ Z1defSrc), (Λc, onZ Z2src), (Λc, onZ Z3src),
   (Λc, onC W2defSrc), (Λc, onC cov2Src), (Λc, onC cov3Src), (Λc, onC cov4Src),
   (Λc, onC accountedSrc), (Λc, onC deepSrc), (Λc, onZ exTopSrc), (Λc, onC EscSrc),
   (Λc, onC AscEscSrc), (Λc, onC TopEscSrc), (Λc, onC EscOkSrc), (Λc, onC BX2src),
   (Λc, onC BXsrc), (Λc, onZ LetExSrc),
   (Λc, onZ S1callSrc), (Λc, onE K1src), (Λc, onC KcapSrc), (Λc, onE E11aSrc), (Λc, onE X1Src),
   (Λc, onE DomFSrc), (Λc, onE DomSrc), (Λc, onE TwoFSrc), (Λc, onE IncSrc), (Λc, onE NoFnSrc),
   (Λc, onE AliasArgSrc), (Λc, onE BlockArgSrc), (Λc, onE CurriedSrc), (Λc, onE BoxCalleeSrc),
   (Λc, onE BoxFSrc), (Λc, onC AnyAscSrc), (Λc, onC FitsSrc), (Λc, onC TooBigSrc),
   (Λc, onE CalleeSrc), (Λc, onE CalleeAnySrc), (Λc, onE CalleeTopSrc), (Λc, onE CalleeArgSrc),
   (Λc, onE CalleeOtherSrc), (Λc, onE CalleeIncSrc), (Λc, onE LetArgSrc), (Λc, onE Id0Src),
   (Λc, onE ValSrc),
   (Λc, onC W2ascSrc), (Λc, onE AndSameSrc), (Λc, onE X3Src), (Λc, onE X4Src),
   (Λc, onE AndTwoSrc), (Λc, onE AndResSrc), (Λc, onE AndIncSrc), (Λc, onE AndOneSrc),
   (Λc, onE AndTopSrc), (Λc, onE AscSrc), (Λc, onE AliasSrc), (Λc, onE Alias2Src),
   (Λc, onE UpperSrc), (Λc, onE LowerSrc), (Λc, onE LoopSrc), (Λc, onE IdTopSrc),
   (Λc, onE CurrySrc), (Λc, onE SideCurrySrc), (Λc, onE LetBodySrc), (Λc, onE BlockSrc),
   (Λc, onC CapSrc), (Λc, onC CapPureSrc), (Λc, onE DeepAscSrc),
   (Λc, onC FldSrc), (Λc, onE FldTySrc), (Λc, onE AscObjSrc), (Λc, onE AscWideSrc),
   (Λc, onE AliasMuSrc), (Λc, onE NestSrc), (Λc, onE FwdObjSrc), (Λc, onC Cap1Src),
   (Λc, onC SelfProjSrc), (Λc, onE RecObjSrc), (Λc, onE BareSrc), (Λc, onC BareCapSrc),
   (Λc, onC LamCapSrc), (Λc, onE FwdSelfSrc), (Λc, onE BareProjSrc), (Λc, onE AmbUseSrc),
   (Λc, onE AmbUse2Src), (Λc, onE OrdASrc), (Λc, onE OrdBSrc), (Λc, onE AmbSrc),
   (Λc, onE E2objSrc), (Λc, onE CycSrc), (Λc, onC Cyc3Src), (Λc, onE AliasRecSrc),
   (Λc, onE NoDomSrc), (Λc, onZ Z1litF),
   (Λk, CE1src), (Λk, CE2src), (Λk, CE3src), (Λk, CE3sSrc), (Λk, CE4src),
   (Λk, CE4negSrc), (Λk, CE4posSrc), (Λk, CE5src), (Λk, CE5ioSrc), (Λk, CE1argSrc),
   (Λk, CE5argSrc), (Λk, CE5argIoSrc), (Λk, KSelfSrc), (Λk, KSelfIoSrc), (Λk, M5src),
   (Λk, WSrc), (Λk, WnegSrc), (Λk, KDomSrc)]

-- Every erasure of every program agrees with the erasure of the resolved body.
example : tablePrograms.all (fun (Λ, w) => [Erasure.D, .S, .A, .C, .G].all (·.agrees Λ w)) =
    true := by
  decide +kernel

/-! ### The programs of the typer

Every closed program of `Notation.lean`, `Typer.lean` and the sections above
that declares no classifier.  Each one whose outermost term is a lambda is a
missing parameter type under `D`, since nothing gives the lambda a goal, as in
Scala.  E2, Z1, Z1def, Z2 and Z3 keep compiling under `D`, since their lambdas
take their domains from a written self shape, a written `let` type or an
ascription.  S1 and S2 are rejected under `D` at a lambda bound by a `let`
with no type, after the fuel their first steps take.

Under `S` and `G` a literal forms its self shape from its definitions.  E2, E7
and accounted compile at the written body.  E5, E6 and C7 compile at the types
of their right-hand sides, which `E5srcR`, `E6srcR` and `C7srcF` write.  S3,
C2, S1, S2 and Z3 compile at the written type, with a self shape other than
the written one, which names a member or its set.  The literal of `freshCell`
forms `read` pure, and the version has no subtyping between two `μ` shapes,
so Z1, Z1def, Z2 and exTop do not meet the written `μ` and are a type
mismatch.  C7 with its boxes written boxes each capability at its own set,
where its written unboxing names `{k1}`, so it is a type mismatch too.  The
recursion limit of LP, PF and LQ2 stays at its fuel. -/

/-- E1 under each erasure.  The written program is rejected, with no reason
of the typer. -/
theorem E1_erased : LambdaRow Λc (onE E1src) (.no .mismatch (spent 11)) := by
  decide +kernel

/-- E2 under each erasure.  Its one lambda is a field of a literal, so `D`
and `C` take its domain from the written self shape, and `S` and `G` form
the written self shape. -/
theorem E2_erased : row Λc (onE E2src) =
    [.same (tyOf Λc (onE E2src)) (spent 60), .same (tyOf Λc (onE E2src)) (spent 62),
     .same (tyOf Λc (onE E2src)) (spent 61), .noSlot, .same (tyOf Λc (onE E2src)) (spent 62),
     .same (tyOf Λc (onE E2src)) (spent 61)] := by
  decide +kernel

/-- E3 under each erasure. -/
theorem E3_erased : LambdaRow Λc (onE E3src) (.no .mismatch (spent 11)) := by
  decide +kernel

/-- E4 under each erasure. -/
theorem E4_erased : LambdaRow Λc (onE E4src) (.no .mismatch (spent 16)) := by
  decide +kernel

/-- E5 under each erasure.  `S` and `G` compile at the type of the
right-hand side. -/
theorem E5_erased : row Λc (onE E5src) =
    [.same (tyOf Λc (onE E5src)) (spent 20), missing 0, .other (tyOf Λc (onE E5srcR)) (spent 11),
     .noSlot, .noSlot, .other (tyOf Λc (onE E5srcR)) (spent 11)] := by
  decide +kernel

/-- E6 closed over its parameter, under each erasure.  `S` and `G` compile at
the type of the right-hand side. -/
theorem E6_erased : row Λc (onE E6srcW) =
    [.same (tyOf Λc (onE E6srcW)) (spent 14), missing 0, .other (tyOf Λc (onE E6srcR)) (spent 3),
     .noSlot, .noSlot, .other (tyOf Λc (onE E6srcR)) (spent 3)] := by
  decide +kernel

/-- E7 under each erasure.  `S` and `G` form the written self shape. -/
theorem E7_erased : row Λc (onE E7src) =
    [.same (tyOf Λc (onE E7src)) (spent 1), .noSlot, .same (tyOf Λc (onE E7src)) (spent 1),
     .noSlot, .noSlot, .same (tyOf Λc (onE E7src)) (spent 1)] := by
  decide +kernel

/-- E8 under each erasure. -/
theorem E8_erased : LambdaRow Λc (onE E8src) (.same (tyOf Λc (onE E8src)) (spent 13)) := by
  decide +kernel

/-- E1s under each erasure. -/
theorem E1s_erased : LambdaRow Λc (onE E1ssrc) (.same (tyOf Λc (onE E1ssrc)) (spent 20)) := by
  decide +kernel

/-- E3s under each erasure. -/
theorem E3s_erased : LambdaRow Λc (onE E3ssrc) (.same (tyOf Λc (onE E3ssrc)) (spent 18)) := by
  decide +kernel

/-- QP1 under each erasure. -/
theorem QP1_erased : LambdaRow Λc (onE PA1src) (.same (tyOf Λc (onE PA1src)) (spent 45)) := by
  decide +kernel

/-- QP4 under each erasure. -/
theorem QP4_erased : LambdaRow Λc (onE P4src) (.same (tyOf Λc (onE P4src)) (spent 28)) := by
  decide +kernel

/-- QP5 under each erasure. -/
theorem QP5_erased : LambdaRow Λc (onE P5src) (.same (tyOf Λc (onE P5src)) (spent 13)) := by
  decide +kernel

/-- R1 under each erasure. -/
theorem R1_erased : LambdaRow Λc (onE R1src) (.same (tyOf Λc (onE R1src)) (spent 17)) := by
  decide +kernel

/-- R2 under each erasure. -/
theorem R2_erased : LambdaRow Λc (onE R2src) (.same (tyOf Λc (onE R2src)) (spent 10)) := by
  decide +kernel

/-- R3 under each erasure. -/
theorem R3_erased : LambdaRow Λc (onE R3src) (.same (tyOf Λc (onE R3src)) (spent 11)) := by
  decide +kernel

/-- R4 under each erasure. -/
theorem R4_erased : LambdaRow Λc (onE R4src) (.same (tyOf Λc (onE R4src)) (spent 9)) := by
  decide +kernel

/-- B1 under each erasure. -/
theorem B1_erased : LambdaRow Λc (onE B1src) (.no .mismatch (spent 2)) := by
  decide +kernel

/-- A1 under each erasure. -/
theorem A1_erased : LambdaRow Λc (onE A1src) (.no .mismatch (spent 11)) := by
  decide +kernel

/-- The alias chain of sixteen links under each erasure. -/
theorem chain16_erased :
    LambdaRow Λc (onE (chainSrc 16)) (.same (tyOf Λc (onE (chainSrc 16))) (spent 203)) := by
  decide +kernel

/-- X1, a variable at its own abstract type, under each erasure. -/
theorem X1_erased : LambdaRow Λc (onE X1src) (.same (tyOf Λc (onE X1src)) (spent 5)) := by
  decide +kernel

/-- X2 under each erasure. -/
theorem X2_erased : LambdaRow Λc (onE X2src) (.same (tyOf Λc (onE X2src)) (spent 10)) := by
  decide +kernel

/-- LP under each erasure.  The written program is at the recursion limit. -/
theorem LP_erased : LambdaRow Λc (onE LPsrc) (.no .limit (marked 32737)) := by
  decide +kernel

/-- PF under each erasure.  The written program is at the recursion limit. -/
theorem PF_erased : LambdaRow Λc (onE PFsrc) (.no .limit (marked 32693)) := by
  decide +kernel

/-- LQ2 under each erasure.  The written program is at the recursion limit. -/
theorem LQ2_erased : LambdaRow Λc (onE LQ2src) (.no .limit (marked 32763)) := by
  decide +kernel

/-- C7 with its boxes written, under each erasure.  `S` and `G` box each
capability at its own set, where the written unboxing names `{k1}`. -/
theorem C7box_erased : row Λc (onC C7boxSrc) =
    [.same (tyOf Λc (onC C7boxSrc)) (spent 31), missing 0, .no .mismatch (spent 13), .noSlot,
     .noSlot, .no .mismatch (spent 13)] := by
  decide +kernel

/-- C7 with no box written, under each erasure.  `S` and `G` compile at the
self shape the definitions form, the fields at the capabilities they hold. -/
theorem C7_erased : row Λc (onC C7src) =
    [.same (tyOf Λc (onC C7src)) (spent 80), missing 0, .other (tyOf Λc (onC C7srcF)) (spent 44),
     .noSlot, .noSlot, .other (tyOf Λc (onC C7srcF)) (spent 44)] := by
  decide +kernel

/-- S3 under each erasure.  `S` and `G` compile at the written type, the
field at the boxed capability where the written shape names `z.A`. -/
theorem S3_erased : row Λc (onC S3src) =
    [.same (tyOf Λc (onC S3src)) (spent 46), missing 0, .other (tyOf Λc (onC S3src)) (spent 15),
     .noSlot, .noSlot, .other (tyOf Λc (onC S3src)) (spent 15)] := by
  decide +kernel

/-- C2 under each erasure.  `C` takes the domains of the fields from the
written self shapes.  `S` and `G` compile at the written type, with `run`
pure. -/
theorem C2_erased : row Λc (onC C2src) =
    [.same (tyOf Λc (onC C2src)) (spent 214), missing 0, .other (tyOf Λc (onC C2src)) (spent 244),
     .noSlot, .same (tyOf Λc (onC C2src)) (spent 218),
     .other (tyOf Λc (onC C2src)) (spent 244)] := by
  decide +kernel

/-- S1 under each erasure.  `D` erases the domain of `op`, bound by a `let`
with no type.  `C` takes the domains from the ascription and the self shape. -/
theorem S1_erased : row Λc (onZ S1progSrc) =
    [.same (tyOf Λc (onZ S1progSrc)) (spent 86), missing 28,
     .other (tyOf Λc (onZ S1progSrc)) (spent 97), .noSlot,
     .same (tyOf Λc (onZ S1progSrc)) (spent 88), .other (tyOf Λc (onZ S1progSrc)) (spent 97)] := by
  decide +kernel

/-- S2 under each erasure.  `C` and `G` erase the domain of `(λy. y : ⊤)`,
whose goal has no function part, so they are a missing parameter type. -/
theorem S2_erased : row Λc (onZ S2src) =
    [.same (tyOf Λc (onZ S2src)) (spent 138), missing 96, .other (tyOf Λc (onZ S2src)) (spent 191),
     .noSlot, missing 96, missing 143] := by
  decide +kernel

/-- Z1 under each erasure.  `D` and `C` take the domains from the ascription
and the self shape.  `S` and `G` form `read` pure, which does not meet the
written `μ`. -/
theorem Z1_erased : row Λc (onZ Z1progSrc) =
    [.same (tyOf Λc (onZ Z1progSrc)) (spent 12), .same (tyOf Λc (onZ Z1progSrc)) (spent 14),
     .no .mismatch (spent 62), .noSlot, .same (tyOf Λc (onZ Z1progSrc)) (spent 14),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z1def under each erasure.  `D` and `C` take the domains from the written
`let` type and the self shape.  `S` and `G` form `read` pure. -/
theorem Z1def_erased : row Λc (onZ Z1defSrc) =
    [.same (tyOf Λc (onZ Z1defSrc)) (spent 31), .same (tyOf Λc (onZ Z1defSrc)) (spent 45),
     .no .mismatch (spent 112), .noSlot, .same (tyOf Λc (onZ Z1defSrc)) (spent 45),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z2 under each erasure.  `D` and `C` fill the domain with the goal's, its
`any` read at the arrow's binder, where the written program holds `any`.
`S` and `G` form `read` pure. -/
theorem Z2_erased : row Λc (onZ Z2src) =
    [.same (tyOf Λc (onZ Z2src)) (spent 12), .other (tyOf Λc (onZ Z2src)) (spent 14),
     .no .mismatch (spent 62), .noSlot, .other (tyOf Λc (onZ Z2src)) (spent 14),
     .no .mismatch (spent 62)] := by
  decide +kernel

/-- Z3 under each erasure.  Every erasure compiles, `S` and `G` with a self
shape other than the written one. -/
theorem Z3_erased : row Λc (onZ Z3src) =
    [.same (tyOf Λc (onZ Z3src)) (spent 101), .same (tyOf Λc (onZ Z3src)) (spent 107),
     .other (tyOf Λc (onZ Z3src)) (spent 154), .noSlot, .same (tyOf Λc (onZ Z3src)) (spent 107),
     .other (tyOf Λc (onZ Z3src)) (spent 154)] := by
  decide +kernel

/-- W2def under each erasure. -/
theorem W2def_erased : LambdaRow Λc (onC W2defSrc) (.same (tyOf Λc (onC W2defSrc)) (spent 2)) := by
  decide +kernel

/-- cov2 under each erasure. -/
theorem cov2_erased : LambdaRow Λc (onC cov2Src) (.same (tyOf Λc (onC cov2Src)) (spent 14)) := by
  decide +kernel

/-- cov3 under each erasure. -/
theorem cov3_erased : LambdaRow Λc (onC cov3Src) (.same (tyOf Λc (onC cov3Src)) (spent 2)) := by
  decide +kernel

/-- cov4 under each erasure. -/
theorem cov4_erased : LambdaRow Λc (onC cov4Src) (.same (tyOf Λc (onC cov4Src)) (spent 32)) := by
  decide +kernel

/-- accounted under each erasure.  `S` and `G` form the written self shape. -/
theorem accounted_erased : row Λc (onC accountedSrc) =
    [.same (tyOf Λc (onC accountedSrc)) (spent 36), missing 0,
     .same (tyOf Λc (onC accountedSrc)) (spent 36), .noSlot, .noSlot,
     .same (tyOf Λc (onC accountedSrc)) (spent 36)] := by
  decide +kernel

/-- W2 deep under each erasure.  The typer rejects the written domain with
`anyNotOk`. -/
theorem deep_erased : LambdaRow Λc (onC deepSrc) (.no (.landed "anyNotOk") (spent 0)) := by
  decide +kernel

/-- exTop under each erasure.  The written program and `C` are rejected by
the typer with `existentialAtTop`.  `D` erases the domain of the lambda
bound to `un` by a written `let`.  `S` and `G` form `read` pure. -/
theorem exTop_erased : row Λc (onZ exTopSrc) =
    [.no (.landed "existentialAtTop") (spent 19), missing 14, .no .mismatch (spent 62), .noSlot,
     .no (.landed "existentialAtTop") (spent 21), .no .mismatch (spent 62)] := by
  decide +kernel

/-- The escape under each erasure.  `C` and `G` take the callback's domains from
the written answer of its `let`, and the typer rejects the fill with the
escape the written program has.  The kernel checks the cells of `D`, `S` and
`A`, and `#eval expect` the whole row. -/
theorem Esc_erased :
    cell .D Λc (onC EscSrc) = missing 0 ∧
    cell .S Λc (onC EscSrc) = .noSlot ∧
    cell .A Λc (onC EscSrc) = .noSlot := by
  decide +kernel
#eval expect (row Λc (onC EscSrc) == [.no (.landed "levelEscape") (spent 31), missing 0, .noSlot,
    .noSlot, .no (.landed "levelEscape") (spent 63), .no (.landed "levelEscape") (spent 63)])
  "Esc: the row differs"

/-- The escape by an ascription under each erasure.  `C` and `G` take the
callback's domains from the ascription, and the typer rejects the fill with
the escape.  The kernel checks the cells of `D`, `S` and `A`, and
`#eval expect` the whole row. -/
theorem AscEsc_erased :
    cell .D Λc (onC AscEscSrc) = missing 0 ∧
    cell .S Λc (onC AscEscSrc) = .noSlot ∧
    cell .A Λc (onC AscEscSrc) = .noSlot := by
  decide +kernel
#eval expect (row Λc (onC AscEscSrc) == [.no (.landed "levelEscape") (spent 88), missing 0,
    .noSlot, .noSlot, .no (.landed "levelEscape") (spent 63),
    .no (.landed "levelEscape") (spent 63)])
  "AscEsc: the row differs"

/-- The escape at the top under each erasure.  Every domain is in a checked
position, so `D`, `C` and `G` give one program, rejected with the
escape.  The kernel checks the cells of `S` and `A`, and `#eval expect` the
whole row. -/
theorem TopEsc_erased :
    cell .S Λc (onC TopEscSrc) = .noSlot ∧
    cell .A Λc (onC TopEscSrc) = .noSlot := by
  decide +kernel
#eval expect (row Λc (onC TopEscSrc) == [.no (.landed "levelEscape") (spent 31),
    .no (.landed "levelEscape") (spent 63), .noSlot, .noSlot,
    .no (.landed "levelEscape") (spent 63), .no (.landed "levelEscape") (spent 63)])
  "TopEsc: the row differs"

/-- EscOk under each erasure.  `C` and `G` fill the callback's domain with
the goal's, its `any` read, so the fill is another one at the written type. -/
theorem EscOk_erased : row Λc (onC EscOkSrc) =
    [.same (tyOf Λc (onC EscOkSrc)) (spent 4), missing 0, .noSlot, .noSlot,
     .other (tyOf Λc (onC EscOkSrc)) (spent 7), .other (tyOf Λc (onC EscOkSrc)) (spent 7)] := by
  decide +kernel

/-- BX2 under each erasure. -/
theorem BX2_erased : LambdaRow Λc (onC BX2src) (.same (tyOf Λc (onC BX2src)) (spent 34)) := by
  decide +kernel

/-- BX under each erasure. -/
theorem BX_erased : LambdaRow Λc (onC BXsrc) (.same (tyOf Λc (onC BXsrc)) (spent 29)) := by
  decide +kernel

/-- A `let` whose bound term has an existential answer, under each erasure.
`C` fills the body under the unpacking, so the fill is an unpacking, which
`PTm.fills` does not relate to the written `let`.  The cell is `shape`, and
`compileE` reports a mismatch.  `S` and `G` form `read` pure. -/
theorem LetEx_erased : row Λc (onZ LetExSrc) =
    [.same (tyOf Λc (onZ LetExSrc)) (spent 20), missing 0, .no .mismatch (spent 62), .noSlot,
     .shape, .no .mismatch (spent 62)] := by
  decide +kernel

/-! ### Call arguments, callee bodies and `val` definitions

A lambda passed as an argument takes the dominant formal of its callee, whole,
so a block and a curried lambda get their inner domains too.  Under `A` every
such program compiles at the written body but TwoF, whose formals have no
dominant one, Inc, whose formals are incomparable, NoFn, whose callee has no
function type, and TooBig, whose closure is too large for its formal, as when
written.  A callee body `λx. g x` takes `g`'s formal, and a `val` definition
its written type.  The rows of the callee bodies and of a lambda bound by a
written `let` leave their own slots to the pairs below, since `D` erases the
outer domain as well. -/

/-- `withFile` applied to its callback, under each erasure.  `A` takes the
callback's domain from the formal.  `C` and `G` erase the inner domain too,
whose goal is the formal's result `⊤`, so they are a missing parameter type.
`S` compiles at the written type with `read` pure. -/
theorem S1call_erased : row Λc (onZ S1callSrc) =
    [.same (tyOf Λc (onZ S1callSrc)) (spent 83), missing 54,
     .other (tyOf Λc (onZ S1callSrc)) (spent 94), .same (tyOf Λc (onZ S1callSrc)) (spent 91),
     missing 54, missing 63] := by
  decide +kernel

/-- K1 under each erasure.  The argument takes the formal. -/
theorem K1_erased : row Λc (onE K1src) =
    [.same (tyOf Λc (onE K1src)) (spent 26), missing 0, .noSlot,
     .same (tyOf Λc (onE K1src)) (spent 33), .same (tyOf Λc (onE K1src)) (spent 33),
     .same (tyOf Λc (onE K1src)) (spent 33)] := by
  decide +kernel

/-- A callback whose parameter captures a platform capability, under each
erasure. -/
theorem Kcap_erased : row Λc (onC KcapSrc) =
    [.same (tyOf Λc (onC KcapSrc)) (spent 31), missing 0, .noSlot,
     .same (tyOf Λc (onC KcapSrc)) (spent 41), .same (tyOf Λc (onC KcapSrc)) (spent 41),
     .same (tyOf Λc (onC KcapSrc)) (spent 41)] := by
  decide +kernel

/-- E11 with the identity passed directly, twice, under each erasure.  Each
argument takes its formal. -/
theorem E11a_erased : row Λc (onE E11aSrc) =
    [.same (tyOf Λc (onE E11aSrc)) (spent 21), missing 0, .noSlot,
     .same (tyOf Λc (onE E11aSrc)) (spent 27), .same (tyOf Λc (onE E11aSrc)) (spent 27),
     .same (tyOf Λc (onE E11aSrc)) (spent 27)] := by
  decide +kernel

/-- An intersection callee whose formals agree on their domain, under each
erasure.  The dominant formal is the one with the result `⊤`. -/
theorem X1arg_erased : row Λc (onE X1Src) =
    [.same (tyOf Λc (onE X1Src)) (spent 31), missing 0, .noSlot,
     .same (tyOf Λc (onE X1Src)) (spent 52), .same (tyOf Λc (onE X1Src)) (spent 52),
     .same (tyOf Λc (onE X1Src)) (spent 52)] := by
  decide +kernel

/-- DomF under each erasure.  The second formal is above the first, so it is
the dominant one. -/
theorem DomF_erased : row Λc (onE DomFSrc) =
    [.same (tyOf Λc (onE DomFSrc)) (spent 31), missing 0, .noSlot,
     .same (tyOf Λc (onE DomFSrc)) (spent 66), .same (tyOf Λc (onE DomFSrc)) (spent 66),
     .same (tyOf Λc (onE DomFSrc)) (spent 66)] := by
  decide +kernel

/-- Dom under each erasure.  The dominant formal is the one with the smaller
domain. -/
theorem Dom_erased : row Λc (onE DomSrc) =
    [.same (tyOf Λc (onE DomSrc)) (spent 41), missing 0, .noSlot,
     .same (tyOf Λc (onE DomSrc)) (spent 66), .same (tyOf Λc (onE DomSrc)) (spent 66),
     .same (tyOf Λc (onE DomSrc)) (spent 66)] := by
  decide +kernel

/-- TwoF under each erasure.  Neither formal is above the other, so there is
no dominant one, where the written program compiles. -/
theorem TwoF_erased : row Λc (onE TwoFSrc) =
    [.same (tyOf Λc (onE TwoFSrc)) (spent 67), missing 0, .noSlot, missing 33, missing 33,
     missing 33] := by
  decide +kernel

/-- Inc under each erasure.  The formals are incomparable, so there is no
dominant one. -/
theorem Inc_erased : row Λc (onE IncSrc) =
    [.same (tyOf Λc (onE IncSrc)) (spent 52), missing 0, .noSlot, missing 17, missing 17,
     missing 17] := by
  decide +kernel

/-- NoFn under each erasure.  The callee has no function type. -/
theorem NoFn_erased : row Λc (onE NoFnSrc) =
    [.no .mismatch (spent 3), missing 0, .noSlot, missing 2, missing 2, missing 2] := by
  decide +kernel

/-- AliasArg under each erasure.  The formal is an alias of a function type,
followed to it. -/
theorem AliasArg_erased : row Λc (onE AliasArgSrc) =
    [.same (tyOf Λc (onE AliasArgSrc)) (spent 9), missing 0, .noSlot,
     .same (tyOf Λc (onE AliasArgSrc)) (spent 21), .same (tyOf Λc (onE AliasArgSrc)) (spent 21),
     .same (tyOf Λc (onE AliasArgSrc)) (spent 21)] := by
  decide +kernel

/-- A block passed as an argument, under each erasure.  `A` erases no lambda
directly passed.  `C` and `G` erase the block's result lambda, which takes
the formal. -/
theorem BlockArg_erased : row Λc (onE BlockArgSrc) =
    [.same (tyOf Λc (onE BlockArgSrc)) (spent 7), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE BlockArgSrc)) (spent 10),
     .same (tyOf Λc (onE BlockArgSrc)) (spent 10)] := by
  decide +kernel

/-- A curried callback, under each erasure.  `A` erases the outer domain,
`C` and `G` both. -/
theorem Curried_erased : row Λc (onE CurriedSrc) =
    [.same (tyOf Λc (onE CurriedSrc)) (spent 6), missing 0, .noSlot,
     .same (tyOf Λc (onE CurriedSrc)) (spent 10), .same (tyOf Λc (onE CurriedSrc)) (spent 10),
     .same (tyOf Λc (onE CurriedSrc)) (spent 10)] := by
  decide +kernel

/-- BoxCallee under each erasure. -/
theorem BoxCallee_erased : row Λc (onE BoxCalleeSrc) =
    [.same (tyOf Λc (onE BoxCalleeSrc)) (spent 8), missing 0, .noSlot,
     .same (tyOf Λc (onE BoxCalleeSrc)) (spent 12), .same (tyOf Λc (onE BoxCalleeSrc)) (spent 12),
     .same (tyOf Λc (onE BoxCalleeSrc)) (spent 12)] := by
  decide +kernel

/-- BoxF under each erasure. -/
theorem BoxF_erased : row Λc (onE BoxFSrc) =
    [.same (tyOf Λc (onE BoxFSrc)) (spent 14), missing 0, .noSlot,
     .same (tyOf Λc (onE BoxFSrc)) (spent 17), .same (tyOf Λc (onE BoxFSrc)) (spent 17),
     .same (tyOf Λc (onE BoxFSrc)) (spent 17)] := by
  decide +kernel

/-- AnyAsc under each erasure.  `C` and `G` also erase the domain of `g`'s
lambda, which reads the written `any`, so the fill is another one. -/
theorem AnyAsc_erased : row Λc (onC AnyAscSrc) =
    [.same (tyOf Λc (onC AnyAscSrc)) (spent 22), missing 0, .noSlot,
     .same (tyOf Λc (onC AnyAscSrc)) (spent 26), .other (tyOf Λc (onC AnyAscSrc)) (spent 26),
     .other (tyOf Λc (onC AnyAscSrc)) (spent 26)] := by
  decide +kernel

/-- Fits under each erasure. -/
theorem Fits_erased : row Λc (onC FitsSrc) =
    [.same (tyOf Λc (onC FitsSrc)) (spent 16), missing 0, .noSlot,
     .same (tyOf Λc (onC FitsSrc)) (spent 20), .same (tyOf Λc (onC FitsSrc)) (spent 20),
     .same (tyOf Λc (onC FitsSrc)) (spent 20)] := by
  decide +kernel

/-- TooBig under each erasure.  The closure is too large for the pure
formal, written or not. -/
theorem TooBig_erased : row Λc (onC TooBigSrc) =
    [.no .mismatch (spent 20), missing 0, .noSlot, .no .mismatch (spent 36),
     .no .mismatch (spent 36), .no .mismatch (spent 36)] := by
  decide +kernel

/-- A callee body under each erasure.  `D` erases the outer domain too. -/
theorem Callee_erased :
    LambdaRow Λc (onE CalleeSrc) (.same (tyOf Λc (onE CalleeSrc)) (spent 5)) := by
  decide +kernel

/-- A callee body at a formal written at `{any}`, under each erasure.  The
fill reads `any`, so it is another one at the written type. -/
theorem CalleeAny_erased : row Λc (onE CalleeAnySrc) =
    [.same (tyOf Λc (onE CalleeAnySrc)) (spent 18), .other (tyOf Λc (onE CalleeAnySrc)) (spent 19),
     .noSlot, .noSlot, .other (tyOf Λc (onE CalleeAnySrc)) (spent 18),
     .other (tyOf Λc (onE CalleeAnySrc)) (spent 18)] := by
  decide +kernel

/-- A callee body ascribed at `⊤`, under each erasure.  `C` and `G` take
`g`'s formal. -/
theorem CalleeTop_erased : row Λc (onE CalleeTopSrc) =
    [.same (tyOf Λc (onE CalleeTopSrc)) (spent 9), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE CalleeTopSrc)) (spent 10),
     .same (tyOf Λc (onE CalleeTopSrc)) (spent 10)] := by
  decide +kernel

/-- A callee body passed as an argument, under each erasure. -/
theorem CalleeArg_erased : row Λc (onE CalleeArgSrc) =
    [.same (tyOf Λc (onE CalleeArgSrc)) (spent 12), missing 0, .noSlot,
     .same (tyOf Λc (onE CalleeArgSrc)) (spent 22), .same (tyOf Λc (onE CalleeArgSrc)) (spent 22),
     .same (tyOf Λc (onE CalleeArgSrc)) (spent 22)] := by
  decide +kernel

/-- CalleeOther under each erasure. -/
theorem CalleeOther_erased :
    LambdaRow Λc (onE CalleeOtherSrc) (.same (tyOf Λc (onE CalleeOtherSrc)) (spent 6)) := by
  decide +kernel

/-- CalleeInc under each erasure. -/
theorem CalleeInc_erased :
    LambdaRow Λc (onE CalleeIncSrc) (.same (tyOf Λc (onE CalleeIncSrc)) (spent 14)) := by
  decide +kernel

/-- LetArg under each erasure. -/
theorem LetArg_erased :
    LambdaRow Λc (onE LetArgSrc) (.same (tyOf Λc (onE LetArgSrc)) (spent 5)) := by
  decide +kernel

/-- Id0 under each erasure. -/
theorem Id0_erased : LambdaRow Λc (onE Id0Src) (.same (tyOf Λc (onE Id0Src)) (spent 2)) := by
  decide +kernel

/-- A `val` definition under each erasure.  The written type is the goal. -/
theorem Val_erased : row Λc (onE ValSrc) =
    [.same (tyOf Λc (onE ValSrc)) (spent 2), .same (tyOf Λc (onE ValSrc)) (spent 4), .noSlot,
     .noSlot, .same (tyOf Λc (onE ValSrc)) (spent 4), .same (tyOf Λc (onE ValSrc)) (spent 4)] := by
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
theorem W2asc_erased : row Λc (onC W2ascSrc) =
    [.same (tyOf Λc (onC W2ascSrc)) (spent 3), .other (tyOf Λc (onC W2ascSrc)) (spent 3), .noSlot,
     .noSlot, .other (tyOf Λc (onC W2ascSrc)) (spent 3),
     .other (tyOf Λc (onC W2ascSrc)) (spent 3)] := by
  decide +kernel

/-- Two function sides of one domain, under each erasure. -/
theorem AndSame_erased : row Λc (onE AndSameSrc) =
    [.same (tyOf Λc (onE AndSameSrc)) (spent 34), .same (tyOf Λc (onE AndSameSrc)) (spent 34),
     .noSlot, .noSlot, .same (tyOf Λc (onE AndSameSrc)) (spent 34),
     .same (tyOf Λc (onE AndSameSrc)) (spent 34)] := by
  decide +kernel

/-- X3 under each erasure.  `C` and `G` compile, where Scala rejects. -/
theorem X3_erased : row Λc (onE X3Src) =
    [.same (tyOf Λc (onE X3Src)) (spent 40), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE X3Src)) (spent 41), .same (tyOf Λc (onE X3Src)) (spent 41)] := by
  decide +kernel

/-- X4 under each erasure.  `S` erases the self shape of the literal in the
lambda's body, which forms it.  `C` and `G` compile, where Scala rejects. -/
theorem X4_erased : row Λc (onE X4Src) =
    [.same (tyOf Λc (onE X4Src)) (spent 42), missing 0, .same (tyOf Λc (onE X4Src)) (spent 93),
     .noSlot, .same (tyOf Λc (onE X4Src)) (spent 43), .same (tyOf Λc (onE X4Src)) (spent 93)] := by
  decide +kernel

/-- Two function sides with comparable domains, under each erasure.  The
larger domain is taken. -/
theorem AndTwo_erased : row Λc (onE AndTwoSrc) =
    [.same (tyOf Λc (onE AndTwoSrc)) (spent 34), .same (tyOf Λc (onE AndTwoSrc)) (spent 38),
     .noSlot, .noSlot, .same (tyOf Λc (onE AndTwoSrc)) (spent 38),
     .same (tyOf Λc (onE AndTwoSrc)) (spent 38)] := by
  decide +kernel

/-- Two function sides whose results the lambda does not meet, under each
erasure. -/
theorem AndRes_erased : row Λc (onE AndResSrc) =
    [.no .mismatch (spent 31), .no .mismatch (spent 35), .noSlot, .noSlot,
     .no .mismatch (spent 35), .no .mismatch (spent 35)] := by
  decide +kernel

/-- Two function sides with incomparable domains, under each erasure.  The
sides do not meet, a type mismatch. -/
theorem AndInc_erased : row Λc (onE AndIncSrc) =
    [.same (tyOf Λc (onE AndIncSrc)) (spent 56), .no .mismatch (spent 4), .noSlot, .noSlot,
     .no .mismatch (spent 4), .no .mismatch (spent 4)] := by
  decide +kernel

/-- One function side and a field the lambda lacks, under each erasure. -/
theorem AndOne_erased : row Λc (onE AndOneSrc) =
    [.no .mismatch (spent 12), .no .mismatch (spent 12), .noSlot, .noSlot,
     .no .mismatch (spent 12), .no .mismatch (spent 12)] := by
  decide +kernel

/-- AndTop under each erasure. -/
theorem AndTop_erased : row Λc (onE AndTopSrc) =
    [.same (tyOf Λc (onE AndTopSrc)) (spent 12), .same (tyOf Λc (onE AndTopSrc)) (spent 12),
     .noSlot, .noSlot, .same (tyOf Λc (onE AndTopSrc)) (spent 12),
     .same (tyOf Λc (onE AndTopSrc)) (spent 12)] := by
  decide +kernel

/-- Asc under each erasure. -/
theorem Asc_erased : row Λc (onE AscSrc) =
    [.same (tyOf Λc (onE AscSrc)) (spent 2), .same (tyOf Λc (onE AscSrc)) (spent 2), .noSlot,
     .noSlot, .same (tyOf Λc (onE AscSrc)) (spent 2), .same (tyOf Λc (onE AscSrc)) (spent 2)] := by
  decide +kernel

/-- Alias under each erasure. -/
theorem Alias_erased : row Λc (onE AliasSrc) =
    [.same (tyOf Λc (onE AliasSrc)) (spent 11), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE AliasSrc)) (spent 12), .same (tyOf Λc (onE AliasSrc)) (spent 12)] := by
  decide +kernel

/-- Alias2 under each erasure. -/
theorem Alias2_erased : row Λc (onE Alias2Src) =
    [.same (tyOf Λc (onE Alias2Src)) (spent 17), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE Alias2Src)) (spent 19), .same (tyOf Λc (onE Alias2Src)) (spent 19)] := by
  decide +kernel

/-- A goal with a function upper bound only, under each erasure.  The lambda
is not below it. -/
theorem Upper_erased : row Λc (onE UpperSrc) =
    [.no .mismatch (spent 7), missing 0, .noSlot, .noSlot, .no .mismatch (spent 1),
     .no .mismatch (spent 1)] := by
  decide +kernel

/-- A goal with a function lower bound only, under each erasure.  It has no
function part. -/
theorem Lower_erased : row Λc (onE LowerSrc) =
    [.same (tyOf Λc (onE LowerSrc)) (spent 11), missing 0, .noSlot, .noSlot, missing 1,
     missing 1] := by
  decide +kernel

/-- A goal whose alias comes back to itself, under each erasure. -/
theorem Loop_erased : row Λc (onE LoopSrc) =
    [.no .mismatch (spent 12), missing 0, .noSlot, .noSlot, missing 3, missing 3] := by
  decide +kernel

/-- A lambda ascribed at `⊤`, under each erasure. -/
theorem IdTop_erased : row Λc (onE IdTopSrc) =
    [.same (tyOf Λc (onE IdTopSrc)) (spent 6), missing 0, .noSlot, .noSlot, missing 0,
     missing 0] := by
  decide +kernel

/-- Curry under each erasure. -/
theorem Curry_erased : row Λc (onE CurrySrc) =
    [.same (tyOf Λc (onE CurrySrc)) (spent 3), .same (tyOf Λc (onE CurrySrc)) (spent 3), .noSlot,
     .noSlot, .same (tyOf Λc (onE CurrySrc)) (spent 3),
     .same (tyOf Λc (onE CurrySrc)) (spent 3)] := by
  decide +kernel

/-- SideCurry under each erasure. -/
theorem SideCurry_erased : row Λc (onE SideCurrySrc) =
    [.same (tyOf Λc (onE SideCurrySrc)) (spent 13), .same (tyOf Λc (onE SideCurrySrc)) (spent 14),
     .noSlot, .noSlot, .same (tyOf Λc (onE SideCurrySrc)) (spent 14),
     .same (tyOf Λc (onE SideCurrySrc)) (spent 14)] := by
  decide +kernel

/-- LetBody under each erasure. -/
theorem LetBody_erased : row Λc (onE LetBodySrc) =
    [.same (tyOf Λc (onE LetBodySrc)) (spent 3), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE LetBodySrc)) (spent 3), .same (tyOf Λc (onE LetBodySrc)) (spent 3)] := by
  decide +kernel

/-- Block under each erasure. -/
theorem Block_erased : row Λc (onE BlockSrc) =
    [.same (tyOf Λc (onE BlockSrc)) (spent 3), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onE BlockSrc)) (spent 3), .same (tyOf Λc (onE BlockSrc)) (spent 3)] := by
  decide +kernel

/-- Cap under each erasure. -/
theorem Cap_erased : row Λc (onC CapSrc) =
    [.same (tyOf Λc (onC CapSrc)) (spent 4), missing 0, .noSlot, .noSlot,
     .same (tyOf Λc (onC CapSrc)) (spent 4), .same (tyOf Λc (onC CapSrc)) (spent 4)] := by
  decide +kernel

/-- A closure over `f` ascribed at a pure type, under each erasure.  The typer
rejects the fill with no reason of its own.  Its reason search reaches the
certificate builder, which reads the well-founded `Ctx.caps`.  The kernel
checks the cells of `D`, `S` and `A`, and `#eval expect` the whole row. -/
theorem CapPure_erased :
    cell .D Λc (onC CapPureSrc) = missing 0 ∧
    cell .S Λc (onC CapPureSrc) = .noSlot ∧
    cell .A Λc (onC CapPureSrc) = .noSlot := by
  decide +kernel
#eval expect (row Λc (onC CapPureSrc) == [.no .mismatch (spent 14), missing 0, .noSlot, .noSlot,
    .no .mismatch (spent 14), .no .mismatch (spent 14)])
  "CapPure: the row differs"

/-- A lambda ascribed at a type with `any` below a field of its domain,
under each erasure.  Every cell is the typer's `anyNotOk`. -/
theorem DeepAsc_erased : row Λc (onE DeepAscSrc) =
    [.no (.landed "anyNotOk") (spent 0), .no (.landed "anyNotOk") (spent 0), .noSlot, .noSlot,
     .no (.landed "anyNotOk") (spent 0), .no (.landed "anyNotOk") (spent 0)] := by
  decide +kernel

/-! ### Literals

A literal without a self shape at a `μ` goal takes the goal's shape, after
following an alias, and otherwise forms its self shape from its definitions in
rounds.  A field reached again while it is typed is a cyclic reference, and a
field whose types have no least one is ambiguous.  The least type of a field
does not depend on the order of an intersection. -/

/-- A field closure under a written self shape, under each erasure. -/
theorem Fld_erased : row Λc (onC FldSrc) =
    [.same (tyOf Λc (onC FldSrc)) (spent 5), missing 0, .same (tyOf Λc (onC FldSrc)) (spent 8),
     .noSlot, .same (tyOf Λc (onC FldSrc)) (spent 8), .same (tyOf Λc (onC FldSrc)) (spent 8)] := by
  decide +kernel

/-- A literal whose field has no written type, under each erasure.  `S` and
`G` give `NoShapeSrcS` of `Elab.lean`, a literal with no self shape and no
goal, which forms the written shape. -/
theorem FldTy_erased : row Λc (onE FldTySrc) =
    [.same (tyOf Λc (onE FldTySrc)) (spent 3), .same (tyOf Λc (onE FldTySrc)) (spent 5),
     .same (tyOf Λc (onE FldTySrc)) (spent 4), .noSlot, .same (tyOf Λc (onE FldTySrc)) (spent 5),
     .same (tyOf Λc (onE FldTySrc)) (spent 4)] := by
  decide +kernel

/-- A literal ascribed at a `μ`, under each erasure.  `S` and `G` take the
`μ` as the self shape. -/
theorem AscObj_erased : row Λc (onE AscObjSrc) =
    [.same (tyOf Λc (onE AscObjSrc)) (spent 3), missing 0,
     .same (tyOf Λc (onE AscObjSrc)) (spent 3), .noSlot, .noSlot,
     .same (tyOf Λc (onE AscObjSrc)) (spent 3)] := by
  decide +kernel

/-- A literal ascribed at a `μ` whose field is larger than the right-hand
side's type, under each erasure. -/
theorem AscWide_erased : row Λc (onE AscWideSrc) =
    [.same (tyOf Λc (onE AscWideSrc)) (spent 5), missing 0,
     .same (tyOf Λc (onE AscWideSrc)) (spent 5), .noSlot, .noSlot,
     .same (tyOf Λc (onE AscWideSrc)) (spent 5)] := by
  decide +kernel

/-- A literal ascribed at an alias of a `μ`, under each erasure.  `S` and `G`
follow the alias to the self shape. -/
theorem AliasMu_erased : row Λc (onE AliasMuSrc) =
    [.same (tyOf Λc (onE AliasMuSrc)) (spent 13), missing 0,
     .same (tyOf Λc (onE AliasMuSrc)) (spent 14), .noSlot,
     .same (tyOf Λc (onE AliasMuSrc)) (spent 15),
     .same (tyOf Λc (onE AliasMuSrc)) (spent 14)] := by
  decide +kernel

/-- Nest under each erasure.  `S` and `G` erase both self shapes, so the
inner literal has no `μ` goal and forms its shape, which `NestSrcW` writes. -/
theorem Nest_erased : row Λc (onE NestSrc) =
    [.same (tyOf Λc (onE NestSrc)) (spent 6), missing 0, .other (tyOf Λc (onE NestSrcW)) (spent 6),
     .noSlot, .noSlot, .other (tyOf Λc (onE NestSrcW)) (spent 6)] := by
  decide +kernel

/-- A field that reads a later field, under each erasure. -/
theorem Fwd_erased : row Λc (onE FwdObjSrc) =
    [.same (tyOf Λc (onE FwdObjSrc)) (spent 12), .same (tyOf Λc (onE FwdObjSrc)) (spent 14),
     .same (tyOf Λc (onE FwdObjSrc)) (spent 16), .noSlot,
     .same (tyOf Λc (onE FwdObjSrc)) (spent 14), .same (tyOf Λc (onE FwdObjSrc)) (spent 16)] := by
  decide +kernel

/-- A field that holds a capability, under each erasure. -/
theorem Cap1_erased : row Λc (onC Cap1Src) =
    [.same (tyOf Λc (onC Cap1Src)) (spent 10), missing 0, .same (tyOf Λc (onC Cap1Src)) (spent 10),
     .noSlot, .noSlot, .same (tyOf Λc (onC Cap1Src)) (spent 10)] := by
  decide +kernel

/-- SelfProj under each erasure.  The written self shape charges `a` at
`{z}`, which the typer rejects.  `S` and `G` form `{z, f}` and compile.  `C`
keeps the written shape and is rejected with it. -/
theorem SelfProj_erased : row Λc (onC SelfProjSrc) =
    [.no .mismatch (spent 36), missing 0, .other (tyOf Λc (onC SelfProjSrcF)) (spent 44), .noSlot,
     .no .mismatch (spent 47), .other (tyOf Λc (onC SelfProjSrcF)) (spent 44)] := by
  decide +kernel

/-- A recursive field, under each erasure.  `S` and `G` are a cyclic
reference at `a`. -/
theorem Rec_erased : row Λc (onE RecObjSrc) =
    [.same (tyOf Λc (onE RecObjSrc)) (spent 7), .same (tyOf Λc (onE RecObjSrc)) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0), .noSlot, .same (tyOf Λc (onE RecObjSrc)) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that is the self, under each erasure. -/
theorem Bare_erased : row Λc (onE BareSrc) =
    [.same (tyOf Λc (onE BareSrc)) (spent 15), .noSlot, .same (tyOf Λc (onE BareSrc)) (spent 15),
     .noSlot, .noSlot, .same (tyOf Λc (onE BareSrc)) (spent 15)] := by
  decide +kernel

/-- BareCap under each erasure.  `S` and `G` form `b` at the snapshot that
knows `a`. -/
theorem BareCap_erased : row Λc (onC BareCapSrc) =
    [.same (tyOf Λc (onC BareCapSrc)) (spent 38), missing 0,
     .other (tyOf Λc (onC BareCapSrcF)) (spent 40), .noSlot, .noSlot,
     .other (tyOf Λc (onC BareCapSrcF)) (spent 40)] := by
  decide +kernel

/-- LamCap under each erasure.  `S` and `G` form the written self shape. -/
theorem LamCap_erased : row Λc (onC LamCapSrc) =
    [.same (tyOf Λc (onC LamCapSrc)) (spent 54), missing 0,
     .same (tyOf Λc (onC LamCapSrc)) (spent 68), .noSlot,
     .same (tyOf Λc (onC LamCapSrc)) (spent 76), .same (tyOf Λc (onC LamCapSrc)) (spent 68)] := by
  decide +kernel

/-- A field that reads a later field that is the self, under each erasure. -/
theorem FwdSelf_erased : row Λc (onE FwdSelfSrc) =
    [.same (tyOf Λc (onE FwdSelfSrc)) (spent 30), .noSlot,
     .same (tyOf Λc (onE FwdSelfSrc)) (spent 33), .noSlot, .noSlot,
     .same (tyOf Λc (onE FwdSelfSrc)) (spent 33)] := by
  decide +kernel

/-- A field that is the self and a later one that reads it, under each
erasure. -/
theorem BareProj_erased : row Λc (onE BareProjSrc) =
    [.same (tyOf Λc (onE BareProjSrc)) (spent 30), .noSlot,
     .same (tyOf Λc (onE BareProjSrc)) (spent 33), .noSlot, .noSlot,
     .same (tyOf Λc (onE BareProjSrc)) (spent 33)] := by
  decide +kernel

/-- A field with two types, one below the other, under each erasure.  `S`
and `G` take the least. -/
theorem AmbUse_erased : row Λc (onE AmbUseSrc) =
    [.same (tyOf Λc (onE AmbUseSrc)) (spent 18), missing 0,
     .same (tyOf Λc (onE AmbUseSrc)) (spent 33), .noSlot, .noSlot,
     .same (tyOf Λc (onE AmbUseSrc)) (spent 33)] := by
  decide +kernel

/-- The same two types in the other order, under each erasure. -/
theorem AmbUse2_erased : row Λc (onE AmbUse2Src) =
    [.same (tyOf Λc (onE AmbUse2Src)) (spent 18), missing 0,
     .same (tyOf Λc (onE AmbUse2Src)) (spent 28), .noSlot, .noSlot,
     .same (tyOf Λc (onE AmbUse2Src)) (spent 28)] := by
  decide +kernel

/-- OrdA under each erasure.  `S` and `G` take the least type of the field,
the second side of `y`'s intersection. -/
theorem OrdA_erased : row Λc (onE OrdASrc) =
    [.same (tyOf Λc (onE OrdASrc)) (spent 18), missing 0, .same (tyOf Λc (onE OrdASrc)) (spent 33),
     .noSlot, .noSlot, .same (tyOf Λc (onE OrdASrc)) (spent 33)] := by
  decide +kernel

/-- OrdB, the sides of `y`'s intersection swapped, under each erasure.  `S`
and `G` take the same least type. -/
theorem OrdB_erased : row Λc (onE OrdBSrc) =
    [.same (tyOf Λc (onE OrdBSrc)) (spent 18), missing 0, .same (tyOf Λc (onE OrdBSrc)) (spent 28),
     .noSlot, .noSlot, .same (tyOf Λc (onE OrdBSrc)) (spent 28)] := by
  decide +kernel

/-- A field with two incomparable types, under each erasure.  `S` and `G`
are ambiguous at `a`. -/
theorem Amb_erased : row Λc (onE AmbSrc) =
    [.same (tyOf Λc (onE AmbSrc)) (spent 12), missing 0, .no (.ambiguous (.trm 0)) (spent 15),
     .noSlot, .noSlot, .no (.ambiguous (.trm 0)) (spent 15)] := by
  decide +kernel

/-- The literal of E2 on its own, under each erasure. -/
theorem E2obj_erased : row Λc (onE E2objSrc) =
    [.same (tyOf Λc (onE E2objSrc)) (spent 3), .same (tyOf Λc (onE E2objSrc)) (spent 5),
     .same (tyOf Λc (onE E2objSrc)) (spent 4), .noSlot, .same (tyOf Λc (onE E2objSrc)) (spent 5),
     .same (tyOf Λc (onE E2objSrc)) (spent 4)] := by
  decide +kernel

/-- Two fields that read each other, under each erasure.  `S` and `G` are a
cyclic reference at `a`. -/
theorem Cyc_erased : row Λc (onE CycSrc) =
    [.same (tyOf Λc (onE CycSrc)) (spent 19), .noSlot, .no (.cyclicRef (.trm 0)) (spent 0),
     .noSlot, .noSlot, .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that reads a cycle of two later fields, under each erasure.  `S`
and `G` are a cyclic reference at `b`. -/
theorem Cyc3_erased : row Λc (onC Cyc3Src) =
    [.same (tyOf Λc (onC Cyc3Src)) (spent 52), .noSlot, .no (.cyclicRef (.trm 1)) (spent 0),
     .noSlot, .noSlot, .no (.cyclicRef (.trm 1)) (spent 0)] := by
  decide +kernel

/-- A recursive field read through an alias of the self, under each erasure.
`S` and `G` are a cyclic reference at `a`. -/
theorem AliasRec_erased : row Λc (onE AliasRecSrc) =
    [.same (tyOf Λc (onE AliasRecSrc)) (spent 7), .same (tyOf Λc (onE AliasRecSrc)) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0), .noSlot, .same (tyOf Λc (onE AliasRecSrc)) (spent 13),
     .no (.cyclicRef (.trm 0)) (spent 0)] := by
  decide +kernel

/-- A field that is a lambda, under each erasure. -/
theorem NoDom_erased : row Λc (onE NoDomSrc) =
    [.same (tyOf Λc (onE NoDomSrc)) (spent 3), .same (tyOf Λc (onE NoDomSrc)) (spent 5),
     .same (tyOf Λc (onE NoDomSrc)) (spent 4), .noSlot, .same (tyOf Λc (onE NoDomSrc)) (spent 5),
     .same (tyOf Λc (onE NoDomSrc)) (spent 4)] := by
  decide +kernel

/-- The literal of `freshCell` on its own, written at the shape its
definitions form, under each erasure. -/
theorem Z1lit_erased : row Λc (onZ Z1litF) =
    [.same (tyOf Λc (onZ Z1litF)) (spent 3), .same (tyOf Λc (onZ Z1litF)) (spent 5),
     .same (tyOf Λc (onZ Z1litF)) (spent 4), .noSlot, .same (tyOf Λc (onZ Z1litF)) (spent 5),
     .same (tyOf Λc (onZ Z1litF)) (spent 4)] := by
  decide +kernel

/-! ### Programs with classifiers

Each program declares its classifiers, its classified platform, and for some
a use set and a kind.  The erasures act on the body only.  CE1, CE2, CE5io,
CE1arg and CE5argIo return their literal from a lambda ascribed at a codomain
`μ`, which gives the self shape, so `S` elaborates to the written body.  CE3,
CE3s, CE4 and KSelf form self shapes other than the written ones, and compile
at the written type.  `compile` moves CE3, CE3s, CE4 and M5 to their declared
use sets.  CE5 and CE5arg stay rejected for the kinding of the body's set at
`except[ThreadLocal]`, and KSelfIo for the kinding of its member at
`only[Control]`.  A domain written at `any` under a filter is filled with the
goal's domain read under the same filter, so the fill of CE2 and CE5io under
`D`, `C` and `G`, and of CE5argIo under `C` and `G`, is another one, at the
written type. -/

/-- `Try.apply` under each erasure, its set filtered at `only[Control]`. -/
theorem CE1_erased : row Λk CE1src =
    [.same (tyOf Λk CE1src) (spent 45), .same (tyOf Λk CE1src) (spent 47),
     .same (tyOf Λk CE1src) (spent 45), .noSlot, .same (tyOf Λk CE1src) (spent 47),
     .same (tyOf Λk CE1src) (spent 45)] := by
  decide +kernel

/-- `Future.apply` under each erasure.  Its domain writes `any` under a
filter, so `D`, `C` and `G` fill it with the goal's domain read, another
fill at the written type. -/
theorem CE2_erased : row Λk CE2src =
    [.same (tyOf Λk CE2src) (spent 56), .other (tyOf Λk CE2src) (spent 58),
     .same (tyOf Λk CE2src) (spent 56), .noSlot, .other (tyOf Λk CE2src) (spent 58),
     .other (tyOf Λk CE2src) (spent 56)] := by
  decide +kernel

/-- A client against a kind-bounded member, under each erasure.  With every
domain erased, the client bound to `c` has no goal: the written answer of
its `let` is the goal of the body, not of the bound term.  `S` and `G` form
`run` pure and compile at the written type. -/
theorem CE3_erased : row Λk CE3src =
    [.same (tyOf Λk CE3src) (spent 174), missing 0, .other (tyOf Λk CE3src) (spent 204), .noSlot,
     .same (tyOf Λk CE3src) (spent 178), .other (tyOf Λk CE3src) (spent 204)] := by
  decide +kernel

/-- CE3 over three `Control` capabilities, under each erasure. -/
theorem CE3s_erased : row Λk CE3sSrc =
    [.same (tyOf Λk CE3sSrc) (spent 253), missing 0, .other (tyOf Λk CE3sSrc) (spent 298), .noSlot,
     .same (tyOf Λk CE3sSrc) (spent 259), .other (tyOf Λk CE3sSrc) (spent 298)] := by
  decide +kernel

/-- A closure read off a kind-bounded member and handed to a filtered domain,
under each erasure. -/
theorem CE4_erased : row Λk CE4src =
    [.same (tyOf Λk CE4src) (spent 212), missing 0, .other (tyOf Λk CE4src) (spent 242), .noSlot,
     .same (tyOf Λk CE4src) (spent 216), .other (tyOf Λk CE4src) (spent 242)] := by
  decide +kernel

/-- CE4 with the member bounded by an unrelated classifier, under each
erasure. -/
theorem CE4neg_erased : LambdaRow Λk CE4negSrc (.no .mismatch (spent 84)) := by
  decide +kernel

/-- The client of CE4 at `only[Control]`, under each erasure. -/
theorem CE4pos_erased : LambdaRow Λk CE4posSrc (.same (tyOf Λk CE4posSrc) (spent 50)) := by
  decide +kernel

/-- A thread-local body passed to `Future.apply`, under each erasure.  The
kinding of `{tl}` at `except[ThreadLocal]` fails, written or erased. -/
theorem CE5_erased : row Λk CE5src =
    [.no .mismatch (spent 40), .no .mismatch (spent 42), .no .mismatch (spent 40), .noSlot,
     .no .mismatch (spent 42), .no .mismatch (spent 40)] := by
  decide +kernel

/-- CE5 with an input-output body, under each erasure. -/
theorem CE5io_erased : row Λk CE5ioSrc =
    [.same (tyOf Λk CE5ioSrc) (spent 34), .other (tyOf Λk CE5ioSrc) (spent 36),
     .same (tyOf Λk CE5ioSrc) (spent 34), .noSlot, .other (tyOf Λk CE5ioSrc) (spent 36),
     .other (tyOf Λk CE5ioSrc) (spent 34)] := by
  decide +kernel

/-- `Try.apply` with its body passed as a closure, under each erasure.  Every
erasure compiles at the written body. -/
theorem CE1arg_erased : row Λk CE1argSrc =
    [.same (tyOf Λk CE1argSrc) (spent 19), .same (tyOf Λk CE1argSrc) (spent 24),
     .same (tyOf Λk CE1argSrc) (spent 19), .same (tyOf Λk CE1argSrc) (spent 22),
     .same (tyOf Λk CE1argSrc) (spent 24), .same (tyOf Λk CE1argSrc) (spent 22)] := by
  decide +kernel

/-- `Future.apply` with a closure over a thread-local function, under each
erasure.  The kinding of the closure's set fails, written or erased. -/
theorem CE5arg_erased : row Λk CE5argSrc =
    [.no .mismatch (spent 85), missing 0, .no .mismatch (spent 85), .no .mismatch (spent 166),
     .no .mismatch (spent 168), .no .mismatch (spent 166)] := by
  decide +kernel

/-- `Future.apply` with a closure over an input-output function, under each
erasure.  `A` compiles at the written body.  `C` and `G` erase the domain
under the ascription too, which reads `any` under the filter. -/
theorem CE5argIo_erased : row Λk CE5argIoSrc =
    [.same (tyOf Λk CE5argIoSrc) (spent 38), missing 0, .same (tyOf Λk CE5argIoSrc) (spent 38),
     .same (tyOf Λk CE5argIoSrc) (spent 42), .other (tyOf Λk CE5argIoSrc) (spent 44),
     .other (tyOf Λk CE5argIoSrc) (spent 42)] := by
  decide +kernel

/-- A literal passed to a client whose parameter bounds a capture member by a
kind, under each erasure.  `S` and `G` form the member at its set and
`run` pure, and the member reaches the kind bound by the kinding search. -/
theorem KSelf_erased : row Λk KSelfSrc =
    [.same (tyOf Λk KSelfSrc) (spent 119), missing 0, .other (tyOf Λk KSelfSrc) (spent 134),
     .noSlot, .same (tyOf Λk KSelfSrc) (spent 121), .other (tyOf Λk KSelfSrc) (spent 134)] := by
  decide +kernel

/-- KSelf with the member at an input-output capability, under each erasure.
The kind bound excludes it, written or erased. -/
theorem KSelfIo_erased : row Λk KSelfIoSrc =
    [.no .mismatch (spent 289), missing 0, .no .mismatch (spent 290), .noSlot,
     .no .mismatch (spent 291), .no .mismatch (spent 290)] := by
  decide +kernel

/-- M5 under each erasure.  `D`, `C` and `G` take the domain from the
ascription, and the program reaches its declared filtered set. -/
theorem M5_erased : row Λk M5src =
    [.same (tyOf Λk M5src) (spent 21), .same (tyOf Λk M5src) (spent 21), .noSlot, .noSlot,
     .same (tyOf Λk M5src) (spent 21), .same (tyOf Λk M5src) (spent 21)] := by
  decide +kernel

/-- W, a restricted variable widened to its restricted set, under each
erasure. -/
theorem W_erased : LambdaRow Λk WSrc (.same (tyOf Λk WSrc) (spent 393)) := by
  decide +kernel

/-- W without the restriction, under each erasure. -/
theorem Wneg_erased : LambdaRow Λk WnegSrc (.no .mismatch (spent 234)) := by
  decide +kernel

/-- A lambda ascribed at a function type whose domain bounds a capture member
by a kind, under each erasure. -/
theorem KDom_erased : row Λk KDomSrc =
    [.same (tyOf Λk KDomSrc) (spent 2), .same (tyOf Λk KDomSrc) (spent 2), .noSlot, .noSlot,
     .same (tyOf Λk KDomSrc) (spent 2), .same (tyOf Λk KDomSrc) (spent 2)] := by
  decide +kernel

/-! ### Erasures no column makes

Each pair is a written program and one erased body of it: the inner domain of
a callback written, the body of a callee or of a `let` with the outer domain
written, the inner self shape of Nest, a field type written in place of the
self shape, the body of a `let` whose bound term has an existential answer,
and SideCurry with its outer domain written. -/

/-- `withFile` applied to its callback with the inner domain written.  The
callback's outer domain comes from the formal. -/
theorem S1callGu_pair : pair Λc (onZ S1callSrc) S1callSrcGu =
    [.same (tyOf Λc (onZ S1callSrc)) (spent 83), .same (tyOf Λc (onZ S1callSrc)) (spent 93)] := by
  decide +kernel

/-- A callee body with the outer domain written.  The body takes `g`'s
formal. -/
theorem Callee_pair : pair Λc (onE CalleeSrc) CalleeSrcD =
    [.same (tyOf Λc (onE CalleeSrc)) (spent 5), .same (tyOf Λc (onE CalleeSrc)) (spent 6)] := by
  decide +kernel

/-- A callee body at a formal written at `{any}`, `g`'s domain written.  The
fill reads `any`. -/
theorem CalleeAny_pair : pair Λc (onE CalleeAnySrc) CalleeAnySrcD =
    [.same (tyOf Λc (onE CalleeAnySrc)) (spent 18),
     .other (tyOf Λc (onE CalleeAnySrc)) (spent 19)] := by
  decide +kernel

/-- A body that calls `g` on another variable is no callee body. -/
theorem CalleeOther_pair : pair Λc (onE CalleeOtherSrc) CalleeOtherSrcD =
    [.same (tyOf Λc (onE CalleeOtherSrc)) (spent 6), missing 0] := by
  decide +kernel

/-- A callee at incomparable domains has no dominant formal. -/
theorem CalleeInc_pair : pair Λc (onE CalleeIncSrc) CalleeIncSrcD =
    [.same (tyOf Λc (onE CalleeIncSrc)) (spent 14), missing 9] := by
  decide +kernel

/-- A lambda bound by a written `let` and then passed has no goal, as Scala's
`val i = x => x`. -/
theorem LetArg_pair : pair Λc (onE LetArgSrc) LetArgSrcD =
    [.same (tyOf Λc (onE LetArgSrc)) (spent 5), missing 0] := by
  decide +kernel

/-- The inner self shape of Nest erased.  The field's written `μ` is the
goal. -/
theorem Nest_pair : pair Λc (onE NestSrc) NestSrcS =
    [.same (tyOf Λc (onE NestSrc)) (spent 6), .same (tyOf Λc (onE NestSrc)) (spent 10)] := by
  decide +kernel

/-- Seventeen literals nested, every self shape erased.  Each field is
elaborated once and checked once more at each enclosing literal. -/
theorem Nest16_pair : pair Λc (onE (NestKSrc true 16)) (NestKSrc false 16) =
    [.same (tyOf Λc (onE (NestKSrc true 16))) (spent 19),
     .same (tyOf Λc (onE (NestKSrc true 16))) (spent 171)] := by
  decide +kernel

/-- A recursive field with its type written in place of the self shape, the
domain erased. -/
theorem RecW_pair : pair Λc (onE RecObjSrc) RecWSrcS =
    [.same (tyOf Λc (onE RecObjSrc)) (spent 7), .same (tyOf Λc (onE RecObjSrc)) (spent 13)] := by
  decide +kernel

/-- A recursive field with its type written in place of the self shape, the
domain written. -/
theorem RecWd_pair : pair Λc (onE RecObjSrc) RecWdSrcS =
    [.same (tyOf Λc (onE RecObjSrc)) (spent 7), .same (tyOf Λc (onE RecObjSrc)) (spent 7)] := by
  decide +kernel

/-- A field type written under the written self shape, the domain erased. -/
theorem FldTyD_pair : pair Λc (onE FldTySrc) FldTySrcD =
    [.same (tyOf Λc (onE FldTySrc)) (spent 3), .same (tyOf Λc (onE FldTySrc)) (spent 5)] := by
  decide +kernel

/-- A field that is a lambda, with its self shape and its domain erased: no
goal reaches the lambda. -/
theorem NoDomDS_pair : pair Λc (onE NoDomSrc) NoDomSrcS =
    [.same (tyOf Λc (onE NoDomSrc)) (spent 3), missing 0] := by
  decide +kernel

/-- The body of a `let` whose bound term has an existential answer, its domain
erased.  The fill is an unpacking, which `PTm.fills` does not relate to the
written `let`, so `compileE` reports a mismatch where the elaborator types the
program. -/
theorem LetEx_pair :
    pair Λc (onZ LetExSrc) LetExSrcD = [.same (tyOf Λc (onZ LetExSrc)) (spent 20), .shape] ∧
    (elabProgOut Λc ((onZ LetExSrc).withSBody LetExSrcD)).1.isOk = true ∧
    reasonAt {} Λc ((onZ LetExSrc).withSBody LetExSrcD) = some .mismatch := by
  decide +kernel

/-- SideCurry with the outer domain written and the inner one erased. -/
theorem SideCurryW_pair : pair Λc (onE SideCurrySrc) SideCurrySrcW =
    [.same (tyOf Λc (onE SideCurrySrc)) (spent 13),
     .same (tyOf Λc (onE SideCurrySrc)) (spent 14)] := by
  decide +kernel

/-- The programs with no written form.  A field whose type names the class
root and a field whose right-hand side unpacks a `fresh` result each need a
written type, which no written form can give.  A lambda ascribed at a capture
member bounded by a kind has no goal with a function part. -/
theorem open_cells : openCell Λc (onE NESrcS) = .no (.needsExplicitType (.trm 0)) (spent 2) ∧
    openCell Λc (onZ NEfreshSrcS) = .no (.needsExplicitType (.trm 0)) (spent 24) ∧
    openCell Λk KGoalSrc = missing 0 := by
  decide +kernel

/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at every distinct erased program whose cell is `same` or
`other`, and at every pair that compiles.  The success is the premise, by
`decide +kernel`.  A program two erasures give alike is listed once, under
every erasure that gives it. -/

/-- The target checker accepts E2 under `D` and `C`. -/
theorem E2_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onE E2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2 under `S` and `G`. -/
theorem E2_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE E2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E5 under `S` and `G`. -/
theorem E5_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE E5src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E6 under `S` and `G`. -/
theorem E6_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE E6srcW)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E7 under `S` and `G`. -/
theorem E7_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE E7src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C7 under `S` and `G`. -/
theorem C7_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onC C7src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S3 under `S` and `G`. -/
theorem S3_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onC S3src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C2 under `S` and `G`. -/
theorem C2_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onC C2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts C2 under `C`. -/
theorem C2_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onC C2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `S`. -/
theorem S1_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onZ S1progSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `C`. -/
theorem S1_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onZ S1progSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1 under `G`. -/
theorem S1_G_checks : CheckerAccepts {} Λc (Erasure.G.prog (onZ S1progSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S2 under `S`. -/
theorem S2_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onZ S2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1 under `D` and `C`. -/
theorem Z1_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onZ Z1progSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1def under `D` and `C`. -/
theorem Z1def_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onZ Z1defSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z2 under `D` and `C`. -/
theorem Z2_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onZ Z2src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `D` and `C`. -/
theorem Z3_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onZ Z3src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `S`. -/
theorem Z3_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onZ Z3src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z3 under `G`. -/
theorem Z3_G_checks : CheckerAccepts {} Λc (Erasure.G.prog (onZ Z3src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts accounted under `S` and `G`. -/
theorem accounted_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onC accountedSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts EscOk under `C` and `G`. -/
theorem EscOk_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onC EscOkSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1call under `S`. -/
theorem S1call_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onZ S1callSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts S1call under `A`. -/
theorem S1call_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onZ S1callSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts K1 under `A`, `C` and `G`. -/
theorem K1_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE K1src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Kcap under `A`, `C` and `G`. -/
theorem Kcap_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onC KcapSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E11a under `A`, `C` and `G`. -/
theorem E11a_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE E11aSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X1arg under `A`, `C` and `G`. -/
theorem X1arg_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE X1Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts DomF under `A`, `C` and `G`. -/
theorem DomF_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE DomFSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Dom under `A`, `C` and `G`. -/
theorem Dom_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE DomSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AliasArg under `A`, `C` and `G`. -/
theorem AliasArg_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onE AliasArgSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BlockArg under `C` and `G`. -/
theorem BlockArg_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE BlockArgSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curried under `A`. -/
theorem Curried_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onE CurriedSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curried under `C` and `G`. -/
theorem Curried_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE CurriedSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BoxCallee under `A`, `C` and `G`. -/
theorem BoxCallee_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onE BoxCalleeSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BoxF under `A`, `C` and `G`. -/
theorem BoxF_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onE BoxFSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AnyAsc under `A`. -/
theorem AnyAsc_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onC AnyAscSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AnyAsc under `C` and `G`. -/
theorem AnyAsc_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onC AnyAscSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fits under `A`, `C` and `G`. -/
theorem Fits_A_checks : CheckerAccepts {} Λc (Erasure.A.prog (onC FitsSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeAny under `D`. -/
theorem CalleeAny_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE CalleeAnySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeAny under `C` and `G`. -/
theorem CalleeAny_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE CalleeAnySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeTop under `C` and `G`. -/
theorem CalleeTop_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE CalleeTopSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CalleeArg under `A`, `C` and `G`. -/
theorem CalleeArg_A_checks :
    CheckerAccepts {} Λc (Erasure.A.prog (onE CalleeArgSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Val under `D`, `C` and `G`. -/
theorem Val_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onE ValSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts W2asc under `D`, `C` and `G`. -/
theorem W2asc_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onC W2ascSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndSame under `D`, `C` and `G`. -/
theorem AndSame_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE AndSameSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X3 under `C` and `G`. -/
theorem X3_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onE X3Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X4 under `S`. -/
theorem X4_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE X4Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X4 under `C`. -/
theorem X4_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onE X4Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts X4 under `G`. -/
theorem X4_G_checks : CheckerAccepts {} Λc (Erasure.G.prog (onE X4Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndTwo under `D`, `C` and `G`. -/
theorem AndTwo_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE AndTwoSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AndTop under `D`, `C` and `G`. -/
theorem AndTop_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE AndTopSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Asc under `D`, `C` and `G`. -/
theorem Asc_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onE AscSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Alias under `C` and `G`. -/
theorem Alias_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE AliasSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Alias2 under `C` and `G`. -/
theorem Alias2_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE Alias2Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Curry under `D`, `C` and `G`. -/
theorem Curry_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE CurrySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts SideCurry under `D`, `C` and `G`. -/
theorem SideCurry_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE SideCurrySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LetBody under `C` and `G`. -/
theorem LetBody_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE LetBodySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Block under `C` and `G`. -/
theorem Block_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE BlockSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Cap under `C` and `G`. -/
theorem Cap_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onC CapSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fld under `S` and `G`. -/
theorem Fld_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onC FldSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fld under `C`. -/
theorem Fld_C_checks : CheckerAccepts {} Λc (Erasure.C.prog (onC FldSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FldTy under `D` and `C`. -/
theorem FldTy_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE FldTySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FldTy under `S` and `G`. -/
theorem FldTy_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE FldTySrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AscObj under `S` and `G`. -/
theorem AscObj_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE AscObjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AscWide under `S` and `G`. -/
theorem AscWide_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE AscWideSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AliasMu under `S` and `G`. -/
theorem AliasMu_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE AliasMuSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AliasMu under `C`. -/
theorem AliasMu_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onE AliasMuSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Nest under `S` and `G`. -/
theorem Nest_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE NestSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fwd under `D` and `C`. -/
theorem Fwd_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onE FwdObjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Fwd under `S` and `G`. -/
theorem Fwd_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE FwdObjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Cap1 under `S` and `G`. -/
theorem Cap1_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onC Cap1Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts SelfProj under `S` and `G`. -/
theorem SelfProj_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onC SelfProjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Rec under `D` and `C`. -/
theorem Rec_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onE RecObjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Bare under `S` and `G`. -/
theorem Bare_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE BareSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BareCap under `S` and `G`. -/
theorem BareCap_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onC BareCapSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LamCap under `S` and `G`. -/
theorem LamCap_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onC LamCapSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts LamCap under `C`. -/
theorem LamCap_C_checks :
    CheckerAccepts {} Λc (Erasure.C.prog (onC LamCapSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts FwdSelf under `S` and `G`. -/
theorem FwdSelf_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE FwdSelfSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts BareProj under `S` and `G`. -/
theorem BareProj_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE BareProjSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AmbUse under `S` and `G`. -/
theorem AmbUse_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE AmbUseSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AmbUse2 under `S` and `G`. -/
theorem AmbUse2_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE AmbUse2Src)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts OrdA under `S` and `G`. -/
theorem OrdA_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE OrdASrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts OrdB under `S` and `G`. -/
theorem OrdB_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onE OrdBSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2obj under `D` and `C`. -/
theorem E2obj_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE E2objSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts E2obj under `S` and `G`. -/
theorem E2obj_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE E2objSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts AliasRec under `D` and `C`. -/
theorem AliasRec_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE AliasRecSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts NoDom under `D` and `C`. -/
theorem NoDom_D_checks :
    CheckerAccepts {} Λc (Erasure.D.prog (onE NoDomSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts NoDom under `S` and `G`. -/
theorem NoDom_S_checks :
    CheckerAccepts {} Λc (Erasure.S.prog (onE NoDomSrc)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1lit under `D` and `C`. -/
theorem Z1lit_D_checks : CheckerAccepts {} Λc (Erasure.D.prog (onZ Z1litF)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts Z1lit under `S` and `G`. -/
theorem Z1lit_S_checks : CheckerAccepts {} Λc (Erasure.S.prog (onZ Z1litF)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1 under `D` and `C`. -/
theorem CE1_D_checks : CheckerAccepts {} Λk (Erasure.D.prog CE1src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1 under `S`. -/
theorem CE1_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE1src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1 under `G`. -/
theorem CE1_G_checks : CheckerAccepts {} Λk (Erasure.G.prog CE1src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE2 under `D` and `C`. -/
theorem CE2_D_checks : CheckerAccepts {} Λk (Erasure.D.prog CE2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE2 under `S`. -/
theorem CE2_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE2 under `G`. -/
theorem CE2_G_checks : CheckerAccepts {} Λk (Erasure.G.prog CE2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE3 under `S` and `G`. -/
theorem CE3_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE3 under `C`. -/
theorem CE3_C_checks : CheckerAccepts {} Λk (Erasure.C.prog CE3src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE3s under `S` and `G`. -/
theorem CE3s_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE3sSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE3s under `C`. -/
theorem CE3s_C_checks : CheckerAccepts {} Λk (Erasure.C.prog CE3sSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE4 under `S` and `G`. -/
theorem CE4_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE4src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE4 under `C`. -/
theorem CE4_C_checks : CheckerAccepts {} Λk (Erasure.C.prog CE4src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5io under `D` and `C`. -/
theorem CE5io_D_checks : CheckerAccepts {} Λk (Erasure.D.prog CE5ioSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5io under `S`. -/
theorem CE5io_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE5ioSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5io under `G`. -/
theorem CE5io_G_checks : CheckerAccepts {} Λk (Erasure.G.prog CE5ioSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1arg under `D` and `C`. -/
theorem CE1arg_D_checks : CheckerAccepts {} Λk (Erasure.D.prog CE1argSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1arg under `S`. -/
theorem CE1arg_S_checks : CheckerAccepts {} Λk (Erasure.S.prog CE1argSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1arg under `A`. -/
theorem CE1arg_A_checks : CheckerAccepts {} Λk (Erasure.A.prog CE1argSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE1arg under `G`. -/
theorem CE1arg_G_checks : CheckerAccepts {} Λk (Erasure.G.prog CE1argSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5argIo under `S`. -/
theorem CE5argIo_S_checks :
    CheckerAccepts {} Λk (Erasure.S.prog CE5argIoSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5argIo under `A`. -/
theorem CE5argIo_A_checks :
    CheckerAccepts {} Λk (Erasure.A.prog CE5argIoSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5argIo under `C`. -/
theorem CE5argIo_C_checks :
    CheckerAccepts {} Λk (Erasure.C.prog CE5argIoSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts CE5argIo under `G`. -/
theorem CE5argIo_G_checks :
    CheckerAccepts {} Λk (Erasure.G.prog CE5argIoSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts KSelf under `S` and `G`. -/
theorem KSelf_S_checks : CheckerAccepts {} Λk (Erasure.S.prog KSelfSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts KSelf under `C`. -/
theorem KSelf_C_checks : CheckerAccepts {} Λk (Erasure.C.prog KSelfSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts M5 under `D`, `C` and `G`. -/
theorem M5_D_checks : CheckerAccepts {} Λk (Erasure.D.prog M5src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts KDom under `D`, `C` and `G`. -/
theorem KDom_D_checks : CheckerAccepts {} Λk (Erasure.D.prog KDomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair S1callGu. -/
theorem S1callGu_pair_checks : CheckerAccepts {} Λc (onZ S1callSrcGu) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair Callee. -/
theorem Callee_pair_checks : CheckerAccepts {} Λc (onE CalleeSrcD) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair CalleeAny. -/
theorem CalleeAny_pair_checks : CheckerAccepts {} Λc (onE CalleeAnySrcD) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair Nest. -/
theorem Nest_pair_checks : CheckerAccepts {} Λc (onE NestSrcS) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair Nest16. -/
theorem Nest16_pair_checks : CheckerAccepts {} Λc (onE (NestKSrc false 16)) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair RecW. -/
theorem RecW_pair_checks : CheckerAccepts {} Λc (onE RecWSrcS) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair RecWd. -/
theorem RecWd_pair_checks : CheckerAccepts {} Λc (onE RecWdSrcS) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair FldTyD. -/
theorem FldTyD_pair_checks : CheckerAccepts {} Λc (onE FldTySrcD) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the erased body of the pair SideCurryW. -/
theorem SideCurryW_pair_checks : CheckerAccepts {} Λc (onE SideCurrySrcW) (by decide +kernel) :=
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
theorem E1_D_rejected : RejectedAbove Λc (Erasure.D.prog (onE E1src)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE E1src) (Erasure.D.surface (onE E1src).body) = missing 0) rfl

/-- S1 with every domain erased: the lambda bound to `op` by a `let` with no
type has no goal. -/
theorem S1_D_rejected :
    RejectedAbove Λc (Erasure.D.prog (onZ S1progSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S1progSrc) (Erasure.D.surface (onZ S1progSrc).body) = missing 28) rfl

/-- S2 with every domain erased. -/
theorem S2_D_rejected : RejectedAbove Λc (Erasure.D.prog (onZ S2src)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S2src) (Erasure.D.surface (onZ S2src).body) = missing 96) rfl

/-- S2 with the domains in checked positions erased: `(λy. y : ⊤)` has a
goal with no function part. -/
theorem S2_C_rejected : RejectedAbove Λc (Erasure.C.prog (onZ S2src)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S2src) (Erasure.C.surface (onZ S2src).body) = missing 96) rfl

/-- S2 as a Scala programmer writes it, rejected at the same lambda. -/
theorem S2_G_rejected : RejectedAbove Λc (Erasure.G.prog (onZ S2src)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S2src) (Erasure.G.surface (onZ S2src).body) = missing 143) rfl

/-- exTop with every domain erased: the argument bound to `un` by a written
`let` has no goal. -/
theorem exTop_D_rejected :
    RejectedAbove Λc (Erasure.D.prog (onZ exTopSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ exTopSrc) (Erasure.D.surface (onZ exTopSrc).body) = missing 14) rfl

/-- `withFile` applied to its callback with both domains erased: the inner
lambda's goal is the formal's result `⊤`. -/
theorem S1call_C_rejected :
    RejectedAbove Λc (Erasure.C.prog (onZ S1callSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S1callSrc) (Erasure.C.surface (onZ S1callSrc).body) = missing 54) rfl

/-- The same with every self shape erased too. -/
theorem S1call_G_rejected :
    RejectedAbove Λc (Erasure.G.prog (onZ S1callSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onZ S1callSrc) (Erasure.G.surface (onZ S1callSrc).body) = missing 63) rfl

/-- A callee whose two formals agree on the parameter and differ in results
neither of which is below the other: no formal dominates. -/
theorem TwoF_A_rejected :
    RejectedAbove Λc (Erasure.A.prog (onE TwoFSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE TwoFSrc) (Erasure.A.surface (onE TwoFSrc).body) = missing 33) rfl

/-- A callee whose two formals are incomparable: no formal dominates. -/
theorem Inc_A_rejected : RejectedAbove Λc (Erasure.A.prog (onE IncSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE IncSrc) (Erasure.A.surface (onE IncSrc).body) = missing 17) rfl

/-- A callee with no function type. -/
theorem NoFn_A_rejected :
    RejectedAbove Λc (Erasure.A.prog (onE NoFnSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE NoFnSrc) (Erasure.A.surface (onE NoFnSrc).body) = missing 2) rfl

/-- A lambda bound by a `let` with no type. -/
theorem Id0_D_rejected : RejectedAbove Λc (Erasure.D.prog (onE Id0Src)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE Id0Src) (Erasure.D.surface (onE Id0Src).body) = missing 0) rfl

/-- A lambda ascribed at `⊤`, which has no function part. -/
theorem IdTop_C_rejected :
    RejectedAbove Λc (Erasure.C.prog (onE IdTopSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE IdTopSrc) (Erasure.C.surface (onE IdTopSrc).body) = missing 0) rfl

/-- A goal that bounds a function type from below only. -/
theorem Lower_C_rejected :
    RejectedAbove Λc (Erasure.C.prog (onE LowerSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE LowerSrc) (Erasure.C.surface (onE LowerSrc).body) = missing 1) rfl

/-- A goal whose alias comes back to itself. -/
theorem Loop_C_rejected :
    RejectedAbove Λc (Erasure.C.prog (onE LoopSrc)) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE LoopSrc) (Erasure.C.surface (onE LoopSrc).body) = missing 3) rfl

/-- CE3 with every domain erased: the client bound by a `let` whose written
answer is the goal of its body has no goal of its own. -/
theorem CE3_D_rejected : RejectedAbove Λk (Erasure.D.prog CE3src) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λk CE3src (Erasure.D.surface CE3src.body) = missing 0) rfl

/-- Two fields that read each other: a cyclic reference at `a`. -/
theorem Cyc_S_rejected : RejectedAbove Λc (Erasure.S.prog (onE CycSrc)) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE CycSrc) (Erasure.S.surface (onE CycSrc).body) =
      .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A recursive field without a written type: a cyclic reference at `a`. -/
theorem Rec_S_rejected : RejectedAbove Λc (Erasure.S.prog (onE RecObjSrc)) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE RecObjSrc) (Erasure.S.surface (onE RecObjSrc).body) =
      .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A recursive field read through an alias of the self: a cyclic reference
at `a`. -/
theorem AliasRec_S_rejected :
    RejectedAbove Λc (Erasure.S.prog (onE AliasRecSrc)) (.cyclicRef (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE AliasRecSrc) (Erasure.S.surface (onE AliasRecSrc).body) =
      .no (.cyclicRef (.trm 0)) (spent 0)) rfl

/-- A field that reads a cycle of two later fields: a cyclic reference at
`b`, the member the walk from `a` reaches twice. -/
theorem Cyc3_S_rejected : RejectedAbove Λc (Erasure.S.prog (onC Cyc3Src)) (.cyclicRef (.trm 1)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onC Cyc3Src) (Erasure.S.surface (onC Cyc3Src).body) =
      .no (.cyclicRef (.trm 1)) (spent 0)) rfl

/-- A field whose two types are incomparable: no least one. -/
theorem Amb_S_rejected : RejectedAbove Λc (Erasure.S.prog (onE AmbSrc)) (.ambiguous (.trm 0)) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE AmbSrc) (Erasure.S.surface (onE AmbSrc).body) =
      .no (.ambiguous (.trm 0)) (spent 15)) rfl

/-- Two function sides with incomparable domains: a type mismatch, where the
compiler forms the union of the domains. -/
theorem AndInc_D_rejected : RejectedWith Λc (Erasure.D.prog (onE AndIncSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onE AndIncSrc) (Erasure.D.surface (onE AndIncSrc).body) =
      .no .mismatch (spent 4))

/-- One function side and a field the lambda lacks. -/
theorem AndOne_D_rejected : RejectedWith Λc (Erasure.D.prog (onE AndOneSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onE AndOneSrc) (Erasure.D.surface (onE AndOneSrc).body) =
      .no .mismatch (spent 12))

/-- Two function sides whose results the lambda does not meet. -/
theorem AndRes_D_rejected : RejectedWith Λc (Erasure.D.prog (onE AndResSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onE AndResSrc) (Erasure.D.surface (onE AndResSrc).body) =
      .no .mismatch (spent 35))

/-- A goal that bounds a function type from above only. -/
theorem Upper_C_rejected : RejectedWith Λc (Erasure.C.prog (onE UpperSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onE UpperSrc) (Erasure.C.surface (onE UpperSrc).body) = .no .mismatch (spent 1))

/-- A closure over `f` at a pure formal. -/
theorem TooBig_A_rejected : RejectedWith Λc (Erasure.A.prog (onC TooBigSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onC TooBigSrc) (Erasure.A.surface (onC TooBigSrc).body) =
      .no .mismatch (spent 36))

/-- C7 with its boxes written and its self shape erased: the formed box
holds `{f1}` where the written unboxing names `{k1}`. -/
theorem C7box_S_rejected : RejectedWith Λc (Erasure.S.prog (onC C7boxSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onC C7boxSrc) (Erasure.S.surface (onC C7boxSrc).body) =
      .no .mismatch (spent 13))

/-- `freshCell` with its self shape erased: the formed `read` is pure, and
no rule relates the formed `μ` to the written one. -/
theorem Z1_S_rejected : RejectedWith Λc (Erasure.S.prog (onZ Z1progSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ Z1progSrc) (Erasure.S.surface (onZ Z1progSrc).body) =
      .no .mismatch (spent 62))

/-- The same in a `let` with a written type. -/
theorem Z1def_S_rejected : RejectedWith Λc (Erasure.S.prog (onZ Z1defSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ Z1defSrc) (Erasure.S.surface (onZ Z1defSrc).body) =
      .no .mismatch (spent 112))

/-- The same in `makeLogger`. -/
theorem Z2_S_rejected : RejectedWith Λc (Erasure.S.prog (onZ Z2src)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ Z2src) (Erasure.S.surface (onZ Z2src).body) = .no .mismatch (spent 62))

/-- The same in exTop. -/
theorem exTop_S_rejected : RejectedWith Λc (Erasure.S.prog (onZ exTopSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ exTopSrc) (Erasure.S.surface (onZ exTopSrc).body) =
      .no .mismatch (spent 62))

/-- The same in the `let` whose bound term has an existential answer. -/
theorem LetEx_S_rejected : RejectedWith Λc (Erasure.S.prog (onZ LetExSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ LetExSrc) (Erasure.S.surface (onZ LetExSrc).body) =
      .no .mismatch (spent 62))

/-- SelfProj with the field's domain erased: the written self shape charges
`a` at `{z}`, as the written program, which the typer rejects. -/
theorem SelfProj_C_rejected : RejectedWith Λc (Erasure.C.prog (onC SelfProjSrc)) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onC SelfProjSrc) (Erasure.C.surface (onC SelfProjSrc).body) =
      .no .mismatch (spent 47))

/-- KSelf with its member at an input-output capability and its self shape
erased: the formed member is `{io}`, which the kind bound of the client's
parameter excludes. -/
theorem KSelfIo_S_rejected : RejectedWith Λk (Erasure.S.prog KSelfIoSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λk KSelfIoSrc (Erasure.S.surface KSelfIoSrc.body) = .no .mismatch (spent 290))

/-- CE5 with every domain erased: the kinding of `{tl}` at
`except[ThreadLocal]` fails, as for the written program. -/
theorem CE5_D_rejected : RejectedWith Λk (Erasure.D.prog CE5src) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λk CE5src (Erasure.D.surface CE5src.body) = .no .mismatch (spent 42))

/-- `Future.apply` with a closure over a thread-local function, the closure's
domain erased: the kinding of the closure's set fails, as for the written
program. -/
theorem CE5arg_A_rejected : RejectedWith Λk (Erasure.A.prog CE5argSrc) .mismatch :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λk CE5argSrc (Erasure.A.surface CE5argSrc.body) = .no .mismatch (spent 166))

/-- exTop with the domains in checked positions erased: the typer rejects
the existential answer outside every scope, as on the written program. -/
theorem exTop_C_rejected :
    RejectedWith Λc (Erasure.C.prog (onZ exTopSrc)) (.landed "existentialAtTop") :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onZ exTopSrc) (Erasure.C.surface (onZ exTopSrc).body) =
      .no (.landed "existentialAtTop") (spent 21))

/-- A lambda ascribed at a type with `any` below a field of its domain: the
typer's `anyNotOk`. -/
theorem DeepAsc_D_rejected :
    RejectedWith Λc (Erasure.D.prog (onE DeepAscSrc)) (.landed "anyNotOk") :=
  erasedCell_rejected (by decide +kernel :
    erasedCell Λc (onE DeepAscSrc) (Erasure.D.surface (onE DeepAscSrc).body) =
      .no (.landed "anyNotOk") (spent 0))

/-- A lambda bound by a written `let` and then passed: the `let` is no call
argument. -/
theorem LetArg_pair_rejected :
    RejectedAbove Λc ((onE LetArgSrc).withSBody LetArgSrcD) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE LetArgSrc) LetArgSrcD = missing 0) rfl

/-- A body that calls `g` on another variable. -/
theorem CalleeOther_pair_rejected :
    RejectedAbove Λc ((onE CalleeOtherSrc).withSBody CalleeOtherSrcD) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE CalleeOtherSrc) CalleeOtherSrcD = missing 0) rfl

/-- A callee body at incomparable domains. -/
theorem CalleeInc_pair_rejected :
    RejectedAbove Λc ((onE CalleeIncSrc).withSBody CalleeIncSrcD) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE CalleeIncSrc) CalleeIncSrcD = missing 9) rfl

/-- A field that is a lambda, in a literal without a self shape and with no
goal. -/
theorem NoDomDS_pair_rejected :
    RejectedAbove Λc ((onE NoDomSrc).withSBody NoDomSrcS) (.missingParamType none) :=
  erasedCell_slot (by decide +kernel :
    erasedCell Λc (onE NoDomSrc) NoDomSrcS = missing 0) rfl

/-- A field whose type names the class root needs a written type. -/
theorem NE_rejected : RejectedAbove Λc (onE NESrcS) (.needsExplicitType (.trm 0)) :=
  openCell_slot (by decide +kernel :
    openCell Λc (onE NESrcS) = .no (.needsExplicitType (.trm 0)) (spent 2)) rfl

/-- A field whose right-hand side unpacks a `fresh` result needs a written
type. -/
theorem NEfresh_rejected : RejectedAbove Λc (onZ NEfreshSrcS) (.needsExplicitType (.trm 0)) :=
  openCell_slot (by decide +kernel :
    openCell Λc (onZ NEfreshSrcS) = .no (.needsExplicitType (.trm 0)) (spent 24)) rfl

/-- A lambda ascribed at a capture member bounded by a kind: the goal has no
function part. -/
theorem KGoal_rejected : RejectedAbove Λk KGoalSrc (.missingParamType none) :=
  openCell_slot (by decide +kernel :
    openCell Λk KGoalSrc = missing 0) rfl

/-- The escape with its callback's domains erased, under `C` and `G`, which
give one program.  The elaborator fails with the tank unmarked, so no budget
compiles it. -/
theorem Esc_C_rejected (b : Budget) :
    (compile b Λc (Erasure.C.prog (onC EscSrc))).isOk = false :=
  elabProgOut_rejects (by decide +kernel :
    elabProgOut Λc (Erasure.C.prog (onC EscSrc)) = (.no .mismatch, spent 63)) b

/-- The escape by an ascription with its callback's domains erased, under `C`
and `G`. -/
theorem AscEsc_C_rejected (b : Budget) :
    (compile b Λc (Erasure.C.prog (onC AscEscSrc))).isOk = false :=
  elabProgOut_rejects (by decide +kernel :
    elabProgOut Λc (Erasure.C.prog (onC AscEscSrc)) = (.no .mismatch, spent 63)) b

/-- The escape at the top with its callback's domains erased, under `D`, `C`
and `G`. -/
theorem TopEsc_C_rejected (b : Budget) :
    (compile b Λc (Erasure.C.prog (onC TopEscSrc))).isOk = false :=
  elabProgOut_rejects (by decide +kernel :
    elabProgOut Λc (Erasure.C.prog (onC TopEscSrc)) = (.no .mismatch, spent 63)) b

/-- A closure over `f` ascribed at a pure type, its domain erased, under `C`
and `G`, which give one program.  The elaborator fails with the tank
unmarked, so no budget compiles it.  The reason, a mismatch, is checked with
the row. -/
theorem CapPure_C_rejected (b : Budget) :
    (compile b Λc (Erasure.C.prog (onC CapPureSrc))).isOk = false :=
  elabProgOut_rejects (by decide +kernel :
    elabProgOut Λc (Erasure.C.prog (onC CapPureSrc)) = (.no .mismatch, spent 14)) b

-- The reason is the typer's escape on the fill, at the goal the typer reaches
-- on the written program, with the same certificate.
#eval expect (escapesAt (compile {} Λc (Erasure.C.prog (onC EscSrc))) EscGoalCtx
    [CapAtom.var .here] [CapAtom.cvar escRoot])
  "the escape under C: not rejected at the goal in EscGoalCtx"

#eval expect ((compile {} Λc (Erasure.C.prog (onC AscEscSrc))).reason?.map Reason.name ==
    some "levelEscape")
  "the escape by an ascription under C: not rejected with the escape"

#eval expect (escapesAt (compile {} Λc (Erasure.C.prog (onC TopEscSrc))) TopGoalCtx
    [CapAtom.var .here] topPlat)
  "the escape at the top under C: not rejected at the goal in TopGoalCtx"

end Erasures

/-! ## Completeness at the direct sites

`compile_complete_canonAt` at the erased programs of the tables whose empty
slots sit at direct sites.  Each theorem says that the written program with
its body erased compiles as the written program does, header, fill, term, use
set, type and derivation, at every budget from some fuel on.  `canonAt`
decides its premises, with every reading of a goal and every run of the typer
taken at `defaultFuel`, and the kernel checks it.  The fill is the written
body in every case.  A theorem is named after the first erasure that gives its
program, and its docstring names every erasure that gives the same program.

The erased programs that compile and are no such case are a lambda whose body
has an empty slot at an intersection with a function side, a literal whose
self shape the rounds form, a literal written in a field whose outer literal
has no self shape either, and a program whose fill reads the `any` of its
goal, which is no written program.  A program at a call argument closes the
section.  The elaborator rejects it, though the typer accepts its fill, which
is the written program. -/

section Complete

/-- The program `w` with its body replaced by `e` compiles as `w` does, at
every budget from some fuel on. -/
def CompilesAs (Λ : LabelTable) (w : SProg) (e : STm) : Prop :=
  ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λ (w.withSBody e) = compile b Λ w

/-! ### Call arguments

The dominant formal of the callee gives the domain. -/

/-- S1 with the domain of its callback erased, under `A`. -/
theorem S1call_A_complete : CompilesAs Λc (onZ S1callSrc) (Erasure.A.surface S1callSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda passed to a callee whose parameter type is written, under `A`,
`C` and `G`. -/
theorem K1_A_complete : CompilesAs Λc (onE K1src) (Erasure.A.surface K1src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callback whose parameter captures a platform capability, under `A`, `C`
and `G`. -/
theorem Kcap_A_complete : CompilesAs Λc (onC KcapSrc) (Erasure.A.surface KcapSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- E11 with the identity passed directly, twice, under `A`, `C` and `G`. -/
theorem E11a_A_complete : CompilesAs Λc (onE E11aSrc) (Erasure.A.surface E11aSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An intersection callee whose formals agree on their domain, under `A`,
`C` and `G`. -/
theorem X1arg_A_complete : CompilesAs Λc (onE X1Src) (Erasure.A.surface X1Src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An intersection callee whose second formal is above the first, under `A`,
`C` and `G`. -/
theorem DomF_A_complete : CompilesAs Λc (onE DomFSrc) (Erasure.A.surface DomFSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An intersection callee whose formals have comparable domains, under `A`,
`C` and `G`. -/
theorem Dom_A_complete : CompilesAs Λc (onE DomSrc) (Erasure.A.surface DomSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee whose formal is an alias of a function type, under `A`, `C` and
`G`. -/
theorem AliasArg_A_complete : CompilesAs Λc (onE AliasArgSrc) (Erasure.A.surface AliasArgSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda passed as an argument, its outer domain erased, under
`A`. -/
theorem Curried_A_complete : CompilesAs Λc (onE CurriedSrc) (Erasure.A.surface CurriedSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with both domains erased, under `C` and `G`. -/
theorem Curried_C_complete : CompilesAs Λc (onE CurriedSrc) (Erasure.C.surface CurriedSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A boxed callee, under `A`, `C` and `G`. -/
theorem BoxCallee_A_complete : CompilesAs Λc (onE BoxCalleeSrc) (Erasure.A.surface BoxCalleeSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A boxed formal, under `A`, `C` and `G`. -/
theorem BoxF_A_complete : CompilesAs Λc (onE BoxFSrc) (Erasure.A.surface BoxFSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee whose formal captures anything, and a closure over `f` as its
argument, under `A`. -/
theorem AnyAsc_A_complete : CompilesAs Λc (onC AnyAscSrc) (Erasure.A.surface AnyAscSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over `f` at a formal that captures `f`, under `A`, `C` and `G`. -/
theorem Fits_A_complete : CompilesAs Λc (onC FitsSrc) (Erasure.A.surface FitsSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee body as a call argument at a formal with no function part, so
the callee of the body gives the domain, under `A`, `C` and `G`. -/
theorem CalleeArg_A_complete : CompilesAs Λc (onE CalleeArgSrc) (Erasure.A.surface CalleeArgSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block as a call argument whose result is a lambda, under `C` and `G`. -/
theorem BlockArg_C_complete : CompilesAs Λc (onE BlockArgSrc) (Erasure.C.surface BlockArgSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Ascriptions and written types

The written type gives the domain through its function part.  A written type
with no function part leaves it to the callee of a body `g x`. -/

/-- `let x : A = λy. y in x`, under `D`, `C` and `G`. -/
theorem Val_D_complete : CompilesAs Λc (onE ValSrc) (Erasure.D.surface ValSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two function sides of one domain, under `D`, `C` and `G`. -/
theorem AndSame_D_complete : CompilesAs Λc (onE AndSameSrc) (Erasure.D.surface AndSameSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two function sides with comparable domains, under `D`, `C` and `G`. -/
theorem AndTwo_D_complete : CompilesAs Λc (onE AndTwoSrc) (Erasure.D.surface AndTwoSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A function side beside `⊤`, under `D`, `C` and `G`. -/
theorem AndTop_D_complete : CompilesAs Λc (onE AndTopSrc) (Erasure.D.surface AndTopSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The identity ascribed `∀(x : ⊤) ⊤`, under `D`, `C` and `G`. -/
theorem Asc_D_complete : CompilesAs Λc (onE AscSrc) (Erasure.D.surface AscSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda ascribed a curried function type, both domains erased,
under `D`, `C` and `G`. -/
theorem Curry_D_complete : CompilesAs Λc (onE CurrySrc) (Erasure.D.surface CurrySrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An ascription whose second side is a selection with a function lower
bound, under `C` and `G`. -/
theorem X3_C_complete : CompilesAs Λc (onE X3Src) (Erasure.C.surface X3Src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda ascribed at an intersection with one function side and an
abstract side, whose body holds a literal with a written self shape, under
`C`. -/
theorem X4_C_complete : CompilesAs Λc (onE X4Src) (Erasure.C.surface X4Src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of a function type, under `C` and `G`. -/
theorem Alias_C_complete : CompilesAs Λc (onE AliasSrc) (Erasure.C.surface AliasSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of an alias, under `C` and `G`. -/
theorem Alias2_C_complete : CompilesAs Λc (onE Alias2Src) (Erasure.C.surface Alias2Src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee body ascribed at `⊤`, which has no function part, so the callee
gives the domain, under `C` and `G`. -/
theorem CalleeTop_C_complete : CompilesAs Λc (onE CalleeTopSrc) (Erasure.C.surface CalleeTopSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda as the body of a `let` with a written function type, under `C`
and `G`. -/
theorem LetBody_C_complete : CompilesAs Λc (onE LetBodySrc) (Erasure.C.surface LetBodySrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block ascribed at a function type, under `C` and `G`. -/
theorem Block_C_complete : CompilesAs Λc (onE BlockSrc) (Erasure.C.surface BlockSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over a capability ascribed a function type that captures it,
under `C` and `G`. -/
theorem Cap_C_complete : CompilesAs Λc (onC CapSrc) (Erasure.C.surface CapSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals with a written self shape

A field takes the domain of its lambda from its type in the shape. -/

/-- E2: a literal whose field is a lambda, projected and applied, under `D`
and `C`. -/
theorem E2_D_complete : CompilesAs Λc (onE E2src) (Erasure.D.surface E2src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- C2, its domains in checked positions erased, under `C`. -/
theorem C2_C_complete : CompilesAs Λc (onC C2src) (Erasure.C.surface C2src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- S1, its domains in checked positions erased, under `C`. -/
theorem S1_C_complete : CompilesAs Λc (onZ S1progSrc) (Erasure.C.surface S1progSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z1, under `D` and `C`. -/
theorem Z1_D_complete : CompilesAs Λc (onZ Z1progSrc) (Erasure.D.surface Z1progSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z1 with `freshCell` defined, under `D` and `C`. -/
theorem Z1def_D_complete : CompilesAs Λc (onZ Z1defSrc) (Erasure.D.surface Z1defSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Z3, under `D` and `C`. -/
theorem Z3_D_complete : CompilesAs Λc (onZ Z3src) (Erasure.D.surface Z3src) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The literal of `freshCell` with the self shape its definitions form,
under `D` and `C`. -/
theorem Z1lit_D_complete : CompilesAs Λc (onZ Z1litF) (Erasure.D.surface Z1litF) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field closure of a literal with a written self shape, under `C`. -/
theorem Fld_C_complete : CompilesAs Λc (onC FldSrc) (Erasure.C.surface FldSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal with a written self shape and a field without its type, under
`D` and `C`. -/
theorem FldTy_D_complete : CompilesAs Λc (onE FldTySrc) (Erasure.D.surface FldTySrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal whose first field reads the second, under `D` and `C`. -/
theorem Fwd_D_complete : CompilesAs Λc (onE FwdObjSrc) (Erasure.D.surface FwdObjSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field with its type written in the self shape, under `D` and
`C`. -/
theorem Rec_D_complete : CompilesAs Λc (onE RecObjSrc) (Erasure.D.surface RecObjSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field that reads itself through an alias of the self, under
`D` and `C`. -/
theorem AliasRec_D_complete : CompilesAs Λc (onE AliasRecSrc) (Erasure.D.surface AliasRecSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure that reads a sibling through the self, beside a field that
holds a capability, under `C`. -/
theorem LamCap_C_complete : CompilesAs Λc (onC LamCapSrc) (Erasure.C.surface LamCapSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The literal of E2 on its own, under `D` and `C`. -/
theorem E2obj_D_complete : CompilesAs Λc (onE E2objSrc) (Erasure.D.surface E2objSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field that is a lambda, under `D` and `C`. -/
theorem NoDom_D_complete : CompilesAs Λc (onE NoDomSrc) (Erasure.D.surface NoDomSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals at a `μ` goal

A literal without a self shape takes the body of the `μ` its goal dealiases
to. -/

/-- A literal ascribed at `μ` of its shape, under `S` and `G`. -/
theorem AscObj_S_complete : CompilesAs Λc (onE AscObjSrc) (Erasure.S.surface AscObjSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal whose field is below the goal's field, under `S` and `G`. -/
theorem AscWide_S_complete : CompilesAs Λc (onE AscWideSrc) (Erasure.S.surface AscWideSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal ascribed at an alias of a `μ`, under `S` and `G`. -/
theorem AliasMu_S_complete : CompilesAs Λc (onE AliasMuSrc) (Erasure.S.surface AliasMuSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with the domain of its lambda field erased and its self shape
written, under `C`. -/
theorem AliasMu_C_complete : CompilesAs Λc (onE AliasMuSrc) (Erasure.C.surface AliasMuSrc) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Programs with classifiers

Whole programs with classifier declarations, a classified platform, and a
declared use set or kind.  The header stays as written, and the fill is the
written body. -/

/-- `Try.apply`, CE1, its domains erased, under `D` and `C`. -/
theorem CE1_D_complete : CompilesAs Λk CE1src (Erasure.D.surface CE1src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- CE1 with its self shapes erased, under `S`. -/
theorem CE1_S_complete : CompilesAs Λk CE1src (Erasure.S.surface CE1src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- CE1 with its checked domains and its self shapes erased, under `G`. -/
theorem CE1_G_complete : CompilesAs Λk CE1src (Erasure.G.surface CE1src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- `Future.apply`, CE2, its self shapes erased, under `S`. -/
theorem CE2_S_complete : CompilesAs Λk CE2src (Erasure.S.surface CE2src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The client of a kind-bounded member, CE3, its checked domains erased,
under `C`. -/
theorem CE3_C_complete : CompilesAs Λk CE3src (Erasure.C.surface CE3src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- CE3 over three platform capabilities, its checked domains erased, under
`C`. -/
theorem CE3s_C_complete : CompilesAs Λk CE3sSrc (Erasure.C.surface CE3sSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- CE4, its checked domains erased, under `C`. -/
theorem CE4_C_complete : CompilesAs Λk CE4src (Erasure.C.surface CE4src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- CE5 with the body at `{io}`, its self shapes erased, under `S`. -/
theorem CE5io_S_complete : CompilesAs Λk CE5ioSrc (Erasure.S.surface CE5ioSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- `Try.apply` with its body passed as a closure, its domains erased, under
`D` and `C`. -/
theorem CE1arg_D_complete : CompilesAs Λk CE1argSrc (Erasure.D.surface CE1argSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with its self shapes erased, under `S`. -/
theorem CE1arg_S_complete : CompilesAs Λk CE1argSrc (Erasure.S.surface CE1argSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with the domain of the closure erased, under `A`. -/
theorem CE1arg_A_complete : CompilesAs Λk CE1argSrc (Erasure.A.surface CE1argSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with its checked domains and its self shapes erased, under `G`. -/
theorem CE1arg_G_complete : CompilesAs Λk CE1argSrc (Erasure.G.surface CE1argSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure that captures an input-output function passed as the body, its
self shapes erased, under `S`. -/
theorem CE5argIo_S_complete : CompilesAs Λk CE5argIoSrc (Erasure.S.surface CE5argIoSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with the domain of the closure erased, under `A`. -/
theorem CE5argIo_A_complete : CompilesAs Λk CE5argIoSrc (Erasure.A.surface CE5argIoSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A client whose parameter bounds a capture member by a kind, its checked
domains erased, under `C`. -/
theorem KSelf_C_complete : CompilesAs Λk KSelfSrc (Erasure.C.surface KSelfSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A program that declares a filtered use set, under `D`, `C` and `G`. -/
theorem M5_D_complete : CompilesAs Λk M5src (Erasure.D.surface M5src.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda ascribed at a function type whose domain bounds a capture member
by a kind, under `D`, `C` and `G`. -/
theorem KDom_D_complete : CompilesAs Λk KDomSrc (Erasure.D.surface KDomSrc.body) :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Erasures no column makes -/

/-- S1's call with the outer domain of its callback erased and the inner one
written. -/
theorem S1callGu_pair_complete : CompilesAs Λc (onZ S1callSrc) S1callSrcGu :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body `λx. g x` bound by a `let`. -/
theorem Callee_pair_complete : CompilesAs Λc (onE CalleeSrc) CalleeSrcD :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal nested in a field of a written self shape, its own self shape
erased. -/
theorem Nest_pair_complete : CompilesAs Λc (onE NestSrc) NestSrcS :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field with a written type equal to the shape's, the domain of its
lambda erased. -/
theorem FldTyD_pair_complete : CompilesAs Λc (onE FldTySrc) FldTySrcD :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

-- Erased programs that compile with no canonical fill: a lambda whose body
-- has an empty slot at an intersection, two literals whose self shapes the
-- rounds form, a literal nested seventeen deep with every self shape erased,
-- two fills that read the `any` of a goal, and a field type written in place
-- of the self shape.
example : canonAt Λc (onE SideCurrySrc) (Erasure.D.surface SideCurrySrc) = false := by
  decide +kernel
example : canonAt Λc (onE E2src) (Erasure.S.surface E2src) = false := by decide +kernel
example : canonAt Λc (onE X4Src) (Erasure.S.surface X4Src) = false := by decide +kernel
example : canonAt Λc (onE (NestKSrc true 16)) (NestKSrc false 16) = false := by decide +kernel
example : canonAt Λc (onE CalleeAnySrc) CalleeAnySrcD = false := by decide +kernel
example : canonAt Λk CE2src (Erasure.D.surface CE2src.body) = false := by decide +kernel
example : canonAt Λc (onE RecObjSrc) RecWSrcS = false := by decide +kernel

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
  cls% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λ(x : ⊤). n)

/-- The same with the argument's domain erased. -/
def MidSrcA : STm :=
  cls% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λx. n)

-- The erased program is the written one with the argument's domain erased.
example : Erasure.A.surface MidSrc = MidSrcA := rfl

/-- The written program compiles, and the erased one is a mismatch. -/
theorem Mid_erased : pair Λc (onE MidSrc) MidSrcA =
    [.same (tyOf Λc (onE MidSrc)) (spent 60), .no .mismatch (spent 77)] := by decide +kernel

/-- The erased program is rejected at every budget. -/
theorem Mid_rejected : RejectedWith Λc ((onE MidSrc).withSBody MidSrcA) .mismatch :=
  erasedCell_rejected (w := onE MidSrc) (n := defaultFuel - 77) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem Mid_checks : CheckerAccepts {} Λc (onE MidSrc) (by decide +kernel) :=
  compile_checks_get _

-- The erased program does not have the written one as its canonical fill.
example : canonAt Λc (onE MidSrc) MidSrcA = false := by decide +kernel

end Complete

end ClassifiersFrontend
