import Coercions.Paths.Frontend.Typer
import Coercions.Paths.Frontend.Elab
import Coercions.Paths.Frontend.Step
import Coercions.Paths.Frontend.StepFC
import Coercions.Paths.DotToFCdot.Safety
import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.DotToFCdot.Acceptance
import Coercions.Paths.FCdot.CheckerCompleteness

/-!
# The pipeline

`compileE` resolves the program to a partial term (`resolveP`), whose empty
slots are a lambda's domain, a literal's self type and a field's type, and
elaborates it (`elabTopF`, `Elab.lean`).  It returns the fill, the resolved
program with its empty slots filled, and a `Compiled`, which holds the type
and the `Paths.DotMNF.HasTy` derivation of the fill's erasure.  Or it returns
the reason the program is rejected: a missing parameter type, a cyclic
reference, candidates with no least type, a mismatch, or the recursion limit.
`compile` forgets the reason (`compile_eq`).  `compileAndRun` follows with the
source machine of `Step.lean` at a step budget.  `compileAndRunFC` translates
the derivation to FCdot and runs the machine of `StepFC.lean` at a
normalization fuel and a step budget.

A program with every slot written elaborates as the typer types it, at the
same fuel.  So `compile` on it is `compileLanded`, the typer's synthesis on the
resolved term (`compile_full`).  The fill agrees with every slot the program
writes (`compileE_fills`).  The four reasons that name an empty slot come only
from a program with an empty slot (`compileE_slot`).  An elaboration that ends
unmarked gives the same verdict at more fuel (`elabTop?_mono`,
`elabTop?_stable`).  A program whose empty slots are lambda domains at the
direct sites compiles to its canonical fill from some fuel on, when the typer
accepts that fill (`compile_complete_direct`).

Eight theorems say what a successful compile is worth.  Each one composes a
result about the calculus.  The front end proves nothing new.

* `compile_checks` is `Paths.FCdot.checkTm_complete` applied to
  `Paths.DotMNF.HasTy.translate_typed`.  The checker takes no fuel, so its
  verdict on the translation is a theorem and not a run.  `compile_checks_get`
  is the same statement for a compile known only to succeed, so that a concrete
  program discharges it with one decided fact.
* `compile_erase` is `Paths.DotMNF.HasTy.translate_erase`.
* `compile_safe` is `Paths.DotMNF.dot_safety` and `compile_not_stuck` is
  `Paths.DotMNF.dot_not_stuck`.
* `compile_run_progress` is `compile_safe` at the state the source driver
  returns.  The driver never answers with a stuck state.
* `compile_consistent` is `Paths.DotMNF.reachable_consistent`.  Every store the
  translated program reaches is typed, and its context proves no `⊤ ≤ ⊥`.
  `compile_fcRun_consistent` is the same at the state the target driver
  returns.
* `compile_no_bad_literal` is `Paths.DotMNF.acceptance_gdot3_any`.  A compiled
  object literal never has the type `μ(x. {A : ⊤..⊥})`.

Each theorem holds for every program.  The hypothesis
`compile b Λ e = some ⟨a, c⟩` is the successful compile.  The content is the
type of `c`, whose `deriv` field is a derivation of
`Paths.DotMNF.HasTy .nil a.erase c.ty`.  The term `a` is the fill, so the
theorems speak of the program inference completed.  The other premises name
what a theorem speaks of: the run `r`, the budgets `m` and `n`, and the
equation `hd` for the programs that are object literals.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Ty Tm Defs Ctx HasTy State Step Steps)

/-! ## The result of a compilation -/

/-- A type for a closed term, with a derivation that the term has it. -/
structure Compiled (t : Tm []) where
  /-- The synthesized type. -/
  ty : Ty []
  /-- The derivation. -/
  deriv : HasTy .nil t ty

/-! ## The pipeline

`compileE` is resolution to a partial term followed by elaboration.  The
result is a dependent pair, because the derivation is about the erasure of the
term the elaborator returns. -/

/-- Resolve to a partial term, then elaborate at the budget's fuel.  The answer
is the fill with its type and derivation, or the reason the program is
rejected.  A program out of scope or out of the label table has no resolution,
and the reason is a mismatch, which names no slot. -/
def compileE (b : Budget) (Λ : LabelTable) (e : STm) :
    Except EReason ((a : ATm []) × Compiled a.erase) :=
  match resolveP Λ e with
  | none => .error .mismatch
  | some p =>
      match (elabTopF b.fuel p).1 with
      | .ok c => .ok ⟨c.a, ⟨c.ty, c.deriv⟩⟩
      | .error r => .error r

/-- Resolve and elaborate at the budget's fuel, without the reason.  The result
is `none` when the program is out of scope, out of the label table, rejected,
or out of the elaborator's reach at the budget. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) :=
  (compileE b Λ e).toOption

/-- The typer's synthesis on a resolved term with every slot written, as a
compilation. -/
def compileLanded (b : Budget) (a : ATm []) : Option ((a : ATm []) × Compiled a.erase) :=
  (synthTop? b a).map fun c => ⟨a, ⟨c.ty, c.deriv⟩⟩

/-- `compile`, then the source machine on the erased term for `m` steps. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ e).map fun r => run m [] ⟨.nil, .nil, r.1.erase⟩

/-- `compile`, then the translation of the derivation and the target machine,
at normalization fuel `n` and step budget `m`. -/
def compileAndRunFC (b : Budget) (n m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × Paths.FCdot.State s) :=
  (compile b Λ e).map fun r => fcRun n m [] ⟨.nil, .nil, r.2.deriv.translate⟩

/-! ## The theorems -/

-- Most theorems never use `h`.  It is what a caller holds.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- The empty source context translates to the empty target context. -/
theorem translate_ctx_nil : Ctx.translate (Ctx.nil : Ctx []) = Paths.FCdot.Ctx.nil := rfl

/-- **The target checker accepts the translation.** -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true :=
  Paths.FCdot.checkTm_complete (translate_ctx_nil ▸ HasTy.translate_typed c.deriv .nil)

/-- **The translation erases to the source term.** -/
theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.Tm.erase c.deriv.translate = Tm.erase a.erase :=
  HasTy.translate_erase c.deriv

/-- **Safety of the compiled program.**  The run `r` names the reached state. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  Paths.DotMNF.dot_safety c.deriv r

/-- **No reachable state of the compiled program is stuck.** -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) : ¬ State.Stuck st :=
  Paths.DotMNF.dot_not_stuck c.deriv r

/-- **The source driver never answers at a stuck state.**  The state `run`
returns is final or `step?` finds a step.  This is `compile_safe` at that
state, using `run_steps` and `step?_eq_none_iff`. -/
theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    let st := (run m [] ⟨.nil, .nil, a.erase⟩).2
    State.Final st ∨ (step? st).isSome := by
  intro st
  have hr : Steps (⟨.nil, .nil, a.erase⟩ : State []) st :=
    run_steps m ⟨.nil, .nil, a.erase⟩
  rcases compile_safe h hr with hfin | hstep
  · exact Or.inl hfin
  · refine Or.inr ?_
    cases hs : step? st with
    | some _ => rfl
    | none => exact absurd hstep (step?_eq_none_iff.mp hs)

/-- **The target machine reaches only consistent stores.**  Every reached state
has a store typed at some context that proves no `⊤ ≤ ⊥`. -/
theorem compile_consistent (h : compile b Λ e = some ⟨a, c⟩) {s : Sig}
    {st : Paths.FCdot.State s}
    (r : Paths.FCdot.Steps (⟨.nil, .nil, c.deriv.translate⟩ : Paths.FCdot.State []) st) :
    ∃ Γ : Paths.FCdot.Ctx s, Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo s, Paths.FCdot.LeCo.HasType Γ ev .top .bot :=
  Paths.DotMNF.reachable_consistent c.deriv r

/-- **The target driver answers with a consistent store.**  This is
`compile_consistent` at the state `fcRun` returns, by `fcRun_steps`. -/
theorem compile_fcRun_consistent (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    let st := (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).2
    ∃ Γ : Paths.FCdot.Ctx (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
      Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
        Paths.FCdot.LeCo.HasType Γ ev .top .bot := by
  intro st
  exact compile_consistent h (fcRun_steps n m _)

/-- **A compiled object literal never has the bad bounds type.**  The equation
`hd` says the program is an object literal.  Its type is then not
`μ(x. {A : ⊤..⊥})` for any `A`. -/
theorem compile_no_bad_literal (h : compile b Λ e = some ⟨a, c⟩) {d : Defs ([],x)}
    (hd : a.erase = .val (.obj d)) (A : Label) :
    c.ty ≠ .mu (.typ A .top .bot) := by
  intro hty
  have hderiv : HasTy .nil (.val (.obj d)) c.ty := hd ▸ c.deriv
  rw [hty] at hderiv
  exact Paths.DotMNF.acceptance_gdot3_any ⟨hderiv⟩

end

/-! ## Inference and the typer

The theorems that relate a compilation to the elaborator and to the typer. -/

section
variable {b : Budget} {Λ : LabelTable} {e : STm}

/-- `compile` is `compileE` without the reason. -/
theorem compile_eq (b : Budget) (Λ : LabelTable) (e : STm) :
    compile b Λ e = (compileE b Λ e).toOption := rfl

/-- A partial term with no empty slot elaborates as the typer types the term it
stands for, candidates and tank. -/
theorem elabF_full {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} (hp : p.full? = some a) :
    elabF Γ p = fullSynthAt Γ p a (PTm.fills_of_full? hp) := by
  rw [elabF]
  split
  · rename_i a' h
    rw [hp, Option.some.injEq] at h
    subst h
    rfl
  · rename_i h
    rw [hp] at h
    cases h

/-- **Every slot written: the typer, at the same fuel.**  A program that
resolves with every slot written compiles as the typer's synthesis on its
resolution. -/
theorem compile_full {a : ATm []} (h : resolve Λ e = some a) :
    compile b Λ e = compileLanded b a := by
  rw [resolve_eq] at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp, Option.bind_some] at h
    simp only [compile, compileE, hp, compileLanded, synthTop?, synthTopF, synthInF, elabTopF,
      elabF_full h, fullSynthAt, Frontend.Fuel.Fu.bind, Frontend.Fuel.Fu.ret]
    cases hs : synthF Ctx.nil a ⟨b.fuel, false⟩ with
    | mk cs t =>
      cases cs with
      | nil => simp [firstCand, Except.toOption]
      | cons c cs =>
        cases ht : t.out <;> simp [firstCand, ht, Except.toOption]

/-- **Inference fills only empty slots.**  The fill of a compiled program
agrees with every slot its partial term writes. -/
theorem compileE_fills {a : ATm []} {c : Compiled a.erase} (h : compileE b Λ e = .ok ⟨a, c⟩) :
    ∃ p, resolveP Λ e = some p ∧ p.fills a = true := by
  unfold compileE at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    dsimp only at h
    refine ⟨p, rfl, ?_⟩
    cases he : (elabTopF b.fuel p).1 with
    | error r =>
      rw [he] at h
      cases h
    | ok c' =>
      rw [he] at h
      cases h
      exact c'.fills

/-- The reasons of the typer's synthesis on a filled term: a mismatch, or none. -/
theorem fullSynthAt_reasons {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} {h : p.fills a = true}
    (t : Frontend.Fuel.Tank) : ∀ r ∈ (fullSynthAt Γ p a h t).1.2, r = .mismatch := by
  intro r hr
  simp only [fullSynthAt, Frontend.Fuel.Fu.bind, Frontend.Fuel.Fu.ret] at hr
  split at hr
  · simp at hr
    exact hr
  · simp at hr

/-- The reason `elabTopF` reports when the typer's synthesis rejects: the
recursion limit or a mismatch. -/
theorem elabTopF_full_error {p : PTm []} {a : ATm []} (hp : p.full? = some a) {n : Nat}
    {r : EReason} (h : (elabTopF n p).1 = .error r) : r = .limit ∨ r = .mismatch := by
  unfold elabTopF at h
  have hrs := fullSynthAt_reasons (Γ := Ctx.nil) (h := PTm.fills_of_full? hp) ⟨n, false⟩
  rw [← elabF_full hp] at hrs
  revert hrs h
  cases elabF Ctx.nil p ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    intro h hrs
    cases cs with
    | cons c cs =>
      cases ht : t.out <;> simp [ht] at h
      exact Or.inl h.symm
    | nil =>
      simp only [Except.error.injEq] at h
      subst h
      unfold Frontend.Reason.Reason.top
      cases ht : t.out with
      | true => exact Or.inl rfl
      | false =>
        cases rs with
        | nil => exact Or.inr rfl
        | cons r rs => exact Or.inr (hrs r (List.mem_cons_self ..))

/-- **The slot reasons arise only where a slot is empty.**  A program rejected
for a missing parameter type, a cyclic reference, a definition that needs a
written type, or candidates with no least type resolves to a partial term with
an empty slot. -/
theorem compileE_slot {r : EReason} (h : compileE b Λ e = .error r) (hr : r.isSlotReason = true) :
    ∃ p, resolveP Λ e = some p ∧ p.full? = none := by
  unfold compileE at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
    cases hr
  | some p =>
    rw [hp] at h
    dsimp only at h
    refine ⟨p, rfl, ?_⟩
    cases hf : p.full? with
    | none => rfl
    | some a =>
      cases he : (elabTopF b.fuel p).1 with
      | ok c =>
        rw [he] at h
        cases h
      | error r' =>
        rw [he] at h
        cases h
        rcases elabTopF_full_error hf he with rfl | rfl <;> cases hr

end

/-! ## The tank of an elaboration

`elabF` is framed (`elabF_framed`, `Elab.lean`), so an elaboration that ends
unmarked does the same with more fuel. -/

/-- A closed elaboration that ends unmarked gives the same verdict at every
larger fuel.  So a rejection that ends unmarked is a rejection by the rules. -/
theorem elabTop?_stable {n k : Nat} {p : PTm []} {r : Except EReason (ECand Ctx.nil p)}
    (h : elabTopF n p = (r, ⟨k, false⟩)) (j : Nat) : (elabTopF (n + j) p).1 = r := by
  unfold elabTopF at h ⊢
  cases hs : elabF Ctx.nil p ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    have ht : t = ⟨k, false⟩ := by
      cases cs with
      | nil => exact (Prod.mk.inj h).2
      | cons c cs => exact (Prod.mk.inj h).2
    have hf := (elabF_framed Ctx.nil p).shift _ _ _ hs (by rw [ht]) j
    have hn : (⟨n + j, false⟩ : Frontend.Fuel.Tank) = (⟨n, false⟩ : Frontend.Fuel.Tank).add j :=
      rfl
    rw [hn, hf]
    subst ht
    cases cs with
    | nil => exact (Prod.mk.inj h).1
    | cons c cs => exact (Prod.mk.inj h).1

/-- An elaborated program that ends unmarked. -/
theorem elabTopF_ok_out {n : Nat} {p : PTm []} {c : ECand Ctx.nil p}
    (h : (elabTopF n p).1 = .ok c) : (elabTopF n p).2.out = false := by
  unfold elabTopF at h ⊢
  cases hs : elabF Ctx.nil p ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    cases cs with
    | nil => cases h
    | cons c' cs =>
      cases ht : t.out with
      | false => rfl
      | true =>
        simp only [ht, if_true] at h
        cases h

/-- **More fuel keeps the answer of a closed elaboration.** -/
theorem elabTop?_mono {n m : Nat} {p : PTm []} {c : ECand Ctx.nil p}
    (h : (elabTopF n p).1 = .ok c) (hnm : n ≤ m) : (elabTopF m p).1 = .ok c := by
  have ho := elabTopF_ok_out h
  have he : elabTopF n p = (.ok c, ⟨(elabTopF n p).2.left, false⟩) := by
    rw [← h, ← ho]
  have := elabTop?_stable he (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

/-! ## Completeness at the direct sites

The elaborator fills a lambda's domain from its goal and hands the filled term
to the typer.  At some sites this is the typer's own clause on the filled
program, after the lookups that read the goal.  At those sites inference loses
no program whose fill the typer accepts.

`Canon Γ p a` says that `a` is the canonical fill of `p`: every empty slot of
`p` is a lambda domain at such a site, filled with the domain the elaborator
reads there.  The sites are the body `g x` of a lambda with no goal, a lambda
whose body has no empty slot in the body of a `let` with a written type, a
call argument, and an ascription.  The path from the root to a slot runs
through written lambdas and `let`s.  A slot under a binder is filled alike in
every context a candidate of the bound term gives.

A call argument and an ascription are sites with premises.  At a call argument
the elaborator checks the filled argument against the dominant formal before
the typer types the filled `let`, and the typer needs only some formal.  At an
ascription the elaborator checks the ascribed term against the written type.
The typer synthesizes it and checks the variable of the body by the `var`
goal, which opens a `μ` and introduces `∧` at a variable.  So the typer's
check of the fill against the goal is a premise of both sites.  At an
ascription the typer's check of the variable at the written type is one too.
A field of a literal is no site: the typer checks the field with the self
bound by `Ctx.consSelf`, and the elaborator with the self at a `μ`.
`Examples.lean` shows a program at an ascription and one at a call argument
that the elaborator rejects though the typer accepts their fills.

`Lag R c c'` says that `c'` does what `c` does, with enough fuel.  From a tank
on which `c` ends unmarked, `c'` reaches a related answer.  `Reaches c x` says
that `c` ends unmarked at `x` from some full tank, and from every larger one
with as many more units left.  The elaborator may spend more fuel than the
typer, at a call argument, or less, at an ascription, where it checks a lambda
the typer synthesizes.  `canon_lag` proves the lag for the typer on the fill
against the elaborator on the partial term, with the same candidate types in
the same order.  `elab_complete_direct` reads it at the top: the elaborator
accepts a program whose canonical fill the typer accepts, from some fuel on,
at that fill and at the typer's type (`elab_complete_direct_fill`,
`compile_complete_direct`).  Some fuel, and not the typer's, since the
elaborator reads the goal on the same tank. -/

section Complete

open Frontend.Fuel PathsFrontend.Core

/-! ### Computations that reach an answer -/

/-- A computation that ends unmarked with `x` from a full tank of `n` units,
and from every larger full tank with as many more units left. -/
def Reaches {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, ∀ k, c ⟨n + k, false⟩ = (x, ⟨m + k, false⟩)

/-- `c'` does what `c` does, with enough fuel.  From a tank on which `c` ends
unmarked with `r`, `c'` reaches an answer related to `r`.  The fuel `c'` needs
is not tied to the fuel `c` spends: the elaborator may spend more or less than
the typer. -/
def Lag {α β : Type} (R : α → β → Prop) (c : Fu α) (c' : Fu β) : Prop :=
  ∀ t r t', c t = (r, t') → t'.out = false → ∃ r', R r r' ∧ Reaches c' r'

/-- A computation that ends unmarked with `x` from some full tank.  A framed
one then reaches `x`. -/
def SettlesTo {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, c ⟨n, false⟩ = (x, ⟨m, false⟩)

section LagLemmas

variable {α β γ δ : Type}

/-- Two tanks with the same fuel and the same mark are equal. -/
theorem tank_eq {t u : Tank} (hl : t.left = u.left) (ho : t.out = u.out) : t = u := by
  cases t
  cases u
  simp_all

/-- An answer returned at no cost is reached. -/
theorem reaches_ret (x : α) : Reaches (Fu.ret x) x :=
  ⟨0, 0, fun _ => rfl⟩

/-- Reaching composes along a `bind`. -/
theorem reaches_bind {c : Fu α} {f : α → Fu β} {x : α} {y : β} (hc : Reaches c x)
    (hf : Reaches (f x) y) : Reaches (Fu.bind c f) y := by
  obtain ⟨n1, m1, h1⟩ := hc
  obtain ⟨n2, m2, h2⟩ := hf
  refine ⟨n1 + n2, m2 + m1, fun k => ?_⟩
  have e1 : (⟨n1 + n2 + k, false⟩ : Tank) = ⟨n1 + (n2 + k), false⟩ := by rw [Nat.add_assoc]
  have e2 : (⟨m1 + (n2 + k), false⟩ : Tank) = ⟨n2 + (m1 + k), false⟩ := by
    rw [Tank.mk.injEq]
    exact ⟨by omega, rfl⟩
  have e3 : (⟨m2 + (m1 + k), false⟩ : Tank) = ⟨m2 + m1 + k, false⟩ := by rw [Nat.add_assoc]
  show (match c ⟨n1 + n2 + k, false⟩ with | (a, t1) => f a t1) = _
  rw [e1, h1]
  show f x ⟨m1 + (n2 + k), false⟩ = _
  rw [e2, h2, e3]

/-- A framed computation that ends unmarked reaches its answer. -/
theorem reaches_of_run {c : Fu α} (hc : Framed c) {t : Tank} {x : α} {t' : Tank}
    (h : c t = (x, t')) (ho : t'.out = false) : Reaches c x := by
  have hto : t.out = false := hc.start h ho
  refine ⟨t.left, t'.left, fun k => ?_⟩
  have hs := hc.shift t x t' h ho k
  have e1 : t.add k = ⟨t.left + k, false⟩ := tank_eq rfl (by simp [hto])
  have e2 : t'.add k = ⟨t'.left + k, false⟩ := tank_eq rfl (by simp [ho])
  rw [e1, e2] at hs
  exact hs

/-- A framed computation that settles reaches its answer. -/
theorem reaches_settles {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) : Reaches c x := by
  obtain ⟨n, m, h⟩ := hs
  exact reaches_of_run hc h rfl

/-- A first try that answers with `stop` set ends `stopOr` at once. -/
theorem reaches_stop {a : β} {c : Fu β} : Reaches (stopOr true a c) a :=
  ⟨0, 0, fun _ => rfl⟩

/-- Without `stop`, `stopOr` on an unmarked tank is its second computation. -/
theorem reaches_go {a : β} {c : Fu β} {y : β} (h : Reaches c y) : Reaches (stopOr false a c) y := by
  obtain ⟨n, m, h⟩ := h
  exact ⟨n, m, fun k => h k⟩

/-- Two answers returned at no cost lag by nothing. -/
theorem lag_ret {R : α → β → Prop} {x : α} {y : β} (h : R x y) : Lag R (Fu.ret x) (Fu.ret y) := by
  intro t r t' hr _
  simp only [Fu.ret, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨y, h, reaches_ret y⟩

/-- A framed computation lags behind itself. -/
theorem lag_self {c : Fu α} (hc : Framed c) : Lag (· = ·) c c := by
  intro t r t' h ho
  exact ⟨r, rfl, reaches_of_run hc h ho⟩

/-- A weaker relation. -/
theorem lag_mono {R R' : α → β → Prop} {c : Fu α} {c' : Fu β} (h : Lag R c c')
    (hR : ∀ x y, R x y → R' x y) : Lag R' c c' := by
  intro t r t' hr ho
  obtain ⟨r', hR', hk⟩ := h t r t' hr ho
  exact ⟨r', hR _ _ hR', hk⟩

/-- Lags compose along a `bind`.  The continuations need to lag only at answers
the first computation gives on a tank it leaves unmarked. -/
theorem lag_bind {R1 : α → β → Prop} {R2 : γ → δ → Prop} {c : Fu α} {c' : Fu β}
    {f : α → Fu γ} {f' : β → Fu δ} (hc : Lag R1 c c') (hf : ∀ x, Framed (f x))
    (hff : ∀ t x t1, c t = (x, t1) → t1.out = false → ∀ y, R1 x y → Lag R2 (f x) (f' y)) :
    Lag R2 (Fu.bind c f) (Fu.bind c' f') := by
  intro t r t' h ho
  simp only [Fu.bind] at h
  cases hct : c t with
  | mk x t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf x).start h ho
    obtain ⟨y, hR1, h1⟩ := hc t x t1 hct ht1
    obtain ⟨r', hR2, h2⟩ := hff t x t1 hct ht1 y hR1 t1 r t' h ho
    exact ⟨r', hR2, reaches_bind h1 h2⟩

/-- The answer of `c`, mapped. -/
theorem lag_map {R : α → β → Prop} {c : Fu α} {g : α → β} (hc : Framed c) (h : ∀ x, R x (g x)) :
    Lag R c (Fu.bind c fun x => Fu.ret (g x)) := by
  intro t r t' hr ho
  exact ⟨g r, h r, reaches_bind (reaches_of_run hc hr ho) (reaches_ret _)⟩

/-- The answer of `c'`, mapped. -/
theorem lag_map_right {R R' : α → β → Prop} {c : Fu α} {c' : Fu β} {g : β → β}
    (h : Lag R c c') (hg : ∀ x y, R x y → R' x (g y)) :
    Lag R' c (Fu.bind c' fun y => Fu.ret (g y)) := by
  intro t r t' hr ho
  obtain ⟨r', hR, hk⟩ := h t r t' hr ho
  exact ⟨g r', hg _ _ hR, reaches_bind hk (reaches_ret _)⟩

/-- A computation that reaches an answer, run first, keeps the lag. -/
theorem lag_prefix {R : α → γ → Prop} {k : Fu α} {c : Fu β} {f : β → Fu γ} {x : β}
    (hs : Reaches c x) (hf : Lag R k (f x)) : Lag R k (Fu.bind c f) := by
  intro t r t' h ho
  obtain ⟨r', hR, hd⟩ := hf t r t' h ho
  exact ⟨r', hR, reaches_bind hs hd⟩

/-- A framed computation that settles at `x` answers `x` on every tank on which
it ends unmarked. -/
theorem settles_unique {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) {t : Tank} {r : α}
    {t' : Tank} (h : c t = (r, t')) (ho : t'.out = false) : r = x := by
  obtain ⟨n, m, hn⟩ := hs
  have hto : t.out = false := hc.start h ho
  by_cases hle : t.left ≤ n
  · have ht : (⟨n, false⟩ : Tank) = t.add (n - t.left) := tank_eq (by simp; omega) (by simp [hto])
    have := hc.shift t r t' h ho (n - t.left)
    rw [← ht, hn] at this
    exact (Prod.mk.inj this).1.symm
  · have ht : t = (⟨n, false⟩ : Tank).add (t.left - n) := tank_eq (by simp; omega) (by simp [hto])
    have := hc.shift ⟨n, false⟩ x ⟨m, false⟩ hn rfl (t.left - n)
    rw [← ht, h] at this
    exact (Prod.mk.inj this).1

/-- A computation that lags behind one that settles reaches a related answer. -/
theorem settles_lag {R : α → β → Prop} {c : Fu α} {c' : Fu β} {x : α} (h : Lag R c c')
    (hs : SettlesTo c x) : ∃ y, R x y ∧ Reaches c' y := by
  obtain ⟨n, m, hn⟩ := hs
  exact h ⟨n, false⟩ x ⟨m, false⟩ hn rfl

/-- The answer of a computation, read from a full tank on which it ends
unmarked, is where it settles. -/
theorem settlesTo_of {c : Fu α} {x : α} {n : Nat} (h1 : (c ⟨n, false⟩).1 = x)
    (h2 : (c ⟨n, false⟩).2.out = false) : SettlesTo c x :=
  ⟨n, (c ⟨n, false⟩).2.left, Prod.ext h1 (tank_eq rfl h2)⟩

/-- The function part of a written function type, at no cost. -/
theorem funPartAt_all {s : Sig} {Γ : Ctx s} {S : Ty s} {V : Ty (s,x)} :
    SettlesTo (funPartAt Γ (.all S V)) (.one S V) :=
  ⟨0, 0, rfl⟩

/-- A `bind` whose first computation is a `bind`, reassociated. -/
theorem bind_bind {c : Fu α} {f : α → Fu β} {g : β → Fu γ} :
    Fu.bind (Fu.bind c f) g = Fu.bind c (fun x => Fu.bind (f x) g) := by
  funext t
  simp only [Fu.bind]

/-- A first try that answers with a nonempty list stops `orElseW`, when the
computation it lags behind settles at a nonempty list. -/
theorem lag_stop {ρ : Type} {R : List γ → List δ × List ρ → Prop} {k : Fu (List γ)}
    {X : Fu (List δ × List ρ)} {Z : List δ × List ρ → Fu (List δ × List ρ)} {cs : List γ}
    (hk : Framed k) (hX : Lag R k X) (hs : SettlesTo k cs) (hne : cs ≠ [])
    (hR : ∀ x y, R x y → x ≠ [] → y.1 ≠ []) :
    Lag R k (Fu.bind X fun r => stopOr (!r.1.isEmpty) r (Z r)) := by
  intro t r t' h ho
  have hr := settles_unique hk hs h ho
  subst hr
  obtain ⟨r', hR', hd⟩ := hX t r t' h ho
  have hne' := hR _ _ hR' hne
  refine ⟨r', hR', reaches_bind hd ?_⟩
  cases hr1 : r'.1 with
  | nil => exact absurd hr1 hne'
  | cons _ _ =>
    simp only [List.isEmpty_cons, Bool.not_false]
    exact reaches_stop

end LagLemmas

/-! ### Lists of answers -/

section LagLists

variable {α β γ δ ρ ε ζ : Type}

/-- The typer's first success over a list against the elaborator's, on two
lists that agree pointwise. -/
theorem lag_firstSome {f : α → Fu (Option γ)} {f' : β → Fu (Option δ × List ρ)}
    {g0 : α → ε} {g : β → ε} {h : γ → ζ} {h' : δ → ζ} :
    ∀ (l : List α) (l' : List β), l'.map g = l.map g0 →
      (∀ x ∈ l, ∀ y, g y = g0 x → Lag (fun o r => r.1.map h' = o.map h) (f x) (f' y)) →
      Lag (fun o r => r.1.map h' = o.map h) (Fu.firstSome f l) (firstSomeR f' l')
  | [], [], _, _ => by
    simp only [Fu.firstSome, firstSomeR]
    exact lag_ret rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, hf => by
    simp only [List.map_cons, List.cons.injEq] at hl
    have ih := lag_firstSome xs ys hl.2 fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    have hx := hf x (List.mem_cons_self ..) y hl.1
    intro t r t' hr ho
    simp only [Fu.firstSome, Fu.orElse] at hr
    cases hat : f x t with
    | mk o1 t1 =>
      rw [hat] at hr
      cases o1 with
      | some v =>
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨r1, hR, hd⟩ := hx t (some v) t1 hat ho
        have hs : r1.1.isSome = true := by
          cases hr1 : r1.1 with
          | none => rw [hr1] at hR; simp at hR
          | some _ => rfl
        refine ⟨r1, hR, ?_⟩
        simp only [firstSomeR, orElseW]
        refine reaches_bind hd ?_
        simp only [hs]
        exact reaches_stop
      | none =>
        cases ht1 : t1.out with
        | true =>
          simp only [ht1, if_true, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [ht1] at ho
        | false =>
          simp only [ht1, Bool.false_eq_true, if_false] at hr
          obtain ⟨r1, hR1, hd1⟩ := hx t none t1 hat ht1
          obtain ⟨r2, hR2, hd2⟩ := ih t1 r t' hr ho
          have hn : r1.1 = none := by
            cases hr1 : r1.1 with
            | none => rfl
            | some _ => rw [hr1] at hR1; simp at hR1
          refine ⟨(r2.1, r1.2 ++ r2.2), hR2, ?_⟩
          simp only [firstSomeR, orElseW]
          refine reaches_bind hd1 ?_
          simp only [hn, Option.isSome_none]
          exact reaches_go (reaches_bind hd2 (reaches_ret _))

/-- The typer's answers over a list against the elaborator's, on two lists that
agree pointwise. -/
theorem lag_flatMap {f : α → Fu (List γ)} {f' : β → Fu (List δ × List ρ)}
    {g0 : α → ε} {g : β → ε} {h : γ → ζ} {h' : δ → ζ} (hfr : ∀ x, Framed (f x)) :
    ∀ (l : List α) (l' : List β), l'.map g = l.map g0 →
      (∀ x ∈ l, ∀ y, g y = g0 x → Lag (fun ys r => r.1.map h' = ys.map h) (f x) (f' y)) →
      Lag (fun ys r => r.1.map h' = ys.map h) (Fu.flatMapL f l) (flatMapR f' l')
  | [], [], _, _ => by
    simp only [Fu.flatMapL, flatMapR]
    exact lag_ret rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, hf => by
    simp only [List.map_cons, List.cons.injEq] at hl
    have ih := lag_flatMap hfr xs ys hl.2 fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    simp only [Fu.flatMapL, flatMapR]
    refine lag_bind (hf x (List.mem_cons_self ..) y hl.1)
      (fun _ => bind_framed (flatMapL_framed hfr xs) fun _ => ret_framed _) ?_
    intro _ ys1 _ _ _ r1 h1
    refine lag_bind ih (fun _ => ret_framed _) ?_
    intro _ zs _ _ _ r2 h2
    exact lag_ret (by simp [List.map_append, h1, h2])

/-- A framed computation lags behind `c` when on every tank it leaves the tank
`c` leaves, with a related answer. -/
theorem lag_of_eq {R : α → β → Prop} {c : Fu α} {c' : Fu β} (hc' : Framed c')
    (h : ∀ t, (c' t).2 = (c t).2 ∧ R (c t).1 (c' t).1) : Lag R c c' := by
  intro t r t' hr ho
  obtain ⟨h1, h2⟩ := h t
  rw [hr] at h1 h2
  have h1' : (c' t).2 = t' := h1
  exact ⟨(c' t).1, h2, reaches_of_run hc' (x := (c' t).1) (t' := t') (Prod.ext rfl h1') ho⟩

end LagLists

/-! ### The canonical fill -/

/-- `T` is the type of a candidate of `a` in a run of the typer that ends
unmarked. -/
def CandTy {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Prop :=
  ∃ t cs t', synthF Γ a t = (cs, t') ∧ t'.out = false ∧ T ∈ cs.map (·.ty)

/-- `a` fills the partial term `p`, checked at `G` in `Γ`, with the domain the
elaborator reads, at a site where the elaborator is the typer's check of `a`.
Every slot written, a lambda without a domain whose body has none at a goal
with a function part, or the body `g x` at a goal without one. -/
inductive CanonChk : {s : Sig} → Ctx s → PTm s → Ty s → ATm s → Prop where
  /-- Every slot written. -/
  | full {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Ty s} {a : ATm s} :
      p.full? = some a → CanonChk Γ p G a
  /-- The domain of the goal's function part. -/
  | lam {s : Sig} {Γ : Ctx s} {b : PTm (s,x)} {G : Ty s} {b' : ATm (s,x)} {S : Ty s}
      {V : Ty (s,x)} :
      b.full? = some b' → SettlesTo (funPartAt Γ G) (.one S V) →
      CanonChk Γ (.lam none b) G (.lam S b')
  /-- The dominant formal of the callee, at a goal with no function part. -/
  | callee {s : Sig} {Γ : Ctx s} {g : BVar s .var} {G : Ty s} {S : Ty s} :
      SettlesTo (funPartAt Γ G) .none → SettlesTo (argGoalF Γ g) (some S) →
      CanonChk Γ (.lam none (.app (.there g) .here)) G (.lam S (.app (.there g) .here))

/-- `a` fills the partial term `p`, synthesized in `Γ`, with the domains the
elaborator reads, and every empty slot is at a direct site: the body `g x` of
a lambda with no goal, a lambda in the body of a `let` with a written type, a
call argument, or an ascribed term.  The path to a slot runs through written
lambdas and through `let`s.  A slot under a `let` binder is filled alike in
every context a candidate of the bound term gives. -/
inductive Canon : {s : Sig} → Ctx s → PTm s → ATm s → Prop where
  /-- Every slot written. -/
  | full {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} : p.full? = some a → Canon Γ p a
  /-- A lambda with a written domain. -/
  | lam {s : Sig} {Γ : Ctx s} {S : Ty s} {t : PTm (s,x)} {a : ATm (s,x)} :
      t.full? = none → Canon (Γ.cons S) t a → Canon Γ (.lam (some S) t) (.lam S a)
  /-- The body `g x` with no goal: the dominant formal of `g`. -/
  | callee {s : Sig} {Γ : Ctx s} {g : BVar s .var} {S : Ty s} :
      SettlesTo (argGoalF Γ g) (some S) →
      Canon Γ (.lam none (.app (.there g) .here)) (.lam S (.app (.there g) .here))
  /-- A `let` without a type that is no call argument. -/
  | letNone {s : Sig} {Γ : Ctx s} {g : LetTag} {t : PTm s} {u : PTm (s,x)} {a1 : ATm s}
      {a2 : ATm (s,x)} :
      (PTm.let g none t u).full? = none → argCallee? g none u = none → Canon Γ t a1 →
      (∀ T0, CandTy Γ a1 T0 → Canon (Γ.cons T0) u a2) →
      Canon Γ (.let g none t u) (.let none a1 a2)
  /-- A call argument `let z = t in f z`: `t` checked at the dominant formal
  `F` of `f`.  The typer checks the fill of `t` at `F` and accepts the filled
  `let`. -/
  | arg {s : Sig} {Γ : Ctx s} {f : BVar s .var} {t : PTm s} {F : Ty s} {a1 : ATm s} :
      t.full? = none → SettlesTo (argGoalF Γ f) (some F) → CanonChk Γ t F a1 →
      (∃ n, (checkF Γ a1 F ⟨n, false⟩).1.isSome = true ∧
        (checkF Γ a1 F ⟨n, false⟩).2.out = false) →
      (∃ n, (synthF Γ (.let none a1 (.app (.there f) .here)) ⟨n, false⟩).1.isEmpty = false ∧
        (synthF Γ (.let none a1 (.app (.there f) .here)) ⟨n, false⟩).2.out = false) →
      Canon Γ (.let .arg none t (.app (.there f) .here)) (.let none a1 (.app (.there f) .here))
  /-- A `let` with a written type that is no ascription: its body is checked
  against the type. -/
  | letAnn {s : Sig} {Γ : Ctx s} {g : LetTag} {U : Ty s} {t : PTm s} {u : PTm (s,x)}
      {a1 : ATm s} {a2 : ATm (s,x)} :
      (PTm.let g (some U) t u).full? = none → u ≠ .path .here → Canon Γ t a1 →
      (∀ T0, CandTy Γ a1 T0 → CanonChk (Γ.cons T0) u U.weaken a2) →
      Canon Γ (.let g (some U) t u) (.let (some U) a1 a2)
  /-- An ascription `let y : U = t in y`: `t` checked at `U`.  The typer checks
  the fill of `t` at `U`, checks the variable at `U` in the context that binds
  it at `U`, and types the filled ascription at `U`. -/
  | asc {s : Sig} {Γ : Ctx s} {g : LetTag} {U : Ty s} {t : PTm s} {a1 : ATm s} :
      t.full? = none → CanonChk Γ t U a1 →
      (∃ n, (checkF Γ a1 U ⟨n, false⟩).1.isSome = true ∧
        (checkF Γ a1 U ⟨n, false⟩).2.out = false) →
      (∃ n, (checkF (Γ.cons U) (.path .here) U.weaken ⟨n, false⟩).1.isSome = true ∧
        (checkF (Γ.cons U) (.path .here) U.weaken ⟨n, false⟩).2.out = false) →
      (∃ n, (synthF Γ (.let (some U) a1 (.path .here)) ⟨n, false⟩).1.map (·.ty) = [U] ∧
        (synthF Γ (.let (some U) a1 (.path .here)) ⟨n, false⟩).2.out = false) →
      Canon Γ (.let g (some U) t (.path .here)) (.let (some U) a1 (.path .here))

/-! ### The elaborator unfolded at the direct sites -/

/-- A partial term with no empty slot is checked as the typer checks the term it
stands for, candidates and tank. -/
theorem elabChkF_full {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} (G : Ty s)
    (hp : p.full? = some a) : elabChkF Γ p G = fullCheckAt Γ p a (PTm.fills_of_full? hp) G := by
  rw [elabChkF]
  split
  · rename_i a' h
    rw [hp, Option.some.injEq] at h
    subst h
    rfl
  · rename_i h
    rw [hp] at h
    cases h

/-- The synthesis of a lambda with a written domain and an empty slot in its
body, unfolded. -/
theorem elabF_lam_some {s : Sig} (Γ : Ctx s) (S : Ty s) {t : PTm (s,x)} (ht : t.full? = none) :
    elabF Γ (.lam (some S) t) = lamSynF Γ S (optAgree_some S) (elabF (Γ.cons S) t) := by
  rw [elabF]
  split
  · rename_i a h
    simp [PTm.full?, ht] at h
  · rfl

/-- The synthesis of a `let` with an empty slot, unfolded. -/
theorem elabF_let {s : Sig} (Γ : Ctx s) (g : LetTag) (ann : Option (Ty s)) (t : PTm s)
    (u : PTm (s,x)) (hp : (PTm.let g ann t u).full? = none) :
    elabF Γ (.let g ann t u) = letF Γ g ann t u (elabF Γ t) (fun G => elabChkF Γ t G)
      (fun T0 => elabF (Γ.cons T0) u) (fun T0 G => elabChkF (Γ.cons T0) u G) := by
  rw [elabF]
  split
  · rename_i a h
    rw [hp] at h
    cases h
  · rfl

/-- A `let` that is no call argument goes to the clause of any `let`. -/
theorem letF_gen {s : Sig} {Γ : Ctx s} {g : LetTag} {ann : Option (Ty s)} {t : PTm s}
    {u : PTm (s,x)} {synT : Fu (ESynth Γ t)} {chkT : (G : Ty s) → Fu (ECheck Γ t G)}
    {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) u)}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) u G)}
    (h : argCallee? g ann u = none) :
    letF Γ g ann t u synT chkT synU chkU =
      letSynF Γ g ann t u (boundF Γ ann t u synT chkT) synU chkU := by
  unfold letF
  split
  · rename_i f b hf _
    rw [h] at hf
    cases hf
  · rfl

/-- A call argument goes to the clause of a call argument. -/
theorem letF_arg {s : Sig} {Γ : Ctx s} {t : PTm s} {f : BVar s .var} {synT : Fu (ESynth Γ t)}
    {chkT : (G : Ty s) → Fu (ECheck Γ t G)}
    {synU : (T0 : Ty s) → Fu (ESynth (Γ.cons T0) (.app (.there f) .here))}
    {chkU : (T0 : Ty s) → (G : Ty (s,x)) → Fu (ECheck (Γ.cons T0) (.app (.there f) .here) G)} :
    letF Γ .arg none t (.app (.there f) .here) synT chkT synU chkU =
      argSynF Γ .arg none t (.app (.there f) .here) f (.app (.there f) .here) (PTm.fills_app _ _) chkT
        fun _ => letSynF Γ .arg none t (.app (.there f) .here)
          (boundF Γ none t (.app (.there f) .here) synT chkT) synU chkU := rfl

/-- A bound term that is no ascription is synthesized. -/
theorem boundF_syn {s : Sig} {Γ : Ctx s} {ann : Option (Ty s)} {t : PTm s} {u : PTm (s,x)}
    {chk : (G : Ty s) → Fu (ECheck Γ t G)} (hu : ann = none ∨ u ≠ .path .here) :
    boundF Γ ann t u (elabF Γ t) chk = elabF Γ t := by
  unfold boundF
  split
  · rename_i a ht
    exact (elabF_full ht).symm
  · split
    · simp at hu
    · rfl

/-- An ascribed term with an empty slot is checked against the written type. -/
theorem boundF_asc {s : Sig} {Γ : Ctx s} {U : Ty s} {t : PTm s} {syn : Fu (ESynth Γ t)}
    {chk : (G : Ty s) → Fu (ECheck Γ t G)} (ht : t.full? = none) :
    boundF Γ (some U) t (.path .here) syn chk =
      Fu.bind (chk U) fun r => Fu.ret (listO (r.1.map fun e => ⟨e.a, U, e.deriv, e.fills⟩), r.2) := by
  unfold boundF
  split
  · rename_i a h
    rw [ht] at h
    cases h
  · rfl

/-- A lambda whose body has no empty slot, at a goal with a function part, is
the typer's check of the lambda filled with the part's domain. -/
theorem lamOneChkF_full {s : Sig} {Γ : Ctx s} {b : PTm (s,x)} {b' : ATm (s,x)} {S : Ty s}
    {V : Ty (s,x)} {G : Ty s} {chk : Fu (ECheck (Γ.cons S) b V)}
    {syn : Unit → Fu (ESynth (Γ.cons S) b)} (hb : b.full? = some b') :
    lamOneChkF Γ b S V G chk syn =
      fullCheckAt Γ (.lam none b) (.lam S b') (PTm.fills_lam rfl (PTm.fills_of_full? hb)) G := by
  unfold lamOneChkF
  split
  · rename_i b'' hb''
    rw [hb, Option.some.injEq] at hb''
    subst hb''
    rfl
  · rename_i hb''
    rw [hb] at hb''
    cases hb''

/-- A `let` with a written type is no call argument. -/
theorem argCallee?_ann {s : Sig} {g : LetTag} {U : Ty s} {u : PTm (s,x)} :
    argCallee? g (some U) u = none := by
  cases g <;> rfl

/-- The typer has no candidate for a `let` whose written type is not well
formed. -/
theorem synthF_let_wf {s : Sig} {Γ : Ctx s} {U : Ty s} {a1 : ATm s} {a2 : ATm (s,x)} {tk : Tank}
    (h : (synthF Γ (.let (some U) a1 a2) tk).1 ≠ []) : Ty.Wf U := by
  by_cases hw : Ty.Wf U
  · exact hw
  · exfalso
    apply h
    rw [synthF]
    simp only [Fu.bind, letAnnC, dif_neg hw]
    cases synthF Γ a1 tk
    rfl

/-- The type of a candidate `letAvoidC` forms depends on the types of the two
candidates it is given, not on their derivations, and so does the tank. -/
theorem letAvoidC_ty {s : Sig} {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} (c1 : Cand Γ t)
    (d1 : HasTy Γ t c1.ty) (c2 : Cand (Γ.cons c1.ty) u) (d2 : HasTy (Γ.cons c1.ty) u c2.ty)
    (tk : Tank) :
    (letAvoidC (⟨c1.ty, d1⟩ : Cand Γ t) (⟨c2.ty, d2⟩ : Cand (Γ.cons c1.ty) u) tk).2 =
        (letAvoidC c1 c2 tk).2 ∧
      (letAvoidC (⟨c1.ty, d1⟩ : Cand Γ t) (⟨c2.ty, d2⟩ : Cand (Γ.cons c1.ty) u) tk).1.map (·.ty) =
        (letAvoidC c1 c2 tk).1.map (·.ty) := by
  unfold letAvoidC
  simp only [Fu.bind]
  cases avoidLet Γ c1.ty c2.ty tk with
  | mk o t1 =>
    cases o with
    | none => simp [Fu.ret]
    | some r =>
      by_cases hw : Ty.Wf r.1 <;> simp [Fu.ret, hw]

/-! ### Agreement of the candidates -/

/-- The elaborator's candidates are the typer's on the fill: the same types in
the same order, each at the term `a`. -/
def SynAgree {s : Sig} {Γ : Ctx s} {p : PTm s} (a : ATm s) (cs : List (Cand Γ a.erase))
    (r : ESynth Γ p) : Prop :=
  r.1.map (fun c => (c.a, c.ty)) = cs.map (fun c => (a, c.ty))

/-- The elaborator's check answers when the typer's check of the fill does, at
the term `a`. -/
def ChkAgree {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Ty s} (a : ATm s)
    (o : Option (HasTy Γ a.erase G)) (r : ECheck Γ p G) : Prop :=
  r.1.map (·.a) = o.map (fun _ => a)

/-- The typer's synthesis of a filled term, as candidates of the partial term,
lags behind the typer. -/
theorem fullSynthAt_lag {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} (h : p.fills a = true) :
    Lag (SynAgree a) (synthF Γ a) (fullSynthAt Γ p a h) :=
  lag_map (synthF_framed Γ a) fun cs => by simp [SynAgree, List.map_map, Function.comp_def]

/-- The same for the typer's check. -/
theorem fullCheckAt_lag {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} (h : p.fills a = true)
    (G : Ty s) : Lag (ChkAgree a) (checkF Γ a G) (fullCheckAt Γ p a h G) :=
  lag_map (checkF_framed Γ a G) fun o => by cases o <;> simp [ChkAgree]

/-- Keeping the first candidate of each type keeps the agreement. -/
theorem dedup_agree {s : Sig} {Γ : Ctx s} {p : PTm s} {t : Tm s} {A : ATm s} :
    ∀ (es : List (ECand Γ p)) (cs : List (Cand Γ t)),
      es.map (fun c => (c.a, c.ty)) = cs.map (fun c => (A, c.ty)) →
      (dedupE es).map (fun c => (c.a, c.ty)) = (dedupTy cs).map (fun c => (A, c.ty))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: es, c :: cs, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := dedup_agree es cs h3
    simp only [dedupE, dedupTy, List.map_cons, h1, h2, List.cons.injEq, true_and]
    have l1 := (List.filter_map (f := fun c : ECand Γ p => (c.a, c.ty))
      (p := fun q => !decide (q.2 = c.ty)) (l := dedupE es))
    have l2 := (List.filter_map (f := fun c : Cand Γ t => (A, c.ty))
      (p := fun q => !decide (q.2 = c.ty)) (l := dedupTy cs))
    simp only [Function.comp_def] at l1 l2
    rw [← l1, ← l2, ih]

/-- The check of a direct site: the elaborator is the typer's check of the fill,
after the readings of the goal. -/
theorem canonChk_lag {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Ty s} {a : ATm s}
    (h : CanonChk Γ p G a) : Lag (ChkAgree a) (checkF Γ a G) (elabChkF Γ p G) := by
  cases h with
  | full hp =>
    rw [elabChkF_full G hp]
    exact fullCheckAt_lag _ G
  | lam hb hs =>
    rw [elabChkF_lam_none]
    refine lag_prefix (reaches_settles (funPartAt_framed _ _) hs) ?_
    dsimp only
    rw [lamOneChkF_full hb]
    exact fullCheckAt_lag _ G
  | callee hf hg =>
    rw [elabChkF_lam_none]
    refine lag_prefix (reaches_settles (funPartAt_framed _ _) hf) ?_
    dsimp only
    simp only [lamCalleeChkF, calleeOf?_app]
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hg) ?_
    dsimp only
    exact fullCheckAt_lag _ G

/-- **The elaborator at the direct sites is the typer on the fill.**  When the
typer's synthesis of the canonical fill ends unmarked, the elaborator gives the
same candidate types in the same order, each at the fill, with enough fuel. -/
theorem canon_lag {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s} (h : Canon Γ p a) :
    Lag (SynAgree a) (synthF Γ a) (elabF Γ p) := by
  induction h with
  | full hp =>
    rw [elabF_full hp]
    exact fullSynthAt_lag _
  | @lam s Γ S t a ht _ ih =>
    rw [elabF_lam_some _ _ ht, synthF]
    unfold lamSynF lamC
    by_cases hwf : Ty.Wf S
    · simp only [dif_pos hwf]
      refine lag_bind ih (fun _ => ret_framed _) ?_
      intro _ cs _ hrun _ r hr
      refine lag_ret ?_
      have := congrArg (List.map fun q : ATm (s,x) × Ty (s,x) => (ATm.lam S q.1, Ty.all S q.2)) hr
      simp only [SynAgree, lamCands, List.map_map, Function.comp_def] at this ⊢
      refine this.trans ?_
      clear this hr hrun
      induction cs with
      | nil => rfl
      | cons c cs ih => exact congrArg ((ATm.lam S a, Ty.all S c.ty) :: ·) ih
    · simp only [dif_neg hwf]
      exact lag_ret rfl
  | callee hs =>
    rw [elabF_lam_none]
    simp only [lamCalleeSynF, calleeOf?_app]
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hs) ?_
    dsimp only
    exact fullSynthAt_lag _
  | @letNone s Γ g t u a1 a2 hp hc _ _ ih1 ih2 =>
    rw [elabF_let _ _ _ _ _ hp, letF_gen hc]
    simp only [letSynF]
    rw [boundF_syn (Or.inl rfl), synthF]
    refine lag_bind ih1 (fun _ => letNoneC_framed _ fun _ => synthF_framed _ _) ?_
    intro t0 c1s t1 hrun ht1 r1 hr1
    unfold letNoneR letNoneC
    refine lag_bind (lag_flatMap (h := fun c => (ATm.let none a1 a2, c.ty))
      (h' := fun c => (c.a, c.ty)) (fun c1 => bind_framed (synthF_framed _ _)
        (flatMapL_framed (letAvoidC_framed c1)))
      c1s r1.1 hr1 ?_) (fun _ => ret_framed _) ?_
    · intro c1 hc1 c1' heq
      obtain ⟨a', T', d', f'⟩ := c1'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hct : CandTy Γ a' c1.ty := ⟨t0, c1s, t1, hrun, ht1, List.mem_map_of_mem hc1⟩
      refine lag_bind (ih2 c1.ty hct) (fun _ => flatMapL_framed (letAvoidC_framed c1) _) ?_
      intro _ c2s _ _ _ r2 hr2
      refine lag_map_right (lag_flatMap (h := fun c => (ATm.let none a' a2, c.ty))
        (h' := fun c => (c.a, c.ty)) (letAvoidC_framed c1) c2s r2.1 hr2 ?_) (fun _ _ h => h)
      intro c2 _ c2' heq2
      obtain ⟨a'', T'', d'', f''⟩ := c2'
      simp only [Prod.mk.injEq] at heq2
      obtain ⟨rfl, rfl⟩ := heq2
      refine lag_of_eq (bind_framed (letAvoidC_framed _ _) fun _ => ret_framed _) fun tk => ?_
      obtain ⟨e1, e2⟩ := letAvoidC_ty c1 d' c2 d'' tk
      simp only [Fu.bind, Fu.ret]
      refine ⟨e1, ?_⟩
      simp only [List.map_map, Function.comp_def]
      have := congrArg (List.map fun T => (ATm.let none a' a'', T)) e2
      simpa [List.map_map, Function.comp_def] using this
    · intro _ cs _ _ _ r hr
      exact lag_ret (dedup_agree _ _ hr)
  | @arg s Γ f t F a1 ht hF hc hchk' hacc' =>
    have hp : (PTm.let .arg none t (.app (.there f) .here)).full? = none := by
      simp [PTm.full?, ht]
    obtain ⟨nc, hc1, hc2⟩ := hchk'
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hc1
    have hchk := settlesTo_of (c := checkF Γ a1 F) hd hc2
    obtain ⟨na, ha1, ha2⟩ := hacc'
    have hacc := settlesTo_of (c := synthF Γ (.let none a1 (.app (.there f) .here))) rfl ha2
    have hne : (synthF Γ (.let none a1 (.app (.there f) .here)) ⟨na, false⟩).1 ≠ [] := by
      intro h
      rw [h] at ha1
      cases ha1
    rw [elabF_let _ _ _ _ _ hp, letF_arg]
    unfold argSynF
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hF) ?_
    dsimp only
    obtain ⟨r', hr', hs'⟩ := settles_lag (canonChk_lag hc) hchk
    unfold orElseW
    rw [bind_bind]
    refine lag_prefix hs' ?_
    obtain ⟨o, rs⟩ := r'
    simp only [ChkAgree] at hr'
    cases o with
    | none => simp at hr'
    | some e' =>
      obtain ⟨ea, ed, ef⟩ := e'
      simp only [Option.map_some, Option.some.injEq] at hr'
      subst hr'
      dsimp only
      refine lag_stop (synthF_framed _ _) (fullSynthAt_lag _) hacc hne ?_
      intro x y hxy hx
      simp only [SynAgree] at hxy
      intro hy
      rw [hy] at hxy
      cases x with
      | nil => exact hx rfl
      | cons _ _ => simp at hxy
  | @letAnn s Γ g U t u a1 a2 hp hu _ hchk ih1 =>
    rw [elabF_let _ _ _ _ _ hp, letF_gen argCallee?_ann]
    simp only [letSynF]
    rw [boundF_syn (Or.inr hu), synthF]
    unfold letAnnR letAnnC
    by_cases hwf : Ty.Wf U
    · simp only [dif_pos hwf]
      refine lag_bind ih1 (fun _ => bind_framed (firstSome_framed (fun _ =>
        mapO_framed _ (checkF_framed _ _ _)) _) fun _ => ret_framed _) ?_
      intro t0 c1s t1 hrun ht1 r1 hr1
      refine lag_bind (lag_firstSome (h := fun c => (ATm.let (some U) a1 a2, c.ty))
        (h' := fun c => (c.a, c.ty)) c1s r1.1 hr1 ?_) (fun _ => ret_framed _) ?_
      · intro c1 hc1 c1' heq
        obtain ⟨a', T', d', f'⟩ := c1'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hct : CandTy Γ a' c1.ty := ⟨t0, c1s, t1, hrun, ht1, List.mem_map_of_mem hc1⟩
        unfold mapO
        refine lag_bind (canonChk_lag (hchk c1.ty hct)) (fun _ => ret_framed _) ?_
        intro _ o _ _ _ r hr
        refine lag_ret ?_
        simp only [ChkAgree] at hr
        cases o <;> cases hr' : r.1 <;> simp_all
      · intro _ o _ _ _ r hr
        refine lag_ret ?_
        simp only [SynAgree]
        cases o <;> cases hr' : r.1 <;> simp_all [listO] <;> rfl
    · simp only [dif_neg hwf]
      refine lag_bind ih1 (fun _ => ret_framed _) ?_
      intro _ _ _ _ _ _ _
      exact lag_ret rfl
  | @asc s Γ g U t a1 ht hc hchk' hvar' hacc' =>
    have hp : (PTm.let g (some U) t (.path .here)).full? = none := by simp [PTm.full?, ht]
    obtain ⟨na, ha1, ha2⟩ := hacc'
    have hacc := settlesTo_of (c := synthF Γ (.let (some U) a1 (.path .here))) rfl ha2
    have hwf : Ty.Wf U := synthF_let_wf (tk := ⟨na, false⟩) (by intro h; rw [h] at ha1; cases ha1)
    obtain ⟨nc, hc1, hc2⟩ := hchk'
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hc1
    obtain ⟨r0, hr0, hs0⟩ := settles_lag (canonChk_lag hc) (settlesTo_of (c := checkF Γ a1 U) hd hc2)
    obtain ⟨nv, hv1, hv2⟩ := hvar'
    obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp hv1
    have hvar := reaches_settles (checkF_framed _ _ _)
      (settlesTo_of (c := checkF (Γ.cons U) (.path .here) U.weaken) hdv hv2)
    obtain ⟨o0, rs0⟩ := r0
    simp only [ChkAgree] at hr0
    cases o0 with
    | none => simp at hr0
    | some e0 =>
      obtain ⟨ea, ed, ef⟩ := e0
      simp only [Option.map_some, Option.some.injEq] at hr0
      subst hr0
      rw [elabF_let _ _ _ _ _ hp, letF_gen argCallee?_ann]
      simp only [letSynF]
      rw [boundF_asc ht]
      intro t0 r t' hrun ho
      have hr := settles_unique (synthF_framed _ _) hacc hrun ho
      subst hr
      unfold letAnnR
      simp only [dif_pos hwf]
      apply Exists.intro
      constructor
      rotate_left
      · apply reaches_bind
        · apply reaches_bind hs0
          exact reaches_ret _
        simp only [Option.map_some, listO, firstSomeR, orElseW]
        apply reaches_bind
        · apply reaches_bind
          · apply reaches_bind
            · rw [elabChkF_full _ (p := .path .here) rfl]
              apply reaches_bind hvar
              exact reaches_ret _
            · exact reaches_ret _
          · exact reaches_stop
        · exact reaches_ret _
      · simp only [SynAgree, Option.map_some]
        have e : ∀ l : List (Cand Γ (ATm.let (some U) ea (.path .here)).erase),
            l.map (fun c => (ATm.let (some U) ea (.path .here), c.ty)) =
              (l.map (·.ty)).map (fun T => (ATm.let (some U) ea (.path .here), T)) := by
          intro l
          induction l with
          | nil => rfl
          | cons c l ih => exact congrArg ((ATm.let (some U) ea (.path .here), c.ty) :: ·) ih
        rw [e, ha1]
        rfl

/-- **Completeness at the direct sites, with the fill.**  A program whose
canonical fill the typer accepts elaborates, from some fuel on, to that fill,
at the type the typer gives it first. -/
theorem elab_complete_direct_fill {p : PTm []} {a : ATm []} {n : Nat} (hc : Canon Ctx.nil p a)
    (hl : (synthTopF n a).1.isSome = true) :
    ∃ n0, ∀ m, n0 ≤ m → ∃ c, (elabTopF m p).1 = .ok c ∧ c.a = a ∧
      (synthTopF n a).1.map (·.ty) = some c.ty := by
  unfold synthTopF synthInF at hl ⊢
  cases hs : synthF Ctx.nil a ⟨n, false⟩ with
  | mk cs t' =>
    rw [hs] at hl
    cases cs with
    | nil => simp [firstCand] at hl
    | cons c0 cs =>
      cases ho : t'.out with
      | true => simp [firstCand, ho] at hl
      | false =>
        obtain ⟨r', hR, n1, m1, hk⟩ := canon_lag hc ⟨n, false⟩ (c0 :: cs) t' hs ho
        refine ⟨n1, fun m hm => ?_⟩
        have hrun := hk (m - n1)
        have htk : (⟨n1 + (m - n1), false⟩ : Tank) = ⟨m, false⟩ := by
          rw [Tank.mk.injEq]
          exact ⟨by omega, rfl⟩
        rw [htk] at hrun
        obtain ⟨es, rs⟩ := r'
        simp only [SynAgree, List.map_cons] at hR
        cases es with
        | nil => simp at hR
        | cons c es =>
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hR
          refine ⟨c, ?_, hR.1.1, ?_⟩
          · unfold elabTopF
            rw [hrun]
            simp
          · simp [firstCand, ho, hR.1.2]

/-- **Completeness at the direct sites.**  A program whose canonical fill the
typer accepts is accepted by the elaborator from some fuel on. -/
theorem elab_complete_direct {p : PTm []} {a : ATm []} {n : Nat} (hc : Canon Ctx.nil p a)
    (hl : (synthTopF n a).1.isSome = true) :
    ∃ n0, ∀ m, n0 ≤ m → (elabTopF m p).1.isOk = true := by
  obtain ⟨n0, h⟩ := elab_complete_direct_fill hc hl
  refine ⟨n0, fun m hm => ?_⟩
  obtain ⟨c, hc', _, _⟩ := h m hm
  rw [hc']
  rfl

/-- **Completeness at the direct sites, through the pipeline.**  A program
that resolves to a partial term whose canonical fill the typer accepts
compiles to that fill at every budget from some fuel on. -/
theorem compile_complete_direct {Λ : LabelTable} {e : STm} {p : PTm []} {a : ATm []} {n : Nat}
    (hp : resolveP Λ e = some p) (hc : Canon Ctx.nil p a) (hl : (synthTopF n a).1.isSome = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → (compile b Λ e).map (·.1) = some a := by
  obtain ⟨n0, h⟩ := elab_complete_direct_fill hc hl
  refine ⟨n0, fun b hb => ?_⟩
  obtain ⟨c, hc', ha, _⟩ := h b.fuel hb
  simp only [compile, compileE, hp, hc', Except.toOption, Option.map_some, ha]

/-- A candidate type of a term in a run that ends unmarked is one of the types
any run that ends unmarked gives. -/
theorem candTy_of {s : Sig} {Γ : Ctx s} {a : ATm s} {n : Nat} {Ts : List (Ty s)}
    (h : ((synthF Γ a ⟨n, false⟩).1.map (·.ty), (synthF Γ a ⟨n, false⟩).2.out) = (Ts, false))
    {T : Ty s} (hT : CandTy Γ a T) : T ∈ Ts := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨t, cs, t', hrun, ho, hmem⟩ := hT
  have hs : SettlesTo (synthF Γ a) (synthF Γ a ⟨n, false⟩).1 := settlesTo_of rfl h.2
  rw [settles_unique (synthF_framed Γ a) hs hrun ho, h.1] at hmem
  exact hmem


/-! ### Deciding the canonical fill -/

/-- The answer of a computation from a full tank of `n` units, when the tank
ends unmarked. -/
def settledAt {α : Type} (c : Fu α) (n : Nat) : Option α :=
  if (c ⟨n, false⟩).2.out then none else some (c ⟨n, false⟩).1

/-- An answer read by `settledAt` is where the computation settles. -/
theorem settlesTo_of_settledAt {α : Type} {c : Fu α} {x : α} {n : Nat}
    (h : settledAt c n = some x) : SettlesTo c x := by
  unfold settledAt at h
  split at h
  · cases h
  · rename_i ho
    simp only [Option.some.injEq] at h
    exact settlesTo_of h (by simpa using ho)

/-- Whether `a` fills `p` checked at `G`, at a direct site, with the readings
of the goal taken from a full tank of `n` units. -/
def canonChkB {s : Sig} (n : Nat) (Γ : Ctx s) (p : PTm s) (G : Ty s) (a : ATm s) : Bool :=
  if p.full? = some a then true
  else
    match p, a with
    | .lam none b, .lam S b' =>
        match settledAt (funPartAt Γ G) n with
        | some (.one S0 _) => decide (S0 = S) && decide (b.full? = some b')
        | some .none =>
            match calleeOf? b with
            | some g => decide (b = .app (.there g) .here) && decide (b' = .app (.there g) .here) &&
                decide (settledAt (argGoalF Γ g) n = some (some S))
            | none => false
        | _ => false
    | _, _ => false

/-- The typer's check of `a` at `G` succeeds from a full tank of `n` units and
ends unmarked. -/
def checksAt {s : Sig} (n : Nat) (Γ : Ctx s) (a : ATm s) (G : Ty s) : Bool :=
  (checkF Γ a G ⟨n, false⟩).1.isSome && !(checkF Γ a G ⟨n, false⟩).2.out

/-- Whether `a` is the canonical fill of `p` synthesized in `Γ`, with the
readings of the goal and the candidates of the bound terms taken from a full
tank of `n` units. -/
def canonB {s : Sig} (n : Nat) (Γ : Ctx s) (p : PTm s) (a : ATm s) : Bool :=
  if p.full? = some a then true
  else
    match p, a with
    | .lam (some S) t, .lam S' a' =>
        decide (S = S') && decide (t.full? = none) && canonB n (Γ.cons S) t a'
    | .lam none b, .lam S b' =>
        match calleeOf? b with
        | some g => decide (b = .app (.there g) .here) && decide (b' = .app (.there g) .here) &&
            decide (settledAt (argGoalF Γ g) n = some (some S))
        | none => false
    | .let tag none t u, .let none a1 a2 =>
        match argCallee? tag none u with
        | none =>
            decide ((PTm.let tag none t u).full? = none) && canonB n Γ t a1 &&
              match settledAt (synthF Γ a1) n with
              | some cs => (cs.map (·.ty)).all fun T0 => canonB n (Γ.cons T0) u a2
              | none => false
        | some f =>
            decide (tag = .arg) && decide (u = .app (.there f) .here) &&
              decide (a2 = .app (.there f) .here) && decide (t.full? = none) &&
              match settledAt (argGoalF Γ f) n with
              | some (some F) =>
                  canonChkB n Γ t F a1 && checksAt n Γ a1 F &&
                    !(synthF Γ (.let none a1 (.app (.there f) .here)) ⟨n, false⟩).1.isEmpty &&
                    !(synthF Γ (.let none a1 (.app (.there f) .here)) ⟨n, false⟩).2.out
              | _ => false
    | .let tag (some U) t u, .let (some U') a1 a2 =>
        decide (U = U') && decide ((PTm.let tag (some U) t u).full? = none) &&
          if u = .path .here then
            decide (a2 = .path .here) && decide (t.full? = none) && canonChkB n Γ t U a1 &&
              checksAt n Γ a1 U && checksAt n (Γ.cons U) (.path .here) U.weaken &&
              decide ((settledAt (synthF Γ (.let (some U) a1 (.path .here))) n).map
                (·.map (·.ty)) = some [U])
          else
            canonB n Γ t a1 &&
              match settledAt (synthF Γ a1) n with
              | some cs => (cs.map (·.ty)).all fun T0 => canonChkB n (Γ.cons T0) u U.weaken a2
              | none => false
    | _, _ => false
termination_by structural p

/-- A check the typer passes from a full tank of `n` units. -/
theorem checksAt_sound {s : Sig} {n : Nat} {Γ : Ctx s} {a : ATm s} {G : Ty s}
    (h : checksAt n Γ a G = true) :
    (checkF Γ a G ⟨n, false⟩).1.isSome = true ∧ (checkF Γ a G ⟨n, false⟩).2.out = false := by
  simp only [checksAt, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

/-- `canonChkB` decides `CanonChk` soundly. -/
theorem canonChkB_sound {s : Sig} {n : Nat} {Γ : Ctx s} {p : PTm s} {G : Ty s} {a : ATm s}
    (h : canonChkB n Γ p G a = true) : CanonChk Γ p G a := by
  unfold canonChkB at h
  split at h
  · rename_i hf
    exact .full hf
  · split at h
    · rename_i b S b'
      split at h
      · rename_i S0 V hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, hb⟩ := h
        exact .lam hb (settlesTo_of_settledAt hs)
      · rename_i hs
        split at h
        · rename_i g hg
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨rfl, rfl⟩, ha⟩ := h
          exact .callee (settlesTo_of_settledAt hs) (settlesTo_of_settledAt ha)
        · cases h
      · cases h
    · cases h

/-- The candidate types `settledAt` reads off the typer are every candidate
type of a run that ends unmarked. -/
theorem candTy_settled {s : Sig} {n : Nat} {Γ : Ctx s} {a : ATm s} {cs : List (Cand Γ a.erase)}
    (h : settledAt (synthF Γ a) n = some cs) {T : Ty s} (hT : CandTy Γ a T) : T ∈ cs.map (·.ty) := by
  unfold settledAt at h
  split at h
  · cases h
  · rename_i ho
    simp only [Option.some.injEq] at h
    subst h
    exact candTy_of (n := n) (Prod.ext rfl (by simpa using ho)) hT

/-- `canonB` decides `Canon` soundly. -/
theorem canonB_sound {n : Nat} : {s : Sig} → {Γ : Ctx s} → (p : PTm s) → (a : ATm s) →
    canonB n Γ p a = true → Canon Γ p a
  | _, Γ, .lam (some S) t, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | lam S' a' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, ht⟩, h3⟩ := h
        exact .lam ht (canonB_sound t a' h3)
      | _ => simp at h
  | _, Γ, .lam none b, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | lam S b' =>
        simp only at h
        split at h
        · rename_i g hg
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨rfl, rfl⟩, ha⟩ := h
          exact .callee (settlesTo_of_settledAt ha)
        · cases h
      | _ => simp at h
  | _, Γ, .let tag none t u, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | «let» ann a1 a2 =>
        cases ann with
        | some _ => simp at h
        | none =>
          simp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hp, h1⟩, h2⟩ := h
            split at h2
            · rename_i cs hcs
              refine .letNone hp hc (canonB_sound t a1 h1) fun T0 hT => ?_
              have hm := candTy_settled hcs hT
              rw [List.all_eq_true] at h2
              exact canonB_sound u a2 (h2 T0 hm)
            · cases h2
          · rename_i f hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ht⟩, h5⟩ := h
            split at h5
            · rename_i F hF
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at h5
              obtain ⟨⟨⟨hc1, hc2⟩, hne⟩, hout⟩ := h5
              exact .arg ht (settlesTo_of_settledAt hF) (canonChkB_sound hc1) ⟨n, checksAt_sound hc2⟩
                ⟨n, hne, hout⟩
            · cases h5
      | _ => simp at h
  | _, Γ, .let tag (some U) t u, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | «let» ann a1 a2 =>
        cases ann with
        | none => simp at h
        | some U' =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨rfl, hp⟩, h⟩ := h
          split at h
          · rename_i hu
            subst hu
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨rfl, ht⟩, hc1⟩, hc2⟩, hc3⟩, hs⟩ := h
            refine .asc ht (canonChkB_sound hc1) ⟨n, checksAt_sound hc2⟩ ⟨n, checksAt_sound hc3⟩
              ⟨n, ?_⟩
            unfold settledAt at hs
            split at hs
            · cases hs
            · rename_i ho
              simp only [Option.map_some, Option.some.injEq] at hs
              exact ⟨hs, by simpa using ho⟩
          · rename_i hu
            simp only [Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            split at h2
            · rename_i cs hcs
              refine .letAnn hp hu (canonB_sound t a1 h1) fun T0 hT => ?_
              have hm := candTy_settled hcs hT
              rw [List.all_eq_true] at h2
              exact canonChkB_sound (h2 T0 hm)
            · cases h2
      | _ => simp at h
  | _, Γ, .path x, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .obj o d, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .app x y, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .proj x l, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
termination_by structural _ _ p => p

/-- Whether the erased program `e` resolves to a partial term whose canonical
fill is the resolution of the written program `w`, and the typer accepts that
fill, all read from a full tank of `n` units. -/
def canonAt (Λ : LabelTable) (e w : STm) (n : Nat := defaultFuel) : Bool :=
  match resolveP Λ e, resolve Λ w with
  | some p, some a => canonB n Ctx.nil p a && (synthTopF n a).1.isSome
  | _, _ => false

/-- **Completeness at the direct sites, decided.**  An erased program that
`canonAt` relates to a written one compiles to the written program's
resolution at every budget from some fuel on. -/
theorem compile_complete_canonAt {Λ : LabelTable} {e w : STm} {n : Nat}
    (h : canonAt Λ e w n = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → (compile b Λ e).map (·.1) = resolve Λ w := by
  unfold canonAt at h
  split at h
  · rename_i p a hp ha
    simp only [Bool.and_eq_true] at h
    rw [ha]
    exact compile_complete_direct hp (canonB_sound p a h.1) h.2
  · cases h

end Complete

/-- **The checker's verdict, read off a successful compile.**  `compile_checks`
from `(compile b Λ e).isSome = true`. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    Paths.FCdot.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

end PathsFrontend
