import Coercions.Nominal.Frontend.Pretty
import Coercions.Nominal.Translation.Pages

/-!
# The examples end to end

Programs of the paths front end that it rejects, written in `pdc%` and compiled
here, and the runs of E5, E7 and E8 through both machines.  The hand programs E1
to E8 and E13, with their slots written and erased, are compiled in
`Pipeline.lean`.

## The paths programs

Each program below is rejected by the paths front end, whose calculus `Paths`
lacks the pDOT rule the program needs.  Here each one compiles.  For each,
`X_tank` gives the units the elaboration uses from `defaultFuel` with the tank
unmarked, `X_shows` prints the fill and its type, `X_compiles` is decided, and
`X_checks` is `compile_checks_get` at the program.

* R2, a singleton used at the declared type of its path.  Paths rejects it after
  4 units (`Paths/Frontend/Examples.lean:773-777`).  pDOT types the argument by
  `ty_sngl`.
* PQ, `p.A` used at `q.A` for `p : q.type`.  Paths rejects it after 12 units
  (`Paths/Frontend/Examples.lean:1191-1195`).  pDOT replaces `p` by `q` by
  `subtyp_sngl_pq`.
* R7, the path `x.a.b` as the operand of an application.  Paths binds the prefix
  by a `let` and loses the path, and rejects it after 46 units
  (`Paths/Frontend/Examples.lean:795-799`).  Here a path stays a path, and
  `x.a.b : x.a.B` by `ty_rec_elim` at `x.a`.
* E7w, E7 with its alias field written at the singleton, `m : c.types.type =
  c.types`.  The paths front end rejects it with a type mismatch (facts §2.16).
  Here the written type is checked by `FieldsOk` and dropped, `ty_def_path`
  gives the field that declaration, and the fill is E7's hand term.
* E9l, E9 as a program: `let r : x.b.type = x.a.b in r` under
  `x : μ(z. {a : z.type} ∧ {b : ⊤})`.  The paths front end rejects it with a type
  mismatch (facts §2.16).  pDOT types `x.a.b : x.b.type` by `ty_path_elim`.

E10 and E11 of `PDot/Source/Examples.lean` are path typings under a context.
Written as programs, the context entries become lambdas and each typing an
annotated `let` or an ascription, and both compile.

## The runs

E5, E7 and E8 are compiled from `Ek_srcI` of `Pipeline.lean`, whose self types
and lambda domains are erased where a goal or the definitions give them.  Their
fills erase to the hand terms (`Ek_fill`), so `compileAndRun` runs the hand term,
and the source run is the run of `PDot/Translation/Pages.lean` step for step:
4, 2 and 9 steps (`Ek_run`).  One step fewer ends at another erasure
(`Ek_run_counts`).

`compileAndRunFC` runs the translation of the derivation the search found.  It
places its casts where the hand derivation does not, so the machine takes other
counts than the pages' 7, 3 and 16: 9, 7 and 24.  Each ends at a final state
with the erasure of the source run (`Ek_fc_end`), and one step fewer ends at a
state that is not final (`Ek_fc_counts`).  `Ek_same` states that the two runs
end at one erasure.  `Ek_shows` prints the erased end of both runs as one text.

## The running example of plan XII

`Run_src` is the running example of plan XII in `pdc%`: a stem `σ` with the trait `T`, the
class `C` that extends it, their method forwarders and the constructor `new$C`, whose body is
the tagged literal `ν(i) as σ.C {…}`, and the body `let y = σ.new$C σ.u.ℓself in (y : σ.T)`.
It compiles at the body of `T` (`Run_type`), since `σ.T` mentions the let-bound `σ` and
widens to its upper bound (D-21). The fill erases to `Run_prog` (`Run_fill`), which differs
from E14 in the body of `new$C`, where the desugaring of the tag adds two `let`s
(`Run_E14`). The source machine ends in 7 steps and the FCn machine in 19, at one erasure
(`Run_same`, `Run_fc_end`). NOM-B holds at the program's class labels `T` and `C`
(`Run_nominal`). A structural literal at `σ.C` outside or inside the stem is rejected, and so
is the literal tagged outside the stem, where `σ` has no class reading. A tag at a type
member that is no class is refused by resolution (`NotCls_unresolved`). Tags at a class of a
nested object compile (`NestTag_src`, `SelfTag_src`), and an instance that lacks a field of
the class body is rejected (`BadTag_reason`).
-/

namespace NominalFrontend.Examples

open NominalFrontend NominalFrontend.Core NominalFrontend.Sources NominalFrontend.ElabChecks
open Paths.FCdot (Sig Label Path)
open Nominal.Source (Ty)

/-! ## R2: a singleton used at the declared type of its path -/

/-- The labels of R2 and PQ. -/
def ΛPQ : LabelTable := [("A", .typ 0)]

/-- R2 as `Paths/Frontend/Notation.lean:581-583` writes it, in `pdc%`. -/
def R2_src : STm := pdc%
  λ(f : ∀(z : ⊤) ⊤). λ(p : {A : f.type..∀(z : ⊤) ⊤}). λ(x : f.type). λ(h : ∀(k : ∀(z : ⊤) ⊤) ⊤). h x

theorem R2_tank : (resolveP ΛPQ R2_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 5, false⟩ := by
  decide +kernel

theorem R2_shows : ppCompileE ΛPQ (compileE {} ΛPQ R2_src) =
    "ok: λ(x : ∀(x : ⊤) ⊤). λ(y : {A : x.type..∀(y : ⊤) ⊤}). λ(z : x.type). λ(w : ∀(w : ∀(w : ⊤) ⊤) ⊤). w z "
      ++ ": ∀(x : ∀(x : ⊤) ⊤) ∀(y : {A : x.type..∀(y : ⊤) ⊤}) ∀(z : x.type) ∀(w : ∀(w : ∀(w : ⊤) ⊤) ⊤) ⊤" := by
  decide +kernel

theorem R2_compiles : (compile {} ΛPQ R2_src).isSome = true := by decide +kernel

theorem R2_checks : Nominal.FCn.checkTm .nil ((compile {} ΛPQ R2_src).get R2_compiles).2.deriv.translate
    ((compile {} ΛPQ R2_src).get R2_compiles).2.ty.translate = true :=
  compile_checks_get R2_compiles

/-! ## PQ: two prefixes of one singleton -/

/-- PQ as `Paths/Frontend/Typer.lean:741-742` writes it, in `pdc%`. -/
def PQ_src : STm := pdc% λ(q : {A : ⊥..⊤}). λ(p : q.type). λ(x : p.A). let y : q.A = x in y

theorem PQ_tank : (resolveP ΛPQ PQ_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 25, false⟩ := by
  decide +kernel

theorem PQ_shows : ppCompileE ΛPQ (compileE {} ΛPQ PQ_src) =
    "ok: λ(x : {A : ⊥..⊤}). λ(y : x.type). λ(z : y.A). let w : x.A = z in w "
      ++ ": ∀(x : {A : ⊥..⊤}) ∀(y : x.type) ∀(z : y.A) x.A" := by
  decide +kernel

theorem PQ_compiles : (compile {} ΛPQ PQ_src).isSome = true := by decide +kernel

theorem PQ_checks : Nominal.FCn.checkTm .nil ((compile {} ΛPQ PQ_src).get PQ_compiles).2.deriv.translate
    ((compile {} ΛPQ PQ_src).get PQ_compiles).2.ty.translate = true :=
  compile_checks_get PQ_compiles

/-! ## R7: a path as the operand of an application -/

/-- The labels of R7. -/
def ΛR7 : LabelTable := [("B", .typ 0), ("a", .trm 0), ("b", .trm 1)]

/-- R7 as `Paths/Frontend/Notation.lean:586-587` writes it, with `{a : …}` for
the stable field `{val a : …}`, which pDOT does not distinguish. -/
def R7_src : STm := pdc% λ(x : {a : μ(z. {B : ⊥..⊤} ∧ {b : z.B})}). λ(h : ∀(k : x.a.B) ⊤). h x.a.b

theorem R7_tank : (resolveP ΛR7 R7_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 13, false⟩ := by
  decide +kernel

/-- The operand stays the path `x.a.b`.  No `let` is inserted (`resolve_noInsert`). -/
theorem R7_shows : ppCompileE ΛR7 (compileE {} ΛR7 R7_src) =
    "ok: λ(x : {a : μ(x. {B : ⊥..⊤} ∧ {b : x.B})}). λ(y : ∀(y : x.a.B) ⊤). y x.a.b "
      ++ ": ∀(x : {a : μ(x. {B : ⊥..⊤} ∧ {b : x.B})}) ∀(y : ∀(y : x.a.B) ⊤) ⊤" := by
  decide +kernel

theorem R7_compiles : (compile {} ΛR7 R7_src).isSome = true := by decide +kernel

theorem R7_checks : Nominal.FCn.checkTm .nil ((compile {} ΛR7 R7_src).get R7_compiles).2.deriv.translate
    ((compile {} ΛR7 R7_src).get R7_compiles).2.ty.translate = true :=
  compile_checks_get R7_compiles

/-! ## E7w: E7 with its alias field written at the singleton -/

/-- E7 with no self type and the field `m` written at `c.types.type`. -/
def E7w_src : STm := pdc%
  let core = ν(c) {types = ν(t) {type A = ⊤, f = λ(u : ⊤). u}, m : c.types.type = c.types} in
  core.m.f core

theorem E7w_tank : (resolveP Λ7 E7w_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 42, false⟩ := by
  decide +kernel

/-- The fill is the hand term E7. -/
theorem E7w_fill : (compile {} Λ7 E7w_src).map (fun r => r.1.erase) = some Nominal.Source.E7_prog := by
  decide +kernel

theorem E7w_shows : ppCompileE Λ7 (compileE {} Λ7 E7w_src) =
    "ok: let x = ν(x : {types : μ(y. {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤})} ∧ {m : x.types.type}) "
      ++ "{types = ν(y : {A : ⊤..⊤} ∧ {f : ∀(z : ⊤) ⊤}) {type A = ⊤, f = λ(z : ⊤). z}, m = x.types} "
      ++ "in x.m.f x : ⊤" := by
  decide +kernel

theorem E7w_compiles : (compile {} Λ7 E7w_src).isSome = true := by decide +kernel

theorem E7w_checks : Nominal.FCn.checkTm .nil ((compile {} Λ7 E7w_src).get E7w_compiles).2.deriv.translate
    ((compile {} Λ7 E7w_src).get E7w_compiles).2.ty.translate = true :=
  compile_checks_get E7w_compiles

/-! ## E9l: E9's singleton at a `let` -/

/-- E9's context entry as a lambda, and the path `x.a.b` at `x.b.type` as a `let`. -/
def E9l_src : STm := pdc% λ(x : μ(z. {a : z.type} ∧ {b : ⊤})). let r : x.b.type = x.a.b in r

theorem E9l_tank : (resolveP Λ9 E9l_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 26, false⟩ := by
  decide +kernel

/-- The type is `∀(x : T) x.b.type`, with `T` the type of `e9_G` and the labels of E9. -/
theorem E9l_type : (compile {} Λ9 E9l_src).map (fun r => r.2.ty) =
    some (.all (.mu (.and (.rcd (.trm Nominal.Source.e9_a (.sngl (.var .here)))) (.rcd (.trm Nominal.Source.e9_b .top))))
      (.sngl ((Path.var .here).sel Nominal.Source.e9_b))) := by
  decide +kernel

theorem E9l_shows : ppCompileE Λ9 (compileE {} Λ9 E9l_src) =
    "ok: λ(x : μ(x. {a : x.type} ∧ {b : ⊤})). let y : x.b.type = x.a.b in y "
      ++ ": ∀(x : μ(x. {a : x.type} ∧ {b : ⊤})) x.b.type" := by
  decide +kernel

theorem E9l_compiles : (compile {} Λ9 E9l_src).isSome = true := by decide +kernel

theorem E9l_checks : Nominal.FCn.checkTm .nil ((compile {} Λ9 E9l_src).get E9l_compiles).2.deriv.translate
    ((compile {} Λ9 E9l_src).get E9l_compiles).2.ty.translate = true :=
  compile_checks_get E9l_compiles

/-! ## E10 and E11 as programs -/

/-- E10's context as lambdas, and the three types of `r` after the first as `let`s. -/
def E10_src : STm := pdc% λ(q : ⊤). λ(p : q.type). λ(r : {a : p.type} ∧ {b : p.type}).
  let r1 : {a : p.type} ∧ {b : q.type} = r in
  let r2 : {a : q.type} ∧ {b : q.type} = r in
  let r3 : {a : q.type} ∧ {b : p.type} = r in r3

theorem E10_tank : (resolveP Λ10 E10_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 125, false⟩ := by
  decide +kernel

theorem E10_compiles : (compile {} Λ10 E10_src).isSome = true := by decide +kernel

theorem E10_checks : Nominal.FCn.checkTm .nil ((compile {} Λ10 E10_src).get E10_compiles).2.deriv.translate
    ((compile {} Λ10 E10_src).get E10_compiles).2.ty.translate = true :=
  compile_checks_get E10_compiles

/-- E11's context as lambdas at `T = ⊤`, and `p : {a : ⊤}` as an ascription. -/
def E11_src : STm := pdc% λ(q : ⊤). λ(p : μ(z. {a : q.type})). (p : {a : ⊤})

theorem E11_tank : (resolveP Λ11 E11_src).map (fun p => (elabTopF .dot [] defaultFuel p).2) =
    some ⟨defaultFuel - 11, false⟩ := by
  decide +kernel

theorem E11_shows : ppCompileE Λ11 (compileE {} Λ11 E11_src) =
    "ok: λ(x : ⊤). λ(y : μ(y. {a : x.type})). (y : {a : ⊤}) : ∀(x : ⊤) ∀(y : μ(y. {a : x.type})) {a : ⊤}" := by
  decide +kernel

theorem E11_compiles : (compile {} Λ11 E11_src).isSome = true := by decide +kernel

theorem E11_checks : Nominal.FCn.checkTm .nil ((compile {} Λ11 E11_src).get E11_compiles).2.deriv.translate
    ((compile {} Λ11 E11_src).get E11_compiles).2.ty.translate = true :=
  compile_checks_get E11_compiles

/-! ## The runs -/

section Runs

variable {b : Budget} {Λ : LabelTable} {e : STm}

/-- A program whose fill erases to `t` runs as `t` does on the source machine. -/
theorem compileAndRun_of_fill {t : Nominal.Source.Tm []}
    (h : (compile b Λ e).map (fun r => r.1.erase) = some t) (n m : Nat) :
    compileAndRun b n m Λ e = some (Nominal.Source.runFuel n m ⟨[], .nil, t⟩) := by
  unfold compileAndRun
  cases hc : compile b Λ e with
  | none =>
    rw [hc] at h
    cases h
  | some r =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h ⊢
    rw [h]

/-- A run of the FCn machine that a decided check shows final, with a decided erasure. -/
theorem compileAndRunFC_end {m : Nat} {T : PDot.Runtime.Conf}
    (hf : (compileAndRunFC b m Λ e).any (fun r => Nominal.Translation.finalB r.2) = true)
    (he : (compileAndRunFC b m Λ e).map (fun r => r.2.erase) = some T) :
    ∃ r, compileAndRunFC b m Λ e = some r ∧ r.2.Final ∧ r.2.erase = T := by
  cases hr : compileAndRunFC b m Λ e with
  | none =>
    rw [hr] at he
    cases he
  | some r =>
    rw [hr] at hf he
    simp only [Option.any_some, Option.map_some, Option.some.injEq] at hf he
    exact ⟨r, rfl, Nominal.Translation.final_of_finalB hf, he⟩

end Runs

/-! ### E5 -/

/-- The source run is the page's run, four steps. -/
theorem E5_run : compileAndRun {} 4 4 Λ5 E5_srcI = some Nominal.Pages.E5.fin :=
  compileAndRun_of_fill E5_fill 4 4

/-- Three steps end at another erasure. -/
theorem E5_run_counts :
    (compileAndRun {} 4 3 Λ5 E5_srcI).map Nominal.Source.Conf.erase ≠ some Nominal.Source.e5Final := by
  rw [compileAndRun_of_fill E5_fill 4 3]
  simpa using Nominal.Pages.E5.counts.1

/-- The machine ends in nine steps at a final state with the source run's erasure. -/
theorem E5_fc : (compileAndRunFC {} 9 Λ5 E5_srcI).map (fun r => r.2.erase) = some Nominal.Source.e5Final := by
  decide +kernel

theorem E5_fc_final : (compileAndRunFC {} 9 Λ5 E5_srcI).any (fun r => Nominal.Translation.finalB r.2) = true := by
  decide +kernel

/-- Eight machine steps end at a state that is not final. -/
theorem E5_fc_counts :
    (compileAndRunFC {} 8 Λ5 E5_srcI).any (fun r => Nominal.Translation.finalB r.2) = false := by
  decide +kernel

theorem E5_fc_end :
    ∃ r, compileAndRunFC {} 9 Λ5 E5_srcI = some r ∧ r.2.Final ∧ r.2.erase = Nominal.Source.e5Final :=
  compileAndRunFC_end E5_fc_final E5_fc

/-- Both machines end at one erasure. -/
theorem E5_same : (compileAndRun {} 4 4 Λ5 E5_srcI).map Nominal.Source.Conf.erase =
    (compileAndRunFC {} 9 Λ5 E5_srcI).map (fun r => r.2.erase) := by
  rw [E5_run, E5_fc]; simp [Nominal.Pages.E5.src_erase]

/-- Both ends, erased, as text. -/
theorem E5_shows :
    ppRunErased Λ5 (compileAndRun {} 4 4 Λ5 E5_srcI) =
      "⟨x0 = ν(x) {d = λy. let z = ν(z) {incr = z, decr = z} in z}, x1 = ν(x) {incr = x, decr = x} | x1.incr.decr⟩" ∧
    ppRunFC Λ5 (compileAndRunFC {} 9 Λ5 E5_srcI) =
      "⟨x0 = ν(x) {d = λy. let z = ν(z) {incr = z, decr = z} in z}, x1 = ν(x) {incr = x, decr = x} | x1.incr.decr⟩" := by
  decide +kernel

/-! ### E7 -/

/-- The source run is the page's run, two steps. -/
theorem E7_run : compileAndRun {} 4 2 Λ7 E7_srcI = some Nominal.Pages.E7.fin :=
  compileAndRun_of_fill E7_fill 4 2

/-- One step ends at another erasure. -/
theorem E7_run_counts :
    (compileAndRun {} 4 1 Λ7 E7_srcI).map Nominal.Source.Conf.erase ≠ some Nominal.Pages.E7.e7Final := by
  rw [compileAndRun_of_fill E7_fill 4 1]
  simpa using Nominal.Pages.E7.counts.1

/-- The machine ends in seven steps at a final state with the source run's erasure. -/
theorem E7_fc : (compileAndRunFC {} 7 Λ7 E7_srcI).map (fun r => r.2.erase) = some Nominal.Pages.E7.e7Final := by
  decide +kernel

theorem E7_fc_final : (compileAndRunFC {} 7 Λ7 E7_srcI).any (fun r => Nominal.Translation.finalB r.2) = true := by
  decide +kernel

/-- Six machine steps end at a state that is not final. -/
theorem E7_fc_counts :
    (compileAndRunFC {} 6 Λ7 E7_srcI).any (fun r => Nominal.Translation.finalB r.2) = false := by
  decide +kernel

theorem E7_fc_end :
    ∃ r, compileAndRunFC {} 7 Λ7 E7_srcI = some r ∧ r.2.Final ∧ r.2.erase = Nominal.Pages.E7.e7Final :=
  compileAndRunFC_end E7_fc_final E7_fc

/-- Both machines end at one erasure. -/
theorem E7_same : (compileAndRun {} 4 2 Λ7 E7_srcI).map Nominal.Source.Conf.erase =
    (compileAndRunFC {} 7 Λ7 E7_srcI).map (fun r => r.2.erase) := by
  rw [E7_run, E7_fc]; simp [Nominal.Pages.E7.src_erase]

theorem E7_shows :
    ppRunErased Λ7 (compileAndRun {} 4 2 Λ7 E7_srcI) = "⟨x0 = ν(x) {types = ν{f = λy. y}, m = x.types} | x0⟩" ∧
    ppRunFC Λ7 (compileAndRunFC {} 7 Λ7 E7_srcI) = "⟨x0 = ν(x) {types = ν{f = λy. y}, m = x.types} | x0⟩" := by
  decide +kernel

/-! ### E8 -/

/-- The source run is the page's run, nine steps. -/
theorem E8_run : compileAndRun {} 4 9 Λ8 E8_srcI = some Nominal.Pages.E8.fin :=
  compileAndRun_of_fill E8_fill 4 9

/-- Eight steps end at another erasure. -/
theorem E8_run_counts :
    (compileAndRun {} 4 8 Λ8 E8_srcI).map Nominal.Source.Conf.erase ≠ some Nominal.Pages.E8.e8Final := by
  rw [compileAndRun_of_fill E8_fill 4 8]
  simpa using Nominal.Pages.E8.counts.1

/-- The machine ends in twenty-four steps at a final state with the source run's erasure. -/
theorem E8_fc : (compileAndRunFC {} 24 Λ8 E8_srcI).map (fun r => r.2.erase) = some Nominal.Pages.E8.e8Final := by
  decide +kernel

theorem E8_fc_final : (compileAndRunFC {} 24 Λ8 E8_srcI).any (fun r => Nominal.Translation.finalB r.2) = true := by
  decide +kernel

/-- Twenty-three machine steps end at a state that is not final. -/
theorem E8_fc_counts :
    (compileAndRunFC {} 23 Λ8 E8_srcI).any (fun r => Nominal.Translation.finalB r.2) = false := by
  decide +kernel

theorem E8_fc_end :
    ∃ r, compileAndRunFC {} 24 Λ8 E8_srcI = some r ∧ r.2.Final ∧ r.2.erase = Nominal.Pages.E8.e8Final :=
  compileAndRunFC_end E8_fc_final E8_fc

/-- Both machines end at one erasure. -/
theorem E8_same : (compileAndRun {} 4 9 Λ8 E8_srcI).map Nominal.Source.Conf.erase =
    (compileAndRunFC {} 24 Λ8 E8_srcI).map (fun r => r.2.erase) := by
  rw [E8_run, E8_fc]; simp [Nominal.Pages.E8.src_erase]

theorem E8_shows :
    ppRunErased Λ8 (compileAndRun {} 4 9 Λ8 E8_srcI) =
      "⟨x0 = λx. λy. λz. let w = y.f z in z, x1 = ν(x) {f = λy. y, me = x}, "
        ++ "x2 = λx. λy. let z = x.f y in y, x3 = λx. let y = x1.me.f x in x | x1⟩" ∧
    ppRunFC Λ8 (compileAndRunFC {} 24 Λ8 E8_srcI) =
      "⟨x0 = λx. λy. λz. let w = y.f z in z, x1 = ν(x) {f = λy. y, me = x}, "
        ++ "x2 = λx. λy. let z = x.f y in y, x3 = λx. let y = x1.me.f x in x | x1⟩" := by
  decide +kernel

/-! ## The running example of plan XII -/

open Paths.FCdot (BVar)
open Nominal.Source (Dec e14_lself e14_u e14_getT e14_vC e14_newC e14_v e14_get e14_w e14_T e14_C e14_L
  e14_Tu e14_Ti e14_dsu e14_dsi fdec tdec ref0 ref1)

/-- The labels of the running example, E14's (`Source/Programs.lean:1351-1373`). -/
def Λ14 : LabelTable := [("ℓself", .trm 0), ("u", .trm 1), ("get$T", .trm 2), ("v$C", .trm 3),
  ("new$C", .trm 4), ("v", .trm 5), ("get", .trm 6), ("w", .trm 7),
  ("A", .typ 0), ("T", .typ 1), ("C", .typ 2), ("L", .typ 3)]

/-- The running example of plan XII "The DOT notation (N4)", in `pdc%`, `$` names in guillemets. -/
def Run_src : STm := pdc%
  let σ = ν(σ) {
    ℓself = σ,
    u = ν(u') {ℓself = u', type A = ⊤},
    class T = μ(this. {ℓself : this.type} ∧ {L : ⊥..⊤} ∧ {v : this.L} ∧ {get : ∀(y : ⊤) this.L}) ∧ ⊤,
    «get$T» : ∀(this : σ.T) ∀(y : ⊤) this.L = λ(this : σ.T). λ(y : ⊤). this.v,
    class C = μ(this. {ℓself : this.type} ∧ {w : ⊤} ∧ {L : ⊤..⊤} ∧ {v : this.L}) ∧ (σ.T ∧ ⊤),
    «v$C» : ∀(this : σ.C) this.L = λ(this : σ.C). this.w,
    «new$C» : ∀(w : ⊤) σ.C = λ(w : ⊤). let ℓ = ν(i) as σ.C {ℓself = i, w = w, type L = ⊤, v = w,
      get : ∀(y : ⊤) i.L = λ(y : ⊤). let g = σ.«get$T» i in g y} in ℓ
  } in let y = σ.«new$C» σ.u.ℓself in (y : σ.T)

/-- The stem's definitions of `Run_src`. -/
def runStem : SDefs := pdcDefs% {
    ℓself = σ,
    u = ν(u') {ℓself = u', type A = ⊤},
    class T = μ(this. {ℓself : this.type} ∧ {L : ⊥..⊤} ∧ {v : this.L} ∧ {get : ∀(y : ⊤) this.L}) ∧ ⊤,
    «get$T» : ∀(this : σ.T) ∀(y : ⊤) this.L = λ(this : σ.T). λ(y : ⊤). this.v,
    class C = μ(this. {ℓself : this.type} ∧ {w : ⊤} ∧ {L : ⊤..⊤} ∧ {v : this.L}) ∧ (σ.T ∧ ⊤),
    «v$C» : ∀(this : σ.C) this.L = λ(this : σ.C). this.w,
    «new$C» : ∀(w : ⊤) σ.C = λ(w : ⊤). let ℓ = ν(i) as σ.C {ℓself = i, w = w, type L = ⊤, v = w,
      get : ∀(y : ⊤) i.L = λ(y : ⊤). let g = σ.«get$T» i in g y} in ℓ }

/-- `Run_src` is the stem `let` with the body `let y = σ.new$C σ.u.ℓself in (y : σ.T)`. -/
theorem Run_src_stem : Run_src =
    .«let» "σ" none (.obj "σ" none runStem) (pdc% let y = σ.«new$C» σ.u.ℓself in (y : σ.T)) := by decide

/-- The structural literal at `σ.C` outside the stem (plan line 690). -/
def StructOut_src : STm := .«let» "σ" none (.obj "σ" none runStem)
  (pdc% let s : σ.C = (let ℓ = ν(o) {ℓself = o, w = σ, type L = ⊤, v = σ} in ℓ) in s)
/-- The same literal inside the stem, as the body of `new$C`. -/
def StructIn_src : STm := pdc%
  let σ = ν(σ) {
    ℓself = σ,
    u = ν(u') {ℓself = u', type A = ⊤},
    class T = μ(this. {ℓself : this.type} ∧ {L : ⊥..⊤} ∧ {v : this.L} ∧ {get : ∀(y : ⊤) this.L}) ∧ ⊤,
    «get$T» : ∀(this : σ.T) ∀(y : ⊤) this.L = λ(this : σ.T). λ(y : ⊤). this.v,
    class C = μ(this. {ℓself : this.type} ∧ {w : ⊤} ∧ {L : ⊤..⊤} ∧ {v : this.L}) ∧ (σ.T ∧ ⊤),
    «v$C» : ∀(this : σ.C) this.L = λ(this : σ.C). this.w,
    «new$C» : ∀(w : ⊤) σ.C = λ(w : ⊤). let s : σ.C = (let ℓ = ν(o) {ℓself = o, w = σ, type L = ⊤, v = σ} in ℓ) in s
  } in let y = σ.«new$C» σ.u.ℓself in (y : σ.T)
/-- The literal tagged outside the stem, where `σ` is let-bound and has no class reading. -/
def TagOut_src : STm := .«let» "σ" none (.obj "σ" none runStem)
  (pdc% let s : σ.C = ν(o) as σ.C {ℓself = o, w = σ, type L = ⊤, v = σ} in s)
/-- A tag at a type member that is no class: resolution refuses it. -/
def NotCls_src : STm := pdc% let m = ν(m) {type C = ⊤} in ν(i) as m.C {ℓself = i}

/-- The body of the trait `T`, `∧` leaning right inside the `μ` as the notation writes it. -/
abbrev run_BodyT {s : Sig} : Ty s :=
  .and (.mu (.and (fdec e14_lself (.sngl ref0)) (.and (tdec e14_L .bot .top)
    (.and (fdec e14_v (.sel ref0 e14_L)) (fdec e14_get (.all .top (.sel ref1 e14_L))))))) .top
/-- The body of the class `C` at the stem `σp`. -/
abbrev run_BodyC {s : Sig} (σp : Path s) : Ty s :=
  .and (.mu (.and (fdec e14_lself (.sngl ref0)) (.and (fdec e14_w .top)
    (.and (tdec e14_L .top .top) (fdec e14_v (.sel ref0 e14_L)))))) (.and (.sel σp e14_T) .top)
/-- The stem's formed self type, in definition order, left nested. -/
abbrev run_Tσ {s : Sig} : Ty (s,x) :=
  .and (.and (.and (.and (.and (.and (fdec e14_lself (.sngl ref0)) (fdec e14_u (.mu e14_Tu)))
    (tdec e14_T .bot run_BodyT))
    (fdec e14_getT (.all (.sel ref0 e14_T) (.all .top (.sel ref1 e14_L)))))
    (tdec e14_C .bot (run_BodyC ref0)))
    (fdec e14_vC (.all (.sel ref0 e14_C) (.sel ref0 e14_L))))
    (fdec e14_newC (.all .top (.sel ref1 e14_C)))
/-- The stem's definitions as the fill erases them. -/
def run_dsσ : Nominal.Source.Defs ([],x) :=
  .cons (.cons (.cons (.cons (.cons (.cons (.cons .nil (.trm e14_lself (.defp ref0)))
    (.trm e14_u (.defv (.new e14_Tu e14_dsu))))
    (.cls e14_T run_BodyT))
    (.trm e14_getT (.defv (.lam (.sel ref0 e14_T) (.val (.lam .top (.path (ref1.sel e14_v))))))))
    (.cls e14_C (run_BodyC ref0)))
    (.trm e14_vC (.defv (.lam (.sel ref0 e14_C) (.path (ref0.sel e14_w))))))
    (.trm e14_newC (.defv (.lam .top (.lett (.lett (.val (.new e14_Ti e14_dsi)) (.lett (.path ref0) (.path ref0)))
      (.path ref0)))))
/-- The fill's erasure. -/
def Run_prog : Nominal.Source.Tm [] :=
  .lett (.val (.new run_Tσ run_dsσ))
    (.lett (.app (ref0.sel e14_newC) ((ref0.sel e14_u).sel e14_lself)) (.lett (.path ref0) (.path ref0)))
/-- The end of the source run, erased. -/
abbrev runFinal : PDot.Runtime.Conf := PDot.Runtime.runFuel 4 7 (Nominal.Source.Conf.erase ⟨[], .nil, Run_prog⟩)

/-- The constructor's body of the running example, a tagged literal bound by a `let`. -/
def newCBody_src : STm := pdc% let ℓ = ν(i) as σ.C {ℓself = i, w = w, type L = ⊤, v = w,
      get : ∀(y : ⊤) i.L = λ(y : ⊤). let g = σ.«get$T» i in g y} in ℓ
/-- Its resolution under `σ, w` (plan lines 666-669). -/
def newCBody_p : PTm (([],x),x) :=
  .«let» .written none
    (.«let» (.inst (.var (.there .here)) (.typ 2)) none
      (.new none (.cons (.cons (.cons (.cons (.cons .nil (.path (.trm 0) (.var .here)))
        (.path (.trm 7) (.var (.there .here)))) (.typ (.typ 3) .top)) (.path (.trm 5) (.var (.there .here))))
        (.lam (.trm 6) (some (.all .top (.sel (.var (.there .here)) (.typ 3)))) (some .top)
          (.«let» .written none (.app ((Path.var (.there (.there (.there .here)))).sel (.trm 2)) (.var (.there .here)))
            (.app (.var .here) (.var (.there .here)))))))
      (.«let» .asc (some (.sel (.var (.there (.there .here))) (.typ 2))) (.path (.var .here)) (.path (.var .here))))
    (.path (.var .here))

theorem Run_fill : (compile {} Λ14 Run_src).map (fun r => r.1.erase) = some Run_prog := by decide +kernel
theorem Run_type : (compile {} Λ14 Run_src).map (fun r => r.2.ty) = some (run_BodyT : Ty []) := by decide +kernel
theorem Run_compiles : (compile {} Λ14 Run_src).isSome = true := by decide +kernel
theorem Run_checks : Nominal.FCn.checkTm .nil ((compile {} Λ14 Run_src).get Run_compiles).2.deriv.translate
    ((compile {} Λ14 Run_src).get Run_compiles).2.ty.translate = true :=
  compile_checks_get Run_compiles
/-- NOM-B at the running example, at the class labels `T` and `C` of the program. -/
theorem Run_nominal : ∃ a c, compileE {} Λ14 Run_src = .ok ⟨a, c⟩ ∧
    c.ann.Nom [Nominal.Source.e14_T, Nominal.Source.e14_C] ∧ c.ann.SealsTagged := by
  have h := Run_compiles
  unfold compile at h
  have hl : (resolveP Λ14 Run_src).map PTm.classLabels = some [Nominal.Source.e14_T, Nominal.Source.e14_C] := by
    decide +kernel
  cases hc : compileE {} Λ14 Run_src with
  | error r =>
    rw [hc] at h
    simp [Except.toOption] at h
  | ok r =>
    obtain ⟨a, c⟩ := r
    obtain ⟨p, hp, hn⟩ := compile_nominal_resolved hc
    rw [hp] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    rw [hl] at hn
    exact ⟨a, c, rfl, hn, compile_seal_sites hc⟩
theorem Run_run : compileAndRun {} 4 7 Λ14 Run_src = some (Nominal.Source.runFuel 4 7 ⟨[], .nil, Run_prog⟩) :=
  compileAndRun_of_fill Run_fill 4 7
theorem Run_src_end : (Nominal.Source.runFuel 4 7 ⟨[], .nil, Run_prog⟩).erase = runFinal := by decide +kernel
theorem Run_run_counts : (Nominal.Source.runFuel 4 6 ⟨[], .nil, Run_prog⟩).erase ≠ runFinal := by decide +kernel
theorem Run_fc : (compileAndRunFC {} 19 Λ14 Run_src).map (fun r => r.2.erase) = some runFinal := by decide +kernel
theorem Run_fc_final : (compileAndRunFC {} 19 Λ14 Run_src).any (fun r => Nominal.Translation.finalB r.2) = true := by
  decide +kernel
theorem Run_fc_counts : (compileAndRunFC {} 18 Λ14 Run_src).any (fun r => Nominal.Translation.finalB r.2) = false := by
  decide +kernel
theorem Run_fc_end : ∃ r, compileAndRunFC {} 19 Λ14 Run_src = some r ∧ r.2.Final ∧ r.2.erase = runFinal :=
  compileAndRunFC_end Run_fc_final Run_fc
/-- Both machines end at one erasure. -/
theorem Run_same : (compileAndRun {} 4 7 Λ14 Run_src).map Nominal.Source.Conf.erase =
    (compileAndRunFC {} 19 Λ14 Run_src).map (fun r => r.2.erase) := by
  rw [Run_run, Run_fc]
  simp [Run_src_end]
theorem Run_shows : ppRunErased Λ14 (compileAndRun {} 4 7 Λ14 Run_src) =
    "⟨x0 = ν(x) {ℓself = x, u = ν{ℓself = x.u}, get$T = λy. λz. y.v, v$C = λy. y.w, new$C = λy. let z = "
      ++ "(let z = ν(z) {ℓself = z, w = y, v = y, get = λw. let u = x.get$T z in u w} in let w = z in w) in z}, "
      ++ "x1 = ν(x) {ℓself = x, w = x0.u.ℓself, v = x0.u.ℓself, get = λy. let z = x0.get$T x in z y} | x1⟩" := by
  rw [Run_run]
  decide +kernel
/-- E14 and the running example both check in FCn (`E14_checks`, `Run_checks`), and their runs end at
erasures that differ in the body of `new$C` only, where the desugaring adds two `let`s. -/
theorem Run_E14 : runFinal ≠ Nominal.Pages.E14.e14Final := by decide +kernel
theorem Run_newC : resolveTm Λ14 ((NameEnv.nil.cons "σ").cons "w") newCBody_src = some newCBody_p := by decide
theorem StructOut_rejected : (compileReason {} Λ14 StructOut_src).any (fun r => decide (r ≠ .limit)) = true := by
  decide +kernel
theorem StructIn_rejected : (compileReason {} Λ14 StructIn_src).any (fun r => decide (r ≠ .limit)) = true := by
  decide +kernel
theorem TagOut_rejected : (compileReason {} Λ14 TagOut_src).any (fun r => decide (r ≠ .limit)) = true := by
  decide +kernel
theorem NotCls_unresolved : resolveP Λ14 NotCls_src = none := by decide
theorem NotCls_reason : compileReason {} Λ14 NotCls_src = some .mismatch := by decide +kernel

/-- The labels of the programs with a class in a nested object (finding G-12). -/
def ΛO : LabelTable := [("o", .trm 0), ("mk", .trm 1), ("a", .trm 2), ("mk2", .trm 3), ("C", .typ 0)]
/-- The class in the nested object `o`, the constructor in the stem: the tag `σ.o.C`. -/
def NestTag_src : STm := pdc% let σ = ν(σ) {o = ν(o) {class C = μ(z. {a : ⊤}) ∧ ⊤},
  mk : ∀(u : ⊤) σ.o.C = λ(u : ⊤). ν(i) as σ.o.C {a = u}} in σ.mk σ
/-- The constructor inside `o` itself: the tag `o.C` at the nested self. -/
def SelfTag_src : STm := pdc% let σ = ν(σ) {o = ν(o) {class C = μ(z. {a : ⊤}) ∧ ⊤,
  mk2 : ∀(u : ⊤) o.C = λ(u : ⊤). ν(i) as o.C {a = u}}} in σ.o.mk2 σ
/-- An instance that claims `σ.o.C` and lacks the class body's field `a`. -/
def BadTag_src : STm := pdc% let σ = ν(σ) {o = ν(o) {class C = μ(z. {a : ⊤}) ∧ ⊤},
  mk : ∀(u : ⊤) σ.o.C = λ(u : ⊤). ν(i) as σ.o.C {mk = u}} in σ.mk σ
theorem NestTag_compiles : (compile {} ΛO NestTag_src).isSome = true := by decide +kernel
/-- The program's type is the class body: `σ.o.C` mentions the let-bound `σ` and widens (D-21). -/
theorem NestTag_type : (compile {} ΛO NestTag_src).map (fun r => r.2.ty) =
    some (.and (.mu (.rcd (.trm (.trm 2) .top))) .top) := by decide +kernel
theorem NestTag_checks : Nominal.FCn.checkTm .nil ((compile {} ΛO NestTag_src).get NestTag_compiles).2.deriv.translate
    ((compile {} ΛO NestTag_src).get NestTag_compiles).2.ty.translate = true :=
  compile_checks_get NestTag_compiles
theorem SelfTag_compiles : (compile {} ΛO SelfTag_src).isSome = true := by decide +kernel
theorem SelfTag_checks : Nominal.FCn.checkTm .nil ((compile {} ΛO SelfTag_src).get SelfTag_compiles).2.deriv.translate
    ((compile {} ΛO SelfTag_src).get SelfTag_compiles).2.ty.translate = true :=
  compile_checks_get SelfTag_compiles
theorem BadTag_reason : compileReason {} ΛO BadTag_src = some .mismatch := by decide +kernel

end NominalFrontend.Examples
