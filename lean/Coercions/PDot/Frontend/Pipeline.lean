import Coercions.PDot.Frontend.Typer
import Coercions.PDot.Frontend.Sources
import Coercions.PDot.Translation.Examples
import Coercions.PDot.FCp.CheckerCompleteness

/-!
# The pipeline without slots

`compile` resolves a program to an annotated term (`resolve`, `Resolve.lean`)
and synthesizes its type with the typer (`compileLanded`, `Typer.lean`).  It
returns the resolved term and a `Compiled`, which holds the type and the
annotated derivation `AHasTy`.  Its erasure `Compiled.deriv` is the
`PDot.Source.HasTy` derivation of the erased term.  `checkAt` checks a resolved
term against a given type.  `compileAndRun` follows a compile with the source
machine of `PDot.Source` at a fuel and a step budget.  `compileAndRunFC`
translates the derivation to FCp and runs its machine at a step budget.

This is the pipeline without slots.  Every slot of the program is written, so
there is nothing to infer, and `compile` is resolution followed by
`compileLanded` (`compile_full`).  The elaborator of stage XF3a puts itself in
front, and `compile` becomes `(compileE b Λ e).toOption`.  Then `compile_full`
is proved again with the same statement.  Every other theorem here is proved
from a successful compile alone, never by unfolding `compile`, so it keeps its
proof.  `compile_isSome` goes through `compile_full` only.

The Head's theorems compose results about the calculus.  The front end proves
nothing new.

* `compile_checks` is `PDot.FCp.checkTm_iff` applied to
  `PDot.Source.HasTy.translate_typed`.  The checker takes no fuel, so its verdict
  on the translation is a theorem.  `compile_checks_get` states it for a compile
  known only to succeed, so that a program discharges it with one decided fact.
* `compile_erase` is `PDot.Source.HasTy.translate_erase`.
* `compile_safe` is `PDot.safety`.  `compile_run_progress` is its first half at
  the configuration the source driver returns.
* `compile_reachable` is `PDot.reachable_typed`, and `compile_lockstep` is
  `PDot.reachable_run`.

Each theorem takes the successful compile `h : compile b Λ e = some ⟨a, c⟩`.
The content is the type of `c`.  The siblings restate these at the drivers
(`compileAndRun_eq` to `compileAndRunFC_consistent`), state that `c.ann` erases
to `c.deriv` (`compile_ann`), and carry the stability of the typer in the fuel
to `checkAt` and `compileLanded` (`checkAt_mono`, `compileLanded_mono`).

The section `Checks` runs the nine hand programs E1 to E8 and E13 of
`Sources.lean`.  For each, `checkAt` types the resolved term at the type of its
hand derivation, `compileLanded` accepts it, and the FCp checker accepts the
image of the compiled derivation.  N1 to N3 are rejected with the tank
unmarked.  The refuter's program G1 compiles, since avoidance takes the meet of
the upper bounds.  E6 costs at most the plan's estimate of 11,000 units.
-/

namespace PDotFrontend

open Frontend.Fuel PDotFrontend.Core
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open PDot.Source (Ty Dec Tm Ctx HasTy Sub)

/-! ## The result of a compilation -/

/-- A type for a closed annotated term, with the annotated derivation. -/
structure Compiled (a : ATm []) where
  ty : Ty []
  ann : AHasTy .nil a ty

/-- The pDOT derivation of the erased term, the erasure of the annotated one. -/
def Compiled.deriv {a : ATm []} (c : Compiled a) : HasTy .nil a.erase c.ty := c.ann.erase

/-! ## The pipeline -/

/-- Check a closed annotated term against a type, with the tank. -/
def checkAtF (b : Budget) (a : ATm []) (T : Ty []) : Option (AHasTy .nil a T) × Tank :=
  checkTopF b.mode b.modules b.fuel a T
/-- Check a closed annotated term against a type.  A marked tank answers `none`. -/
def checkAt (b : Budget) (a : ATm []) (T : Ty []) : Option (AHasTy .nil a T) := (checkAtF b a T).1
/-- Synthesize the type of a closed annotated term, with the tank. -/
def compileLandedF (b : Budget) (a : ATm []) : Option (Compiled a) × Tank :=
  let r := synthTopF b.mode b.modules b.fuel a
  (r.1.map fun c => ⟨c.ty, c.deriv⟩, r.2)
/-- Synthesize the type of a closed annotated term.  A marked tank answers `none`. -/
def compileLanded (b : Budget) (a : ATm []) : Option (Compiled a) := (compileLandedF b a).1
/-- Resolution, then `compileLanded`.  XF3a puts the elaborator in front. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) : Option ((a : ATm []) × Compiled a) :=
  (resolve Λ e).bind fun a => (compileLanded b a).map (⟨a, ·⟩)

/-- Compile, then run the source machine. -/
def compileAndRun (b : Budget) (n m : Nat) (Λ : LabelTable) (e : STm) : Option PDot.Source.Conf :=
  (compile b Λ e).map fun r => PDot.Source.runFuel n m ⟨[], .nil, r.1.erase⟩
/-- Compile, translate to FCp, then run the FCp machine. -/
def compileAndRunFC (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × PDot.FCp.State s) :=
  (compile b Λ e).map fun r => PDot.Translation.runOf m ⟨[], ⟨.nil, .nil, r.2.deriv.translate⟩⟩

/-! ## The Head's theorems and their siblings -/

theorem compile_full {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    compile b Λ e = (compileLanded b a).map (⟨a, ·⟩) := by
  simp only [compile, h, Option.bind_some]

section Head

set_option linter.unusedVariables false

variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a}

theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    PDot.FCp.checkTm .nil c.deriv.translate c.ty.translate = true :=
  PDot.FCp.checkTm_iff.mpr (PDot.Source.HasTy.translate_typed c.deriv .nil)

theorem compile_checks_get (h : (compile b Λ e).isSome = true) :
    PDot.FCp.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {c' : PDot.Source.Conf}
    (hc : PDot.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    (PDot.Source.NormForm c'.tm ∨ ∃ c'', PDot.Source.Step c' c'') ∧
    (∀ p, c'.tm = .path p → PDot.Source.PathSafe c'.store p) :=
  PDot.safety c.deriv hc

theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    c.deriv.translate.erase = a.erase.erase :=
  PDot.Source.HasTy.translate_erase c.deriv

theorem compile_reachable (h : compile b Λ e = some ⟨a, c⟩) {c' : PDot.Source.Conf}
    (hc : PDot.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    ∃ (st : PDot.FCp.State c'.s) (ρ : Rename [] c'.s),
      st.Typed (c.ty.translate.rename ρ) ∧ st.erase = c'.erase ∧
      ∀ Γ, PDot.FCp.Store.Typed st.σ Γ → ¬ ∃ ev, PDot.FCp.LeCo.HasType Γ ev PDot.FCp.Ty.top PDot.FCp.Ty.bot :=
  PDot.reachable_typed c.deriv hc

theorem compile_lockstep (h : compile b Λ e = some ⟨a, c⟩) {c' : PDot.Source.Conf}
    (hc : PDot.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    ∃ st : PDot.FCp.State c'.s,
      PDot.FCp.Steps PDot.FCp.appView ⟨.nil, .nil, c.deriv.translate⟩ st ∧ st.erase = c'.erase :=
  PDot.reachable_run c.deriv hc

theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    let c' := PDot.Source.runFuel n m ⟨[], .nil, a.erase⟩
    PDot.Source.NormForm c'.tm ∨ ∃ c'', PDot.Source.Step c' c'' :=
  (compile_safe h (PDot.Source.Reds.of_runFuel n m _)).1

theorem compile_ann (h : compile b Λ e = some ⟨a, c⟩) : c.ann.erase = c.deriv := rfl

theorem compileAndRun_eq (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    compileAndRun b n m Λ e = some (PDot.Source.runFuel n m ⟨[], .nil, a.erase⟩) := by
  simp only [compileAndRun, h, Option.map_some]

theorem compileAndRun_progress (h : compile b Λ e = some ⟨a, c⟩) {n m : Nat} {c' : PDot.Source.Conf}
    (hr : compileAndRun b n m Λ e = some c') :
    PDot.Source.NormForm c'.tm ∨ ∃ c'', PDot.Source.Step c' c'' := by
  rw [compileAndRun_eq h] at hr
  cases hr
  exact compile_run_progress h n m

theorem compileAndRunFC_eq (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    compileAndRunFC b m Λ e = some (PDot.Translation.runOf m ⟨[], ⟨.nil, .nil, c.deriv.translate⟩⟩) := by
  simp only [compileAndRunFC, h, Option.map_some]

theorem compileAndRunFC_reaches (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × PDot.FCp.State s} (hr : compileAndRunFC b m Λ e = some r) :
    PDot.FCp.Steps PDot.FCp.appView ⟨.nil, .nil, c.deriv.translate⟩ r.2 := by
  rw [compileAndRunFC_eq h] at hr
  cases hr
  exact PDot.Translation.steps_of_runOf m ⟨[], ⟨.nil, .nil, c.deriv.translate⟩⟩

theorem compileAndRunFC_typed (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × PDot.FCp.State s} (hr : compileAndRunFC b m Λ e = some r) :
    ∃ ρ : Rename [] r.1, r.2.Typed (c.ty.translate.rename ρ) :=
  PDot.FCp.Steps.typed (PDot.image_typed c.deriv) (compileAndRunFC_reaches h hr)

theorem compileAndRunFC_consistent (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × PDot.FCp.State s} (hr : compileAndRunFC b m Λ e = some r) :
    ∃ Γ : PDot.FCp.Ctx r.1, PDot.FCp.Store.Typed r.2.σ Γ ∧
      ¬ ∃ ev, PDot.FCp.LeCo.HasType Γ ev PDot.FCp.Ty.top PDot.FCp.Ty.bot :=
  PDot.FCp.reachable_consistent (PDot.Source.HasTy.translate_typed c.deriv .nil) (compileAndRunFC_reaches h hr)

theorem checkAt_mono {a : ATm []} {T : Ty []} {d : AHasTy .nil a T} (h : checkAt b a T = some d)
    {n : Nat} (hn : b.fuel ≤ n) : checkAt { b with fuel := n } a T = some d :=
  checkTopF_mono h hn

theorem compileLanded_mono {a : ATm []} {c : Compiled a} (h : compileLanded b a = some c)
    {n : Nat} (hn : b.fuel ≤ n) : compileLanded { b with fuel := n } a = some c := by
  unfold compileLanded compileLandedF at h ⊢
  simp only [Option.map_eq_some_iff] at h ⊢
  obtain ⟨c', h', rfl⟩ := h
  exact ⟨c', synthTopF_mono h' hn, rfl⟩

end Head

/-- A compile succeeds when `compileLanded` accepts the resolved term.  Proved from
`compile_full` alone, so it keeps its proof when XF3a replaces the body of `compile`. -/
theorem compile_isSome {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (resolve Λ e).any (fun a => (compileLanded b a).isSome) = true) : (compile b Λ e).isSome = true := by
  cases hr : resolve Λ e with
  | none => simp [hr] at h
  | some a =>
    rw [compile_full hr]
    simp only [hr, Option.any_some] at h
    simpa [Option.isSome_map] using h

/-! ## Checks

The nine hand programs of `Sources.lean`, each checked at the type of its hand
derivation, compiled, and its image accepted by the FCp checker.  Then N1 to N3
rejected with the tank unmarked, N1 with no compile, the refuter's program G1,
and the cost of E6.  N1 and N2 are rejected by the shape of a path definition
under a declared type that is no singleton, at 0 units, so they do not exercise
the bad bounds their names suggest.  N3 is rejected at the first view of
`x.zz`. -/

section Checks

open PDotFrontend.Sources
open PDot.Source (e1_Td e2_Tz compiler_T list_T sngl_T e13_T)

theorem E1_checkAt : (resolve Λ1 E1_src).any (fun a => (checkAt {} a (.mu e1_Td)).isSome) = true := by decide +kernel
theorem E1_landed : (resolve Λ1 E1_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E1_compiles : (compile {} Λ1 E1_src).isSome = true := compile_isSome E1_landed
theorem E1_checks : PDot.FCp.checkTm .nil ((compile {} Λ1 E1_src).get E1_compiles).2.deriv.translate
    ((compile {} Λ1 E1_src).get E1_compiles).2.ty.translate = true := compile_checks_get E1_compiles

theorem E2_checkAt : (resolve Λ2 E2_src).any (fun a => (checkAt {} a (.mu e2_Tz)).isSome) = true := by decide +kernel
theorem E2_landed : (resolve Λ2 E2_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E2_compiles : (compile {} Λ2 E2_src).isSome = true := compile_isSome E2_landed
theorem E2_checks : PDot.FCp.checkTm .nil ((compile {} Λ2 E2_src).get E2_compiles).2.deriv.translate
    ((compile {} Λ2 E2_src).get E2_compiles).2.ty.translate = true := compile_checks_get E2_compiles

theorem E3_checkAt : (resolve Λ3 E3_src).any (fun a => (checkAt {} a compiler_T).isSome) = true := by decide +kernel
theorem E3_landed : (resolve Λ3 E3_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E3_compiles : (compile {} Λ3 E3_src).isSome = true := compile_isSome E3_landed
theorem E3_checks : PDot.FCp.checkTm .nil ((compile {} Λ3 E3_src).get E3_compiles).2.deriv.translate
    ((compile {} Λ3 E3_src).get E3_compiles).2.ty.translate = true := compile_checks_get E3_compiles

theorem E4_checkAt : (resolve Λ4 E4_src).any (fun a => (checkAt {} a list_T).isSome) = true := by decide +kernel
theorem E4_landed : (resolve Λ4 E4_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E4_compiles : (compile {} Λ4 E4_src).isSome = true := compile_isSome E4_landed
theorem E4_checks : PDot.FCp.checkTm .nil ((compile {} Λ4 E4_src).get E4_compiles).2.deriv.translate
    ((compile {} Λ4 E4_src).get E4_compiles).2.ty.translate = true := compile_checks_get E4_compiles

theorem E5_checkAt : (resolve Λ5 E5_src).any (fun a => (checkAt {} a sngl_T).isSome) = true := by decide +kernel
theorem E5_landed : (resolve Λ5 E5_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E5_compiles : (compile {} Λ5 E5_src).isSome = true := compile_isSome E5_landed
theorem E5_checks : PDot.FCp.checkTm .nil ((compile {} Λ5 E5_src).get E5_compiles).2.deriv.translate
    ((compile {} Λ5 E5_src).get E5_compiles).2.ty.translate = true := compile_checks_get E5_compiles

theorem E6_checkAt : (resolve Λ6 E6_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E6_landed : (resolve Λ6 E6_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E6_compiles : (compile {} Λ6 E6_src).isSome = true := compile_isSome E6_landed
theorem E6_checks : PDot.FCp.checkTm .nil ((compile {} Λ6 E6_src).get E6_compiles).2.deriv.translate
    ((compile {} Λ6 E6_src).get E6_compiles).2.ty.translate = true := compile_checks_get E6_compiles

theorem E7_checkAt : (resolve Λ7 E7_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E7_landed : (resolve Λ7 E7_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E7_compiles : (compile {} Λ7 E7_src).isSome = true := compile_isSome E7_landed
theorem E7_checks : PDot.FCp.checkTm .nil ((compile {} Λ7 E7_src).get E7_compiles).2.deriv.translate
    ((compile {} Λ7 E7_src).get E7_compiles).2.ty.translate = true := compile_checks_get E7_compiles

theorem E8_checkAt : (resolve Λ8 E8_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E8_landed : (resolve Λ8 E8_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E8_compiles : (compile {} Λ8 E8_src).isSome = true := compile_isSome E8_landed
theorem E8_checks : PDot.FCp.checkTm .nil ((compile {} Λ8 E8_src).get E8_compiles).2.deriv.translate
    ((compile {} Λ8 E8_src).get E8_compiles).2.ty.translate = true := compile_checks_get E8_compiles

theorem E13_checkAt : (resolve Λ13 E13_src).any (fun a => (checkAt {} a (.mu e13_T)).isSome) = true := by decide +kernel
theorem E13_landed : (resolve Λ13 E13_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E13_compiles : (compile {} Λ13 E13_src).isSome = true := compile_isSome E13_landed
theorem E13_checks : PDot.FCp.checkTm .nil ((compile {} Λ13 E13_src).get E13_compiles).2.deriv.translate
    ((compile {} Λ13 E13_src).get E13_compiles).2.ty.translate = true := compile_checks_get E13_compiles
theorem N1_rejected : (resolve ΛN1 N1_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N2_rejected : (resolve ΛN2 N2_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N3_rejected : (resolve ΛN3 N3_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N1_compile : compile {} ΛN1 N1_src = none := by decide +kernel

/-- The labels of the refuter's program G1. -/
def ΛG : LabelTable := [("A", .typ 0), ("c", .trm 0)]
/-- G1: a binder with two upper bounds of `A`, typed through their meet. -/
def G1_src : STm := pdt%
  (λ(f : ∀(z : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) z.A). λ(x : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}). let y = x in f y
    : ∀(f : ∀(z : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) z.A) ∀(x : ({A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) ∧ ⊤) {c : ⊤})
theorem G1_compiles : (compile {} ΛG G1_src).isSome = true := by decide +kernel

theorem E6_cost : (resolve Λ6 E6_src).any (fun a => used (checkAtF {} a .top) ≤ 11000) = true := by decide +kernel

end Checks

end PDotFrontend
