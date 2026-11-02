import Coercions.Nominal.Translation.Examples

/-!
# The runs of E5, E7, E8 and E14 at both levels (plan X, stage X7, group g2, and plan XII)

One page per program that runs, in `namespace Nominal.Pages`.  Each page runs the program on the
source (`Source.runFuel`) and its image on the FCn machine (`Translation.runOf`), and the kernel
decides that both runs end in one runtime configuration, the end of the runtime's run of the erased
program.  The machine takes more steps than the source, since it moves `let` frames and casts in
steps that keep the erasure.

* `E5`: `sngl_t` runs in four source steps and seven machine steps to `path o.incr.decr`, a path of
  depth two (`e5Final`, `Source/Erasure.lean`).
* `E7`: `E7_prog` runs in two source steps and three machine steps to `path core`, through the
  module alias `core.m.f`.
* `E8`: `E8_prog` runs in nine source steps and sixteen machine steps to `path o`, through `g`, `h`
  and `k`.
* `E14`: `E14_prog`, plan XII's class program, runs in four source steps and nine machine steps to
  `path ℓ`, the instance of `C`.  Its end is the runtime's own run of the erased program
  (`e14Final`).  The image the machine runs holds the two class definitions and the three seals.

On each page `both` states the two runs, their common erasure, that the source ends in a normal
form and that the machine ends in a final state.  `counts` makes the step counts exact: one source
step fewer ends at another erasure, and one machine step fewer at a state that is not final.  `safe`
is `Nominal.safety` at the end of the source run.  For E5 and E7 `store_agrees` shows that X4's
hand-written final store (`FCn.C0Ex.E5.σ`, `FCn.C0Ex.E7.σ`), on which X4 proves the answer's lookup
safe, erases to the store the runs reach.

Binders are named in comments only.  `(s,x)` adds one variable, and `.here` is the newest variable
of a signature.
-/

namespace Nominal.Pages

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Source Translation

/-! ## E5: `SingletonTypeExample.v` -/

namespace E5

/-- The configuration that starts E5. -/
abbrev start : Source.Conf := ⟨[], .nil, sngl_t⟩
/-- The state that starts E5's image. -/
abbrev init : (s : Sig) × FCn.State s := ⟨[], ⟨.nil, .nil, SG_d.translate⟩⟩
/-- The end of the source run. -/
abbrev fin : Source.Conf := Source.runFuel 4 4 start

theorem src_erase : fin.erase = e5Final := by decide +kernel
theorem fcp_erase : (runOf 7 init).2.erase = e5Final := by decide +kernel
theorem fcp_final : finalB (runOf 7 init).2 = true := by decide +kernel
/-- The counts are exact: three source steps end at another erasure, and six machine steps at a
state that is not final. -/
theorem counts : (Source.runFuel 4 3 start).erase ≠ e5Final ∧ finalB (runOf 6 init).2 = false := by
  decide +kernel
/-- X4's hand-written final store of E5 erases to the store the runs reach. -/
theorem store_agrees : FCn.C0Ex.E5.σ.erase = e5Final.store := by decide +kernel

/-- Both runs end in `e5Final`, the source at a normal form, the machine at a final state. -/
theorem both :
    Source.Reds start fin ∧ fin.erase = e5Final ∧ Source.NormForm fin.tm ∧
    FCn.Steps FCn.appView init.2 (runOf 7 init).2 ∧ (runOf 7 init).2.erase = e5Final ∧
    (runOf 7 init).2.Final := by
  refine ⟨Source.Reds.of_runFuel 4 4 _, src_erase, ?_, steps_of_runOf 7 init, fcp_erase,
    final_of_finalB fcp_final⟩
  have hn := (final_of_finalB fcp_final).erase_normForm
  rw [fcp_erase, ← src_erase] at hn
  exact (Source.erase_normForm _).1 hn

/-- `Nominal.safety` at the end of the source run. -/
theorem safe : (Source.NormForm fin.tm ∨ ∃ c', Source.Step fin c') ∧
    (∀ p, fin.tm = .path p → Source.PathSafe fin.store p) :=
  Nominal.safety SG_d (Source.Reds.of_runFuel 4 4 _)

end E5

/-! ## E7: a module alias as a prefix -/

namespace E7

abbrev start : Source.Conf := ⟨[], .nil, E7_prog⟩
abbrev init : (s : Sig) × FCn.State s := ⟨[], ⟨.nil, .nil, E7_d.translate⟩⟩
abbrev fin : Source.Conf := Source.runFuel 4 2 start

/-- The end of E7's run: `core` allocated, `path core` in focus. -/
abbrev e7Final : PDot.Runtime.Conf :=
  ⟨(([] : Sig),x), PDot.Runtime.Store.nil.cons (Val.new e7_Tc e7_coreDefs).erase, .path (.var .here)⟩   -- .here is core

theorem runtime_run : PDot.Runtime.runFuel 4 2 start.erase = e7Final := by decide +kernel
theorem src_erase : fin.erase = e7Final := by decide +kernel
theorem fcp_erase : (runOf 3 init).2.erase = e7Final := by decide +kernel
theorem fcp_final : finalB (runOf 3 init).2 = true := by decide +kernel
/-- The counts are exact: one source step ends at another erasure, and two machine steps at a
state that is not final. -/
theorem counts : (Source.runFuel 4 1 start).erase ≠ e7Final ∧ finalB (runOf 2 init).2 = false := by
  decide +kernel
/-- X4's hand-written final store of E7 erases to the store the runs reach. -/
theorem store_agrees : FCn.C0Ex.E7.σ.erase = e7Final.store := by decide +kernel

theorem both :
    Source.Reds start fin ∧ fin.erase = e7Final ∧ Source.NormForm fin.tm ∧
    FCn.Steps FCn.appView init.2 (runOf 3 init).2 ∧ (runOf 3 init).2.erase = e7Final ∧
    (runOf 3 init).2.Final := by
  refine ⟨Source.Reds.of_runFuel 4 2 _, src_erase, ?_, steps_of_runOf 3 init, fcp_erase,
    final_of_finalB fcp_final⟩
  have hn := (final_of_finalB fcp_final).erase_normForm
  rw [fcp_erase, ← src_erase] at hn
  exact (Source.erase_normForm _).1 hn

theorem safe : (Source.NormForm fin.tm ∨ ∃ c', Source.Step fin c') ∧
    (∀ p, fin.tm = .path p → Source.PathSafe fin.store p) :=
  Nominal.safety E7_d (Source.Reds.of_runFuel 4 2 _)

end E7

/-! ## E8: replacement at an abstract member -/

namespace E8

abbrev start : Source.Conf := ⟨[], .nil, E8_prog⟩
abbrev init : (s : Sig) × FCn.State s := ⟨[], ⟨.nil, .nil, E8_d.translate⟩⟩
abbrev fin : Source.Conf := Source.runFuel 4 9 start

/-- The end of E8's run: `g`, `o`, `h = g o` and `k = h o.me` allocated, `path o` in focus. -/
abbrev e8Final : PDot.Runtime.Conf :=
  ⟨(((([] : Sig),x),x),x),x,                                          -- g, o, h, k
   (((PDot.Runtime.Store.nil.cons (e8_g (s := [])).erase).cons (Val.new e8_To e8_oDefs).erase).cons
      -- h = λ(y). λ(v). let w = y.f v in v, with y and v the .here of their bodies
      (.lam (.val (.lam (.lett (.app ((Path.var (.there .here)).sel e8_f) (.var .here)) (.path (.var (.there .here)))))))).cons
      -- k = λ(v). let w = o.me.f v in v
      (.lam (.lett (.app (((Path.var (.there (.there .here))).sel e8_me).sel e8_f) (.var .here)) (.path (.var (.there .here))))),
   .path (.var (.there (.there .here)))⟩                              -- o

theorem runtime_run : PDot.Runtime.runFuel 4 9 start.erase = e8Final := by decide +kernel
theorem src_erase : fin.erase = e8Final := by decide +kernel
theorem fcp_erase : (runOf 16 init).2.erase = e8Final := by decide +kernel
theorem fcp_final : finalB (runOf 16 init).2 = true := by decide +kernel
/-- The counts are exact: eight source steps end at another erasure, and fifteen machine steps at
a state that is not final. -/
theorem counts : (Source.runFuel 4 8 start).erase ≠ e8Final ∧ finalB (runOf 15 init).2 = false := by
  decide +kernel

theorem both :
    Source.Reds start fin ∧ fin.erase = e8Final ∧ Source.NormForm fin.tm ∧
    FCn.Steps FCn.appView init.2 (runOf 16 init).2 ∧ (runOf 16 init).2.erase = e8Final ∧
    (runOf 16 init).2.Final := by
  refine ⟨Source.Reds.of_runFuel 4 9 _, src_erase, ?_, steps_of_runOf 16 init, fcp_erase,
    final_of_finalB fcp_final⟩
  have hn := (final_of_finalB fcp_final).erase_normForm
  rw [fcp_erase, ← src_erase] at hn
  exact (Source.erase_normForm _).1 hn

theorem safe : (Source.NormForm fin.tm ∨ ∃ c', Source.Step fin c') ∧
    (∀ p, fin.tm = .path p → Source.PathSafe fin.store p) :=
  Nominal.safety E8_d (Source.Reds.of_runFuel 4 9 _)

end E8

/-! ## E14: a class and a trait (plan XII) -/

namespace E14

/-- The configuration that starts E14. -/
abbrev start : Source.Conf := ⟨[], .nil, E14_prog⟩
/-- The state that starts E14's image. -/
abbrev init : (s : Sig) × FCn.State s := ⟨[], ⟨.nil, .nil, E14_d.translate⟩⟩
/-- The end of the source run. -/
abbrev fin : Source.Conf := Source.runFuel 4 4 start
/-- The runtime's own run of the erased program, the configuration both runs reach. -/
abbrev e14Final : PDot.Runtime.Conf := PDot.Runtime.runFuel 4 4 start.erase
theorem final_tm : e14Final.tm = .path (.var .here) := by decide +kernel      -- path ℓ, the instance
theorem src_erase : fin.erase = e14Final := by decide +kernel
theorem fcp_erase : (runOf 9 init).2.erase = e14Final := by decide +kernel
theorem fcp_final : finalB (runOf 9 init).2 = true := by decide +kernel
/-- The counts are exact: three source steps end at another erasure, and eight machine steps at a
state that is not final. -/
theorem counts : (Source.runFuel 4 3 start).erase ≠ e14Final ∧ finalB (runOf 8 init).2 = false := by
  decide +kernel

/-- Both runs end in `e14Final`, the source at a normal form, the machine at a final state. -/
theorem both :
    Source.Reds start fin ∧ fin.erase = e14Final ∧ Source.NormForm fin.tm ∧
    FCn.Steps FCn.appView init.2 (runOf 9 init).2 ∧ (runOf 9 init).2.erase = e14Final ∧
    (runOf 9 init).2.Final := by
  refine ⟨Source.Reds.of_runFuel 4 4 _, src_erase, ?_, steps_of_runOf 9 init, fcp_erase,
    final_of_finalB fcp_final⟩
  have hn := (final_of_finalB fcp_final).erase_normForm
  rw [fcp_erase, ← src_erase] at hn
  exact (Source.erase_normForm _).1 hn

/-- `Nominal.safety` at the end of the source run. -/
theorem safe : (Source.NormForm fin.tm ∨ ∃ c', Source.Step fin c') ∧
    (∀ p, fin.tm = .path p → Source.PathSafe fin.store p) :=
  Nominal.safety E14_d (Source.Reds.of_runFuel 4 4 _)

end E14

end Nominal.Pages
