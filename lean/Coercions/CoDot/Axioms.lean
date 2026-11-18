import Coercions.CoDot

/-!
# Axiom audit of CoDot

`lake env lean lean/Coercions/CoDot/Axioms.lean` prints the axioms that each
theorem of the library depends on: at most `propext`, `Quot.sound` and
`Classical.choice`. This module is not imported by `Coercions.CoDot`.
-/

/-! ## `Subst.lean` -/

#print axioms CoDot.CoTy.anySubject
#print axioms CoDot.CoTy.rename
#print axioms CoDot.CoTy.csubst
#print axioms CoDot.CoSub.inst_ok
#print axioms CoDot.app_all_wrapper

/-! ## `Eval.lean` -/

#print axioms CoDot.VTy.no_bot
#print axioms CoDot.VTy.canon_fld
#print axioms CoDot.VTy.canon_all
#print axioms CoDot.VTy.canon_typ
#print axioms CoDot.VTy.canon_pair
#print axioms CoDot.Step.preservation
#print axioms CoDot.EvTy.progress
#print axioms CoDot.Ev.measure
#print axioms CoDot.Step.measure_lt

/-! ## `Elimination.lean` -/

#print axioms CoDot.app_step_wrapper
#print axioms CoDot.sel_step_wrapper

/-! ## `Term.lean` -/

#print axioms CoDot.Typed.rename
#print axioms CoDot.Typed.csubst
#print axioms CoDot.Typed.inst
#print axioms CoDot.Typed.letRef
#print axioms CoDot.Typed.alloc
#print axioms CoDot.Typed.defs_record
#print axioms CoDot.Typed.defs_field

/-! ## `Machine.lean` -/

#print axioms CoDot.StoreTy.lookup
#print axioms CoDot.StoreTy.wf
#print axioms CoDot.StoreTy.defines
#print axioms CoDot.ContTy.weaken
#print axioms CoDot.State.Ok.init
#print axioms CoDot.State.Ok.step
#print axioms CoDot.State.Ok.progress
#print axioms CoDot.safety

/-! ## `Admin.lean` -/

#print axioms CoDot.MStep.split
#print axioms CoDot.AStep.adm_lt
#print axioms CoDot.AStepsN.bound
#print axioms CoDot.admin_normalizes

/-! ## `Elab.lean` -/

#print axioms CoDot.elab_sub
#print axioms CoDot.elab_var
#print axioms CoDot.elab_tm
#print axioms CoDot.elab_defs
#print axioms CoDot.elaboration

/-! ## `Bridge.lean` -/

#print axioms CoDot.RStep.erase
#print axioms CoDot.AStep.erase
#print axioms CoDot.State.Final.erase
#print axioms CoDot.State.final_of_erase
#print axioms CoDot.dot_step_det
#print axioms CoDot.lift_step
#print axioms CoDot.erase_not_stuck
#print axioms CoDot.source_reach
#print axioms CoDot.source_safety

/-! ## `WadlerFest.lean` -/

#print axioms CoDotSafety.dot_safety
#print axioms WadlerFest.codot_safety
#print axioms WadlerFest.Retained.codot_safety
#print axioms WadlerFest.Sorted.codot_safety

/-! ## `Examples.lean` -/

#print axioms CoDot.E9_elab
#print axioms CoDot.E10_elab
#print axioms CoDot.E11_elab
#print axioms CoDot.E12_elab
