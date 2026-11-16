import Coercions.Selective.Dot

/-! Axiom audit of the `SelectiveDot` library. Replay with
`lake env lean lean/Coercions/Selective/Dot/Axioms.lean`. -/

open SelDot SelDot.Probes

#print axioms Wf.embed
#print axioms var_inv
#print axioms cast_untyped
#print axioms half1
#print axioms half2
#print axioms gap
#print axioms wit_typed
#print axioms primitive_nontrans
#print axioms cRecv_typed
#print axioms r_typed
#print axioms cSel_typed
#print axioms ex2_typed
#print axioms ex2_erase
#print axioms ex2_bare_gap
#print axioms p3_new
#print axioms p3_kept
#print axioms p3_both
#print axioms pBad_untyped
#print axioms step_refl_validates
#print axioms step_refl_validates_under_binder
#print axioms cY_typed
#print axioms r4_typed
#print axioms certY_typed
#print axioms certY_bare_gap
#print axioms cast_inv
#print axioms p5_typed_under_D
#print axioms p5_untyped_under_top
#print axioms step_checks_source_body
#print axioms Prim.wf_left
#print axioms Prim.wf_right
