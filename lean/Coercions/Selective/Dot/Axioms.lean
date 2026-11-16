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
-- structural lemmas
#print axioms HasTy.rename
#print axioms PathTy.psubst
#print axioms Prim.psubst
#print axioms CertTy.psubst
#print axioms HasTy.psubst
#print axioms CertTy.narrow
#print axioms HasTy.narrow
#print axioms CertTy.substPath
#print axioms HasTy.substPath
-- inert contexts
#print axioms Inv.sub
#print axioms TTy.inv
#print axioms TTy.sel_bounds
#print axioms PathTy.tight
#print axioms Prim.tight
#print axioms CertTy.tight
#print axioms PathTy.fun_inv
#print axioms PathTy.fld_inv
-- certificates
#print axioms CertTy.andI
#print axioms TSub.cert
#print axioms AllSub.collapse
-- safety
#print axioms HasTy.strip
#print axioms StoreTy.inert
#print axioms canonical_fun
#print axioms canonical_obj
#print axioms progress
#print axioms preservation
#print axioms safety
