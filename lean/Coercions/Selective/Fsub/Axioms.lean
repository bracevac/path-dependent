import Coercions.Selective.Fsub
/-! `#print axioms` for every theorem and for the main functions. -/
open SelFsub SelFsub.Witness SelFsub.Examples

-- Syntax
#print axioms liftRen_comp
#print axioms Ty.rename_rename
#print axioms Ty.rename_weaken
#print axioms Ty.subst_rename
#print axioms Ty.rename_subst
#print axioms liftS_var
#print axioms Ty.subst_var
#print axioms Ty.weaken_subst
#print axioms Ty.weaken_sub0
#print axioms liftN_var
#print axioms Tele.subst_var
-- Prim
#print axioms prim?
#print axioms boundIs_true
#print axioms primDir_base
#print axioms primDir_sound
#print axioms primDir_complete
#print axioms prim?_iff
#print axioms Prim.inv
#print axioms TyRen.lift
#print axioms TyRen.weaken
#print axioms Prim.rename
#print axioms Prim.weaken
#print axioms ctxYX_XY
#print axioms ctxYX_Y
#print axioms ctxYX_not
#print axioms ctxYX_checker
#print axioms ctxZYX_XY
#print axioms ctxZYX_YZ
#print axioms ctxZYX_not
#print axioms primitive_nontrans
-- Cert
#print axioms synthC
#print axioms checkC
#print axioms CTy.endpoints
#print axioms CTy.endpoints_unique
#print axioms Cert.valid_iff
#print axioms synthC_iff
#print axioms checkC_iff
#print axioms CTy.rename
#print axioms CTy.weaken
-- Sub
#print axioms primitive_sound
#print axioms coercion_sound
#print axioms coercion_transitive
#print axioms coercion_exists_transitive
-- Lift
#print axioms Cert.arr
#print axioms Cert.all
#print axioms CTy.arrDom
#print axioms CTy.arrCod
#print axioms CTy.allBound
#print axioms CTy.allBody
#print axioms CTy.arr
#print axioms CTy.all
-- Complete
#print axioms Sub.toCert
#print axioms Sub.toCert_typed
#print axioms coercion_iff
-- Subst
#print axioms Cert.ofPrim
#print axioms Cert.subst
#print axioms Cert.narrow
#print axioms Cert.inst
#print axioms EntryTy.cert
#print axioms CSub.lift
#print axioms CSub.liftTele
#print axioms Cert.ofPrim_typed
#print axioms CTy.subst
#print axioms CSub.narrow
#print axioms CTy.narrow
#print axioms CSub.inst
#print axioms CTy.inst
-- Invert
#print axioms Cert.arrInv
#print axioms Cert.allInv
#print axioms CTy.top_inv
#print axioms CTy.arr_inv
#print axioms CTy.all_inv
-- Witness
#print axioms chainL_typed
#print axioms chainR_typed
#print axioms chain_not_prim
#print axioms chain_step_rejected
#print axioms chain_middle_not_prim
#print axioms arr_typed
#print axioms arr_not_prim
#print axioms all_typed
#print axioms all_not_prim
#print axioms bad_parts
#print axioms bad_rejected
#print axioms bad_untyped
#print axioms good_typed
#print axioms dYZ_typed
#print axioms nb_narrow
#print axioms nb_narrow_typed
#print axioms nb_not_prim
#print axioms na_narrow
#print axioms na_narrow_typed
#print axioms na_not_prim
#print axioms nu_narrow_typed
#print axioms nu_not_prim
#print axioms dWZ_typed
#print axioms sb_inst
#print axioms sb_inst_typed
#print axioms sa_inst
#print axioms sa_inst_typed
#print axioms sa_not_prim
#print axioms arr_inv_components
#print axioms all_inv_components
-- Term
#print axioms Tm.erase
#print axioms Tm.renTy
#print axioms Tm.substTy
#print axioms Tm.subst
#print axioms Tm.erase_erase
#print axioms Tm.erase_renTy
#print axioms Tm.erase_subst
#print axioms Ty.rename_sub0
#print axioms liftS_comp
#print axioms Ty.subst_subst
#print axioms Ty.subst_sub0
-- Typing
#print axioms synthTm
#print axioms HTy.unique
#print axioms synthTm_sound
#print axioms synthTm_complete
#print axioms synthTm_iff
-- Safety
#print axioms HTy.renTy
#print axioms HTy.append
#print axioms HTy.subst
#print axioms HTy.substTy
#print axioms HTy.canon_lam
#print axioms HTy.canon_tlam
#print axioms preservation
#print axioms progress
#print axioms safety
#print axioms Value.no_step
#print axioms Step.det
-- Exact
#print axioms FTy.erase_eq
#print axioms elaboration_typed
#print axioms elaboration_complete
#print axioms typability_iff
#print axioms fsub_safety
-- Examples
#print axioms arg_bare_rejected
#print axioms arg_one_step_rejected
#print axioms arg_cast_typed
#print axioms argRun_typed
#print axioms argRun_steps
#print axioms argRun_value
#print axioms nest_typed
#print axioms nest_subject_rejected
#print axioms nest_mismatch_rejected
#print axioms calleeF_typed
#print axioms callee_bare_rejected
#print axioms calleeApp_typed
#print axioms tb_step
#print axioms tb_bare_rejected
#print axioms tbReduct_erase
#print axioms tbReduct_typed
#print axioms tbEntry_eq
#print axioms tb_arg_cast
#print axioms tb_arg_cast_typed
#print axioms bRedex_typed
#print axioms b_step
#print axioms b_bare_rejected
#print axioms b_min_typed
#print axioms bReduct_erase
#print axioms bReduct_typed
