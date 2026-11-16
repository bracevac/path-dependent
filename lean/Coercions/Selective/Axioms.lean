import Coercions.Selective.Prim
import Coercions.Selective.Syntax
import Coercions.Selective.Typing
import Coercions.Selective.Check
import Coercions.Selective.Sound
import Coercions.Selective.Lift
import Coercions.Selective.Complete
import Coercions.Selective.Annotate
import Coercions.Selective.Rename
import Coercions.Selective.Typer
import Coercions.Selective.Witness
import Coercions.Selective.Matrix
import Coercions.Selective.Negative
import Coercions.Selective.Subst
import Coercions.Selective.Hybrid

/-!
# Axiom audit

`#print axioms` for every theorem of the library, module by module, and for
the functions of `Annotate.lean` and the DOT-MNF retyping functions of
`Subst.lean`.  The allowed axioms are
`propext` and `Quot.sound`.  This module is not imported by the library root;
replay it with `lake env lean lean/Coercions/Selective/Axioms.lean`.
-/

-- Selective/Prim.lean (29)
#print axioms Selective.exp_rename_iff
#print axioms Selective.exp_iff_members
#print axioms Selective.Exp.rename
#print axioms Selective.Prim.rename
#print axioms Selective.Prim.weaken
#print axioms Selective.stepB_sound
#print axioms Selective.primN_sound
#print axioms Selective.prim?_sound
#print axioms Selective.sz_pos
#print axioms Selective.primN_complete
#print axioms Selective.prim?_complete
#print axioms Selective.prim?_iff
#print axioms Selective.not_prim_of
#print axioms Selective.sz_rename
#print axioms Selective.sz_substVar
#print axioms Selective.Chain.single
#print axioms Selective.Chain.append
#print axioms Selective.Chain.snoc
#print axioms Selective.Chain.rename
#print axioms Selective.Chain.fld
#print axioms Selective.Chain.typU
#print axioms Selective.Chain.typL
#print axioms Selective.Chain.typ
#print axioms Selective.Chain.allCod
#print axioms Selective.Chain.allDom
#print axioms Selective.Chain.all
#print axioms Selective.Chain.andCongL
#print axioms Selective.Chain.andCongR
#print axioms Selective.Chain.and

-- Selective/Syntax.lean (4)
#print axioms Selective.Atom.root_rename
#print axioms Selective.HTm.erase_rename
#print axioms Selective.HVal.erase_rename
#print axioms Selective.HDefs.erase_rename

-- Selective/Typing.lean (10)
#print axioms Selective.HTy.atom_iff
#print axioms Selective.HTy.lam_iff
#print axioms Selective.HTy.app_iff
#print axioms Selective.HTy.obj_iff
#print axioms Selective.HTy.proj_iff
#print axioms Selective.HTy.let_iff
#print axioms Selective.HTy.cast_iff
#print axioms Selective.HDefsTy.typ_iff
#print axioms Selective.HDefsTy.trm_iff
#print axioms Selective.HDefsTy.and_iff

-- Selective/Check.lean (14)
#print axioms Selective.memU_iff
#print axioms Selective.memL_iff
#print axioms Selective.synthA_complete
#print axioms Selective.synthC_complete
#print axioms Selective.synthP_complete
#print axioms Selective.synthA_sound
#print axioms Selective.synthC_sound
#print axioms Selective.synthP_sound
#print axioms Selective.synthA_iff
#print axioms Selective.synthC_iff
#print axioms Selective.synthP_iff
#print axioms Selective.checkC_iff
#print axioms Selective.CTy.endpoints_unique
#print axioms Selective.ATy.unique

-- Selective/Sound.lean (14)
#print axioms Selective.Exp.toHasTy
#print axioms Selective.FExp.toHasTy
#print axioms Selective.primitive_sound
#print axioms Selective.ATy.sound
#print axioms Selective.CTy.sound
#print axioms Selective.PTy.sound
#print axioms Selective.coercion_sound
#print axioms Selective.elaboration_typed
#print axioms Selective.defs_typed
#print axioms Selective.elaboration_erases
#print axioms Selective.compiled_safety
#print axioms Selective.compiled_not_stuck
#print axioms Selective.coercion_transitive
#print axioms Selective.coercion_exists_transitive

-- Selective/Lift.lean (8)
#print axioms Selective.CTy.liftFld
#print axioms Selective.CTy.liftTypU
#print axioms Selective.CTy.liftTypL
#print axioms Selective.CTy.liftAllD
#print axioms Selective.CTy.liftAllCG
#print axioms Selective.CTy.liftAllC
#print axioms Selective.CTy.liftAndL
#print axioms Selective.CTy.liftAndR

-- Selective/Complete.lean (7)
#print axioms Selective.cert_complete
#print axioms Selective.atom_complete
#print axioms Selective.elaboration_complete
#print axioms Selective.defs_complete
#print axioms Selective.typability_iff
#print axioms Selective.coercion_iff
#print axioms Selective.atom_iff

-- Selective/Annotate.lean (12)
#print axioms DotMNF.Sub.toCert
#print axioms DotMNF.HasTy.toAtom?
#print axioms DotMNF.HasTy.toH
#print axioms DotMNF.DefsTy.toH
#print axioms DotMNF.HasTy.toAtom
#print axioms DotMNF.Sub.toCert_typed
#print axioms DotMNF.HasTy.toAtom?_typed
#print axioms DotMNF.HasTy.toAtom_typed
#print axioms DotMNF.HasTy.toH_typed
#print axioms DotMNF.DefsTy.toH_typed
#print axioms Selective.E3sub_toCert_checks
#print axioms Selective.E3_toH_checks

-- Selective/Rename.lean (9)
#print axioms Selective.FExp.rename
#print axioms Selective.ATy.rename
#print axioms Selective.CTy.rename
#print axioms Selective.PTy.rename
#print axioms Selective.HTy.rename
#print axioms Selective.HDefsTy.rename
#print axioms Selective.ATy.weaken
#print axioms Selective.CTy.weaken
#print axioms Selective.HTy.weaken

-- Selective/Typer.lean (18)
#print axioms Selective.PRename.Inverts.lift
#print axioms Selective.PRename.unsucc_inverts
#print axioms DotMNF.Ty.unrename_rename
#print axioms DotMNF.Ty.rename_of_unrename
#print axioms DotMNF.Ty.unrename_iff
#print axioms DotMNF.Ty.unweaken?_spec
#print axioms DotMNF.Defs.distinct?_iff
#print axioms Selective.fexpN_sound
#print axioms Selective.fexpN_complete
#print axioms Selective.fexps_iff
#print axioms Selective.synthTm_sound
#print axioms Selective.synthVal_sound
#print axioms Selective.synthDefs_sound
#print axioms Selective.synthTm_complete
#print axioms Selective.synthDefs_complete
#print axioms Selective.synthTm_iff
#print axioms Selective.synthDefs_iff
#print axioms Selective.untypable_of_synthTm

-- Selective/Witness.lean (64)
#print axioms Selective.Γr_lookup_x
#print axioms Selective.Γr_lookup_b
#print axioms Selective.Γr_lookup_c
#print axioms Selective.row1_baseline_steps
#print axioms Selective.row1_app_implicit
#print axioms Selective.E3_not_prim
#print axioms Selective.E3_half1
#print axioms Selective.E3_half2
#print axioms Selective.E3_rejected
#print axioms Selective.E3s_typed
#print axioms Selective.E3s_atom_typed
#print axioms Selective.half1
#print axioms Selective.half2
#print axioms Selective.realizable_gap
#print axioms Selective.realizable_gap'
#print axioms Selective.wit_typed
#print axioms Selective.wit_checks
#print axioms Selective.primitive_nontrans
#print axioms Selective.realizable_nontrans
#print axioms Selective.realization_erase
#print axioms Selective.realization_typed
#print axioms Selective.realization_safe
#print axioms Selective.gapNeeded_bare_untypable
#print axioms Selective.gapBody_typed
#print axioms Selective.gapNeeded_typed
#print axioms Selective.gapNeeded_safe
#print axioms Selective.three_not_prim
#print axioms Selective.three_not_prim'
#print axioms Selective.c3L_typed
#print axioms Selective.c3R_typed
#print axioms Selective.c3_erase
#print axioms Selective.fn_not_prim
#print axioms Selective.fnCo_checks
#print axioms Selective.row5_callee
#print axioms Selective.FG_not_prim
#print axioms Selective.FGco_checks
#print axioms Selective.cod_under_source
#print axioms Selective.ty_not_prim
#print axioms Selective.tyCo_checks
#print axioms Selective.fd_not_prim
#print axioms Selective.fdCo_checks
#print axioms Selective.sel_operand_lookup
#print axioms Selective.assoc_proj
#print axioms Selective.sel_operand_left
#print axioms Selective.no_lookup_through_sel
#print axioms Selective.row8_not_prim
#print axioms Selective.row8_receiver
#print axioms Selective.bad_not_prim
#print axioms Selective.bad_co
#print axioms Selective.bad_not_prim_any
#print axioms Selective.badLam_typed
#print axioms Selective.badLam_safe
#print axioms Selective.loopObj_bad_H
#print axioms Selective.mismC_rejected
#print axioms Selective.mismC_parts
#print axioms Selective.K_not_primitive
#print axioms Selective.goodK_checks
#print axioms Selective.goodK_typed
#print axioms Selective.badK_rejected
#print axioms Selective.badK_untyped
#print axioms Selective.LP_prim
#print axioms Selective.LP_left_operand
#print axioms Selective.LP_left_explicit
#print axioms Selective.loop_decided

-- Selective/Matrix.lean (48)
#print axioms Selective.mu_step1
#print axioms Selective.mu_step2
#print axioms Selective.mu_no_chain
#print axioms Selective.mu_co
#print axioms Selective.obj_at_mu_H
#print axioms Selective.V_not_primitive
#print axioms Selective.unfold_after_cast_H
#print axioms Selective.nested_erase
#print axioms Selective.B2s_no_hidden_chain
#print axioms Selective.B2c_hidden_chain
#print axioms Selective.after_H
#print axioms Selective.after_H_weaken
#print axioms Selective.open_H
#print axioms Selective.bb_H
#print axioms Selective.progH_erase
#print axioms Selective.progH_typed
#print axioms Selective.progH_steps
#print axioms Selective.reductNaive_erase
#print axioms Selective.arg_not_prim
#print axioms Selective.reductNaive_untypable
#print axioms Selective.reductH_erase
#print axioms Selective.reductH_typed
#print axioms Selective.argument_slot_repairs_counterexample
#print axioms Selective.R1.hPlain_erase
#print axioms Selective.R1.hPlain_typed
#print axioms Selective.R1.yArg_root
#print axioms Selective.R1.app_type
#print axioms Selective.R1.hPlain_safe
#print axioms Selective.R1.hPlainN_erase
#print axioms Selective.R1.hPlainN_typed
#print axioms Selective.uProjH_erase
#print axioms Selective.uProjH_typed
#print axioms Selective.E9H_erase
#print axioms Selective.E9H_typed
#print axioms Selective.P4H_erase
#print axioms Selective.P4H_typed
#print axioms Selective.P5H_erase
#print axioms Selective.P5H_typed
#print axioms Selective.bothApp_erase
#print axioms Selective.bothApp_typed
#print axioms Selective.codexTop_primitive
#print axioms Selective.certY_checks
#print axioms Selective.certY_typed
#print axioms Selective.fun_invertible_H
#print axioms Selective.muBridge_different
#print axioms Selective.muBridge_not_primitive
#print axioms Selective.muBridge_checks
#print axioms Selective.distinct_mu_inclusion

-- Selective/Negative.lean (20)
#print axioms Selective.CTy.chain_of_stepOnly
#print axioms Selective.stepOnly_of_chain
#print axioms Selective.stepOnly_iff_chain
#print axioms Selective.R1.rebind_loses_root
#print axioms Selective.R1.atom_keeps_root
#print axioms Selective.chainK_stepOnly
#print axioms Selective.K_receiver_free_chain
#print axioms Selective.TypIsh.weaken
#print axioms Selective.Γ0_y
#print axioms Selective.typ_step
#print axioms Selective.dom_step
#print axioms Selective.dom_chain
#print axioms Selective.TypIsh.codOK
#print axioms Selective.exp_domR
#print axioms Selective.cod_step
#print axioms Selective.domR_D0
#print axioms Selective.inv_step
#print axioms Selective.inv_chain
#print axioms Selective.Y_no_receiver_free_chain
#print axioms Selective.Y_no_receiver_free_coercion

-- Selective/Subst.lean (7)
#print axioms DotMNF.Sub.retype
#print axioms DotMNF.HasTy.retype
#print axioms DotMNF.DefsTy.retype
#print axioms Selective.HTy.retype
#print axioms Selective.HTy.subst_atom
#print axioms Selective.Prim.subst_atom
#print axioms Selective.CTy.subst_atom

-- Selective/Hybrid.lean (49)
#print axioms Selective.Hybrid.prim_decided
#print axioms Selective.Hybrid.prim_not_transitive
#print axioms Selective.Hybrid.var_exact
#print axioms Selective.Hybrid.step_rule
#print axioms Selective.Hybrid.seq_rule
#print axioms Selective.Hybrid.cast_rule
#print axioms Selective.Hybrid.app_rule
#print axioms Selective.Hybrid.cast_seq
#print axioms Selective.Hybrid.cast_erases
#print axioms Selective.Hybrid.atom_type_unique
#print axioms Selective.Hybrid.cert_checker
#print axioms Selective.Hybrid.term_checker
#print axioms Selective.Hybrid.coercion_exact
#print axioms Selective.Hybrid.typability_exact
#print axioms Selective.Hybrid.annotation
#print axioms Selective.Hybrid.annotation_checks
#print axioms Selective.Hybrid.trans_is_seq
#print axioms Selective.Hybrid.safety
#print axioms Selective.Hybrid.not_stuck
#print axioms Selective.Hybrid.ex1_cert
#print axioms Selective.Hybrid.ex1_gap
#print axioms Selective.Hybrid.ex1_bare_rejected
#print axioms Selective.Hybrid.ex1_one_step_rejected
#print axioms Selective.Hybrid.ex1_typed
#print axioms Selective.Hybrid.ex1_checked
#print axioms Selective.Hybrid.ex1_nested_casts
#print axioms Selective.Hybrid.ex1_one_written_step
#print axioms Selective.Hybrid.ex1_erases
#print axioms Selective.Hybrid.ex1_source_typed
#print axioms Selective.Hybrid.ex1_term_cast
#print axioms Selective.Hybrid.ex1_term_cast_one_step
#print axioms Selective.Hybrid.ex1_closed_erases
#print axioms Selective.Hybrid.ex1_closed_typed
#print axioms Selective.Hybrid.ex1_closed_safe
#print axioms Selective.Hybrid.ex2_term
#print axioms Selective.Hybrid.ex2_bare_rejected
#print axioms Selective.Hybrid.ex2_not_primitive
#print axioms Selective.Hybrid.ex2_bare_receiver_rejected
#print axioms Selective.Hybrid.reach_step
#print axioms Selective.Hybrid.reach_chain
#print axioms Selective.Hybrid.ex2_no_step_only
#print axioms Selective.Hybrid.ex2_receiver
#print axioms Selective.Hybrid.ex2_typed
#print axioms Selective.Hybrid.ex2_erases
#print axioms Selective.Hybrid.ex2_closed_erases
#print axioms Selective.Hybrid.ex2_closed_typed
#print axioms Selective.Hybrid.ex2_closed_safe
#print axioms Selective.Hybrid.receiver_evidence_needed
#print axioms Selective.Hybrid.views_typed
