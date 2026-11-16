import Coercions.Selective.FsubDeclarative
/-! `#print axioms` for every theorem and function of `SelFsubDecl`. -/
open SelFsub

-- Sub
#print axioms Sub.rename
#print axioms Sub.weaken
#print axioms TySub.lift
#print axioms Sub.subst
#print axioms TySub.inst
#print axioms Sub.narrow
#print axioms Sub.top_inv
#print axioms Sub.arr_inv
#print axioms Sub.all_inv
-- Typing
#print axioms FTy.renTy
#print axioms FTy.append
#print axioms FTy.subst
#print axioms FTy.substTy
#print axioms FTy.canon_lam
#print axioms FTy.canon_tlam
-- Safety
#print axioms fsub_preservation
#print axioms fsub_progress
#print axioms fsub_safety_direct
