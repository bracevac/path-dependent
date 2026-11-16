import Coercions.Selective.Dot.Vanilla

/-! Axiom audit of the `SelectiveDotVanilla` library. Replay with
`lake env lean lean/Coercions/Selective/Dot/Vanilla/Axioms.lean`. -/

open SelDot SelDot.Vanilla

#print axioms pathTy_sound
#print axioms prim_sound
#print axioms certTy_sound
#print axioms hasTy_sound
#print axioms DotMNF.Sub.toCert
#print axioms DotMNF.HasTy.toPath
#print axioms DotMNF.HasTy.elab
#print axioms DotMNF.Sub.toCert_typed
#print axioms DotMNF.HasTy.toPath_typed
#print axioms DotMNF.HasTy.elab_erase
#print axioms DotMNF.HasTy.elab_typed
#print axioms typability_iff
#print axioms coercion_iff
#print axioms trans_is_seq
#print axioms step_ofDot
#print axioms step_of_ofDot
#print axioms final_ofDot
#print axioms stuck_ofDot
#print axioms dot_safety_direct
