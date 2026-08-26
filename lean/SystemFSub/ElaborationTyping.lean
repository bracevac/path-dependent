import SystemFSub.ElaborationContext
import SystemFSub.ElaborationSubstitution
import SystemFSub.ElaborationTerms
import SystemFCo.Typing

/-!
# Type preservation of F<: elaboration

This is the compiler theorem: source subtyping derivations elaborate to typed
target coercions, and source typing derivations elaborate to typed target
expressions. The target contains neither subtyping nor subsumption.
-/

namespace SystemFSub.Elaboration

noncomputable def elaborateSubTyping
    {sig : SystemFSub.Sig} {context : SystemFSub.Ctx sig}
    {source target : SystemFSub.Ty sig}
    (derivation : SystemFSub.Ty.Sub context source target) :
    SystemFCo.Co.HasType (translateCtx context) (elaborateSub derivation)
      (translateTy source) (translateTy target) := by
  induction derivation with
  | refl => exact .refl
  | trans _ _ first_ih second_ih => exact .trans first_ih second_ih
  | top => exact .top
  | bound lookup => exact .cvar (translateLookupBound lookup)
  | arrow _ _ parameter_ih result_ih =>
      exact .arrow parameter_ih result_ih
  | @all sig context targetBound sourceBound sourceBody targetBody
      bound body bound_ih body_ih =>
      apply SystemFCo.Co.HasType.poly
      apply SystemFCo.Co.HasType.qual
      · apply SystemFCo.Co.HasType.trans
        · exact .cvar .here
        · exact (bound_ih.weaken .tvar).weaken
            (.cvar (.tvar .here) ((translateTy targetBound).weaken .tvar))
      · have sourceEq :
            (translateTy sourceBody).subst
              (SystemFCo.Subst.rebindCVar
                (.trans (.cvar .here)
                  (((elaborateSub bound).weaken .tvar).weaken .cvar))) =
              translateTy sourceBody := by
          have equal : TargetTVarEq
              (SystemFCo.Subst.rebindCVar
                (.trans (.cvar .here)
                  (((elaborateSub bound).weaken .tvar).weaken .cvar)))
              (SystemFCo.Subst.id : SystemFCo.Subst
                (translateSig (sig,X)) (translateSig (sig,X))) := by
            constructor
            intro X
            cases X with
            | there X => rfl
          exact (targetTy_subst_congr (translateTy sourceBody) equal).trans
            (SystemFCo.Ty.subst_id _)
        exact sourceEq.symm ▸ body_ih

noncomputable def elaborateTermTyping
    {sig : SystemFSub.Sig} {context : SystemFSub.Ctx sig}
    {term : SystemFSub.Tm sig} {ty : SystemFSub.Ty sig}
    (derivation : SystemFSub.Tm.HasType context term ty) :
    SystemFCo.Exp.HasType (translateCtx context) (elaborateTerm derivation)
      (translateTy ty) := by
  induction derivation with
  | var lookup => exact .var (translateLookupVar lookup)
  | @abs sig context parameter body result bodyTyping body_ih =>
      apply SystemFCo.Exp.HasType.abs
      change (translateCtx context).bindVar (translateTy parameter) |-e
        elaborateTerm bodyTyping : translateTy (result.weaken (k := .var))
        at body_ih
      rw [translateTy_weaken_var] at body_ih
      exact body_ih
  | app _ _ function_ih argument_ih => exact .app function_ih argument_ih
  | @tabs sig context bound body result bodyTyping body_ih =>
      exact .tabs (.cabs body_ih)
  | @tapp sig context function bound body argument functionTyping boundTyping
      function_ih =>
      have bound_ih := elaborateSubTyping boundTyping
      have bound_opened :
          SystemFCo.Co.HasType (translateCtx context)
            (elaborateSub boundTyping)
            ((SystemFCo.Ty.tvar .here).subst
              (SystemFCo.Subst.openTVar (translateTy argument)))
            (((translateTy bound).weaken .tvar).subst
              (SystemFCo.Subst.openTVar (translateTy argument))) := by
        have targetEq :
            (((translateTy bound).weaken .tvar).subst
              (SystemFCo.Subst.openTVar (translateTy argument))) =
              translateTy bound := by
          unfold SystemFCo.Ty.weaken
          exact SystemFCo.Ty.rename_weaken_subst_cancel (translateTy bound)
            (SystemFCo.Subst.openTVar (translateTy argument))
            (SystemFCo.Subst.weakenAsSubst_comp_openTVar
              (translateTy argument))
        exact targetEq.symm ▸ bound_ih
      have applied := SystemFCo.Exp.HasType.capp
        (SystemFCo.Exp.HasType.tapp (argument := translateTy argument)
          function_ih)
        bound_opened
      simpa only [translateTy_open body argument (elaborateSub boundTyping)]
        using applied
  | sub termTyping subtype term_ih =>
      exact .cast term_ih (elaborateSubTyping subtype)

end SystemFSub.Elaboration
