import LambdaPFC.Typing

/-!
# Well-formed full LambdaPFC contexts and typed path substitution

The full compiler needs a well-formedness derivation for every precise path
result, including interval-valued selections.  LambdaPFC contexts do not
store this invariant intrinsically, so this module supplies it together with
the source-only substitution facts needed by `Path.Ty.sel_r`.

No semantic realization, runtime subtyping, restricted fragment, or target
language is involved.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

/-- Every binding was well formed in the context preceding it. -/
inductive ContextWellFormed : {n : Nat} -> Ctx n -> Type where
  | nil : ContextWellFormed .nil
  | snoc :
      ContextWellFormed context ->
      Tau.Wf context (.ty sourceType) ->
      ContextWellFormed (context.snoc sourceType)

/-- A simultaneous path substitution respecting all source bindings. -/
structure TypedPathSubstitution
    (sourceContext : Ctx n) (targetContext : Ctx m)
    (substitution : PathSubst n m) : Type where
  lookup : (index : Fin n) ->
    Path.Ty targetContext (substitution index)
      (.ty ((sourceContext.lookup index).subst substitution))

theorem PathSubst.weaken_comp_lift
    (substitution : PathSubst n m) :
    FinFun.weaken.asSubst.comp substitution.lift =
      substitution.comp FinFun.weaken.asSubst := by
  funext index
  change substitution.lift index.succ =
    (substitution index).subst FinFun.weaken.asSubst
  rw [PathSubst.lift_succ, Path.subst_asSubst]
  rfl

theorem Ty.weaken_subst_lift
    (sourceType : Ty n) (substitution : PathSubst n m) :
    sourceType.weaken.subst substitution.lift =
      (sourceType.subst substitution).weaken := by
  rw [Ty.weaken, ← Ty.subst_asSubst]
  rw [Ty.subst_comp, PathSubst.weaken_comp_lift]
  rw [← Ty.subst_comp, Ty.subst_asSubst]
  rfl

theorem Tau.weaken_subst_lift
    (sourceType : Tau n kind) (substitution : PathSubst n m) :
    sourceType.weaken.subst substitution.lift =
      (sourceType.subst substitution).weaken := by
  rw [Tau.weaken, ← Tau.subst_asSubst]
  rw [Tau.subst_comp, PathSubst.weaken_comp_lift]
  rw [← Tau.subst_comp, Tau.subst_asSubst]
  rfl

theorem Ty.rename_weaken_subst_lift
    (sourceType : Ty n) (substitution : PathSubst n m) :
    (sourceType.rename FinFun.weaken).subst substitution.lift =
      (sourceType.subst substitution).rename FinFun.weaken := by
  simpa only [Ty.weaken] using Ty.weaken_subst_lift sourceType substitution

theorem Ty.rename_weaken_open
    (sourceType : Ty n) (argument : Path n) :
    (sourceType.rename FinFun.weaken).subst (PathSubst.openAt argument) =
      sourceType := by
  simpa only [Ty.weaken, Ty.open] using Ty.weaken_open sourceType argument

namespace PathTyping

/-- Precise path typing is stable under every typed path substitution. -/
noncomputable def subst
    {sourceContext : Ctx n} {targetContext : Ctx m}
    {substitution : PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution) :
    Path.Ty sourceContext path sourceType ->
      Path.Ty targetContext (path.subst substitution)
        (sourceType.subst substitution)
  | .var => typed.lookup _
  | .fst receiver => (subst typed receiver).fst
  | .sel_r receiver => by
      simpa only [Path.subst, Tau.open_subst] using
        (subst typed receiver).sel_r
  | .sel_l receiver tail labelsNe =>
      .sel_l (subst typed receiver) (subst typed tail) labelsNe

end PathTyping

namespace TypedPathSubstitution

/-- The variable-only substitution which weakens past one new binding. -/
noncomputable def weaken
    (context : Ctx n) (newest : Ty n) :
    TypedPathSubstitution context (context.snoc newest)
      FinFun.weaken.asSubst where
  lookup index := by
    simpa only [FinFun.asSubst_apply, Ctx.lookup, Ty.subst_asSubst,
      Path.rename] using
      (Path.Ty.var :
        Path.Ty (context.snoc newest) (.var index.succ)
          (.ty ((context.snoc newest).lookup index.succ)))

/-- Lift a typed substitution through one source binder. -/
noncomputable def lift
    {sourceContext : Ctx n} {targetContext : Ctx m}
    {substitution : PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution)
    (newest : Ty n) :
    TypedPathSubstitution (sourceContext.snoc newest)
      (targetContext.snoc (newest.subst substitution)) substitution.lift where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · change Path.Ty (targetContext.snoc (newest.subst substitution))
        (.var 0) (.ty (newest.weaken.subst substitution.lift))
      simpa only [Ty.weaken_subst_lift] using
        (Path.Ty.var :
          Path.Ty (targetContext.snoc (newest.subst substitution)) (.var 0)
            (.ty ((targetContext.snoc
              (newest.subst substitution)).lookup 0)))
    · have olderTyping := PathTyping.subst
          (weaken targetContext (newest.subst substitution))
          (typed.lookup older)
      change Path.Ty (targetContext.snoc (newest.subst substitution))
        (substitution older).weaken
        (.ty ((sourceContext.lookup older).weaken.subst
          substitution.lift))
      simpa only [Ty.weaken_subst_lift, Path.subst_asSubst,
        Tau.subst_asSubst, Path.weaken, Tau.rename,
        Ty.rename_weaken_subst_lift] using
        olderTyping

/-- Opening by a precisely typed path is a typed substitution. -/
noncomputable def openAt
    {context : Ctx n} {newest : Ty n} {argument : Path n}
    (typing : Path.Ty context argument (.ty newest)) :
    TypedPathSubstitution (context.snoc newest) context
      (PathSubst.openAt argument) where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · change Path.Ty context argument
        (.ty (newest.weaken.subst (PathSubst.openAt argument)))
      have cancel :
          newest.weaken.subst (PathSubst.openAt argument) = newest := by
        simpa only [Ty.open] using Ty.weaken_open newest argument
      exact cancel.symm ▸ typing
    · change Path.Ty context (.var older)
        (.ty ((context.lookup older).weaken.subst
          (PathSubst.openAt argument)))
      have cancel :
          (context.lookup older).weaken.subst
              (PathSubst.openAt argument) = context.lookup older := by
        simpa only [Ty.open] using
          Ty.weaken_open (context.lookup older) argument
      exact cancel.symm ▸
        (Path.Ty.var : Path.Ty context (.var older)
          (.ty (context.lookup older)))

end TypedPathSubstitution

namespace Subtyping

/-- Full source subtyping is stable under typed path substitution. -/
noncomputable def subst
    {sourceContext : Ctx n} {targetContext : Ctx m}
    {substitution : PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution) :
    Tau.Sub sourceContext sourceType targetType ->
      Tau.Sub targetContext (sourceType.subst substitution)
        (targetType.subst substitution)
  | .refl => .refl
  | .trans first second => .trans (subst typed first) (subst typed second)
  | .bot => .bot
  | .top => .top
  | .widen pathTyping => .widen (PathTyping.subst typed pathTyping)
  | .symm pathTyping => .symm (PathTyping.subst typed pathTyping)
  | .sel_hi pathTyping nonempty =>
      .sel_hi (PathTyping.subst typed pathTyping) (subst typed nonempty)
  | .sel_lo pathTyping nonempty =>
      .sel_lo (PathTyping.subst typed pathTyping) (subst typed nonempty)
  | @Tau.Sub.fun _ _ domain _ _ _ parameter result =>
      .fun (subst typed parameter)
        (subst (typed.lift domain) result)
  | @Tau.Sub.pair _ _ first _ _ _ _ _ parameter member =>
      .pair (subst typed parameter)
        (subst (typed.lift first) member)
  | .bounds lower upper nonempty =>
      .bounds (subst typed lower) (subst typed upper)
        (subst typed nonempty)

end Subtyping

namespace TypeWellFormed

/-- Full generalized-type well-formedness is stable under typed paths. -/
noncomputable def subst
    {sourceContext : Ctx n} {targetContext : Ctx m}
    {substitution : PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution) :
    Tau.Wf sourceContext sourceType ->
      Tau.Wf targetContext (sourceType.subst substitution)
  | .bot => .bot
  | .top => .top
  | .path pathTyping => .path (PathTyping.subst typed pathTyping)
  | .sel pathTyping nonempty =>
      .sel (PathTyping.subst typed pathTyping)
        (Subtyping.subst typed nonempty)
  | @Tau.Wf.fun _ _ domain _ domainWf codomainWf =>
      .fun (subst typed domainWf)
        (subst (typed.lift domain) codomainWf)
  | @Tau.Wf.pair _ _ first _ _ _ firstWf memberWf =>
      .pair (subst typed firstWf)
        (subst (typed.lift first) memberWf)
  | .bounds_wf lower upper nonempty =>
      .bounds_wf (subst typed lower) (subst typed upper)
        (Subtyping.subst typed nonempty)

noncomputable def weaken
    {context : Ctx n}
    (wf : Tau.Wf context sourceType) (newest : Ty n) :
    Tau.Wf (context.snoc newest) sourceType.weaken := by
  simpa only [Tau.subst_asSubst, Tau.weaken] using
    subst (TypedPathSubstitution.weaken context newest) wf

noncomputable def openAt
    {context : Ctx n}
    (wf : Tau.Wf (context.snoc newest) sourceType)
    (typing : Path.Ty context argument (.ty newest)) :
    Tau.Wf context (sourceType.open argument) :=
  subst (TypedPathSubstitution.openAt typing) wf

end TypeWellFormed

namespace ContextWellFormed

/-- Every lookup from a well-formed context has a well-formed result. -/
noncomputable def lookup
    {context : Ctx n}
    (wf : ContextWellFormed context) (index : Fin n) :
    Tau.Wf context (.ty (context.lookup index)) := by
  induction wf with
  | nil => exact Fin.elim0 index
  | @snoc n context sourceType contextWf sourceWf ih =>
      refine Fin.cases ?_ (fun older => ?_) index
      · exact TypeWellFormed.weaken sourceWf sourceType
      · exact TypeWellFormed.weaken (ih older) sourceType

end ContextWellFormed

namespace PathTyping

/-- Precise path typing synthesizes a well-formed generalized type in every
well-formed context.  The result is kind-generic, covering both locations
and interval-valued type selections. -/
noncomputable def resultWf
    {context : Ctx n}
    (contextWf : ContextWellFormed context) :
    Path.Ty context path sourceType -> Tau.Wf context sourceType
  | .var => contextWf.lookup _
  | .fst receiver => by
      have receiverWf := resultWf contextWf receiver
      cases receiverWf with
      | pair firstWf _ => exact firstWf
  | .sel_r receiver => by
      have receiverWf := resultWf contextWf receiver
      cases receiverWf with
      | pair _ memberWf =>
          exact TypeWellFormed.openAt memberWf
            (Path.Ty.fst receiver)
  | .sel_l _ tail _ => resultWf contextWf tail

end PathTyping

end LambdaPToFCo.Full
