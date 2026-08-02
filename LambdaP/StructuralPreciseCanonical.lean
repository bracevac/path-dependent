import LambdaP.StructuralPreciseStore
import LambdaP.StructuralResolution
import LambdaP.StructuralApplicationCompatibility
import LambdaP.StructuralRefinedProgress

/-!
Operational canonical interfaces for exact structural stores.

This file deliberately contains only the conditional exact-store boundary.
The old concrete-head development also imported counterexamples and a
possible-head hierarchy tied to the conflated singleton syntax; those are not
part of the calculus.  The two observation predicates below are the
small interfaces consumed by exact-state progress.
-/

namespace LambdaP

/-! ## Exact lookup -/

/-- A function observation at a store variable is represented by an
abstraction in that cell. -/
def Store.FunctionCheckReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Ty n}
      {U : LambdaP.Ty (n + 1)},
    Path.StructCheck Gamma (Path.RuntimeEq sigma) (.var x)
      (Tau.ty (Ty.Fun S U)) ->
    exists A body, Store.Binds sigma x (Tm.abs A body)

/-- The two concrete observations made by path and machine progress. -/
structure Store.HeadCheckReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  function : Store.FunctionCheckReflection Gamma sigma
  pair : Store.PairCheckReflection Gamma sigma

/-- Promote a path known to resolve to `x` to the exact context type of
`x`. -/
private theorem Path.StructCheck.at_precise_result
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {P : LambdaP.Ty n}
    (hr : Path.reduce p sigma x)
    (hp : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Single (Path.var x))))
    (hx : Ctx.Binds Gamma x P) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty P) := by
  have hsingle : Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single p)) (Tau.ty P) :=
    .trans (Tau.StructSub.single_runtime (Path.RuntimeEq.of_reduce hr))
      (.widen (.var hx))
  exact .promote hp hsingle

/-- Static-aligned lookup reconstructs the term singleton of its result in
an exact structural store.  Type-member selection remains distinct as
`Ty.TSel`; this theorem concerns term-location resolution only. -/
theorem Store.StructPreciseTy.lookup_singleton
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n}
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Single (Path.var x))) := by
  induction hr with
  | var =>
      obtain ⟨P, hx⟩ := Ctx.Binds.exists Gamma _
      exact .promote (.var hx) .refl
  | fst hr hbind ih =>
      obtain ⟨P, hx, hprecise⟩ := hstore.of_store_binds hbind
      have hp := (ih hstore).at_precise_result hr.toReduce hx
      cases hprecise with
      | pair hy hz =>
          simpa only using Path.StructCheck.fst hp
      | tpair hy hT =>
          simpa only using Path.StructCheck.fst hp
  | sel_hit hr hbind ih =>
      obtain ⟨P, hx, hprecise⟩ := hstore.of_store_binds hbind
      have hp := (ih hstore).at_precise_result hr.toReduce hx
      cases hprecise with
      | pair hy hz =>
          simpa only [Tau.weaken_open] using Path.StructCheck.sel_r hp
  | sel_miss hr hbind hne htail ih ihtail =>
      obtain ⟨P, hx, hprecise⟩ := hstore.of_store_binds hbind
      have hp := (ih hstore).at_precise_result hr.toReduce hx
      cases hprecise with
      | pair hy hz =>
          exact Path.StructCheck.sel_l hp (ihtail hstore) hne
      | tpair hy hT =>
          exact Path.StructCheck.sel_l hp (ihtail hstore) hne

/-- Big-step term-path reduction has the same singleton reconstruction
property. -/
theorem Store.StructPreciseTy.reduce_singleton
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Single (Path.var x))) :=
  hstore.lookup_singleton hr.toLookup

/-- In an exact structural store, a reducing term path and its result
variable support the same proper structural checks. -/
theorem Store.StructPreciseTy.reduce_check_iff
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty T) <->
      Path.StructCheck Gamma (Path.RuntimeEq sigma)
        (Path.var x) (Tau.ty T) := by
  constructor
  · exact fun hp => hp.reduce_to_var hr
  · intro hx
    have halias := hstore.reduce_singleton hr
    have hsub : Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty (Ty.Single p)) (Tau.ty T) :=
      .trans (Tau.StructSub.single_runtime (Path.RuntimeEq.of_reduce hr))
        (.widen hx)
    exact .promote halias hsub

/-- Runtime equality transports proper checks between paths which actually
resolve. -/
theorem Store.StructPreciseTy.runtimeEq_reduce_check_iff
    (hstore : Store.StructPreciseTy Gamma sigma)
    (heq : Path.RuntimeEq sigma p q)
    (hp : Path.reduce p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty T) <->
      Path.StructCheck Gamma (Path.RuntimeEq sigma) q (Tau.ty T) := by
  have hq : Path.reduce q sigma x := (heq.reduce_iff x).mp hp
  exact (hstore.reduce_check_iff hp).trans
    (hstore.reduce_check_iff hq).symm

/-! ## Conditional concrete-head boundary -/

/-- The exact singleton-head pushback still needed by progress.  The
premises mention proper term singletons only; abstract selections use
`Ty.TSel` and cannot enter this interface by syntax confusion. -/
structure Store.StructPreciseSingletonHeadPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  function : forall {x : Fin n} {S : LambdaP.Ty n}
      {U : LambdaP.Ty (n + 1)},
    Store.StructPreciseTy Gamma sigma ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Fun S U)) ->
    exists A body, Store.Binds sigma x (Tm.abs A body)
  pair : forall {x : Fin n} {S : LambdaP.Ty n}
      {a : Name} {k : Kind} {d : Tau (n + 1) k},
    Store.StructPreciseTy Gamma sigma ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Pair S a d)) ->
    exists (y : Fin n) (delta : Def n k),
      @Store.Binds n sigma x (@Tm.pair n k y a delta)

/-- Singleton-head pushback supplies precisely the pair/function reflection
used by structural progress. -/
theorem Store.StructPreciseTy.headCheckReflection_of_singletonPushback
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma) :
    Store.HeadCheckReflection Gamma sigma := by
  constructor
  · intro x S U hfun
    exact hpush.function hstore (.widen hfun)
  · intro x S a k d hpair
    exact hpush.pair hstore (.widen hpair)

/-! ## Conditional function pushback boundary -/

/-- Function-signature inversion at an exact context entry, reduced to the
singleton suffix produced by path-term inversion. -/
def Store.StructPreciseSingletonFunctionPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n}
      {S A : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)},
    Store.StructPreciseTy Gamma sigma ->
    Ctx.Binds Gamma x (Ty.Fun A B) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Fun S U)) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U)

/-- Function pushback tied directly to the exact context entry and stored
closure. -/
def Store.StructExactFunctionPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n}
      {S A : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)}
      {body : Tm (n + 1)},
    Store.StructPreciseTy Gamma sigma ->
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x (Ty.Fun A B) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) (Ty.Fun S U) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U)

/-- Singleton function pushback is sufficient for exact function
pushback. -/
theorem Store.StructPreciseSingletonFunctionPushback.to_exact
    (hpush : Store.StructPreciseSingletonFunctionPushback Gamma sigma) :
    Store.StructExactFunctionPushback Gamma sigma := by
  intro x S A U B body hstore hbind hctx hfun
  cases hfun.path_inversion rfl with
  | intro P hp hsingle hwf =>
      exact hpush hstore hctx hsingle

/-- Exact-store beta opening from the minimal explicit pushback property. -/
theorem Store.StructPreciseTy.open_application_of_exactPushback
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p q : Path n} {x y : Fin n}
    {S : LambdaP.Ty n}
    {U : LambdaP.Ty (n + 1)}
    {A : LambdaP.Ty n} {body : Tm (n + 1)}
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hpush : Store.StructExactFunctionPushback Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (hfun : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U))
    (harg : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path q) S) :
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (body.open y) (U.open q) := by
  obtain ⟨P, hctx, hprecise⟩ := hstore.of_store_binds hbind
  cases hprecise with
  | abs hbody hA =>
      have hfunAtX := hfun.reduce_path hp
      obtain ⟨hdom, hcod⟩ := hpush hstore hbind hctx hfunAtX
      have hargAtS : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
          (Tm.path (Path.var y)) S := harg.reduce_path hq
      have hargAtA : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
          (Tm.path (Path.var y)) A :=
        Tm.StructCheck.sub hargAtS hdom hA
      have hopened := hbody.open_var_of_path_term
        (Path.RuntimeEq.isEquivCongr sigma) hargAtA
      have hfunWf : Tau.StructWf Gamma (Path.RuntimeEq sigma)
          (Tau.ty (Ty.Fun S U)) := by
        cases hfun.path_inversion rfl with
        | intro precise hcheck hsub hwf => exact hwf
      exact Store.structResultOpening Gamma sigma hq harg hfunWf hcod hopened

end LambdaP
