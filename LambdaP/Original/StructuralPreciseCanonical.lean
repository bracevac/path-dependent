import LambdaP.Original.StructuralPreciseStore
import LambdaP.Original.StructuralResolution
import LambdaP.Original.StructuralApplicationCompatibility
import LambdaP.Original.StructuralHeadReflection

/-!
Operational canonical facts for exact structural stores.

An exact structural store exposes the introduction type of every stored
value in its context.  Consequently operational lookup can reconstruct a
structural singleton classification without assuming that the source path
was already typed.  This is the reverse lookup direction which fails for a
public store hiding a pair behind `Top`.
-/

namespace LambdaP.Original

/-! ## Every resolving path has its result singleton -/

/-- Promote a path already known to denote `x` to the exact context type of
`x`.  Runtime singleton conversion supplies `{p} <: {x}` and ordinary
widening supplies `{x} <: P`. -/
private theorem Path.StructCheck.at_precise_result
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {P : LambdaP.Original.Ty n}
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

/-- Static-aligned lookup reconstructs the singleton of its result in an
exact structural store.  The miss case is why the proof uses `Path.lookup`:
its recursive premise is exactly the `p.fst` path used by `sel_l`. -/
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

/-- Historical big-step reduction has the same singleton reconstruction
property, by the checked equivalence with static-aligned lookup. -/
theorem Store.StructPreciseTy.reduce_singleton
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Single (Path.var x))) :=
  hstore.lookup_singleton hr.toLookup

/-! ## Bidirectional lookup preservation for proper checks -/

/-- In an exact structural store, a reducing path and its result variable
support exactly the same proper structural checks.  The forward implication
is the general `reduce_to_var` theorem; exactness is used only in the reverse
direction to reconstruct the source singleton. -/
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

/-- Runtime equality transports every proper check between paths which
actually resolve.  Unlike `RuntimePathValid`, this statement says nothing
about stuck paths introduced by contextual congruence. -/
theorem Store.StructPreciseTy.runtimeEq_reduce_check_iff
    (hstore : Store.StructPreciseTy Gamma sigma)
    (heq : Path.RuntimeEq sigma p q)
    (hp : Path.reduce p sigma x) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty T) <->
      Path.StructCheck Gamma (Path.RuntimeEq sigma) q (Tau.ty T) := by
  have hq : Path.reduce q sigma x := (heq.reduce_iff x).mp hp
  exact (hstore.reduce_check_iff hp).trans
    (hstore.reduce_check_iff hq).symm

/-! ## Exact concrete-head boundary -/

/-- Head-only form of exact singleton pushback.  This is the smallest
remaining premise for progress: a singleton subtype to a concrete function
or pair must agree with the constructor stored at that exact location. -/
structure Store.StructPreciseSingletonHeadPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  function : forall {x : Fin n} {S : LambdaP.Original.Ty n}
      {U : LambdaP.Original.Ty (n + 1)},
    Store.StructPreciseTy Gamma sigma ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Fun S U)) ->
    exists A body, Store.Binds sigma x (Tm.abs A body)
  pair : forall {x : Fin n} {S : LambdaP.Original.Ty n}
      {a : Name} {k : Kind} {d : Tau (n + 1) k},
    Store.StructPreciseTy Gamma sigma ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Pair S a d)) ->
    exists (y : Fin n) (delta : Def n k),
      @Store.Binds n sigma x (@Tm.pair n k y a delta)

/-- Singleton head pushback gives the exact pair/function reflection used by
structural progress.  A checked variable always supplies its singleton
subtype by `widen`; no arbitrary check transport is used. -/
theorem Store.StructPreciseTy.headCheckReflection_of_singletonPushback
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma) :
    Store.HeadCheckReflection Gamma sigma := by
  constructor
  · intro x S U hfun
    exact hpush.function hstore (.widen hfun)
  · intro x S a k d hpair
    exact hpush.pair hstore (.widen hpair)

/-! ## Exact function pushback boundary -/

/-- The remaining subtype inversion, stated at its smallest exact-store
boundary.  The context entry is the closure's syntax-directed function type;
the premise is precisely the singleton suffix obtained by inverting a checked
path term at that location.

Unlike the old public-store property, there is no hidden public type `X`, no
second precise codomain, and no transitive `Fun A B <: X` suffix. -/
def Store.StructPreciseSingletonFunctionPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n}
      {S A : LambdaP.Original.Ty n}
      {U B : LambdaP.Original.Ty (n + 1)},
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
closure.  This is the property consumed by exact-store beta preservation. -/
def Store.StructExactFunctionPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n}
      {S A : LambdaP.Original.Ty n}
      {U B : LambdaP.Original.Ty (n + 1)}
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

/-- The singleton subtype boundary is sufficient: path-term inversion
returns exactly its premise. -/
theorem Store.StructPreciseSingletonFunctionPushback.to_exact
    (hpush : Store.StructPreciseSingletonFunctionPushback Gamma sigma) :
    Store.StructExactFunctionPushback Gamma sigma := by
  intro x S A U B body hstore hbind hctx hfun
  cases hfun.path_inversion rfl with
  | intro P hp hsingle hwf =>
      exact hpush hstore hctx hsingle

/-- Exact-store beta opening from the minimal pushback property.

Store inversion supplies the one codomain recorded in the context, so the
ambiguity present in `Store.StructPreciseFunctionPushback` disappears.
Dependent result opening is the already proved unconditional theorem. -/
theorem Store.StructPreciseTy.open_application_of_exactPushback
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p q : Path n} {x y : Fin n}
    {S : LambdaP.Original.Ty n}
    {U : LambdaP.Original.Ty (n + 1)}
    {A : LambdaP.Original.Ty n} {body : Tm (n + 1)}
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

/-!
This removes raw runtime conversion as an obstruction for every path that
participates in term evaluation.  Pair/function reflection still requires a
canonical-head argument for a variable checked through structural
subtyping; the remaining hard cases are abstract member bounds, not lookup
or path conversion.
-/

end LambdaP.Original
