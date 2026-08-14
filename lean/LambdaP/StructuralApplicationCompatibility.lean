import LambdaP.StructuralApplicationBoundary
import LambdaP.StructuralPathSubstitution
import LambdaP.StructuralRefinedProgress
import LambdaP.StructuralValueInversion

/-!
The application obligation for the direct syntactic approach, factored where
operator has already resolved to a store location.

There is no unchecked path-validity assumption here.  In particular, the
counterexample in `StructuralRuntimePathValidity` shows that a reducing path
need not inherit every check of its result variable.  Applications only use
the valid direction, proved by `Tm.StructCheck.reduce_path`: an already
checked operator path may be replaced by the variable to which it reduces.

The first theorem below shows that this replacement removes all composite
path machinery from `Store.StructAppCompatibility`.  What remains is a
function-specific pushback/canonical-forms property for a public store
location.  The final section also records why co-resolution settles equality
of the two opened result *types*, but does not by itself provide the
term-checking transformer in the compatibility contract: structural term
subsumption additionally asks for well-formedness of its target.
-/

namespace LambdaP

/-! ## Reduction to a local function-reflection property -/

/-- `StructAppCompatibility` after the operator has been reduced to its
location.  This formulation deliberately retains the argument path: its
reduction is used both to open the closure body at the runtime location and
to compare that opening with the statically mentioned path. -/
def Store.StructFunctionReflection (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {q : Path n} {x y : Fin n}
      {S A X : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)}
      {body : Tm (n + 1)},
    Store.StructTy Gamma sigma ->
    Path.reduce q sigma y ->
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x X ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun A B)) (Tau.ty X) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) (Ty.Fun S U) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path q) S ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      (forall {t : Tm n},
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t
          (B.rename (FinFun.openAt y)) ->
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t (U.open q))

/-- The existing application contract is exactly function reflection at the
resolved variable.  Thus no reverse preservation theorem for arbitrary
reducing paths is needed at the application boundary. -/
theorem Store.structAppCompatibility_iff_functionReflection :
    Store.StructAppCompatibility Gamma sigma <->
      Store.StructFunctionReflection Gamma sigma := by
  constructor
  · intro hcompat q x y S A X U B body hstore hq hbind hctx hactual
      hfun harg
    exact hcompat hstore Path.reduce.var hq hbind hctx hactual hfun harg
  · intro hreflect p q x y S A X U B body hstore hp hq hbind hctx
      hactual hfun harg
    exact hreflect hstore hq hbind hctx hactual
      (hfun.reduce_path hp) harg

/-! ## What co-resolution proves about dependent results -/

/-- Opening a dependent result at a reducing argument path is structurally
convertible to opening it at the result location.  This is the complete
type-level contribution of co-resolution to application preservation. -/
theorem Tau.StructConv.open_result_runtime
    {n : Nat} {sigma : Store n} {q : Path n} {y : Fin n}
    {U : LambdaP.Ty (n + 1)}
    (hq : Path.reduce q sigma y) :
    Tau.StructConv (Path.RuntimeEq sigma)
      (Tau.ty (U.rename (FinFun.openAt y))) (Tau.ty (U.open q)) := by
  change Tau.StructConv (Path.RuntimeEq sigma)
    ((Tau.ty U).rename (FinFun.openAt y)) ((Tau.ty U).open q)
  rw [Tau.rename_openAt_eq_open_var]
  exact Tau.StructConv.replace (R := Path.RuntimeEq sigma)
    (template := Tau.ty U) (Path.RuntimeEq.of_reduce hq).symm

/-- The corresponding cast on terms is available once the target opening is
known well-formed.  `Tm.StructCheck.sub` needs this extra premise; raw
co-resolution and `Tau.StructConv` contain no typing evidence from which it
could be recovered. -/
theorem Tm.StructCheck.cast_open_result_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {q : Path n} {y : Fin n} {U : LambdaP.Ty (n + 1)}
    {t : Tm n}
    (hq : Path.reduce q sigma y)
    (hU : Tau.StructWf Gamma (Path.RuntimeEq sigma)
      (Tau.ty (U.open q)))
    (ht : Tm.StructCheck Gamma (Path.RuntimeEq sigma) t
      (U.rename (FinFun.openAt y))) :
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) t (U.open q) :=
  Tm.StructCheck.sub ht
    (Tau.StructSub.conv (Tau.StructConv.open_result_runtime hq)) hU

/-! ## The observation-sized premise actually used by beta reduction -/

/-- A weaker form of function reflection in which `B` is tied to the
syntax-directed type of the stored abstraction.  The original contract
quantifies over every `B` satisfying `Fun A B <: X`; store inversion only
needs the particular `B` obtained from the abstraction introduction rule.
-/
def Store.StructPreciseFunctionReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {q : Path n} {x y : Fin n}
      {S A X : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)}
      {body : Tm (n + 1)},
    Store.StructTy Gamma sigma ->
    Path.reduce q sigma y ->
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x X ->
    Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
      (Tm.abs A body) (Ty.Fun A B) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun A B)) (Tau.ty X) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) (Ty.Fun S U) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path q) S ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      (forall {t : Tm n},
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t
          (B.rename (FinFun.openAt y)) ->
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t (U.open q))

/-- The genuinely function-specific part of the obligation.  It says that
observing the resolved closure location at `Fun S U` pushes back through its
public type to the usual contravariant domain and covariant dependent
codomain premises.  Unlike `StructPreciseFunctionReflection`, it mentions
neither the argument nor operational opening.

Proving this directly from `Store.StructTy` is the public-widening/canonical
forms problem for this approach.  Abstract members are the
non-syntax-directed case: their
nonempty-bounds premise should connect the lower function signature to the
upper one, but an arbitrary structural transitivity suffix hides that
connection. -/
def Store.StructPreciseFunctionPushback
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n}
      {S A X : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)}
      {body : Tm (n + 1)},
    Store.StructTy Gamma sigma ->
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x X ->
    Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
      (Tm.abs A body) (Ty.Fun A B) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun A B)) (Tau.ty X) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) (Ty.Fun S U) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U)

/-- The non-function-specific dependent substitution/opening principle which
turns a codomain subtype below the formal parameter into the checking
transformer used by beta preservation.  This is standard dependent
substitution plus the final co-resolution conversion `U[y] = U[q]`; it is
kept separate from store function reflection so that the two proof problems
are not conflated. -/
def Store.StructResultOpening (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {q : Path n} {y : Fin n} {S : LambdaP.Ty n}
      {B U : LambdaP.Ty (n + 1)} {t : Tm n},
    Path.reduce q sigma y ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path q) S ->
    Tau.StructWf Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun S U)) ->
    Tau.StructSub (Gamma.snoc S)
      (Path.ScopedLift (Path.RuntimeEq sigma))
      (Tau.ty B) (Tau.ty U) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) t
      (B.rename (FinFun.openAt y)) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) t (U.open q)

/-- `StructResultOpening` is unconditional.  Dependent substitution opens
the observed codomain's well-formedness directly at the checked argument
path.  The codomain subtype is opened at the runtime result variable, and
co-resolution converts only its target from `U[y]` to `U[q]`. -/
theorem Store.structResultOpening (Gamma : Ctx n) (sigma : Store n) :
    Store.StructResultOpening Gamma sigma := by
  intro q y S B U t hq harg hfunWf hcod ht
  have hqS : Path.StructCheck Gamma (Path.RuntimeEq sigma) q
      (Tau.ty S) := by
    cases harg.path_inversion rfl with
    | intro precise hcheck hsingle hwf =>
        exact Path.StructCheck.promote hcheck hsingle
  have hyArg : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var y)) S := harg.reduce_path hq
  have hyS : Path.StructCheck Gamma (Path.RuntimeEq sigma) (Path.var y)
      (Tau.ty S) := by
    cases hyArg.path_inversion rfl with
    | intro precise hcheck hsingle hwf =>
        exact Path.StructCheck.promote hcheck hsingle
  cases hfunWf with
  | «fun» hS hU =>
      have htarget : Tau.StructWf Gamma (Path.RuntimeEq sigma)
          (Tau.ty (U.open q)) :=
        hU.open_path (Path.RuntimeEq.isEquivCongr sigma) hqS
      have hopen := hcod.open_var
        (Path.RuntimeEq.isEquivCongr sigma) hyS
      have hresult : Tau.StructSub Gamma (Path.RuntimeEq sigma)
          (Tau.ty (B.rename (FinFun.openAt y)))
          (Tau.ty (U.open q)) :=
        Tau.StructSub.trans hopen
          (Tau.StructSub.conv (Tau.StructConv.open_result_runtime hq))
      exact Tm.StructCheck.sub ht hresult htarget

/-- Function pushback and ordinary dependent result opening together imply
the precise compatibility premise used by the machine proof. -/
theorem Store.StructPreciseFunctionPushback.and_resultOpening
    (hpush : Store.StructPreciseFunctionPushback Gamma sigma)
    (hopen : Store.StructResultOpening Gamma sigma) :
    Store.StructPreciseFunctionReflection Gamma sigma := by
  intro q x y S A X U B body hstore hq hbind hctx hprecise hactual
    hfun harg
  obtain ⟨hdom, hcod⟩ := hpush hstore hbind hctx hprecise hactual hfun
  have hfunWf : Tau.StructWf Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun S U)) := by
    cases hfun.path_inversion rfl with
    | intro precise hcheck hsub hwf => exact hwf
  exact ⟨hdom, fun ht => hopen hq harg hfunWf hcod ht⟩

/-- Once dependent path substitution is available, precise function
reflection reduces entirely to function pushback through the public store
type. -/
theorem Store.StructPreciseFunctionPushback.to_preciseFunctionReflection
    (hpush : Store.StructPreciseFunctionPushback Gamma sigma) :
    Store.StructPreciseFunctionReflection Gamma sigma :=
  hpush.and_resultOpening (Store.structResultOpening Gamma sigma)

/-- The old compatibility contract implies the precise, observation-sized
one.  The converse is intentionally not claimed because the old contract's
codomain `B` is not required to be the stored body's introduction type. -/
theorem Store.StructAppCompatibility.to_preciseFunctionReflection
    (hcompat : Store.StructAppCompatibility Gamma sigma) :
    Store.StructPreciseFunctionReflection Gamma sigma := by
  intro q x y S A X U B body hstore hq hbind hctx hprecise hactual
    hfun harg
  exact hcompat hstore Path.reduce.var hq hbind hctx hactual hfun harg

/-- Beta opening needs only precise function reflection.  Structural store
inversion supplies the precise abstraction type, reduction replaces both
paths by their result locations, and the previously proved one-binder
opening theorem checks the concrete reduct. -/
theorem Store.StructTy.open_application_of_preciseFunctionReflection
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p q : Path n} {x y : Fin n}
    {S : LambdaP.Ty n}
    {U : LambdaP.Ty (n + 1)}
    {A : LambdaP.Ty n} {body : Tm (n + 1)}
    (hstore : Store.StructTy Gamma sigma)
    (hreflect : Store.StructPreciseFunctionReflection Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (hfun : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U))
    (harg : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path q) S) :
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (body.open y) (U.open q) := by
  obtain ⟨X, P, hctx, hpublic, hprecise, hactualPublic⟩ :=
    hstore.of_store_binds hbind
  cases hprecise with
  | abs hbody hA =>
      obtain ⟨hdom, hresult⟩ := hreflect hstore hq hbind hctx
        (Tm.StructPrecise.abs hbody hA) hactualPublic
        (hfun.reduce_path hp) harg
      have hargAtS : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
          (Tm.path (Path.var y)) S := harg.reduce_path hq
      have hargAtA : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
          (Tm.path (Path.var y)) A :=
        Tm.StructCheck.sub hargAtS hdom hA
      have hopened := hbody.open_var_of_path_term
        (Path.RuntimeEq.isEquivCongr sigma) hargAtA
      exact hresult hopened

end LambdaP
