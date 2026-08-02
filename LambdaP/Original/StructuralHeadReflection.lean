import LambdaP.Original.StructuralRuntimePathValidity
import LambdaP.Original.StructuralRefinedProgress

/-!
Concrete-head reflection for structural path observations.

Full transport of `Path.StructCheck` along runtime equality is stronger than
the operational semantics needs, and `StructuralRuntimePathValidity` gives a
typed-store counterexample to it.  Projection and application inspect only
two concrete observations: a pair (including its label and member kind), or
an abstraction.  The predicates below record exactly those observations at
an already resolved store variable.

The source judgment already has this property for every historically typed
store.  The proof factors a cell through its precise introduction type and
uses the source canonical-forms lemmas.  Extending that result from
`Path.Ty` to arbitrary `Path.StructCheck` is the residual semantic obligation:
runtime conversion and structural transitivity can expose a concrete head
through singleton and abstract-member chains.
-/

namespace LambdaP.Original

/-! ## Observation-sized structural invariant -/

/-- A structurally observed function at a store variable is represented by
an abstraction in that cell.  No claim is made about its domain or codomain;
beta preservation needs the stronger compatibility relation in
`StructuralApplicationCompatibility`. -/
def Store.FunctionCheckReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Original.Ty n}
      {U : LambdaP.Original.Ty (n + 1)},
    Path.StructCheck Gamma (Path.RuntimeEq sigma) (.var x)
      (Tau.ty (Ty.Fun S U)) ->
    exists A body, Store.Binds sigma x (Tm.abs A body)

/-- The two concrete heads inspected by the machine and path evaluator.
`pair` is the existing label-and-kind-sensitive progress premise. -/
structure Store.HeadCheckReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  function : Store.FunctionCheckReflection Gamma sigma
  pair : Store.PairCheckReflection Gamma sigma

/-- Allocation-indexed structural store typing which retains only concrete
head reflection, rather than validity of every runtime equation at every
type.  The extension premise is exactly the local proof obligation generated
by `lift`; no reverse check-transport principle is built in. -/
inductive Store.HeadReflectingStructTy :
    {n : Nat} -> Ctx n -> Store n -> Prop where
| empty : Store.HeadReflectingStructTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.HeadReflectingStructTy Gamma sigma ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ->
    (vv : v.IsValue) ->
    Store.HeadCheckReflection
      (Gamma.snoc T) (Store.val sigma v vv) ->
    Store.HeadReflectingStructTy
      (Gamma.snoc T) (Store.val sigma v vv)

theorem Store.HeadReflectingStructTy.toStructTy
    (h : Store.HeadReflectingStructTy Gamma sigma) :
    Store.StructTy Gamma sigma := by
  induction h with
  | empty => exact .empty
  | val hstore hcheck vv hreflect ih => exact .val ih hcheck vv

theorem Store.HeadReflectingStructTy.headCheckReflection
    (h : Store.HeadReflectingStructTy Gamma sigma) :
    Store.HeadCheckReflection Gamma sigma := by
  cases h with
  | empty =>
      constructor
      · intro x
        exact Fin.elim0 x
      · intro x
        exact Fin.elim0 x
  | val hstore hcheck vv hreflect => exact hreflect

/-- A checked operator path may first be replaced by its result variable;
function reflection then supplies the closure required by the machine. -/
theorem Store.HeadCheckReflection.function_of_reduce
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n}
    {S : LambdaP.Original.Ty n} {U : LambdaP.Original.Ty (n + 1)}
    (h : Store.HeadCheckReflection Gamma sigma)
    (hr : Path.reduce p sigma x)
    (hp : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Fun S U))) :
    exists A body, Store.Binds sigma x (Tm.abs A body) :=
  h.function (hp.reduce_to_var hr)

/-- The corresponding pair fact is exactly the local fact needed by path
progress after replacing a checked path by its result variable. -/
theorem Store.HeadCheckReflection.pair_of_reduce
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {S : LambdaP.Original.Ty n}
    {a : Name} {k : Kind} {d : Tau (n + 1) k}
    (h : Store.HeadCheckReflection Gamma sigma)
    (hr : Path.reduce p sigma x)
    (hp : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
      (Tau.ty (Ty.Pair S a d))) :
    exists (y : Fin n) (delta : Def n k),
      @Store.Binds n sigma x (@Tm.pair n k y a delta) :=
  h.pair (hp.reduce_to_var hr)

/-- The pair half of head reflection discharges the residual premise in the
refined path-progress development. -/
theorem Store.HeadCheckReflection.refinedPairSimulation
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (hhead : Store.HeadCheckReflection Gamma sigma)
    (hrefined : Store.RefinedTy Gamma sigma) :
    Store.RefinedPairSimulation Gamma sigma :=
  ⟨hrefined, hhead.pair⟩

/-! ## What historical store typing already proves -/

/-- Function reflection restricted to the original precise path judgment. -/
def Store.SourceFunctionReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Original.Ty n}
      {U : LambdaP.Original.Ty (n + 1)},
    Path.Ty Gamma (.var x) (Tau.ty (Ty.Fun S U)) ->
    exists A body, Store.Binds sigma x (Tm.abs A body)

/-- Pair reflection restricted to the original precise path judgment. -/
def Store.SourcePairReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Original.Ty n} {a : Name}
      {k : Kind} {d : Tau (n + 1) k},
    Path.Ty Gamma (.var x) (Tau.ty (Ty.Pair S a d)) ->
    exists (y : Fin n) (delta : Def n k),
      @Store.Binds n sigma x (@Tm.pair n k y a delta)

/-- Source-level counterpart of `HeadCheckReflection`. -/
structure Store.SourceHeadReflection
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  function : Store.SourceFunctionReflection Gamma sigma
  pair : Store.SourcePairReflection Gamma sigma

/-- Public historical store typing reflects every source-observed function
head.  Subsumption in a store cell is handled by precise value inversion. -/
theorem Store.Ty.sourceFunctionReflection
    (hstore : Store.Ty Gamma sigma) :
    Store.SourceFunctionReflection Gamma sigma := by
  intro x S U hx
  cases hx with
  | var hctx =>
      obtain ⟨v, P, hbind, hprecise, hpublic, hsub⟩ :=
        hstore.toRefined.of_ctx_binds hctx
      obtain ⟨A, body, B, hv, hP, hbody, hA⟩ :=
        hprecise.fun_canonical hsub
      subst v
      exact ⟨A, body, hbind⟩

/-- Public historical store typing also reflects source-observed pair label
and member kind. -/
theorem Store.Ty.sourcePairReflection
    (hstore : Store.Ty Gamma sigma) :
    Store.SourcePairReflection Gamma sigma := by
  intro x S a k d hx
  cases hx with
  | var hctx =>
      obtain ⟨v, P, hbind, hprecise, hpublic, hsub⟩ :=
        hstore.toRefined.of_ctx_binds hctx
      obtain ⟨y, delta, hv⟩ := hprecise.pair_canonical_kind hsub
      subst v
      exact ⟨y, delta, hbind⟩

theorem Store.Ty.sourceHeadReflection
    (hstore : Store.Ty Gamma sigma) :
    Store.SourceHeadReflection Gamma sigma :=
  ⟨hstore.sourceFunctionReflection, hstore.sourcePairReflection⟩

/-! ## The opaque-allocation counterexample is accepted -/

namespace StructuralRuntimePathValidity.Counterexample

theorem GammaY_onlyTop : Ctx.OnlyTop GammaY := by
  intro z T hb
  cases hb with
  | here => rfl
  | there hb => cases hb

theorem sigmaY_headCheckReflection :
    Store.HeadCheckReflection GammaY sigmaY := by
  constructor
  · intro z S U hz
    exact (hz.onlyTop GammaY_onlyTop).2.elim
  · intro z S a k d hz
    exact (hz.onlyTop GammaY_onlyTop).2.elim

/-- Although this store refutes arbitrary check transport along runtime
equality, no variable in its all-`Top` context can be structurally observed
at a concrete function type. -/
theorem functionCheckReflection :
    Store.FunctionCheckReflection Gamma sigma := by
  intro z S U hz
  exact (hz.onlyTop context_onlyTop).2.elim

/-- Nor can a variable be structurally observed at a concrete pair type.
Thus hiding the pair behind `Top` remains legal. -/
theorem pairCheckReflection :
    Store.PairCheckReflection Gamma sigma := by
  intro z S a k d hz
  exact (hz.onlyTop context_onlyTop).2.elim

/-- Concrete-head reflection is strictly more permissive than full runtime
path validity: the same checked store satisfies the former and refutes the
latter. -/
theorem headCheckReflection_but_not_runtimePathValid :
    Store.HeadCheckReflection Gamma sigma /\
      ¬ Store.StructTy.RuntimePathValid Gamma sigma := by
  refine ⟨⟨functionCheckReflection, pairCheckReflection⟩, ?_⟩
  exact runtimePathValid_counterexample.2

/-- Unlike the full runtime-valid store invariant, the observation-sized
allocation invariant admits both opaque allocations in the counterexample. -/
theorem store_headReflectingStructTy :
    Store.HeadReflectingStructTy Gamma sigma := by
  apply Store.HeadReflectingStructTy.val
  · apply Store.HeadReflectingStructTy.val
    · exact .empty
    · exact Tm.StructCheck.of_source y_top_typing _
    · exact sigmaY_headCheckReflection
  · exact Tm.StructCheck.of_source x_top_typing _
  · exact ⟨functionCheckReflection, pairCheckReflection⟩

end StructuralRuntimePathValidity.Counterexample

/-!
The source theorem above is intentionally not promoted to
`Store.HeadCheckReflection`: `Path.StructCheck` adds runtime conversion,
singleton promotion, and structural subtyping.  Proving that those rules
preserve just the two concrete observations requires a possible-types
interpretation of resolving term and type members (including the
nonempty-bound premises).  The opaque-`Top` example proves that asking for
all checks to transport is unnecessary, while the lemmas in this file give
the exact weaker target needed for progress.
-/

end LambdaP.Original
