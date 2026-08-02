import LambdaP.Repaired.StructuralNarrowing
import LambdaP.Repaired.StructuralValueInversion

/-!
A store invariant indexed by the exact structural introduction type of every
stored value.

`Store.StructTy` records the type at which a value happened to be checked at
allocation time.  That type may hide the value's constructor by subsumption.
`Store.StructPreciseTy` instead extends the context with the
`Tm.StructPrecise` type recovered by value inversion.  This makes concrete
store lookup syntax-directed while retaining the fully structural body and
well-formedness premises.

The precise context is also stable under machine allocation.  A suspended
`let` body was checked under the public type of its argument; after value
inversion, structural narrowing checks it under the precise type.  The
scoped runtime relation is then mapped into the concrete relation of the
extended store.
-/

namespace LambdaP.Repaired

/-! ## Exact structural stores -/

/-- A store and context built in lockstep from structural value-introduction
types.  The precise witness is stated in the pre-allocation scope and at the
runtime relation of the current store. -/
inductive Store.StructPreciseTy :
    {n : Nat} -> Ctx n -> Store n -> Prop where
| empty : Store.StructPreciseTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.StructPreciseTy Gamma sigma ->
    Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P ->
    (vv : v.IsValue) ->
    Store.StructPreciseTy (Gamma.snoc P) (Store.val sigma v vv)

/-- Forgetting exact introduction types yields the ordinary structural store
invariant at the same (now precise) context. -/
theorem Store.StructPreciseTy.toStructTy
    (h : Store.StructPreciseTy Gamma sigma) :
    Store.StructTy Gamma sigma := by
  induction h with
  | empty => exact .empty
  | val hstore hprecise vv ih =>
      exact .val ih hprecise.toStructCheck vv

/-- Every precise store location has aligned store and context bindings and
an exact introduction witness in the current intrinsic scope.  Older
witnesses are weakened together with the growing runtime relation. -/
theorem Store.StructPreciseTy.lookup_exists
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.StructPreciseTy Gamma sigma) (x : Fin n) :
    exists v P,
      Store.Binds sigma x v /\
      Ctx.Binds Gamma x P /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P := by
  induction h with
  | empty => exact Fin.elim0 x
  | @val n Gamma sigma v P hstore hprecise vv ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨v.weaken, P.weaken, Store.Binds.here, Ctx.Binds.here,
          hprecise.weaken_runtime P v vv⟩
      · obtain ⟨u, U, hu, hU, hpreciseU⟩ := ih y
        exact ⟨u.weaken, U.weaken, Store.Binds.there hu,
          Ctx.Binds.there hU, hpreciseU.weaken_runtime P v vv⟩

/-- Inversion from a concrete store lookup, with the precise witness already
transported to the full current store. -/
theorem Store.StructPreciseTy.of_store_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {v : Tm n}
    (h : Store.StructPreciseTy Gamma sigma)
    (hb : Store.Binds sigma x v) :
    exists P,
      Ctx.Binds Gamma x P /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P := by
  obtain ⟨u, P, hu, hP, hprecise⟩ := h.lookup_exists x
  cases hu.unique hb
  exact ⟨P, hP, hprecise⟩

/-- Conversely, each precise-context binding identifies the corresponding
stored value and its current-scope introduction witness. -/
theorem Store.StructPreciseTy.of_ctx_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {P : LambdaP.Repaired.Ty n}
    (h : Store.StructPreciseTy Gamma sigma)
    (hb : Ctx.Binds Gamma x P) :
    exists v,
      Store.Binds sigma x v /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P := by
  obtain ⟨v, U, hv, hU, hprecise⟩ := h.lookup_exists x
  cases hU.unique hb
  exact ⟨v, hv, hprecise⟩

/-- If both aligned lookups are supplied, their exact introduction type is
forced by context functionality. -/
theorem Store.StructPreciseTy.lookup
    (h : Store.StructPreciseTy Gamma sigma)
    (hs : Store.Binds sigma x v) (hc : Ctx.Binds Gamma x P) :
    Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P := by
  obtain ⟨U, hU, hv⟩ := h.of_store_binds hs
  cases hU.unique hc
  exact hv

/-- A precise store still supplies the value existence fact used by machine
progress. -/
theorem Store.StructPreciseTy.lookup_value
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.StructPreciseTy Gamma sigma) (x : Fin n) :
    exists v, Store.Binds sigma x v /\ v.IsValue := by
  obtain ⟨v, P, hv, hP, hprecise⟩ := h.lookup_exists x
  exact ⟨v, hv, hprecise.isValue⟩

/-! ## Precise structural machine states -/

/-- Structural state typing whose store context contains exact value
introduction types.  Continuations and the current term retain ordinary
structural checking, since evaluation may observe them through supertypes. -/
inductive State.PreciseStructTy : Ctx n -> State n ->
    LambdaP.Repaired.Ty n -> Prop where
| ok :
    Store.StructPreciseTy Gamma sigma ->
    Tm.Cont.StructTy Gamma sigma S k T ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) t S ->
    State.PreciseStructTy Gamma ⟨sigma, k, t⟩ T

/-- Forgetting store precision recovers the earlier structural state
invariant. -/
theorem State.PreciseStructTy.toStructTy
    (h : State.PreciseStructTy Gamma state T) :
    State.StructTy Gamma state T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .ok hstore.toStructTy hcont hterm

/-- Preservation for precise states has the same two intrinsic-scope cases
as `StructPreserve`: either the context is unchanged, or allocation appends
one exact introduction type. -/
inductive PreciseStructPreserve : Ctx n -> State m ->
    LambdaP.Repaired.Ty n -> Prop where
| same :
    State.PreciseStructTy Gamma state T ->
    PreciseStructPreserve Gamma state T
| extend :
    State.PreciseStructTy (Gamma.snoc P) state T.weaken ->
    PreciseStructPreserve Gamma state T

theorem PreciseStructPreserve.toStructPreserve
    (h : PreciseStructPreserve Gamma state T) :
    StructPreserve Gamma state T := by
  cases h with
  | same ht => exact .same ht.toStructTy
  | extend ht => exact .extend ht.toStructTy

/-! ## Allocation -/

/-- Identity is an exact renaming of a context to itself. -/
private theorem Renaming.structPrecise_identity (Gamma : Ctx n) :
    Renaming Gamma FinFun.id Gamma := by
  intro x T hx
  simpa only [Ty.rename_id] using hx

/-- After allocation, every equation from the scoped pre-allocation relation
is an equation in the concrete extended-store relation. -/
private theorem Path.RelHom.structPrecise_scoped_to_runtime
    {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue} :
    Path.RelHom (Path.ScopedLift (Path.RuntimeEq sigma))
      (Path.RuntimeEq (Store.val sigma v vv)) FinFun.id := by
  intro p q hpq
  simpa only [Path.rename_id] using hpq.to_runtime_extension

/-- Allocation preserves the precise structural state invariant.

The current value may have been checked at a public type `S`.  Value
inversion recovers its introduction type `P` and `P <: S`.  Narrowing changes
the suspended body from `Gamma,S` to `Gamma,P`; relation transport changes
the scoped pre-allocation runtime relation to the actual extended-store
relation.  The store and continuation are then extended under `P`. -/
theorem PreciseStructPreserve.lift
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {v : Tm n} {t : Tm (n + 1)}
    {T : LambdaP.Repaired.Ty n}
    (vv : v.IsValue)
    (h : State.PreciseStructTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, v⟩ T) :
    PreciseStructPreserve Gamma
      ⟨Store.val sigma v vv, Tm.Cont.weaken k, t⟩ T := by
  cases h with
  | ok hstore hcont hvalue =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              obtain ⟨P, hprecise, hsub⟩ := hvalue.value_inversion vv
              have hbodyNarrow := hbody.narrow hsub
              have hbodyRuntime := hbodyNarrow.renameExact
                (Renaming.structPrecise_identity (Gamma.snoc P))
                (Path.RelHom.structPrecise_scoped_to_runtime
                  (v := v) (vv := vv))
              apply PreciseStructPreserve.extend
              apply State.PreciseStructTy.ok
                (Store.StructPreciseTy.val hstore hprecise vv)
                (hrest.weaken_runtime (U := P) v vv)
              simpa only [Tm.rename_id, Ty.rename_id] using hbodyRuntime

/-- Packaging for the corresponding historical machine step. -/
theorem State.Step.precise_lift_preservation
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {v : Tm n} {t : Tm (n + 1)}
    {T : LambdaP.Repaired.Ty n} {vv : v.IsValue}
    (step : State.Step
      ⟨sigma, Tm.Frame.let t :: k, v⟩
      ⟨Store.val sigma v vv, Tm.Cont.weaken k, t⟩)
    (h : State.PreciseStructTy Gamma
      ⟨sigma, Tm.Frame.let t :: k, v⟩ T) :
    PreciseStructPreserve Gamma
      ⟨Store.val sigma v vv, Tm.Cont.weaken k, t⟩ T := by
  cases step with
  | lift vv => exact PreciseStructPreserve.lift vv h

end LambdaP.Repaired
