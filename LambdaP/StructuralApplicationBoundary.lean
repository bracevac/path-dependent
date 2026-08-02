import LambdaP.StructuralMachineInvariant

/-!
The application boundary for the fully structural runtime invariant.

As in the earlier deep checker, inversion retains an application's two
introduction premises and represents trailing subsumption by a polymorphic
transformer.  The structural system improves the dynamic side in two ways:

* the checked one-binder opening theorem is available, so no opening axiom is
  assumed;
* argument compatibility can be stated as the standard contravariant domain
  relation.  Reduction first checks the result location at the call-site
  domain, and structural subsumption then checks it at the closure's domain.

The dependent-result component remains a checking transformer rather than a
bare subtype premise.  The application introduction rule has no separate
well-formedness premise for `U.open q`, so turning a result subtype into term
subsumption would require an unjustified target-well-formedness assumption.
-/

namespace LambdaP

/-! ## Syntax-directed inversion -/

/-- Structural checking of a syntactic abstraction exposes its body type,
domain well-formedness, and the complete introduction-to-observation subtype
suffix. -/
theorem Tm.StructCheck.abs_inversion_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {v : Tm n} {T : LambdaP.Ty n}
    (h : Tm.StructCheck Gamma R v T) :
    forall {A : LambdaP.Ty n} {body : Tm (n + 1)},
      v = Tm.abs A body ->
      exists B,
        Tm.StructCheck (Gamma.snoc A) (Path.ScopedLift R) body B /\
        Tau.StructWf Gamma R (Tau.ty A) /\
        Tau.StructSub Gamma R
          (Tau.ty (Ty.Fun A B)) (Tau.ty T) := by
  induction h with
  | path hp =>
      intro A body heq
      cases heq
  | abs hbody hwf ih =>
      intro A body heq
      cases heq
      exact ⟨_, hbody, hwf, .refl⟩
  | app hp hq ihp ihq =>
      intro A body heq
      cases heq
  | pair hy hz =>
      intro A body heq
      cases heq
  | tpair hy hwf =>
      intro A body heq
      cases heq
  | «let» hs hwf ht ihs iht =>
      intro A body heq
      cases heq
  | typed ht hwf ih =>
      intro A body heq
      cases heq
  | sub ht hs hwf ih =>
      intro A body heq
      obtain ⟨B, hbody, hA, hbase⟩ := ih heq
      exact ⟨B, hbody, hA, .trans hbase hs⟩

theorem Tm.StructCheck.abs_inversion
    (h : Tm.StructCheck Gamma R (Tm.abs A body) T) :
    exists B,
      Tm.StructCheck (Gamma.snoc A) (Path.ScopedLift R) body B /\
      Tau.StructWf Gamma R (Tau.ty A) /\
      Tau.StructSub Gamma R
        (Tau.ty (Ty.Fun A B)) (Tau.ty T) :=
  h.abs_inversion_of_eq rfl

/-- Application inversion through trailing structural subsumption.  The
post-cast is polymorphic in the checked term and can therefore be applied to
the reduct after opening. -/
theorem Tm.StructCheck.app_inversion_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {u : Tm n} {T : LambdaP.Ty n}
    (h : Tm.StructCheck Gamma R u T) :
    forall {p q : Path n}, u = Tm.app p q ->
      exists S U,
        Tm.StructCheck Gamma R (Tm.path p) (Ty.Fun S U) /\
        Tm.StructCheck Gamma R (Tm.path q) S /\
        (forall {t : Tm n},
          Tm.StructCheck Gamma R t (U.open q) ->
          Tm.StructCheck Gamma R t T) := by
  induction h with
  | path hp =>
      intro p q heq
      cases heq
  | abs ht hwf ih =>
      intro p q heq
      cases heq
  | app hp hq ihp ihq =>
      intro p q heq
      cases heq
      exact ⟨_, _, hp, hq, fun ht => ht⟩
  | pair hy hz =>
      intro p q heq
      cases heq
  | tpair hy hwf =>
      intro p q heq
      cases heq
  | «let» hs hwf ht ihs iht =>
      intro p q heq
      cases heq
  | typed ht hwf ih =>
      intro p q heq
      cases heq
  | sub ht hs hwf ih =>
      intro p q heq
      obtain ⟨S, U, hp, hq, post⟩ := ih heq
      exact ⟨S, U, hp, hq,
        fun hresult => Tm.StructCheck.sub (post hresult) hs hwf⟩

theorem Tm.StructCheck.app_inversion
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {p q : Path n} {T : LambdaP.Ty n}
    (h : Tm.StructCheck Gamma R (Tm.app p q) T) :
    exists S U,
      Tm.StructCheck Gamma R (Tm.path p) (Ty.Fun S U) /\
      Tm.StructCheck Gamma R (Tm.path q) S /\
      (forall {t : Tm n},
        Tm.StructCheck Gamma R t (U.open q) ->
        Tm.StructCheck Gamma R t T) :=
  h.app_inversion_of_eq rfl

/-! ## Current-scope store lookup -/

/-- Store checking is available at the scope in which a cell is looked up;
old derivations are weakened together with the runtime relation. -/
theorem Store.StructTy.lookup_checked
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.StructTy Gamma sigma) (x : Fin n) :
    exists v T,
      Store.Binds sigma x v /\
      Ctx.Binds Gamma x T /\
      Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T := by
  induction h with
  | empty => exact Fin.elim0 x
  | @val n Gamma sigma v T hstore hcheck vv ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨v.weaken, T.weaken, Store.Binds.here, Ctx.Binds.here,
          hcheck.weaken_runtime T v vv⟩
      · obtain ⟨u, U, hu, hU, hcheckU⟩ := ih y
        exact ⟨u.weaken, U.weaken, Store.Binds.there hu,
          Ctx.Binds.there hU, hcheckU.weaken_runtime T v vv⟩

/-- Concrete lookup inversion for a structurally checked store. -/
theorem Store.StructTy.of_store_binds_checked
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {v : Tm n}
    (h : Store.StructTy Gamma sigma) (hb : Store.Binds sigma x v) :
    exists T,
      Ctx.Binds Gamma x T /\
      Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T := by
  obtain ⟨u, T, hu, hT, hcheck⟩ := h.lookup_checked x
  cases hu.unique hb
  exact ⟨T, hT, hcheck⟩

/-! ## Minimal call-signature compatibility -/

/-- The local semantic relation still missing between a resolving call-site
signature and the syntax-directed signature of the stored abstraction.

`X` is the public context type of the operator location.  Store inversion
and abstraction inversion establish `Fun A B <: X`; the contract relates
that actual signature to the call-site signature `Fun S U`.  Its domain
component is ordinary structural subtyping.  Its dependent-result component
is the weakest usable form: a transformer on any term checked at the opened
actual codomain. -/
def Store.StructAppCompatibility (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {p q : Path n} {x y : Fin n}
      {S A X : LambdaP.Ty n}
      {U B : LambdaP.Ty (n + 1)}
      {body : Tm (n + 1)},
    Store.StructTy Gamma sigma ->
    Path.reduce p sigma x ->
    Path.reduce q sigma y ->
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x X ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Fun A B)) (Tau.ty X) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U) ->
    Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path q) S ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty A) /\
      (forall {t : Tm n},
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t
          (B.rename (FinFun.openAt y)) ->
        Tm.StructCheck Gamma (Path.RuntimeEq sigma) t (U.open q))

/-- Structural lookup recovers the closure body.  Domain compatibility,
path replacement, and the proved term-opening theorem then check the
concrete reduct at the call-site introduction result. -/
theorem Store.StructTy.open_application
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p q : Path n} {x y : Fin n}
    {S : LambdaP.Ty n}
    {U : LambdaP.Ty (n + 1)}
    {A : LambdaP.Ty n} {body : Tm (n + 1)}
    (hstore : Store.StructTy Gamma sigma)
    (hcompat : Store.StructAppCompatibility Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (hfun : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U))
    (harg : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path q) S) :
    Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (body.open y) (U.open q) := by
  obtain ⟨X, hctx, hpublic⟩ := hstore.of_store_binds_checked hbind
  obtain ⟨B, hbody, hA, hactualPublic⟩ := hpublic.abs_inversion
  obtain ⟨hdom, hresult⟩ := hcompat hstore hp hq hbind hctx
    hactualPublic hfun harg
  have hargAtS : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var y)) S := harg.reduce_path hq
  have hargAtA : Tm.StructCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var y)) A :=
    Tm.StructCheck.sub hargAtS hdom hA
  have hopened := hbody.open_var_of_path_term
    (Path.RuntimeEq.isEquivCongr sigma) hargAtA
  exact hresult hopened

/-! ## Conditional application preservation -/

theorem StructPreserve.app
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n}
    {x y : Fin n} {A : LambdaP.Ty n}
    {body : Tm (n + 1)} {T : LambdaP.Ty n}
    (hcompat : Store.StructAppCompatibility Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (h : State.StructTy Gamma ⟨sigma, k, Tm.app p q⟩ T) :
    StructPreserve Gamma ⟨sigma, k, body.open y⟩ T := by
  cases h with
  | ok hstore hcont happ =>
      obtain ⟨S, U, hfun, harg, post⟩ := happ.app_inversion
      have hopened := hstore.open_application hcompat
        hp hq hbind hfun harg
      exact .same (.ok hstore hcont (post hopened))

/-- Full packaging for a machine step whose source is an application. -/
theorem State.Step.struct_app_preservation
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n} {target : State n}
    {T : LambdaP.Ty n}
    (hcompat : Store.StructAppCompatibility Gamma sigma)
    (step : State.Step ⟨sigma, k, Tm.app p q⟩ target)
    (h : State.StructTy Gamma ⟨sigma, k, Tm.app p q⟩ T) :
    StructPreserve Gamma target T := by
  cases step with
  | app hp hq hbind =>
      exact StructPreserve.app hcompat hp hq hbind h

end LambdaP
