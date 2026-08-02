import LambdaP.Original.DeepMachineInvariant
import LambdaP.Original.Canonical

/-!
Syntax-directed value inversion for the deep runtime checker.

`Tm.DeepCheck` deliberately admits trailing source subtyping and path
conversion.  As for the source judgment, those rules obscure the type
assigned by the value-introduction rule.  `Tm.DeepPrecise` retains that
introduction type while using the deep premises required for abstraction
bodies and type members.
-/

namespace LambdaP.Original

/-- The type assigned directly by a deep value-introduction rule. -/
inductive Tm.DeepPrecise : {n : Nat} -> (Gamma : Ctx n) ->
    Path.ConvRel n -> Tm n -> LambdaP.Original.Ty n -> Prop where
| abs :
    Tm.DeepCheck (Gamma.snoc S) (Path.ConvLift R) t T ->
    Tau.DeepWf Gamma R (Tau.ty S) ->
    Tm.DeepPrecise Gamma R (Tm.abs S t) (Ty.Fun S T)
| pair :
    Ctx.Binds Gamma y S ->
    Ctx.Binds Gamma z T ->
    Tm.DeepPrecise Gamma R (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Gamma y S ->
    Tau.DeepWf Gamma R (Tau.ty T) ->
    Tm.DeepPrecise Gamma R (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)

/-- A deeply precise term is a value. -/
theorem Tm.DeepPrecise.isValue
    (h : Tm.DeepPrecise Gamma R v P) : v.IsValue := by
  cases h <;> constructor

/-- Forgetting precision recovers the deep checking derivation. -/
theorem Tm.DeepPrecise.toDeepCheck
    (h : Tm.DeepPrecise Gamma R v P) :
    Tm.DeepCheck Gamma R v P := by
  cases h with
  | abs ht hwf => exact .abs ht hwf
  | pair hy hz => exact .pair hy hz
  | tpair hy hwf => exact .tpair hy hwf

/-- Deep precise value typing is stable under relation-respecting renaming. -/
theorem Tm.DeepPrecise.rename
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {v : Tm n} {P : LambdaP.Original.Ty n}
    (h : Tm.DeepPrecise Gamma R v P) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m}
        {R' : Path.ConvRel m},
      Renaming Gamma f Delta ->
      (forall {p q}, R p q -> R' (p.rename f) (q.rename f)) ->
      Tm.DeepPrecise Delta R' (v.rename f) (P.rename f) := by
  cases h with
  | abs ht hwf =>
      intro m f Delta R' rho hmap
      simpa only [Tm.rename, Ty.rename] using
        Tm.DeepPrecise.abs
          (ht.rename rho.ext (Path.ConvLift.rename hmap))
          (hwf.rename rho hmap)
  | pair hy hz =>
      intro m f Delta R' rho hmap
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.DeepPrecise.pair (rho hy) (rho hz)
  | tpair hy hwf =>
      intro m f Delta R' rho hmap
      simpa only [Tm.rename, Def.rename, LambdaP.Original.Ty.rename,
        Tau.rename, Path.rename, <- Tau.weaken_rename] using
        Tm.DeepPrecise.tpair (rho hy) (hwf.rename rho hmap)

/-- Runtime-store growth weakens a deep precise witness in lockstep with the
public context and the concrete runtime conversion relation. -/
theorem Tm.DeepPrecise.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {v : Tm n} {P : LambdaP.Original.Ty n}
    (h : Tm.DeepPrecise Gamma (Path.RuntimeEq sigma) v P)
    (S : LambdaP.Original.Ty n) (u : Tm n) (uv : u.IsValue) :
    Tm.DeepPrecise (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma u uv)) v.weaken P.weaken := by
  simpa only [Tm.weaken, Ty.weaken] using
    h.rename (Renaming.weaken (S := S))
      (fun hpq => by
        simpa only [Path.weaken] using hpq.weaken u uv)

/-- Value inversion for deep checking.  Every trailing deep-subsumption step
is accumulated after the syntax-directed introduction type. -/
theorem Tm.DeepCheck.value_inversion
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {v : Tm n} {T : LambdaP.Original.Ty n}
    (h : Tm.DeepCheck Gamma R v T) (hv : v.IsValue) :
    exists P,
      Tm.DeepPrecise Gamma R v P /\
      Tau.DeepSub Gamma R (Tau.ty P) (Tau.ty T) := by
  induction h with
  | path hp => cases hv
  | abs ht hwf ih =>
      exact ⟨_, Tm.DeepPrecise.abs ht hwf, .refl⟩
  | app hp hq ihp ihq => cases hv
  | pair hy hz =>
      exact ⟨_, Tm.DeepPrecise.pair hy hz, .refl⟩
  | tpair hy hwf =>
      exact ⟨_, Tm.DeepPrecise.tpair hy hwf, .refl⟩
  | «let» hs hwf ht ihs iht => cases hv
  | typed ht hwf ih => cases hv
  | sub ht hs hwf ih =>
      obtain ⟨P, hp, hP⟩ := ih hv
      exact ⟨P, hp, .trans hP hs⟩

/-! ## Store lookup inversion -/

/-- Every location of a deeply typed store has its public context type and
checking derivation, together with a syntax-directed value type below it.
All witnesses are stated in the current store scope. -/
theorem Store.DeepTy.lookup_exists
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.DeepTy Gamma sigma) (x : Fin n) :
    exists v T P,
      Store.Binds sigma x v /\
      Ctx.Binds Gamma x T /\
      Tm.DeepCheck Gamma (Path.RuntimeEq sigma) v T /\
      Tm.DeepPrecise Gamma (Path.RuntimeEq sigma) v P /\
      Tau.DeepSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty P) (Tau.ty T) := by
  induction h with
  | empty => exact Fin.elim0 x
  | @val n Gamma sigma v T hstore hcheck vv ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · obtain ⟨P, hprecise, hsub⟩ := hcheck.value_inversion vv
        exact ⟨v.weaken, T.weaken, P.weaken,
          Store.Binds.here, Ctx.Binds.here,
          hcheck.weaken_runtime T v vv,
          hprecise.weaken_runtime T v vv,
          hsub.weaken_runtime T v vv⟩
      · obtain ⟨u, U, P, hu, hU, hcheckU, hprecise, hsub⟩ := ih y
        exact ⟨u.weaken, U.weaken, P.weaken,
          Store.Binds.there hu, Ctx.Binds.there hU,
          hcheckU.weaken_runtime T v vv,
          hprecise.weaken_runtime T v vv,
          hsub.weaken_runtime T v vv⟩

/-- Inverting a concrete store lookup recovers the public type recorded at
that location and both its public and syntax-directed deep derivations. -/
theorem Store.DeepTy.of_store_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {v : Tm n}
    (h : Store.DeepTy Gamma sigma) (hb : Store.Binds sigma x v) :
    exists T P,
      Ctx.Binds Gamma x T /\
      Tm.DeepCheck Gamma (Path.RuntimeEq sigma) v T /\
      Tm.DeepPrecise Gamma (Path.RuntimeEq sigma) v P /\
      Tau.DeepSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty P) (Tau.ty T) := by
  obtain ⟨u, T, P, hu, hT, hcheck, hprecise, hsub⟩ :=
    h.lookup_exists x
  cases hu.unique hb
  exact ⟨T, P, hT, hcheck, hprecise, hsub⟩

/-- Inverting a public context lookup recovers the matching stored value and
the same precise factorization. -/
theorem Store.DeepTy.of_ctx_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {T : LambdaP.Original.Ty n}
    (h : Store.DeepTy Gamma sigma) (hb : Ctx.Binds Gamma x T) :
    exists v P,
      Store.Binds sigma x v /\
      Tm.DeepCheck Gamma (Path.RuntimeEq sigma) v T /\
      Tm.DeepPrecise Gamma (Path.RuntimeEq sigma) v P /\
      Tau.DeepSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty P) (Tau.ty T) := by
  obtain ⟨v, U, P, hv, hU, hcheck, hprecise, hsub⟩ :=
    h.lookup_exists x
  cases hU.unique hb
  exact ⟨v, P, hv, hcheck, hprecise, hsub⟩

/-! ## Canonical heads for source-only suffixes -/

/-- If the suffix after deep value inversion is ordinary source subtyping,
a function observation has the expected abstraction canonical form. -/
theorem Tm.DeepPrecise.fun_canonical_source
    (hp : Tm.DeepPrecise Gamma R v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Fun S T))) :
    exists A body B,
      v = Tm.abs A body /\
      P = Ty.Fun A B /\
      Tm.DeepCheck (Gamma.snoc A) (Path.ConvLift R) body B /\
      Tau.DeepWf Gamma R (Tau.ty A) := by
  cases hp with
  | abs ht hwf => exact ⟨_, _, _, rfl, rfl, ht, hwf⟩
  | pair hy hz => exact (Tau.Sub.pair_not_fun hs).elim
  | tpair hy hwf => exact (Tau.Sub.pair_not_fun hs).elim

/-- The corresponding source-only pair canonical form retains the member
label and distinguishes term and type definitions. -/
theorem Tm.DeepPrecise.pair_canonical_source
    (hp : Tm.DeepPrecise Gamma R v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Pair S a d))) :
    (exists y z,
      v = Tm.pair y a (Def.val z) /\
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken))) \/
    (exists y U,
      v = Tm.pair y a (Def.type U) /\
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.intv U U).weaken) := by
  cases hp with
  | abs ht hwf => exact (Tau.Sub.fun_not_pair hs).elim
  | pair hy hz =>
      have hlabel := Tau.Sub.pair_label hs
      subst a
      exact .inl ⟨_, _, rfl, rfl⟩
  | tpair hy hwf =>
      have hlabel := Tau.Sub.pair_label hs
      subst a
      exact .inr ⟨_, _, rfl, rfl⟩

/-!
These canonical lemmas intentionally take `Tau.Sub`, not arbitrary
`Tau.DeepSub`.  A `Tau.DeepConv.replace` step is generated from an untyped
abstract relation `R`.  In particular it may relate two singleton paths with
unrelated source types.  Source selection can enter a singleton through a
lower abstract bound, conversion can replace that path, and source widening
can leave the singleton at the unrelated path's type.  Consequently the
source `Tau.MayHead` interpretation is not preserved by arbitrary deep
conversion.  Extending canonical forms to the full suffix requires a typed
conversion environment, not another syntactic inversion lemma.
-/

end LambdaP.Original
