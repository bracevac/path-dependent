import LambdaP.Repaired.StructuralMachineInvariant
import LambdaP.Repaired.Canonical

/-!
Syntax-directed value inversion for the fully structural runtime checker.

`Tm.StructCheck` admits structural subsumption, so a value's public type need
not expose its introduction form.  `Tm.StructPrecise` retains that form while
using the structural premises required for abstraction bodies and type
members.  The store lemmas return every witness in the current intrinsic
scope; older cells are weakened together with the runtime relation.
-/

namespace LambdaP.Repaired

/-- The type assigned directly by a structural value-introduction rule. -/
inductive Tm.StructPrecise : {n : Nat} -> (Gamma : Ctx n) ->
    (R : Path n -> Path n -> Prop) -> Tm n ->
    LambdaP.Repaired.Ty n -> Prop where
| abs :
    Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T ->
    Tau.StructWf Gamma R (Tau.ty S) ->
    Tm.StructPrecise Gamma R (Tm.abs S t) (Ty.Fun S T)
| pair :
    Ctx.Binds Gamma y S ->
    Ctx.Binds Gamma z T ->
    Tm.StructPrecise Gamma R (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Gamma y S ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructPrecise Gamma R (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)

theorem Tm.StructPrecise.isValue
    (h : Tm.StructPrecise Gamma R v P) : v.IsValue := by
  cases h <;> constructor

/-- Forgetting precision recovers structural checking. -/
theorem Tm.StructPrecise.toStructCheck
    (h : Tm.StructPrecise Gamma R v P) :
    Tm.StructCheck Gamma R v P := by
  cases h with
  | abs ht hwf => exact .abs ht hwf
  | pair hy hz => exact .pair hy hz
  | tpair hy hwf => exact .tpair hy hwf

/-- Exact relation-respecting renaming for structural precise values. -/
theorem Tm.StructPrecise.renameExact
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {v : Tm n} {P : LambdaP.Repaired.Ty n}
    (h : Tm.StructPrecise Gamma R v P) :
    ∀ {m : Nat} {f : FinFun n m} {Delta : Ctx m}
        {E : Path m -> Path m -> Prop},
      Renaming Gamma f Delta ->
      Path.RelHom R E f ->
      Tm.StructPrecise Delta E (v.rename f) (P.rename f) := by
  cases h with
  | abs ht hwf =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename] using
        Tm.StructPrecise.abs
          (ht.renameExact rho.ext hrel.scoped)
          (hwf.renameExact rho hrel)
  | pair hy hz =>
      intro m f Delta E rho hrel
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.StructPrecise.pair (rho hy) (rho hz)
  | tpair hy hwf =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Def.rename, LambdaP.Repaired.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.StructPrecise.tpair (rho hy) (hwf.renameExact rho hrel)

/-- Runtime-store growth weakens the precise witness in lockstep with its
public context and concrete runtime path relation. -/
theorem Tm.StructPrecise.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {v : Tm n} {P : LambdaP.Repaired.Ty n}
    (h : Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P)
    (S : LambdaP.Repaired.Ty n) (u : Tm n) (uv : u.IsValue) :
    Tm.StructPrecise (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma u uv)) v.weaken P.weaken := by
  simpa only [Tm.weaken, Ty.weaken] using
    h.renameExact (Renaming.weaken (S := S))
      (Path.RelHom.runtime_weaken u uv)

/-! ## Value inversion -/

/-- Every structural checking derivation of a value factors through its
syntax-directed introduction type.  Trailing structural subsumption is
accumulated in the final witness. -/
theorem Tm.StructCheck.value_inversion
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {v : Tm n} {T : LambdaP.Repaired.Ty n}
    (h : Tm.StructCheck Gamma R v T) (hv : v.IsValue) :
    ∃ P,
      Tm.StructPrecise Gamma R v P ∧
      Tau.StructSub Gamma R (Tau.ty P) (Tau.ty T) := by
  induction h with
  | path hp => cases hv
  | abs ht hwf ih =>
      exact ⟨_, Tm.StructPrecise.abs ht hwf, .refl⟩
  | app hp hq ihp ihq => cases hv
  | pair hy hz =>
      exact ⟨_, Tm.StructPrecise.pair hy hz, .refl⟩
  | tpair hy hwf =>
      exact ⟨_, Tm.StructPrecise.tpair hy hwf, .refl⟩
  | «let» hs hwf ht ihs iht => cases hv
  | typed ht hwf ih => cases hv
  | sub ht hs hwf ih =>
      obtain ⟨P, hp, hP⟩ := ih hv
      exact ⟨P, hp, .trans hP hs⟩

/-! ## Store lookup inversion -/

/-- Every location of a structurally typed store has public and precise
checking witnesses in the current store scope. -/
theorem Store.StructTy.lookup_exists
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (h : Store.StructTy Gamma sigma) (x : Fin n) :
    ∃ v T P,
      Store.Binds sigma x v ∧
      Ctx.Binds Gamma x T ∧
      Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ∧
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P ∧
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
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

/-- Inverting a concrete store lookup recovers the aligned public context
type and its precise structural factorization. -/
theorem Store.StructTy.of_store_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {v : Tm n}
    (h : Store.StructTy Gamma sigma) (hb : Store.Binds sigma x v) :
    ∃ T P,
      Ctx.Binds Gamma x T ∧
      Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ∧
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P ∧
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty P) (Tau.ty T) := by
  obtain ⟨u, T, P, hu, hT, hcheck, hprecise, hsub⟩ :=
    h.lookup_exists x
  cases hu.unique hb
  exact ⟨T, P, hT, hcheck, hprecise, hsub⟩

/-- Inverting a public context lookup recovers the matching stored value and
the same current-scope factorization. -/
theorem Store.StructTy.of_ctx_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {x : Fin n} {T : LambdaP.Repaired.Ty n}
    (h : Store.StructTy Gamma sigma) (hb : Ctx.Binds Gamma x T) :
    ∃ v P,
      Store.Binds sigma x v ∧
      Tm.StructCheck Gamma (Path.RuntimeEq sigma) v T ∧
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P ∧
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty P) (Tau.ty T) := by
  obtain ⟨v, U, P, hv, hU, hcheck, hprecise, hsub⟩ :=
    h.lookup_exists x
  cases hU.unique hb
  exact ⟨v, P, hv, hcheck, hprecise, hsub⟩

/-! ## Canonical forms for source-only suffixes -/

/-- A source-subtyping suffix from a precise structural value to a function
type forces an abstraction. -/
theorem Tm.StructPrecise.fun_canonical_source
    (hp : Tm.StructPrecise Gamma R v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Fun S T))) :
    ∃ A body B,
      v = Tm.abs A body ∧
      P = Ty.Fun A B ∧
      Tm.StructCheck (Gamma.snoc A) (Path.ScopedLift R) body B ∧
      Tau.StructWf Gamma R (Tau.ty A) := by
  cases hp with
  | abs ht hwf => exact ⟨_, _, _, rfl, rfl, ht, hwf⟩
  | pair hy hz => exact (Tau.Sub.pair_not_fun hs).elim
  | tpair hy hwf => exact (Tau.Sub.pair_not_fun hs).elim

/-- A source-subtyping suffix to a pair preserves the member label and the
term/type definition distinction. -/
theorem Tm.StructPrecise.pair_canonical_source
    (hp : Tm.StructPrecise Gamma R v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Pair S a d))) :
    (∃ y z,
      v = Tm.pair y a (Def.val z) ∧
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken))) ∨
    (∃ y U,
      v = Tm.pair y a (Def.type U) ∧
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

/-! ## Runtime validity for the direct syntactic approach -/

/-- Runtime equations are *typing-valid* for a structurally typed store when
they transport every structural path check in both directions.

This is the missing semantic property needed to extend the source-only
canonical lemmas from `Tau.Sub` to arbitrary `Tau.StructSub`: the
`Tau.StructConv.replace` constructor accepts an untyped runtime equation, so
store typing alone currently supplies no derivation that the replacement
path supports the same eliminations and generalized type. -/
def Store.StructTy.RuntimePathValid
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  ∀ {k : Kind} {p q : Path n} {d : Tau n k},
    Path.RuntimeEq sigma p q ->
    (Path.StructCheck Gamma (Path.RuntimeEq sigma) p d ↔
      Path.StructCheck Gamma (Path.RuntimeEq sigma) q d)

/-!
For canonical forms below binders, the same property must be stable under
`Gamma.snoc S` / `Path.ScopedLift`; at the concrete store boundary this is
discharged only after allocating the value represented by the binder.  A
proof of `RuntimePathValid` (and its scoped/allocation closure) would make
runtime conversion a typed equality.  Without it, an arbitrary relation edge
can replace a singleton path by one with an unrelated type, so neither
function-vs-pair disjointness nor pair-label preservation follows from a raw
`Tau.StructSub` derivation.
-/

end LambdaP.Repaired
