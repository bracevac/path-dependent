import LambdaP.RefinedPathProgress
import LambdaP.StructuralRuntimeLemmas

/-!
Structural progress obligations for refined stores.

The structural opening theorem now discharges the binder mismatch in a
dependent pair member: a premise proved under `Gamma, self : {y}` can be
opened at `y`, and runtime co-resolution converts the static occurrence of
`y` to the path which produced it.  This file proves that local fact and then
isolates the remaining store-level condition needed for weak pair transport.

The remaining condition is deliberately observation-sized.  It does not ask
for preservation of arbitrary types: it asks only that a structural pair
check on a result variable be reflected by the value stored at that variable.
-/

namespace LambdaP

/-! ## Renaming-as-opening algebra -/

private theorem Path.rename_as_subst
    (p : Path n) (f : FinFun n m) :
    p.rename f = p.subst (fun x => .var (f x)) := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.rename, Path.subst, ih]
  | sel p a ih => simp only [Path.rename, Path.subst, ih]

private theorem PathSubst.lift_vars (f : FinFun n m) :
    (fun x => Path.var (f.ext x)) =
      PathSubst.lift (fun x => Path.var (f x)) := by
  funext x
  refine Fin.cases ?_ (fun y => ?_) x <;> rfl

mutual

private theorem Ty.rename_as_subst
    (T : Ty n) (f : FinFun n m) :
    T.rename f = T.subst (fun x => .var (f x)) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.rename, Ty.subst, Ty.rename_as_subst S f,
        Ty.rename_as_subst T f.ext]
      rw [PathSubst.lift_vars]
  | .Pair S a d => by
      simp only [Ty.rename, Ty.subst, Ty.rename_as_subst S f,
        Tau.rename_as_subst d f.ext]
      rw [PathSubst.lift_vars]
  | .Single p => by
      simp only [Ty.rename, Ty.subst, Path.rename_as_subst]
  | .TSel p A => by
      simp only [Ty.rename, Ty.subst, Path.rename_as_subst]

private theorem Tau.rename_as_subst
    (d : Tau n k) (f : FinFun n m) :
    d.rename f = d.subst (fun x => .var (f x)) :=
  match d with
  | .ty T => by simp only [Tau.rename, Tau.subst, Ty.rename_as_subst]
  | .intv S T => by
      simp only [Tau.rename, Tau.subst, Ty.rename_as_subst]

end

/-- On generalized types, opening by a variable is exactly the machine's
`FinFun.openAt` renaming. -/
theorem Tau.rename_openAt_eq_open_var
    (d : Tau (n + 1) k) (x : Fin n) :
    d.rename (FinFun.openAt x) = d.open (.var x) := by
  rw [Tau.rename_as_subst]
  unfold Tau.open
  congr 1
  funext y
  refine Fin.cases ?_ (fun z => ?_) y <;> rfl

/-! ## The dependent-member opening step -/

/-- Open a structural member-subtyping premise under the precise singleton
binder `{y}`, then transport only the target member along an ambient path
equation.  This is the two-path form absent from exact source opening. -/
theorem Tau.StructSub.open_precise_member
    {n : Nat} {Gamma : Ctx n}
    {R : Path n -> Path n -> Prop}
    {y : Fin n} {r : Path n} {k : Kind}
    {d1 d2 : Tau (n + 1) k}
    (hR : Path.IsEquivCongr R)
    (h : Tau.StructSub
      (Gamma.snoc (Ty.Single (.var y))) (Path.ScopedLift R) d1 d2)
    (hyr : R (.var y) r) :
    Tau.StructSub Gamma R (d1.open (.var y)) (d2.open r) := by
  obtain ⟨U, hy⟩ := Ctx.Binds.exists Gamma y
  have hyCheck : Path.StructCheck Gamma R (.var y) (Tau.ty U) :=
    Path.StructCheck.var hy
  have hopen := h.open_var_of_singleton hR hyCheck
    (Tau.StructSub.refl (Gamma := Gamma) (R := R)
      (d := Tau.ty (Ty.Single (.var y))))
  rw [Tau.rename_openAt_eq_open_var,
    Tau.rename_openAt_eq_open_var] at hopen
  exact Tau.StructSub.trans hopen
    (Tau.StructSub.conv (Tau.StructConv.replace d2 hyr))

/-- Concrete runtime specialization.  If `r` reduces to `y`, co-resolution
provides the equation needed by `open_precise_member`. -/
theorem Tau.StructSub.open_precise_member_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {y : Fin n} {r : Path n} {k : Kind}
    {d1 d2 : Tau (n + 1) k}
    (h : Tau.StructSub
      (Gamma.snoc (Ty.Single (.var y)))
      (Path.ScopedLift (Path.RuntimeEq sigma)) d1 d2)
    (hr : Path.reduce r sigma y) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (d1.open (.var y)) (d2.open r) :=
  h.open_precise_member (Path.RuntimeEq.isEquivCongr sigma)
    (Path.RuntimeEq.of_reduce hr).symm

/-- Source pair-member subtyping embeds into the structural judgment and
therefore enjoys runtime-aware two-path opening. -/
theorem Tau.Sub.open_precise_member_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {y : Fin n} {r : Path n} {k : Kind}
    {d1 d2 : Tau (n + 1) k}
    (h : Tau.Sub (Gamma.snoc (Ty.Single (.var y))) d1 d2)
    (hr : Path.reduce r sigma y) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (d1.open (.var y)) (d2.open r) :=
  (Tau.StructSub.of_source h
    (Path.ScopedLift (Path.RuntimeEq sigma))).open_precise_member_runtime hr

/-- Concrete term-member instance.  The syntax-directed precise member
`{z}` is weakened below the pair binder; after opening, it is again `{z}`
and is structurally below the static member opened by the resolving first
component `r`. -/
theorem Tau.Sub.open_precise_value_member_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {y z : Fin n} {r : Path n} {d : Tau (n + 1) .star}
    (h : Tau.Sub (Gamma.snoc (Ty.Single (.var y)))
      (Tau.ty (Ty.Single (.var z))).weaken d)
    (hr : Path.reduce r sigma y) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (.var z))) (d.open r) := by
  simpa only [Tau.weaken_open] using h.open_precise_member_runtime hr

/-- Concrete type-member instance for the syntax-directed precise interval
`U..U`. -/
theorem Tau.Sub.open_precise_type_member_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {y : Fin n} {r : Path n} {U : LambdaP.Ty n}
    {d : Tau (n + 1) .iota}
    (h : Tau.Sub (Gamma.snoc (Ty.Single (.var y)))
      (Tau.intv U U).weaken d)
    (hr : Path.reduce r sigma y) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.intv U U) (d.open r) := by
  simpa only [Tau.weaken_open] using h.open_precise_member_runtime hr

/-! ## The residual pair-shape contract -/

/-- Runtime pair-check reflection at an already resolved variable.

This is the least store-facing premise needed after structural lookup
preservation: if the result variable structurally checks at a concrete pair
type, its stored value must have the same label and dependent-member kind. -/
def Store.PairCheckReflection (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Ty n} {a : Name}
      {k : Kind} {d : Tau (n + 1) k},
    Path.StructCheck Gamma (Path.RuntimeEq sigma) (.var x)
      (Tau.ty (Ty.Pair S a d)) ->
    exists (y : Fin n) (delta : Def n k),
      Store.Binds sigma x (Tm.pair y a delta)

/-- Refined store typing plus the minimal pair-check reflection property. -/
structure Store.RefinedPairSimulation
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  refined : Store.RefinedTy Gamma sigma
  reflect : Store.PairCheckReflection Gamma sigma

/-- The structural simulation yields the original weak `PairTransport`
contract.  The source path derivation embeds structurally, and reduction
checks the result variable at the same pair type before reflection. -/
theorem Store.RefinedPairSimulation.pairTransport
    (h : Store.RefinedPairSimulation Gamma sigma) :
    Path.PairTransport Gamma sigma := by
  intro p x S a k d hr hp
  apply h.reflect
  exact (Path.StructCheck.of_source hp _).reduce_to_var hr

/-- Consequently refined-store path progress follows from this single local
reflection premise. -/
theorem Path.reduce_progress_refined_of_simulation
    (h : Store.RefinedPairSimulation Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    exists x, Path.reduce p sigma x :=
  Path.reduce_progress_refined_of_pairTransport
    h.refined h.pairTransport hp

/-!
`open_precise_member_runtime` discharges the binder change that previously
blocked the dependent-member case.  What remains is not another opening
lemma: `Store.RefinedTy` records source subtyping from a precise value type to
its public type, while `Path.StructCheck` may reach a pair through structural
singleton promotion and runtime conversion.  Reflecting that observation
back to the concrete stored value is exactly `Store.PairCheckReflection`.
It requires a typed-validity/canonical-forms property for runtime equations;
raw `Path.RuntimeEq` deliberately carries no typing premise.
-/

end LambdaP
