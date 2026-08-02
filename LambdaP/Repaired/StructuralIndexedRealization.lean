import LambdaP.Repaired.StructuralResolution
import LambdaP.Repaired.StructuralPreciseStore

/-!
A guarded, step-indexed experiment for store realization.

This file is intentionally separate from `StructuralRealization`.  It tests
the most direct way of giving an interval semantic (rather than syntactic)
bounds: at level `i + 1`, a stored type `W` realizes `[L, U]` when inhabitants
of `L` map to inhabitants of `W`, and inhabitants of `W` map to inhabitants of
`U`, at the strictly smaller level `i`.  The smaller index makes the negative
occurrences accepted by Lean's termination checker.

Functions remain shallow.  Their denotation records exactly the introduction
and structural-subtyping residues needed by beta pushback; making arrows deep
would require a logical relation on terms and machine states, which is
orthogonal to the type-member issue tested here.
-/

namespace LambdaP.Repaired
namespace IndexedRealization

/-- The endpoint represented by a stored definition. -/
def defEndpoint : Def n k -> Path.Endpoint n
| .val x => .val x
| .type W => .type W

mutual

/-- Finite approximation to membership of a store location in a proper type.

The index is spent only when following a stored component or type alias.
Function witnesses are deliberately shallow and proof-relevant so that a
function observation can return the exact abstraction and its two pushback
residues. -/
def Possible (Gamma : Ctx n) (sigma : Store n) :
    Nat -> Fin n -> Ty n -> Prop
| 0, _, _ => True
| _ + 1, _, .Top => True
| _ + 1, _, .Bot => False
| _ + 1, x, .Fun S U =>
    exists A body B,
      Store.Binds sigma x (Tm.abs A body) /\
      Ctx.Binds Gamma x (Ty.Fun A B) /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
        (Tm.abs A body) (Ty.Fun A B) /\
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U)
| i + 1, x, .Pair S a (.ty T) =>
    exists y z,
      Store.Binds sigma x (Tm.pair y a (Def.val z)) /\
      Path.StructCheck Gamma (Path.RuntimeEq sigma)
        (Path.var y) (Tau.ty S) /\
      Possible Gamma sigma i y S /\
      Possible Gamma sigma i z (T.open (Path.var y))
| i + 1, x, .Pair S A (.intv L U) =>
    exists y W,
      Store.Binds sigma x (Tm.pair y A (Def.type W)) /\
      Path.StructCheck Gamma (Path.RuntimeEq sigma)
        (Path.var y) (Tau.ty S) /\
      Possible Gamma sigma i y S /\
      Interval Gamma sigma i W
        (L.open (Path.var y)) (U.open (Path.var y))
| _ + 1, x, .Single p =>
    Path.Resolve p sigma (.val x)
| i + 1, x, .TSel p A =>
    exists W,
      Path.Resolve (p.sel A) sigma (.type W) /\
      Possible Gamma sigma i x W

/-- Finite approximation to a stored type lying between two bounds.

Both function spaces mention `Possible` only at the predecessor index.  This
is the guarded occurrence which an unindexed mutual inductive definition
cannot express. -/
def Interval (Gamma : Ctx n) (sigma : Store n) :
    Nat -> Ty n -> Ty n -> Ty n -> Prop
| 0, _, _, _ => True
| i + 1, W, L, U =>
    (forall x, Possible Gamma sigma i x L ->
      Possible Gamma sigma i x W) /\
    (forall x, Possible Gamma sigma i x W ->
      Possible Gamma sigma i x U)

end

/-- Endpoint realization packages the two kind-indexed finite readings. -/
def Realizes (Gamma : Ctx n) (sigma : Store n) (i : Nat)
    (endpoint : Path.Endpoint n) (d : Tau n k) : Prop :=
  match endpoint, d with
  | .val x, .ty T => Possible Gamma sigma i x T
  | .type W, .intv L U => Interval Gamma sigma i W L U
  | .val _, .intv _ _ => False
  | .type _, .ty _ => False

/-- Limit membership: a location belongs at every finite approximation. -/
def AllPossible (Gamma : Ctx n) (sigma : Store n)
    (x : Fin n) (T : Ty n) : Prop :=
  forall i, Possible Gamma sigma i x T

/-- Limit endpoint realization. -/
def AllRealizes (Gamma : Ctx n) (sigma : Store n)
    (endpoint : Path.Endpoint n) (d : Tau n k) : Prop :=
  forall i, Realizes Gamma sigma i endpoint d

/-! ## Exact store introductions -/

/-- A precisely stored value inhabits its introduction type at every finite
approximation.  This separates the store-construction issue from semantic
closure under subtyping. -/
theorem possible_all_of_precise_binds
    (hprecise : Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P)
    (hbind : Store.Binds sigma x v)
    (hctx : Ctx.Binds Gamma x P) :
    AllPossible Gamma sigma x P := by
  intro i
  induction i with
  | zero => trivial
  | succ i ih =>
      cases hprecise with
      | abs hbody hwf =>
          exact ⟨_, _, _, hbind, hctx, .abs hbody hwf,
            .refl, .refl⟩
      | pair hy hz =>
          refine ⟨_, _, hbind, ?_, ?_, ?_⟩
          · exact .promote (.var hy) .refl
          · cases i with
            | zero => trivial
            | succ i => exact Path.Resolve.var
          · simpa only [Tau.weaken_open] using
              (show Possible Gamma sigma i _
                (Ty.Single (Path.var _)) from by
                  cases i with
                  | zero => trivial
                  | succ i => exact Path.Resolve.var)
      | tpair hy hwf =>
          rename_i y S T A
          refine ⟨_, _, hbind, ?_, ?_, ?_⟩
          · exact .promote (.var hy) .refl
          · cases i with
            | zero => trivial
            | succ i => exact Path.Resolve.var
          · cases i with
            | zero => trivial
            | succ i =>
                simp only [Interval]
                rw [show (T.rename FinFun.weaken).open (Path.var y) = T from
                  Ty.weaken_open T (Path.var y)]
                exact ⟨fun _ h => h, fun _ h => h⟩

/-- Every exact context entry is realized at all finite levels. -/
theorem Store.StructPreciseTy.possible_all_of_ctx_binds
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hctx : Ctx.Binds Gamma x P) :
    AllPossible Gamma sigma x P := by
  obtain ⟨v, hbind, hprecise⟩ := hstore.of_ctx_binds hctx
  exact possible_all_of_precise_binds hprecise hbind hctx

/-! ## Exact function observation -/

/-- Limit membership at a function type exposes exactly the abstraction and
the domain/codomain residues required by beta pushback.  Only level one is
needed because arrows are shallow. -/
theorem AllPossible.function_pushback
    (h : AllPossible Gamma sigma x (Ty.Fun S U)) :
    exists A body B,
      Store.Binds sigma x (Tm.abs A body) /\
      Ctx.Binds Gamma x (Ty.Fun A B) /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
        (Tm.abs A body) (Ty.Fun A B) /\
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U) := by
  simpa only [Possible] using h 1

/-! ## Index accounting for abstract selections -/

/-- Reading an upper bound spends one level: the selected alias and the
interval maps are both available at the predecessor approximation. -/
theorem selection_upper_spends_one
    (hsel : Possible Gamma sigma (i + 1) x (Ty.TSel p A))
    (hresolve : Path.Resolve (p.sel A) sigma (.type W))
    (hintv : Realizes Gamma sigma (i + 1) (.type W) (Tau.intv S T)) :
    Possible Gamma sigma i x T := by
  simp only [Possible] at hsel
  obtain ⟨W', hresolve', hW'⟩ := hsel
  cases hresolve'.deterministic hresolve
  have hmaps := hintv
  simp only [Realizes, Interval] at hmaps
  exact hmaps.2 x hW'

/-- Conversely, a lower-bound map constructs selection membership one level
later.  The opposite shifts in this and `selection_upper_spends_one` are the
source of the variance problem for a uniform fuel-cost theorem. -/
theorem selection_lower_builds_next
    (hresolve : Path.Resolve (p.sel A) sigma (.type W))
    (hintv : Realizes Gamma sigma (i + 1) (.type W) (Tau.intv S T))
    (hS : Possible Gamma sigma i x S) :
    Possible Gamma sigma (i + 1) x (Ty.TSel p A) := by
  refine ⟨W, hresolve, ?_⟩
  have hmaps := hintv
  simp only [Realizes, Interval] at hmaps
  exact hmaps.1 x hS

/-! ## The soundness interfaces tested by this model -/

/-- Covariant finite transport is necessarily allowed to consume fuel.
This is the natural theorem shape for singleton widening and type selection. -/
def CovariantTransport (Gamma : Ctx n) (sigma : Store n)
    (S T : Ty n) : Prop :=
  exists cost, forall i x,
    Possible Gamma sigma (i + cost) x S ->
    Possible Gamma sigma i x T

/-- Interval transport needs its lower-bound premise in the opposite
polarity.  A merely fuel-consuming covariant map cannot consume an inhabitant
available only at the target index; this is the critical `bounds` obstruction
for the naive indexed model. -/
def IntervalTransport (Gamma : Ctx n) (sigma : Store n)
    (L U L' U' : Ty n) : Prop :=
  forall W,
    AllRealizes Gamma sigma (.type W) (Tau.intv L U) ->
    AllRealizes Gamma sigma (.type W) (Tau.intv L' U')

end IndexedRealization
end LambdaP.Repaired
