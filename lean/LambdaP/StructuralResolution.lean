import LambdaP.RuntimeConversion

/-!
Generalized operational resolution for the proof of structural soundness.

The source evaluator returns locations and therefore covers only paths
of kind `star`.  A path of kind `iota` stops at a stored type definition.
`Path.Resolve` records both outcomes without changing the source calculus or
the machine.  Its term fragment is exactly `Path.reduce`.
-/

namespace LambdaP

namespace Path

/-- The two possible outcomes of following a path through a store. -/
inductive Endpoint (n : Nat) : Type where
| val : Fin n -> Endpoint n
| type : LambdaP.Ty n -> Endpoint n

/-- Follow a path to either a value location or a stored type definition. -/
inductive Resolve : Path n -> Store n -> Endpoint n -> Prop where
| var : Resolve (.var x) sigma (.val x)
| fst :
    Resolve p sigma (.val x) ->
    Store.Binds sigma x (Tm.pair y a d) ->
    Resolve p.fst sigma (.val y)
| sel_val :
    Resolve p sigma (.val x) ->
    Store.Binds sigma x (Tm.pair y a (Def.val z)) ->
    Resolve (p.sel a) sigma (.val z)
| sel_type :
    Resolve p sigma (.val x) ->
    Store.Binds sigma x (Tm.pair y a (Def.type U)) ->
    Resolve (p.sel a) sigma (.type U)
| sel_miss :
    Resolve p sigma (.val x) ->
    Store.Binds sigma x (Tm.pair y b d) ->
    a ≠ b ->
    Resolve ((Path.var y).sel a) sigma e ->
    Resolve (p.sel a) sigma e

/-- Generalized resolution is the graph of a partial function. -/
theorem Resolve.deterministic
    (h1 : Resolve p sigma e1) (h2 : Resolve p sigma e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | var =>
      cases h2
      rfl
  | fst hp1 hb1 ih =>
      cases h2 with
      | fst hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
  | sel_val hp1 hb1 ih =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_type hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_type hp1 hb1 ih =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
      | sel_type hp2 hb2 =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          rfl
      | sel_miss hp2 hb2 hne2 _ =>
          cases ih hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne2 rfl).elim
  | sel_miss hp1 hb1 hne1 htail1 ihp ihtail =>
      cases h2 with
      | sel_val hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_type hp2 hb2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact (hne1 rfl).elim
      | sel_miss hp2 hb2 _ htail2 =>
          cases ihp hp2
          cases Store.Binds.unique hb1 hb2
          exact ihtail htail2

/-! ## Agreement with the source term-path evaluator -/

theorem reduce.toResolve (h : Path.reduce p sigma x) :
    Resolve p sigma (.val x) := by
  induction h with
  | var => exact .var
  | fst hp hb ih => exact .fst ih hb
  | sel_hit hp hb ih => exact .sel_val ih hb
  | sel_miss hp hb hne htail ihp ihtail =>
      exact .sel_miss ihp hb hne ihtail

private theorem Resolve.toReduce_of_eq (h : Resolve p sigma e) :
    forall x, e = .val x -> Path.reduce p sigma x := by
  induction h with
  | var =>
      intro x he
      cases he
      exact .var
  | fst hp hb ih =>
      intro x he
      cases he
      exact .fst (ih _ rfl) hb
  | sel_val hp hb ih =>
      intro x he
      cases he
      exact .sel_hit (ih _ rfl) hb
  | sel_type hp hb ih =>
      intro x he
      cases he
  | sel_miss hp hb hne htail ihp ihtail =>
      intro x he
      exact .sel_miss (ihp _ rfl) hb hne (ihtail _ he)

theorem Resolve.toReduce (h : Resolve p sigma (.val x)) :
    Path.reduce p sigma x :=
  h.toReduce_of_eq x rfl

theorem resolve_val_iff_reduce :
    Resolve p sigma (.val x) <-> Path.reduce p sigma x :=
  ⟨Resolve.toReduce, reduce.toResolve⟩

/-! ## Substitution congruence -/

/-- Pointwise-equivalent substitutions have the same generalized resolution
graph after substitution into an arbitrary path. -/
theorem Resolve.subst_congr
    {l n : Nat} {sigma : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n} {e : Endpoint n}
    (hrho : forall x e,
      Resolve (rho1 x) sigma e <-> Resolve (rho2 x) sigma e)
    (h : Resolve (r.subst rho1) sigma e) :
    Resolve (r.subst rho2) sigma e := by
  induction r generalizing e with
  | var x => exact (hrho x e).mp h
  | fst r ih =>
      simp only [Path.subst] at h |-
      cases h with
      | fst hp hb => exact .fst (ih hp) hb
  | sel r a ih =>
      simp only [Path.subst] at h |-
      cases h with
      | sel_val hp hb => exact .sel_val (ih hp) hb
      | sel_type hp hb => exact .sel_type (ih hp) hb
      | sel_miss hp hb hne htail =>
          exact .sel_miss (ih hp) hb hne htail

theorem Resolve.subst_iff
    {l n : Nat} {sigma : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n} {e : Endpoint n}
    (hrho : forall x e,
      Resolve (rho1 x) sigma e <-> Resolve (rho2 x) sigma e) :
    Resolve (r.subst rho1) sigma e <->
      Resolve (r.subst rho2) sigma e := by
  constructor
  · exact Resolve.subst_congr hrho
  · exact Resolve.subst_congr (fun x e => (hrho x e).symm)

theorem Resolve.open_iff
    {n : Nat} {sigma : Store n} {p q : Path n} {e : Endpoint n}
    (hpq : forall e, Resolve p sigma e <-> Resolve q sigma e)
    (r : Path (n + 1)) :
    Resolve (r.open p) sigma e <-> Resolve (r.open q) sigma e := by
  apply Resolve.subst_iff
  intro x endpoint
  refine Fin.cases ?_ (fun _ => ?_) x
  · exact hpq endpoint
  · rfl

/-! ## Runtime equality has semantic content at both kinds -/

/-- Runtime equality preserves the generalized resolution graph.  The
`congr` case is why type-member endpoints, although absent from the machine,
are still transported correctly. -/
theorem RuntimeEq.resolve_iff
    {n : Nat} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) (e : Endpoint n) :
    Resolve p sigma e <-> Resolve q sigma e := by
  induction h generalizing e with
  | refl => rfl
  | symm _ ih => exact (ih e).symm
  | trans _ _ ih1 ih2 => exact (ih1 e).trans (ih2 e)
  | coresolve hp hq =>
      constructor
      · intro he
        have heq : e = .val _ := he.deterministic hp.toResolve
        cases heq
        exact hq.toResolve
      · intro he
        have heq : e = .val _ := he.deterministic hq.toResolve
        cases heq
        exact hp.toResolve
  | congr _ r ih =>
      exact Resolve.open_iff (fun endpoint => ih endpoint) r

end Path

end LambdaP
