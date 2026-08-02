import LambdaP.Typing

/-!
Small source-level regression examples for the two pair-subtyping
rules.  They show that the restricted rules still support the intended use
of dependent type members: an exact member can be widened to an abstract
interval, and the first component can subsequently be widened independently.
-/

namespace LambdaP
namespace Examples

open Ty
open Tau

/-- The exact type member `{x}..{x}`, where `x` is the pair binder. -/
def exactSelfMember (n : Nat) : Tau (n + 1) .iota :=
  .intv (.Single (.var 0)) (.Single (.var 0))

/-- The proper abstract interval `Bot..{x}`, still dependent on the pair
binder. -/
def abstractSelfMember (n : Nat) : Tau (n + 1) .iota :=
  .intv .Bot (.Single (.var 0))

/-- Generic interval widening under a singleton pair binder.  The scoped
premises are the ordinary `L <: T <: U` obligations; the opened premises
record the same comparison after identifying the binder with `p`.

The source interval is exact, so its nonemptiness premise is reflexivity.
-/
theorem pair_single_member_widen_exact_interval
    {Gamma : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    {L T U : Ty (n + 1)}
    (hp : Path.Ty Gamma p (.ty P))
    (hlo : Tau.Sub (Gamma.snoc (.Single p)) (.ty L) (.ty T))
    (hhi : Tau.Sub (Gamma.snoc (.Single p)) (.ty T) (.ty U))
    (hloOpen : Tau.Sub Gamma (.ty (L.open p)) (.ty (T.open p)))
    (hhiOpen : Tau.Sub Gamma (.ty (T.open p)) (.ty (U.open p))) :
    Tau.Sub Gamma
      (.ty (.Pair (.Single p) a (.intv T T)))
      (.ty (.Pair (.Single p) a (.intv L U))) := by
  apply Tau.Sub.pair_single_member hp
  · exact .bounds hlo hhi .refl
  · exact .bounds hloOpen hhiOpen .refl

/-- After changing the member, `pair_fst` independently widens the first
component from the singleton `{p}` to the ordinary type `P` of `p`.
-/
theorem pair_rules_widen_exact_interval
    {Gamma : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    {L T U : Ty (n + 1)}
    (hp : Path.Ty Gamma p (.ty P))
    (hlo : Tau.Sub (Gamma.snoc (.Single p)) (.ty L) (.ty T))
    (hhi : Tau.Sub (Gamma.snoc (.Single p)) (.ty T) (.ty U))
    (hloOpen : Tau.Sub Gamma (.ty (L.open p)) (.ty (T.open p)))
    (hhiOpen : Tau.Sub Gamma (.ty (T.open p)) (.ty (U.open p))) :
    Tau.Sub Gamma
      (.ty (.Pair (.Single p) a (.intv T T)))
      (.ty (.Pair P a (.intv L U))) := by
  exact .trans
    (pair_single_member_widen_exact_interval hp hlo hhi hloOpen hhiOpen)
    (.pair_fst (.widen hp))

/-- A direct dependent instance: `{x}..{x}` is widened to `Bot..{x}`.
Both the exact and abstract members mention the first component.
-/
theorem exact_self_member_to_abstract_self_member
    {Gamma : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    (hp : Path.Ty Gamma p (.ty P)) :
    Tau.Sub Gamma
      (.ty (.Pair (.Single p) a (exactSelfMember n)))
      (.ty (.Pair (.Single p) a (abstractSelfMember n))) := by
  apply pair_single_member_widen_exact_interval hp
  · exact .bot
  · exact .refl
  · exact .bot
  · exact .refl

/-- The same dependent member widening followed by first-component
covariance. -/
theorem exact_self_member_to_widened_abstract_pair
    {Gamma : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    (hp : Path.Ty Gamma p (.ty P)) :
    Tau.Sub Gamma
      (.ty (.Pair (.Single p) a (exactSelfMember n)))
      (.ty (.Pair P a (abstractSelfMember n))) := by
  exact .trans (exact_self_member_to_abstract_self_member hp)
    (.pair_fst (.widen hp))

/-- The exact interval assigned by `Tm.Ty.tpair` stores the outer path `p`.
This is definitionally its weakening under the pair binder. -/
def storedExactMember (p : Path n) : Tau (n + 1) .iota :=
  (Tau.intv (.Single p) (.Single p)).weaken

/-- A concrete, inhabited example.  The term defines the exact member
`{p}..{p}`.  Under the singleton binder, the newest variable has type `{p}`;
singleton symmetry therefore changes the stored upper bound to `{x}`.  The
result is subsumed at the dependent abstract type

`Pair P A (Bot..{x})`.
-/
theorem typed_type_pair_at_dependent_abstract_type
    {Gamma : Ctx n} {y : Fin n} {P : Ty n} {A : Name}
    (hy : Ctx.Binds Gamma y P)
    (hP : Tau.Wf Gamma (.ty P)) :
    Tm.Ty Gamma
      (.pair y A (.type (.Single (.var y))))
      (.Pair P A (abstractSelfMember n)) := by
  let p : Path n := .var y
  have hp : Path.Ty Gamma p (.ty P) := .var hy
  have hnew : Path.Ty (Gamma.snoc (.Single p)) (.var 0)
      (.ty ((.Single p : Ty n).weaken)) :=
    .var Ctx.Binds.here
  have hmember : Tau.Sub Gamma
      (.ty (.Pair (.Single p) A (storedExactMember p)))
      (.ty (.Pair (.Single p) A (abstractSelfMember n))) := by
    apply Tau.Sub.pair_single_member hp
    · exact .bounds .bot (.symm hnew) .refl
    · exact .bounds .bot .refl .refl
  have hsub : Tau.Sub Gamma
      (.ty (.Pair (.Single p) A (storedExactMember p)))
      (.ty (.Pair P A (abstractSelfMember n))) :=
    .trans hmember (.pair_fst (.widen hp))
  have hnewP : Path.Ty (Gamma.snoc P) (.var 0) (.ty P.weaken) :=
    .var Ctx.Binds.here
  have htarget : Tau.Wf Gamma (.ty (.Pair P A (abstractSelfMember n))) :=
    .pair hP (.bounds_wf .bot (.path hnewP) .bot)
  apply Tm.Ty.sub (Tm.Ty.tpair hy (.path hp)) hsub htarget

end Examples
end LambdaP
