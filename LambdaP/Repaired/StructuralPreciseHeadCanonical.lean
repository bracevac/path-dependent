import LambdaP.Repaired.StructuralRealization
import LambdaP.Repaired.StructuralPreciseCanonical
import LambdaP.Repaired.StructuralConversionInversion

/-!
Head-only canonical facts for exact structural stores.

This module is deliberately narrower than `StructuralRealization`: it does
not define path or type realization.  It records only that runtime type
conversion preserves the outer constructor of a generalized type, and uses
that fact to invert an already established `Store.Possible` witness at the
two heads inspected by the evaluator.
-/

namespace LambdaP.Repaired

/-! ## Outer constructors are invariant under runtime conversion -/

inductive Tau.OuterTag : Type where
| top
| bot
| fun
| pair (a : Name) (k : Kind)
| single
| tsel
| interval
deriving DecidableEq

def Ty.outerTag : Ty n -> Tau.OuterTag
| .Top => .top
| .Bot => .bot
| .Fun _ _ => .fun
| .Pair (k := k) _ a _ => .pair a k
| .Single _ => .single
| .TSel _ _ => .tsel

def Tau.outerTag : Tau n k -> Tau.OuterTag
| .ty T => T.outerTag
| .intv _ _ => .interval

@[simp] theorem Ty.outerTag_open (T : Ty (n + 1)) (p : Path n) :
    (T.open p).outerTag = T.outerTag := by
  cases T <;> rfl

@[simp] theorem Tau.outerTag_open (d : Tau (n + 1) k) (p : Path n) :
    (d.open p).outerTag = d.outerTag := by
  cases d with
  | ty T => exact Ty.outerTag_open T p
  | intv L U => rfl

theorem Tau.StructConv.outerTag_eq
    (h : Tau.StructConv R d1 d2) : d1.outerTag = d2.outerTag := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | replace template hpq => simp only [Tau.outerTag_open]

/-! ## Inversion of possible concrete heads -/

private def Path.Endpoint.Realizes.KindInvariant
    (endpoint : Path.Endpoint n) {k : Kind} (_ : Tau n k) : Prop :=
  match endpoint with
  | .val _ => k = .star
  | .type _ => k = .iota

private theorem Path.Endpoint.Realizes.kind_invariant
    (h : Path.Endpoint.Realizes Gamma sigma endpoint d) :
    Path.Endpoint.Realizes.KindInvariant endpoint d := by
  refine Path.Endpoint.Realizes.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun endpoint d _ =>
      Path.Endpoint.Realizes.KindInvariant endpoint d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; rfl
  · intros; rfl
  · intro endpoint k d1 d2 hr hc ih
    exact ih

theorem Path.Endpoint.Realizes.val_kind
    {d : Tau n k}
    (h : Path.Endpoint.Realizes Gamma sigma (.val x) d) :
    k = .star :=
  h.kind_invariant

theorem Path.Endpoint.Realizes.type_kind
    {d : Tau n k}
    (h : Path.Endpoint.Realizes Gamma sigma (.type W) d) :
    k = .iota :=
  h.kind_invariant

theorem Path.Endpoint.Realizes.def_kind
    {delta : Def n k1} {d : Tau n k2}
    (h : Path.Endpoint.Realizes Gamma sigma delta.endpoint d) :
    k1 = k2 := by
  cases delta with
  | val x => exact h.val_kind.symm
  | type W => exact h.type_kind.symm

private def Store.Possible.HeadInvariant
    (Gamma : Ctx n) (sigma : Store n) (x : Fin n) :
    LambdaP.Repaired.Ty n -> Prop
| Ty.Fun _ _ =>
    exists A body, Store.Binds sigma x (Tm.abs A body)
| Ty.Pair (k := k) _ a _ =>
    exists (y : Fin n) (delta : Def n k),
      Store.Binds sigma x (@Tm.pair n k y a delta)
| _ => True

private theorem Store.Possible.HeadInvariant.conv
    (hhead : Store.Possible.HeadInvariant Gamma sigma x S)
    (hconv : Tau.StructConv (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty T)) :
    Store.Possible.HeadInvariant Gamma sigma x T := by
  have htag := hconv.outerTag_eq
  cases S <;> cases T <;>
    simp_all [Tau.outerTag, Ty.outerTag, Store.Possible.HeadInvariant]
  obtain ⟨hlabel, hkind⟩ := htag
  cases hkind
  exact hhead

/-- The function and pair head inversions packaged as one motive for the
mutual `Possible`/`Realizes` recursor.  Packaging them together avoids any
proof-size recursion through the conversion constructor. -/
private theorem Store.Possible.head_invariant
    (h : Store.Possible Gamma sigma x T) :
    Store.Possible.HeadInvariant Gamma sigma x T := by
  refine Store.Possible.rec
    (motive_1 := fun x T _ =>
      Store.Possible.HeadInvariant Gamma sigma x T)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros
    trivial
  · intro x A body B S U hbind hctx hprecise hdom hcod
    exact ⟨A, body, hbind⟩
  · intro x y a kDelta delta S k d hbind hfirst hpossible hmember ihp ihm
    have hk := hmember.def_kind
    cases hk
    exact ⟨y, delta, hbind⟩
  · intros
    trivial
  · intros
    trivial
  · intro x S T hpossible hconv ih
    exact ih.conv hconv
  · intros
    trivial
  · intros
    trivial
  · intros
    trivial

/-- A possible inhabitant of a function type is stored as an abstraction. -/
theorem Store.Possible.fun_binding
    (h : Store.Possible Gamma sigma x (Ty.Fun S U)) :
    exists A body, Store.Binds sigma x (Tm.abs A body) :=
  h.head_invariant

/-- A possible inhabitant of a pair type is stored as a pair with the same
label and the same term/type member kind. -/
theorem Store.Possible.pair_binding
    {k : Kind} {d : Tau (n + 1) k}
    (h : Store.Possible Gamma sigma x (Ty.Pair S a d)) :
    exists (y : Fin n) (delta : Def n k),
      Store.Binds sigma x (@Tm.pair n k y a delta) :=
  h.head_invariant

/-! ## Function-signature read-off -/

private def Store.Possible.FunctionInvariant
    (Gamma : Ctx n) (sigma : Store n) (x : Fin n) :
    LambdaP.Repaired.Ty n -> Prop
| Ty.Fun S U =>
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
| _ => True

private theorem Store.Possible.FunctionInvariant.conv
    (hhead : Store.Possible.FunctionInvariant Gamma sigma x X)
    (hconv : Tau.StructConv (Path.RuntimeEq sigma)
      (Tau.ty X) (Tau.ty T)) :
    Store.Possible.FunctionInvariant Gamma sigma x T := by
  cases T with
  | Top => trivial
  | Bot => trivial
  | Fun S U =>
      cases X with
      | Top =>
          have htag := hconv.outerTag_eq
          cases htag
      | Bot =>
          have htag := hconv.outerTag_eq
          cases htag
      | Fun S0 U0 =>
          obtain ⟨A, body, B, hbind, hctx, hprecise, hdom, hcod⟩ :=
            hhead
          obtain ⟨hdomConv, hcodConv⟩ := hconv.fun_parts
          refine ⟨A, body, B, hbind, hctx, hprecise,
            .trans (.conv hdomConv.symm) hdom, ?_⟩
          exact .trans (hcod.narrow (.conv hdomConv.symm))
            (.conv hcodConv)
      | Pair S0 a d =>
          have htag := hconv.outerTag_eq
          cases htag
      | Single p =>
          have htag := hconv.outerTag_eq
          cases htag
      | TSel p A =>
          have htag := hconv.outerTag_eq
          cases htag
  | Pair S a d => trivial
  | Single p => trivial
  | TSel p A => trivial

private theorem Store.Possible.function_invariant
    (h : Store.Possible Gamma sigma x T) :
    Store.Possible.FunctionInvariant Gamma sigma x T := by
  refine Store.Possible.rec
    (motive_1 := fun x T _ =>
      Store.Possible.FunctionInvariant Gamma sigma x T)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros
    trivial
  · intro x A body B S U hbind hctx hprecise hdom hcod
    exact ⟨A, body, B, hbind, hctx, hprecise, hdom, hcod⟩
  · intros
    trivial
  · intros
    trivial
  · intros
    trivial
  · intro x S T hpossible hconv ih
    exact ih.conv hconv
  · intros
    trivial
  · intros
    trivial
  · intros
    trivial

/-- A possible function exposes its exact stored abstraction signature and
the contravariant/covariant residues needed by beta preservation.  Trailing
runtime conversion is decomposed componentwise; narrowing moves the stored
codomain residue to the converted domain context. -/
theorem Store.Possible.function_signature
    (h : Store.Possible Gamma sigma x (Ty.Fun S U)) :
    exists A body B,
      Store.Binds sigma x (Tm.abs A body) /\
      Ctx.Binds Gamma x (Ty.Fun A B) /\
      Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
        (Tm.abs A body) (Ty.Fun A B) /\
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty S) (Tau.ty A) /\
      Tau.StructSub (Gamma.snoc S)
        (Path.ScopedLift (Path.RuntimeEq sigma))
        (Tau.ty B) (Tau.ty U) :=
  h.function_invariant

end LambdaP.Repaired
