import LambdaP.Repaired.StructuralResolution
import LambdaP.Repaired.StructuralPreciseStore
import LambdaP.Repaired.StructuralRefinedProgress

/-!
Store-indexed realization for the minimally repaired calculus.

`Path.Resolve` is the dynamic counterpart of generalized path checking: it
returns either a value location or a stored type definition.  The mutually
defined predicates below say what it means for such an endpoint to realize a
generalized type.  They are deliberately proof-only.  In particular, they do
not add a typing rule and do not replace primitive transitivity.

The important point of the repair appears in the last two proper-type cases:
`single` is realized by co-resolution with a term location, whereas `tsel` is
realized through a stored type definition.  These cases were one constructor
in the original syntax.
-/

namespace LambdaP.Repaired

namespace Def

/-- View a stored definition as a generalized path-resolution endpoint. -/
def endpoint : Def n k -> Path.Endpoint n
| .val x => .val x
| .type T => .type T

end Def

mutual

/-- A store location is a possible inhabitant of a proper type.  Function
and pair cases retain exactly the syntactic residues needed by progress and
beta preservation. -/
inductive Store.Possible
    (Gamma : Ctx n) (sigma : Store n) : Fin n -> Ty n -> Prop where
| top :
    Store.Possible Gamma sigma x Ty.Top
| fun :
    Store.Binds sigma x (Tm.abs A body) ->
    Ctx.Binds Gamma x (Ty.Fun A B) ->
    Tm.StructPrecise Gamma (Path.RuntimeEq sigma)
      (Tm.abs A body) (Ty.Fun A B) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty A) ->
    Tau.StructSub (Gamma.snoc S)
      (Path.ScopedLift (Path.RuntimeEq sigma))
      (Tau.ty B) (Tau.ty U) ->
    Store.Possible Gamma sigma x (Ty.Fun S U)
| pair :
    Store.Binds sigma x (Tm.pair y a delta) ->
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var y) (Tau.ty S) ->
    Store.Possible Gamma sigma y S ->
    Path.Endpoint.Realizes Gamma sigma (Def.endpoint delta)
      (d.open (Path.var y)) ->
    Store.Possible Gamma sigma x (Ty.Pair S a d)
| single :
    Path.Resolve p sigma (.val x) ->
    Store.Possible Gamma sigma x (Ty.Single p)
| tsel :
    Path.Resolve (p.sel A) sigma (.type W) ->
    Store.Possible Gamma sigma x W ->
    Store.Possible Gamma sigma x (Ty.TSel p A)
| conv :
    Store.Possible Gamma sigma x S ->
    Tau.StructConv (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty T) ->
    Store.Possible Gamma sigma x T

/-- A generalized resolution endpoint realizes a generalized type.  At
proper kind this delegates to `Store.Possible`; at interval kind the stored
definition is sandwiched between the advertised bounds. -/
inductive Path.Endpoint.Realizes
    (Gamma : Ctx n) (sigma : Store n) :
    Path.Endpoint n -> Tau n k -> Prop where
| val :
    Store.Possible Gamma sigma x T ->
    Path.Endpoint.Realizes Gamma sigma (.val x) (Tau.ty T)
| type :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty L) (Tau.ty W) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty W) (Tau.ty U) ->
    Path.Endpoint.Realizes Gamma sigma (.type W) (Tau.intv L U)
| conv :
    Path.Endpoint.Realizes Gamma sigma endpoint d1 ->
    Tau.StructConv (Path.RuntimeEq sigma) d1 d2 ->
    Path.Endpoint.Realizes Gamma sigma endpoint d2

end

/-! ## Elementary realization and conversion inversion -/

/-- Runtime conversion of intervals acts componentwise. -/
private theorem Tau.StructConv.intv_parts_aux
    (h : Tau.StructConv R d1 d2) :
    forall L1 U1, d1 = Tau.intv L1 U1 ->
    forall L2 U2, d2 = Tau.intv L2 U2 ->
      Tau.StructConv R (Tau.ty L1) (Tau.ty L2) /\
      Tau.StructConv R (Tau.ty U1) (Tau.ty U2) := by
  induction h with
  | refl =>
      intro L1 U1 h1 L2 U2 h2
      cases h1
      cases h2
      exact ⟨.refl, .refl⟩
  | @symm d1 d2 h ih =>
      intro L1 U1 h1 L2 U2 h2
      obtain ⟨hlo, hhi⟩ := ih L2 U2 h2 L1 U1 h1
      exact ⟨hlo.symm, hhi.symm⟩
  | @trans d1 d2 d3 h1 h2 ih1 ih2 =>
      intro L1 U1 hstart L3 U3 hend
      cases hstart
      cases hend
      cases d2 with
      | intv L2 U2 =>
          obtain ⟨hlo1, hhi1⟩ := ih1 L1 U1 rfl L2 U2 rfl
          obtain ⟨hlo2, hhi2⟩ := ih2 L2 U2 rfl L3 U3 rfl
          exact ⟨hlo1.trans hlo2, hhi1.trans hhi2⟩
  | replace template hpq =>
      intro L1 U1 h1 L2 U2 h2
      cases template with
      | intv L U =>
          cases h1
          cases h2
          exact ⟨.replace (Tau.ty L) hpq, .replace (Tau.ty U) hpq⟩

theorem Tau.StructConv.intv_parts
    (h : Tau.StructConv R (Tau.intv L1 U1) (Tau.intv L2 U2)) :
    Tau.StructConv R (Tau.ty L1) (Tau.ty L2) /\
    Tau.StructConv R (Tau.ty U1) (Tau.ty U2) :=
  h.intv_parts_aux L1 U1 rfl L2 U2 rfl

theorem Tau.StructConv.intv_lo
    (h : Tau.StructConv R (Tau.intv L1 U1) (Tau.intv L2 U2)) :
    Tau.StructConv R (Tau.ty L1) (Tau.ty L2) :=
  h.intv_parts.1

theorem Tau.StructConv.intv_hi
    (h : Tau.StructConv R (Tau.intv L1 U1) (Tau.intv L2 U2)) :
    Tau.StructConv R (Tau.ty U1) (Tau.ty U2) :=
  h.intv_parts.2

/-- The two endpoint-specific inversions packaged as one motive for the
mutual `Possible`/`Realizes` recursor. -/
private def Path.Endpoint.Realizes.Invariant
    (Gamma : Ctx n) (sigma : Store n) (endpoint : Path.Endpoint n) :
    Tau n k -> Prop
| .ty T =>
    forall x, endpoint = .val x -> Store.Possible Gamma sigma x T
| .intv L U =>
    forall W, endpoint = .type W ->
      Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty L) (Tau.ty W) /\
      Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty W) (Tau.ty U)

private theorem Path.Endpoint.Realizes.invariant
    (h : Path.Endpoint.Realizes Gamma sigma endpoint d) :
    Path.Endpoint.Realizes.Invariant Gamma sigma endpoint d := by
  refine Path.Endpoint.Realizes.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun endpoint d _ =>
      Path.Endpoint.Realizes.Invariant Gamma sigma endpoint d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro x T hp _ x' heq
    cases heq
    exact hp
  · intro L W U hlo hhi W' heq
    cases heq
    exact ⟨hlo, hhi⟩
  · intro endpoint k d1 d2 hr hc ih
    cases d1 with
    | ty S =>
        cases d2 with
        | ty T =>
            intro x heq
            exact Store.Possible.conv (ih x heq) hc
    | intv L1 U1 =>
        cases d2 with
        | intv L2 U2 =>
            intro W heq
            obtain ⟨hlo, hhi⟩ := ih W heq
            exact ⟨
              .trans (.conv hc.intv_lo.symm) hlo,
              .trans hhi (.conv hc.intv_hi)⟩

theorem Path.Endpoint.Realizes.val_possible
    (h : Path.Endpoint.Realizes Gamma sigma (.val x) (Tau.ty T)) :
    Store.Possible Gamma sigma x T :=
  h.invariant x rfl

/-- Inversion of a realized type-definition endpoint, including trailing
runtime conversion. -/
theorem Path.Endpoint.Realizes.type_bounds
    (h : Path.Endpoint.Realizes Gamma sigma (.type W) (Tau.intv L U)) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty L) (Tau.ty W) /\
      Tau.StructSub Gamma (Path.RuntimeEq sigma)
        (Tau.ty W) (Tau.ty U) :=
  h.invariant W rfl

/-! ## Exact-store inhabitants -/

/-- A syntax-directed value in an exact store inhabits its precise
introduction type. -/
theorem Tm.StructPrecise.possible_of_binds
    (hprecise : Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P)
    (hbind : Store.Binds sigma x v)
    (hctx : Ctx.Binds Gamma x P) :
    Store.Possible Gamma sigma x P := by
  cases hprecise with
  | abs hbody hwf =>
      exact .fun hbind hctx (.abs hbody hwf) .refl .refl
  | pair hy hz =>
      apply Store.Possible.pair hbind
        (.promote (.var hy) .refl) (.single .var)
      simpa only [Def.endpoint, Tau.weaken_open] using
        (Path.Endpoint.Realizes.val
          (Store.Possible.single
            (Gamma := Gamma) (sigma := sigma)
            (p := Path.var _) Path.Resolve.var))
  | tpair hy hwf =>
      apply Store.Possible.pair hbind
        (.promote (.var hy) .refl) (.single .var)
      simpa only [Def.endpoint, Tau.weaken_open] using
        (Path.Endpoint.Realizes.type
          (Gamma := Gamma) (sigma := sigma)
          (L := _) (W := _) (U := _) .refl .refl)

/-- Every exact context entry is a possible inhabitant at the aligned store
location. -/
theorem Store.StructPreciseTy.possible_of_ctx_binds
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hctx : Ctx.Binds Gamma x P) :
    Store.Possible Gamma sigma x P := by
  obtain ⟨v, hbind, hprecise⟩ := hstore.of_ctx_binds hctx
  exact hprecise.possible_of_binds hbind hctx

end LambdaP.Repaired
