import LambdaPHistory.DeepValueInversion

/-!
The application boundary for the deep machine invariant.

Trailing deep subsumption obscures an application's introduction result, but
does not change its two premises.  The inversion theorem below additionally
returns the accumulated suffix as a transformer on arbitrary checked terms.
This avoids inventing a well-formedness premise for the introduction case.

The dynamic application case has two further, logically separate inputs.
`Tm.DeepOpening` substitutes a checked location for one formal binder.
`Store.AppCompatibility` relates the signature observed at a resolving call
site to the syntax-directed signature of the stored abstraction.  The latter
contains only the two facts not already supplied by deep store lookup:

* the resolved argument location checks at the abstraction's own domain;
* after opening, the abstraction's own result can be checked at the result
  observed at the call site.
-/

namespace LambdaPHistory

/-! ## Subsumption-aware application inversion -/

/-- Inversion through every trailing deep-subsumption rule.  `post` is
polymorphic in the checked term, so it can later be applied to the reduct. -/
theorem Tm.DeepCheck.app_inversion_of_eq
    {n : Nat} {Gamma : Ctx n} {E : Path.ConvRel n}
    {u : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma E u T) :
    forall {p q : Path n}, u = Tm.app p q ->
      exists S U,
        Tm.DeepCheck Gamma E (Tm.path p) (Ty.Fun S U) /\
        Tm.DeepCheck Gamma E (Tm.path q) S /\
        (forall {t : Tm n},
          Tm.DeepCheck Gamma E t (U.open q) ->
          Tm.DeepCheck Gamma E t T) := by
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
        fun hresult => Tm.DeepCheck.sub (post hresult) hs hwf⟩

/-- Public form of subsumption-aware application inversion. -/
theorem Tm.DeepCheck.app_inversion
    {n : Nat} {Gamma : Ctx n} {E : Path.ConvRel n}
    {p q : Path n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma E (Tm.app p q) T) :
    exists S U,
      Tm.DeepCheck Gamma E (Tm.path p) (Ty.Fun S U) /\
      Tm.DeepCheck Gamma E (Tm.path q) S /\
      (forall {t : Tm n},
        Tm.DeepCheck Gamma E t (U.open q) ->
        Tm.DeepCheck Gamma E t T) :=
  h.app_inversion_of_eq rfl

/-! ## The local call-signature contract -/

/-- Compatibility between a concrete resolving call and the
syntax-directed signature of the abstraction found in the store.

Deep store lookup supplies `B`, the body derivation under `A`, and the
precise witness in the final premise.  The contract therefore asks only for
argument-domain compatibility and a result-checking transformer.  It does
not assume the desired checked reduct. -/
def Store.AppCompatibility (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {p q : Path n} {x y : Fin n}
      {S : LambdaPHistory.Ty n}
      {U : LambdaPHistory.Ty (n + 1)}
      {A : LambdaPHistory.Ty n} {body : Tm (n + 1)}
      {B : LambdaPHistory.Ty (n + 1)},
    Store.DeepTy Gamma sigma ->
    Path.reduce p sigma x ->
    Path.reduce q sigma y ->
    Store.Binds sigma x (Tm.abs A body) ->
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U) ->
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma) (Tm.path q) S ->
    Tm.DeepPrecise Gamma (Path.RuntimeEq sigma)
      (Tm.abs A body) (Ty.Fun A B) ->
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
        (Tm.path (Path.var y)) A /\
      (forall {t : Tm n},
        Tm.DeepCheck Gamma (Path.RuntimeEq sigma) t
          (B.rename (FinFun.openAt y)) ->
        Tm.DeepCheck Gamma (Path.RuntimeEq sigma) t (U.open q))

/-- Deep lookup, call compatibility, and one-binder opening give the checked
application reduct at the call site's introduction result. -/
theorem Store.DeepTy.open_application
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p q : Path n} {x y : Fin n}
    {S : LambdaPHistory.Ty n}
    {U : LambdaPHistory.Ty (n + 1)}
    {A : LambdaPHistory.Ty n} {body : Tm (n + 1)}
    (hstore : Store.DeepTy Gamma sigma)
    (hopening : Tm.DeepOpening)
    (hcompat : Store.AppCompatibility Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (hfun : Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path p) (Ty.Fun S U))
    (harg : Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path q) S) :
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (body.open y) (U.open q) := by
  obtain ⟨Tpublic, P, hctx, hpublic, hprecise, hsub⟩ :=
    hstore.of_store_binds hbind
  cases hprecise with
  | abs hbody hdomain =>
      obtain ⟨hactual, hresult⟩ :=
        hcompat hstore hp hq hbind hfun harg
          (Tm.DeepPrecise.abs hbody hdomain)
      exact hresult (hopening hbody hactual)

/-! ## Conditional preservation of the machine application step -/

/-- The full historical application transition preserves the deep state
invariant, conditional exactly on binder opening and local call-signature
compatibility.  The inversion `post` applies the original trailing
subsumption to the reduct without reconstructing its derivation. -/
theorem DeepPreserve.app
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n}
    {x y : Fin n} {A : LambdaPHistory.Ty n}
    {body : Tm (n + 1)}
    {T : LambdaPHistory.Ty n}
    (hopening : Tm.DeepOpening)
    (hcompat : Store.AppCompatibility Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (h : State.DeepTy Gamma ⟨sigma, k, Tm.app p q⟩ T) :
    DeepPreserve Gamma ⟨sigma, k, body.open y⟩ T := by
  cases h with
  | ok hstore hcont happ =>
      obtain ⟨S, U, hfun, harg, post⟩ := happ.app_inversion
      have hopened := hstore.open_application hopening hcompat
        hp hq hbind hfun harg
      exact .same (.ok hstore hcont (post hopened))

/-- Packaging for an arbitrary `State.Step` whose source is an application;
dependent elimination identifies its target with the corresponding opened
body. -/
theorem State.Step.deep_app_preservation
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n} {target : State n}
    {T : LambdaPHistory.Ty n}
    (hopening : Tm.DeepOpening)
    (hcompat : Store.AppCompatibility Gamma sigma)
    (step : State.Step ⟨sigma, k, Tm.app p q⟩ target)
    (h : State.DeepTy Gamma ⟨sigma, k, Tm.app p q⟩ T) :
    DeepPreserve Gamma target T := by
  cases step with
  | app hp hq hbind =>
      exact DeepPreserve.app hopening hcompat hp hq hbind h

end LambdaPHistory
