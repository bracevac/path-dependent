import LambdaP.Original.StructuralPrecisePushbackCounterexample

/-!
The exact-store singleton function pushback property is also false.

`StructuralPrecisePushbackCounterexample` derives `Top` below the exact
function type of a stored closure `g`, using an exact `Top..Top` member.  We
append a second closure `f` whose domain is `Bot`.  Then

`{f} <: Top <: type(g)`

observes `f` at a function with domain `Top`, although its exact domain is
`Bot`.  Function pushback would require `Top <: Bot`.  A small mutual shape
interpretation proves that no such derivation exists in this context.  It
covers structural conversion, primitive transitivity, promotion, abstract
bounds, and dependent pairs.
-/

namespace LambdaP.Original
namespace StructuralPreciseFunctionPushbackCounterexample

/-! ## Append a closure with domain `Bot` -/

abbrev fType : Ty 2 :=
  Ty.Fun Ty.Bot (Ty.Single (Path.var 0))

abbrev fValue : Tm 2 :=
  Tm.abs Ty.Bot (Tm.path (Path.var 0))

theorem f_value : fValue.IsValue := by
  exact .abs

theorem f_precise :
    Tm.StructPrecise StructuralPrecisePushbackCounterexample.Gamma
      (Path.RuntimeEq StructuralPrecisePushbackCounterexample.sigma)
      fValue fType := by
  exact Tm.StructPrecise.abs
    (Tm.StructCheck.path (Path.StructCheck.var Ctx.Binds.here))
    Tau.StructWf.bot

abbrev Gamma : Ctx 3 :=
  StructuralPrecisePushbackCounterexample.Gamma.snoc fType

abbrev sigma : Store 3 :=
  Store.val StructuralPrecisePushbackCounterexample.sigma fValue f_value

theorem store_precise : Store.StructPreciseTy Gamma sigma := by
  exact Store.StructPreciseTy.val
    StructuralPrecisePushbackCounterexample.store_precise f_precise f_value

abbrev f : Fin 3 := 0
abbrev qRoot : Fin 3 := 1
abbrev g : Fin 3 := 2

abbrev exactFType : Ty 3 := fType.weaken
abbrev observedGType : Ty 3 :=
  Ty.Fun Ty.Top (Ty.Single (Path.var 0))

theorem f_context : Ctx.Binds Gamma f exactFType := by
  exact Ctx.Binds.here

/-- Weakening the two-cell derivation preserves `Top <: type(g)` under the
new exact allocation. -/
theorem top_sub_observed_function :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty Ty.Top) (Tau.ty observedGType) := by
  simpa only [Gamma, sigma, observedGType,
    StructuralPrecisePushbackCounterexample.fType,
    StructuralPrecisePushbackCounterexample.fType0,
    Tau.weaken, Ty.weaken, Tau.rename, Ty.rename, Path.rename] using
    StructuralPrecisePushbackCounterexample.top_sub_function.weaken_runtime
      fType fValue f_value

/-- The new closure singleton is therefore below the older closure's
function type. -/
theorem f_singleton_sub_observed_function :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var f))) (Tau.ty observedGType) := by
  exact Tau.StructSub.trans Tau.StructSub.top top_sub_observed_function

/-! ## `Top <: Bot` remains impossible -/

mutual

/-- Types which do not expose `Bot` at an eliminable positive position.
Function domains and codomains are intentionally ignored: the structural
path judgment has no function eliminator. -/
def Ty.BottomSafe : LambdaP.Original.Ty n -> Prop
| .Top => True
| .Bot => False
| .Fun _ _ => True
| .Pair S _ d => Ty.BottomSafe S /\ Tau.BottomSafe d
| .Single _ => True

/-- For an interval only its upper bound is exposed by `sel_hi`. -/
def Tau.BottomSafe : Tau n k -> Prop
| .ty T => Ty.BottomSafe T
| .intv _ U => Ty.BottomSafe U

end

mutual

theorem Ty.BottomSafe.rename_iff
    (T : LambdaP.Original.Ty n) (rho : FinFun n m) :
    Ty.BottomSafe (T.rename rho) <-> Ty.BottomSafe T :=
  match T with
  | .Top => Iff.rfl
  | .Bot => Iff.rfl
  | .Fun _ _ => Iff.rfl
  | .Pair S a d => by
      simp only [Ty.rename, Ty.BottomSafe,
        Ty.BottomSafe.rename_iff S rho,
        Tau.BottomSafe.rename_iff d rho.ext]
  | .Single p => Iff.rfl

theorem Tau.BottomSafe.rename_iff
    (d : Tau n k) (rho : FinFun n m) :
    Tau.BottomSafe (d.rename rho) <-> Tau.BottomSafe d :=
  match d with
  | .ty T => by
      simp only [Tau.rename, Tau.BottomSafe,
        Ty.BottomSafe.rename_iff]
  | .intv L U => by
      simp only [Tau.rename, Tau.BottomSafe,
        Ty.BottomSafe.rename_iff]

end


mutual

theorem Ty.BottomSafe.subst_iff
    (T : LambdaP.Original.Ty n) (rho : PathSubst n m) :
    Ty.BottomSafe (T.subst rho) <-> Ty.BottomSafe T :=
  match T with
  | .Top => Iff.rfl
  | .Bot => Iff.rfl
  | .Fun _ _ => Iff.rfl
  | .Pair S a d => by
      simp only [Ty.subst, Ty.BottomSafe,
        Ty.BottomSafe.subst_iff S rho,
        Tau.BottomSafe.subst_iff d rho.lift]
  | .Single p => Iff.rfl

theorem Tau.BottomSafe.subst_iff
    (d : Tau n k) (rho : PathSubst n m) :
    Tau.BottomSafe (d.subst rho) <-> Tau.BottomSafe d :=
  match d with
  | .ty T => by
      simp only [Tau.subst, Tau.BottomSafe,
        Ty.BottomSafe.subst_iff]
  | .intv L U => by
      simp only [Tau.subst, Tau.BottomSafe,
        Ty.BottomSafe.subst_iff]

end


theorem Tau.BottomSafe.open_iff
    (d : Tau (n + 1) k) (p : Path n) :
    Tau.BottomSafe (d.open p) <-> Tau.BottomSafe d := by
  exact Tau.BottomSafe.subst_iff d (PathSubst.openAt p)

/-- Structural conversion preserves the abstraction because path
replacement cannot change any exposed outer constructor. -/
theorem structConv_bottomSafe_iff
    (h : Tau.StructConv R d1 d2) :
    Tau.BottomSafe d1 <-> Tau.BottomSafe d2 := by
  induction h with
  | refl => exact Iff.rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | replace template hpq =>
      exact (Tau.BottomSafe.open_iff template _).trans
        (Tau.BottomSafe.open_iff template _).symm

/-- Every binding in a context satisfies the positive-position
abstraction. -/
def Ctx.BottomSafe (Delta : Ctx n) : Prop :=
  forall {x T}, Ctx.Binds Delta x T -> Ty.BottomSafe T

theorem Ctx.BottomSafe.nil : Ctx.BottomSafe Ctx.nil := by
  intro x T hx
  cases hx

theorem Ctx.BottomSafe.snoc
    (hctx : Ctx.BottomSafe Delta) (hT : Ty.BottomSafe T) :
    Ctx.BottomSafe (Delta.snoc T) := by
  intro x U hx
  cases hx with
  | here =>
      exact (Ty.BottomSafe.rename_iff T FinFun.weaken).mpr hT
  | there hx =>
      exact (Ty.BottomSafe.rename_iff _ FinFun.weaken).mpr (hctx hx)

private abbrev CheckBottomSafeMotive
    {n : Nat} (Delta : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Delta R p d) : Prop :=
  Ctx.BottomSafe Delta -> Tau.BottomSafe d

private abbrev SubBottomSafeMotive
    {n : Nat} (Delta : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Delta R d1 d2) : Prop :=
  Ctx.BottomSafe Delta -> Tau.BottomSafe d1 -> Tau.BottomSafe d2

/-- Simultaneously, every structural path classification is bottom-safe and
structural subtyping preserves bottom-safety. -/
theorem Path.StructCheck.bottomSafe
    (h : Path.StructCheck Delta R p d)
    (hctx : Ctx.BottomSafe Delta) : Tau.BottomSafe d := by
  induction h using Path.StructCheck.rec
      (motive_2 := SubBottomSafeMotive) with
  | var hb => exact hctx hb
  | sub hp hs ihp ihs => exact ihs hctx (ihp hctx)
  | promote hp hs ihp ihs => exact ihs hctx trivial
  | fst hp ih => exact (ih hctx).1
  | sel_r hp ih =>
      exact (Tau.BottomSafe.open_iff _ _).mpr (ih hctx).2
  | sel_l hp htail hne ihp ihtail => exact ihtail hctx
  | refl => exact fun _ hd => hd
  | trans h1 h2 ih1 ih2 =>
      exact fun hc hd => ih2 hc (ih1 hc hd)
  | conv hconv => exact fun _ hd => (structConv_bottomSafe_iff hconv).mp hd
  | bot => exact fun _ hd => hd.elim
  | top => exact fun _ _ => trivial
  | widen hp ih => exact fun hc _ => ih hc
  | symm hp ih => exact fun _ _ => trivial
  | sel_hi hp hbounds ihp ihbounds => exact fun hc _ => ihp hc
  | sel_lo hp hbounds ihp ihbounds => exact fun _ _ => trivial
  | «fun» hdom hcod ihdom ihcod => exact fun _ _ => trivial
  | pair hfst hsnd ihfst ihsnd =>
      intro hc hd
      exact ⟨ihfst hc hd.1, ihsnd (hc.snoc hd.1) hd.2⟩
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      exact fun hc hd => ihhi hc hd

/-- The subtyping half of `Path.StructCheck.bottomSafe`, exposed for the
non-derivability result below. -/
theorem structSub_bottomSafe
    (h : Tau.StructSub Delta R d1 d2) :
    Ctx.BottomSafe Delta -> Tau.BottomSafe d1 -> Tau.BottomSafe d2 := by
  induction h using Tau.StructSub.rec
      (motive_1 := CheckBottomSafeMotive) with
  | var hb => exact fun hctx => hctx hb
  | sub hp hs ihp ihs => exact fun hctx => ihs hctx (ihp hctx)
  | promote hp hs ihp ihs => exact fun hctx => ihs hctx trivial
  | fst hp ih => exact fun hctx => (ih hctx).1
  | sel_r hp ih =>
      exact fun hctx =>
        (Tau.BottomSafe.open_iff _ _).mpr (ih hctx).2
  | sel_l hp htail hne ihp ihtail => exact fun hctx => ihtail hctx
  | refl => exact fun _ hd => hd
  | trans h1 h2 ih1 ih2 =>
      exact fun hctx hd => ih2 hctx (ih1 hctx hd)
  | conv hconv =>
      exact fun _ hd => (structConv_bottomSafe_iff hconv).mp hd
  | bot => exact fun _ hd => hd.elim
  | top => exact fun _ _ => trivial
  | widen hp ih => exact fun hctx _ => ih hctx
  | symm hp ih => exact fun _ _ => trivial
  | sel_hi hp hbounds ihp ihbounds => exact fun hctx _ => ihp hctx
  | sel_lo hp hbounds ihp ihbounds => exact fun _ _ => trivial
  | «fun» hdom hcod ihdom ihcod => exact fun _ _ => trivial
  | pair hfst hsnd ihfst ihsnd =>
      intro hctx hd
      exact ⟨ihfst hctx hd.1, ihsnd (hctx.snoc hd.1) hd.2⟩
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      exact fun hctx hd => ihhi hctx hd

theorem context_bottomSafe : Ctx.BottomSafe Gamma := by
  apply Ctx.BottomSafe.snoc
  · apply Ctx.BottomSafe.snoc
    · exact Ctx.BottomSafe.nil.snoc
        (T := StructuralPrecisePushbackCounterexample.fType0) trivial
    · exact ⟨trivial, trivial⟩
  · trivial

/-- In this exact context structural subtyping cannot derive the domain
relation demanded by function pushback. -/
theorem not_top_sub_bot :
    ¬ Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty Ty.Top) (Tau.ty Ty.Bot) := by
  intro hbad
  exact structSub_bottomSafe hbad context_bottomSafe trivial

/-! ## Checked failure of signature pushback -/

/-- The exact singleton function pushback property is false: the premise
observes the `Bot`-domain closure at a `Top`-domain function, while its domain
conclusion is underivable. -/
theorem not_singleton_function_pushback :
    ¬ Store.StructPreciseSingletonFunctionPushback Gamma sigma := by
  intro hpush
  have hout := hpush store_precise f_context
    f_singleton_sub_observed_function
  exact not_top_sub_bot hout.1

end StructuralPreciseFunctionPushbackCounterexample
end LambdaP.Original
