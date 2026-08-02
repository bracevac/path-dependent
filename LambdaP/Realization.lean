import LambdaP.StructuralRealization
import LambdaP.StructuralPathSubstitution
import LambdaP.StructuralConversionInversion

/-!
Proof-relevant semantic maps for the calculus.

The ordinary realization in `StructuralRealization` records interval bounds
as structural-subtyping derivations.  That is enough for endpoint inversion,
but not for a structural proof of `sel_lo`/`sel_hi`: interpreting one of
those stored derivations would be a recursive call on a proof which is not a
subterm of the current derivation.  Replacing the bounds by functions is not
strictly positive.

The relations below defunctionalize those functions.  In particular, a
realized interval stores finite `Tau.SemMap` codes for its lower and upper
maps.  The pair-subtyping rules are reflected directly: first
components may widen while the member is unchanged; changing a member at a
singleton first-component type carries an explicit map between the two
members opened at the singleton path.  At run time the stored first component
co-resolves with that path, so conversion moves the stored member to the
explicit opening, the finite map acts there, and conversion moves it back.

This removes the construction-side circularity of the unrestricted pair
rule without imposing a step index or a DOT-style stratification discipline.
Interpretation is kept separate because runtime conversion requires
component inversion below binders.
-/

namespace LambdaP

mutual

/-- Canonical, conversion-normalized evidence that a store location
inhabits a proper type. -/
inductive Store.MappedPossible
    (Gamma : Ctx n) (sigma : Store n) : Fin n -> Ty n -> Prop where
| top : Store.MappedPossible Gamma sigma x Ty.Top
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
    Store.MappedPossible Gamma sigma x (Ty.Fun S U)
| pair {k : Kind} {delta : Def n k} {d : Tau (n + 1) k} :
    Store.Binds sigma x (@Tm.pair n k y a delta) ->
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var y) (Tau.ty S) ->
    Store.MappedPossible Gamma sigma y S ->
    Path.Endpoint.MappedRealizes Gamma sigma (Def.endpoint delta)
      (d.open (Path.var y)) ->
    Store.MappedPossible Gamma sigma x (Ty.Pair S a d)
| single :
    Path.Resolve p sigma (.val x) ->
    Store.MappedPossible Gamma sigma x (Ty.Single p)
| tsel :
    Path.Resolve (p.sel A) sigma (.type W) ->
    Store.MappedPossible Gamma sigma x W ->
    Store.MappedPossible Gamma sigma x (Ty.TSel p A)

/-- Endpoint realization whose interval bounds are semantic-map codes. -/
inductive Path.Endpoint.MappedRealizes
    (Gamma : Ctx n) (sigma : Store n) :
    Path.Endpoint n -> Tau n k -> Prop where
| val :
    Store.MappedPossible Gamma sigma x T ->
    Path.Endpoint.MappedRealizes Gamma sigma (.val x) (Tau.ty T)
| type :
    Tau.SemMap Gamma sigma (Tau.ty L) (Tau.ty W) ->
    Tau.SemMap Gamma sigma (Tau.ty W) (Tau.ty U) ->
    Path.Endpoint.MappedRealizes Gamma sigma (.type W) (Tau.intv L U)

/-- A finite code for a semantic map.  Static premises are retained so that
erasure yields the exact structural-subtyping derivation used by typing and
preservation. -/
inductive Tau.SemMap (Gamma : Ctx n) (sigma : Store n) :
    Tau n k -> Tau n k -> Prop where
| refl : Tau.SemMap Gamma sigma d d
| trans :
    Tau.SemMap Gamma sigma d1 d2 ->
    Tau.SemMap Gamma sigma d2 d3 ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) d1 d3 ->
    Tau.SemMap Gamma sigma d1 d3
| conv :
    Tau.StructConv (Path.RuntimeEq sigma) d1 d2 ->
    Tau.SemMap Gamma sigma d1 d2
| bot : Tau.SemMap Gamma sigma (Tau.ty Ty.Bot) (Tau.ty T)
| top : Tau.SemMap Gamma sigma (Tau.ty T) (Tau.ty Ty.Top)
| widen :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty T) ->
    Path.Resolve p sigma (.val x) ->
    Store.MappedPossible Gamma sigma x T ->
    Tau.SemMap Gamma sigma (Tau.ty (Ty.Single p)) (Tau.ty T)
| single_alias :
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      p (Tau.ty (Ty.Single q)) ->
    Path.Resolve p sigma (.val x) ->
    Path.Resolve q sigma (.val x) ->
    Tau.SemMap Gamma sigma
      (Tau.ty (Ty.Single q)) (Tau.ty (Ty.Single p))
| sel_hi :
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (p.sel A) (Tau.intv S T) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty T) ->
    Path.Resolve (p.sel A) sigma (.type W) ->
    Tau.SemMap Gamma sigma (Tau.ty W) (Tau.ty T) ->
    Tau.SemMap Gamma sigma (Tau.ty (Ty.TSel p A)) (Tau.ty T)
| sel_lo :
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (p.sel A) (Tau.intv S T) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty T) ->
    Path.Resolve (p.sel A) sigma (.type W) ->
    Tau.SemMap Gamma sigma (Tau.ty S) (Tau.ty W) ->
    Tau.SemMap Gamma sigma (Tau.ty S) (Tau.ty (Ty.TSel p A))
| fun :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S') (Tau.ty S) ->
    Tau.StructSub (Gamma.snoc S')
      (Path.ScopedLift (Path.RuntimeEq sigma))
      (Tau.ty T) (Tau.ty T') ->
    Tau.SemMap Gamma sigma
      (Tau.ty (Ty.Fun S T)) (Tau.ty (Ty.Fun S' T'))
| pair_fst :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty S') ->
    Tau.SemMap Gamma sigma (Tau.ty S) (Tau.ty S') ->
    Tau.SemMap Gamma sigma
      (Tau.ty (Ty.Pair S a d)) (Tau.ty (Ty.Pair S' a d))
| pair_single_member :
    Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty P) ->
    Tau.StructSub (Gamma.snoc (Ty.Single p))
      (Path.ScopedLift (Path.RuntimeEq sigma)) d d' ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (d.open p) (d'.open p) ->
    Tau.SemMap Gamma sigma (d.open p) (d'.open p) ->
    Tau.SemMap Gamma sigma
      (Tau.ty (Ty.Pair (Ty.Single p) a d))
      (Tau.ty (Ty.Pair (Ty.Single p) a d'))
| bounds :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S') (Tau.ty S) ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty T) (Tau.ty T') ->
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty S) (Tau.ty T) ->
    Tau.SemMap Gamma sigma (Tau.ty S') (Tau.ty S) ->
    Tau.SemMap Gamma sigma (Tau.ty T) (Tau.ty T') ->
    Tau.SemMap Gamma sigma
      (Tau.intv S T) (Tau.intv S' T')

end

/-! ## Erasure -/

/-- Forget semantic evidence and recover the structural derivation denoted
by a finite map code. -/
theorem Tau.SemMap.erase
    (h : Tau.SemMap Gamma sigma d1 d2) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma) d1 d2 := by
  cases h with
  | refl => exact .refl
  | trans h1 h2 hstruct => exact hstruct
  | conv hc => exact .conv hc
  | bot => exact .bot
  | top => exact .top
  | widen hp hr hpossible => exact .widen hp
  | single_alias hp hrp hrq => exact .symm hp
  | sel_hi hp hbounds hr hmap => exact .sel_hi hp hbounds
  | sel_lo hp hbounds hr hmap => exact .sel_lo hp hbounds
  | «fun» hdom hcod => exact .fun hdom hcod
  | pair_fst hdom hmap => exact .pair_fst hdom
  | pair_single_member hp hscoped hopen hmap =>
      exact .pair_single_member hp hscoped hopen
  | bounds hlo hhi hnonempty hmapLo hmapHi =>
      exact .bounds hlo hhi hnonempty

/-! ## Exact-store base realization -/

theorem Tm.StructPrecise.mappedPossible_of_binds
    (hprecise : Tm.StructPrecise Gamma (Path.RuntimeEq sigma) v P)
    (hbind : Store.Binds sigma x v)
    (hctx : Ctx.Binds Gamma x P) :
    Store.MappedPossible Gamma sigma x P := by
  cases hprecise with
  | abs hbody hwf =>
      exact .fun hbind hctx (.abs hbody hwf) .refl .refl
  | pair hy hz =>
      apply Store.MappedPossible.pair hbind
        (.promote (.var hy) .refl) (.single .var)
      simpa only [Def.endpoint, Tau.weaken_open] using
        (Path.Endpoint.MappedRealizes.val
          (Store.MappedPossible.single
            (Gamma := Gamma) (sigma := sigma)
            (p := Path.var _) Path.Resolve.var))
  | tpair hy hwf =>
      apply Store.MappedPossible.pair hbind
        (.promote (.var hy) .refl) (.single .var)
      simpa only [Def.endpoint, Tau.weaken_open] using
        (Path.Endpoint.MappedRealizes.type
          (Gamma := Gamma) (sigma := sigma)
          (L := _) (W := _) (U := _)
          Tau.SemMap.refl Tau.SemMap.refl)

theorem Store.StructPreciseTy.mappedPossible_of_ctx_binds
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hctx : Ctx.Binds Gamma x P) :
    Store.MappedPossible Gamma sigma x P := by
  obtain ⟨v, hbind, hprecise⟩ := hstore.of_ctx_binds hctx
  exact hprecise.mappedPossible_of_binds hbind hctx

/-! ## Canonical read-off from mapped possibility -/

/-- A mapped possible function exposes the exact stored abstraction and the
domain/codomain residues used by application preservation. -/
theorem Store.MappedPossible.function_signature
    (h : Store.MappedPossible Gamma sigma x (Ty.Fun S U)) :
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
  cases h with
  | «fun» hbind hctx hprecise hdom hcod =>
      exact ⟨_, _, _, hbind, hctx, hprecise, hdom, hcod⟩

/-- In particular, a mapped possible function location stores an
abstraction. -/
theorem Store.MappedPossible.fun_binding
    (h : Store.MappedPossible Gamma sigma x (Ty.Fun S U)) :
    exists A body, Store.Binds sigma x (Tm.abs A body) := by
  obtain ⟨A, body, B, hbind, _⟩ := h.function_signature
  exact ⟨A, body, hbind⟩

/-- A mapped possible dependent pair stores a pair with the advertised
label and member kind. -/
theorem Store.MappedPossible.pair_binding
    {k : Kind} {d : Tau (n + 1) k}
    (h : Store.MappedPossible Gamma sigma x (Ty.Pair S a d)) :
    exists (y : Fin n) (delta : Def n k),
      Store.Binds sigma x (@Tm.pair n k y a delta) := by
  cases h with
  | pair hbind hfirst hpossible hmember =>
      exact ⟨_, _, hbind⟩

/-! ## Interpretation of finite maps -/

private inductive Tau.MapTag : Type where
| top | bot | function | pair (a : Name) (k : Kind)
| single | tsel | interval
deriving DecidableEq

private def Ty.mapTag : Ty n -> Tau.MapTag
| .Top => .top
| .Bot => .bot
| .Fun _ _ => .function
| .Pair (k := k) _ a _ => .pair a k
| .Single _ => .single
| .TSel _ _ => .tsel

private def Tau.mapTag : Tau n k -> Tau.MapTag
| .ty T => T.mapTag
| .intv _ _ => .interval

@[simp] private theorem Ty.mapTag_open (T : Ty (n + 1)) (p : Path n) :
    (T.open p).mapTag = T.mapTag := by
  cases T <;> rfl

@[simp] private theorem Tau.mapTag_open
    (d : Tau (n + 1) k) (p : Path n) :
    (d.open p).mapTag = d.mapTag := by
  cases d with
  | ty T => exact Ty.mapTag_open T p
  | intv L U => rfl

private theorem Tau.StructConv.mapTag_eq
    (h : Tau.StructConv R d1 d2) : d1.mapTag = d2.mapTag := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | replace template hpq => simp only [Tau.mapTag_open]

def Tau.SemMap.Action
    (Gamma : Ctx n) (sigma : Store n) :
    Tau n k -> Tau n k -> Prop
| d1, d2 =>
    forall endpoint,
      Path.Endpoint.MappedRealizes Gamma sigma endpoint d1 ->
      Path.Endpoint.MappedRealizes Gamma sigma endpoint d2

def Tau.SemMap.comp
    (h1 : Tau.SemMap Gamma sigma d1 d2)
    (h2 : Tau.SemMap Gamma sigma d2 d3) :
    Tau.SemMap Gamma sigma d1 d3 :=
  .trans h1 h2 (.trans h1.erase h2.erase)

/-- Mapped realization is invariant under runtime conversion.  Recursing on
the realization (rather than on conversion) makes dependent pair members
genuine recursive subproofs. -/
private theorem Path.Endpoint.MappedRealizes.convert
    (hrealizes : Path.Endpoint.MappedRealizes Gamma sigma endpoint d1) :
    forall d2,
      Tau.StructConv (Path.RuntimeEq sigma) d1 d2 ->
      Path.Endpoint.MappedRealizes Gamma sigma endpoint d2 := by
  refine Path.Endpoint.MappedRealizes.rec
    (motive_1 := fun x S _ => forall T,
      Tau.StructConv (Path.RuntimeEq sigma) (Tau.ty S) (Tau.ty T) ->
      Store.MappedPossible Gamma sigma x T)
    (motive_2 := fun endpoint d1 _ => forall d2,
      Tau.StructConv (Path.RuntimeEq sigma) d1 d2 ->
      Path.Endpoint.MappedRealizes Gamma sigma endpoint d2)
    (motive_3 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrealizes
  · intro x T hc
    cases hc.top_target_eq
    exact .top
  · intro x A body B S U hbind hctx hprecise hdom hcod T hc
    have htag := hc.mapTag_eq
    cases T with
    | Top => cases htag
    | Bot => cases htag
    | Fun S2 U2 =>
        obtain ⟨hcDom, hcCod⟩ := hc.fun_parts
        exact .fun hbind hctx hprecise
          (.trans (.conv hcDom.symm) hdom)
          (.trans (hcod.narrow (.conv hcDom.symm)) (.conv hcCod))
    | Pair S2 a2 d2 => cases htag
    | Single q => cases htag
    | TSel q C => cases htag
  · intro x y a k delta S d hbind hfirst hpossible hmember
      ihFirst ihMember T hc
    have htag := hc.mapTag_eq
    cases T with
    | Top => cases htag
    | Bot => cases htag
    | Fun S2 U2 => cases htag
    | @Pair _ k2 S2 a2 d2 =>
        obtain ⟨hlabel, hkind⟩ := hc.pair_label_kind
        cases hlabel
        cases hkind
        obtain ⟨hcFirst, hcMember⟩ := hc.pair_components
        have hcOpened := hcMember.subst
          (Path.SubstRelHom.openAt
            (Path.RuntimeEq.isEquivCongr sigma) (Path.var y))
        exact .pair hbind (.sub hfirst (.conv hcFirst))
          (ihFirst S2 hcFirst)
          (ihMember (d2.open (Path.var y)) hcOpened)
    | Single q => cases htag
    | TSel q C => cases htag
  · intro p x hr T hc
    have htag := hc.mapTag_eq
    cases T with
    | Top => cases htag
    | Bot => cases htag
    | Fun S U => cases htag
    | Pair S a d => cases htag
    | Single q =>
        have hpq := hc.single_paths
          (Path.RuntimeEq.isEquivCongr sigma)
        exact .single ((hpq.resolve_iff (.val x)).mp hr)
    | TSel q A => cases htag
  · intro W x p A hr hpossible ih T hc
    have htag := hc.mapTag_eq
    cases T with
    | Top => cases htag
    | Bot => cases htag
    | Fun S U => cases htag
    | Pair S a d => cases htag
    | Single q => cases htag
    | TSel q B =>
        obtain ⟨hlabel, hpq⟩ := hc.tsel_parts
          (Path.RuntimeEq.isEquivCongr sigma)
        cases hlabel
        have hsel := (Path.RuntimeEq.isEquivCongr sigma).sel hpq A
        exact .tsel ((hsel.resolve_iff (.type W)).mp hr) hpossible
  · intro x T hpossible ih d2 hc
    cases d2 with
    | ty U => exact .val (ih U hc)
  · intro L W U hlo hhi ihLo ihHi d2 hc
    cases d2 with
    | intv L2 U2 =>
        obtain ⟨hcLo, hcHi⟩ := hc.interval_components
        exact .type ((Tau.SemMap.conv hcLo.symm).comp hlo)
          (hhi.comp (Tau.SemMap.conv hcHi))
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

theorem Tau.StructConv.mapped_action
    (hc : Tau.StructConv (Path.RuntimeEq sigma) d1 d2) :
    Tau.SemMap.Action Gamma sigma d1 d2 := by
  intro endpoint hrealizes
  exact hrealizes.convert d2 hc

/-- Every semantic code acts on mapped realization, provided runtime
conversion acts on it.  The hypothesis is isolated deliberately: all
source constructors, including abstract bounds and the dependent pair
binder, are interpreted below. -/
theorem Tau.SemMap.action_of_conv
    (hconv : forall {k : Kind} {d1 d2 : Tau n k},
      Tau.StructConv (Path.RuntimeEq sigma) d1 d2 ->
      Tau.SemMap.Action Gamma sigma d1 d2)
    (hmap : Tau.SemMap Gamma sigma d1 d2) :
    Tau.SemMap.Action Gamma sigma d1 d2 := by
  refine Tau.SemMap.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun d1 d2 _ => Tau.SemMap.Action Gamma sigma d1 d2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmap
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro k d
    exact fun _ h => h
  · intro k d1 d2 d3 hm1 hm2 hstruct ih1 ih2
    exact fun endpoint hr => ih2 endpoint (ih1 endpoint hr)
  · intro k d1 d2 hc
    exact hconv hc
  · intro T endpoint hsource
    cases hsource with
    | val hp => cases hp
  · intro T endpoint hsource
    cases hsource with
    | val hp => exact .val .top
  · intro p T x hp hr hpossible ih endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | single hr' =>
            cases hr.deterministic hr'
            exact .val hpossible
  · intro p q x hp hrp hrq endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | single hrq' =>
            cases hrq.deterministic hrq'
            exact .val (.single hrp)
  · intro p A S T W hp hbounds hr hupper ih endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | tsel hr' hpossible =>
            cases hr.deterministic hr'
            exact ih (.val _) (.val hpossible)
  · intro p A S T W hp hbounds hr hlower ih endpoint hsource
    have htargetW := ih endpoint hsource
    cases htargetW with
    | val hpossible => exact .val (.tsel hr hpossible)
  · intro S' S T T' hdom hcod endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | «fun» hbind hctx hprecise hsourceDom hsourceCod =>
            exact .val (.fun hbind hctx hprecise
              (.trans hdom hsourceDom)
              (.trans (hsourceCod.narrow hdom) hcod))
  · intro S S' k d a hdom hfirstMap ihFirst endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | @pair x0 y a0 kDelta delta S0 d0
            hbind hfirst hpossible hrealizes =>
            have hfirstTarget := ihFirst (.val y) (.val hpossible)
            cases hfirstTarget with
            | val hpossibleTarget =>
                exact .val (.pair hbind (.sub hfirst hdom)
                  hpossibleTarget hrealizes)
  · intro p P k d d' a hp hscoped hopen hopenMap
      ihOpened endpoint hsource
    cases hsource with
    | val hsourcePossible =>
        cases hsourcePossible with
        | @pair x0 y a0 kDelta delta S0 d0
            hbind hfirst hpossible hmember =>
            cases hpossible with
            | single hpResolve =>
                have hyp : Path.RuntimeEq sigma (Path.var y) p :=
                  .coresolve Path.reduce.var hpResolve.toReduce
                have htoP : Tau.StructConv (Path.RuntimeEq sigma)
                    (d.open (Path.var y)) (d.open p) :=
                  .replace d hyp
                have hfromP : Tau.StructConv (Path.RuntimeEq sigma)
                    (d'.open p) (d'.open (Path.var y)) :=
                  .replace d' hyp.symm
                exact .val (.pair hbind hfirst (.single hpResolve)
                  ((ihOpened _
                    (hmember.convert (d.open p) htoP)).convert
                      (d'.open (Path.var y)) hfromP))
  · intro S' S T T' hlo hhi hnonempty hmapLo hmapHi
      ihLo ihHi endpoint hsource
    cases hsource with
    | type hsourceLo hsourceHi =>
      exact .type (hmapLo.comp hsourceLo) (hsourceHi.comp hmapHi)

theorem Tau.SemMap.action
    (hmap : Tau.SemMap Gamma sigma d1 d2) :
    Tau.SemMap.Action Gamma sigma d1 d2 :=
  hmap.action_of_conv (fun hc => hc.mapped_action)

/-! ## Fundamental theorem for structural path checking and subtyping -/

/-- A path substitution is semantically realized when every source context
entry resolves to an endpoint realizing its substituted type.  Static
context substitution and preservation of the abstract path relation remain
separate hypotheses, because they are also needed to transport the retained
typing premises in semantic-map codes. -/
abbrev Path.MappedSubstitution
    (Gamma : Ctx n) (rho : PathSubst n m)
    (Delta : Ctx m) (sigma : Store m) : Prop :=
  forall {x T}, Ctx.Binds Gamma x T ->
    exists endpoint,
      Path.Resolve (rho x) sigma endpoint /\
      Path.Endpoint.MappedRealizes Delta sigma endpoint
        (Tau.ty (T.subst rho))

/-- The left-looking selection rule follows the first component of the
same resolved pair before resuming lookup at the missed label. -/
private theorem Path.Resolve.sel_miss_fst
    (hp : Path.Resolve p sigma (.val x))
    (hbind : Store.Binds sigma x (Tm.pair y b delta))
    (hne : a ≠ b)
    (htail : Path.Resolve (p.fst.sel a) sigma endpoint) :
    Path.Resolve (p.sel a) sigma endpoint := by
  have hfst := Path.Resolve.fst hp hbind
  have hfstEq := Path.RuntimeEq.of_reduce hfst.toReduce
  have htailEq := (Path.RuntimeEq.isEquivCongr sigma).sel hfstEq a
  exact .sel_miss hp hbind hne
    ((htailEq.resolve_iff endpoint).mp htail)

private abbrev PathMappedSubstMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Gamma R p d) : Prop :=
  forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
      {sigma : Store m},
    Path.StructSubstitution Gamma rho Delta (Path.RuntimeEq sigma) ->
    Path.SubstRelHom R (Path.RuntimeEq sigma) rho ->
    Path.MappedSubstitution Gamma rho Delta sigma ->
    exists endpoint,
      Path.Resolve (p.subst rho) sigma endpoint /\
      Path.Endpoint.MappedRealizes Delta sigma endpoint (d.subst rho)

private abbrev SubMappedSubstMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop :=
  forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
      {sigma : Store m},
    Path.StructSubstitution Gamma rho Delta (Path.RuntimeEq sigma) ->
    Path.SubstRelHom R (Path.RuntimeEq sigma) rho ->
    Path.MappedSubstitution Gamma rho Delta sigma ->
    Tau.SemMap Delta sigma (d1.subst rho) (d2.subst rho)

/-- Fundamental theorem for generalized path checking.  It is stated under
an arbitrary realized simultaneous path substitution so that the proof is
stable under all source binders; the exact-store theorem below is the
identity instance. -/
theorem Path.StructCheck.mapped_subst
    (h : Path.StructCheck Gamma R p d) :
    PathMappedSubstMotive Gamma R p d h := by
  induction h using Path.StructCheck.rec
      (motive_2 := SubMappedSubstMotive) with
  | var hb =>
      intro m rho Delta sigma hctx hrel henv
      exact henv hb
  | sub hp hs ihp ihs =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      have hmap := ihs hctx hrel henv
      exact ⟨endpoint, hresolve, hmap.action endpoint hrealizes⟩
  | promote hp hs ihp ihs =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          have hmap := ihs hctx hrel henv
          refine ⟨.val _, hresolve, ?_⟩
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            hmap.action (.val _)
              (Path.Endpoint.MappedRealizes.val
                (Store.MappedPossible.single hresolve))
  | fst hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y a k delta S d hbind hfirst hfirstPossible hmember =>
              refine ⟨.val y, ?_, ?_⟩
              · simpa only [Path.subst] using
                  Path.Resolve.fst hresolve hbind
              · simpa only [Tau.subst, Ty.subst] using
                  Path.Endpoint.MappedRealizes.val hfirstPossible
  | sel_r hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y a k delta S d hbind hfirst hfirstPossible hmember =>
              have hfstR := Path.Resolve.fst hresolve hbind
              have heq := Path.RuntimeEq.of_reduce hfstR.toReduce
              have hmember' := hmember.convert _
                (Tau.StructConv.replace _ heq.symm)
              cases S with
              | val z =>
                  refine ⟨.val z, ?_, ?_⟩
                  · simpa only [Path.subst] using
                      Path.Resolve.sel_val hresolve hbind
                  · simpa only [Path.subst, Tau.subst, Ty.subst,
                      Tau.open_subst, Def.endpoint] using hmember'
              | type W =>
                  refine ⟨.type W, ?_, ?_⟩
                  · simpa only [Path.subst] using
                      Path.Resolve.sel_type hresolve hbind
                  · simpa only [Path.subst, Tau.subst, Ty.subst,
                      Tau.open_subst, Def.endpoint] using hmember'
  | sel_l hp htail hne ihp ihtail =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      obtain ⟨tailEndpoint, htailResolve, htailRealizes⟩ :=
        ihtail hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y b k delta S d hbind hfirst hfirstPossible hmember =>
              refine ⟨tailEndpoint, ?_, htailRealizes⟩
              simpa only [Path.subst] using
                Path.Resolve.sel_miss_fst hresolve hbind hne htailResolve
  | refl =>
      intro m rho Delta sigma hctx hrel henv
      exact .refl
  | trans h1 h2 ih1 ih2 =>
      intro m rho Delta sigma hctx hrel henv
      exact (ih1 hctx hrel henv).comp (ih2 hctx hrel henv)
  | conv hc =>
      intro m rho Delta sigma hctx hrel henv
      exact .conv (hc.subst hrel)
  | bot =>
      intro m rho Delta sigma hctx hrel henv
      simp only [Tau.subst, Ty.subst]
      exact .bot
  | top =>
      intro m rho Delta sigma hctx hrel henv
      simp only [Tau.subst, Ty.subst]
      exact .top
  | widen hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.widen (hp.subst hctx hrel) hresolve hpossible
  | symm hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | single hqresolve =>
              simpa only [Tau.subst, Ty.subst, Path.subst] using
                Tau.SemMap.single_alias
                  (hp.subst hctx hrel) hresolve hqresolve
  | sel_hi hp hbounds ihp ihbounds =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | type hlower hupper =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.sel_hi (hp.subst hctx hrel)
              (hbounds.subst hctx hrel) hresolve hupper
  | sel_lo hp hbounds ihp ihbounds =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | type hlower hupper =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.sel_lo (hp.subst hctx hrel)
              (hbounds.subst hctx hrel) hresolve hlower
  | «fun» hdom hcod ihdom ihcod =>
      intro m rho Delta sigma hctx hrel henv
      simpa only [Tau.subst, Ty.subst] using
        Tau.SemMap.fun (hdom.subst hctx hrel)
          (hcod.subst hctx.lift hrel.scoped)
  | pair_fst hdom ihdom =>
      intro m rho Delta sigma hctx hrel henv
      simpa only [Tau.subst, Ty.subst] using
        Tau.SemMap.pair_fst (hdom.subst hctx hrel)
          (ihdom hctx hrel henv)
  | pair_single_member hp hscoped hopen ihp ihscoped ihopen =>
      intro m rho Delta sigma hctx hrel henv
      have hopen' := hopen.subst hctx hrel
      have hopenMap := ihopen hctx hrel henv
      rw [Tau.open_subst, Tau.open_subst] at hopen' hopenMap
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.SemMap.pair_single_member (hp.subst hctx hrel)
          (hscoped.subst hctx.lift hrel.scoped) hopen' hopenMap
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro m rho Delta sigma hctx hrel henv
      exact Tau.SemMap.bounds
        (hlo.subst hctx hrel) (hhi.subst hctx hrel)
        (hnonempty.subst hctx hrel)
        (ihlo hctx hrel henv) (ihhi hctx hrel henv)

/-- Fundamental theorem for structural generalized subtyping.  Semantic-map
construction follows the source derivation structurally.  The explicit
opened premise of `pair_single_member` is precisely the recursive evidence
needed for the dependent member case. -/
theorem Tau.StructSub.mapped_subst
    (h : Tau.StructSub Gamma R d1 d2) :
    SubMappedSubstMotive Gamma R d1 d2 h := by
  induction h using Tau.StructSub.rec
      (motive_1 := PathMappedSubstMotive) with
  | var hb =>
      intro m rho Delta sigma hctx hrel henv
      exact henv hb
  | sub hp hs ihp ihs =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      exact ⟨endpoint, hresolve,
        (ihs hctx hrel henv).action endpoint hrealizes⟩
  | promote hp hs ihp ihs =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          refine ⟨.val _, hresolve, ?_⟩
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            (ihs hctx hrel henv).action (.val _)
              (Path.Endpoint.MappedRealizes.val
                (Store.MappedPossible.single hresolve))
  | fst hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y a k delta S d hbind hfirst hfirstPossible hmember =>
              refine ⟨.val y, ?_, ?_⟩
              · simpa only [Path.subst] using Path.Resolve.fst hresolve hbind
              · simpa only [Tau.subst, Ty.subst] using
                  Path.Endpoint.MappedRealizes.val hfirstPossible
  | sel_r hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y a k delta S d hbind hfirst hfirstPossible hmember =>
              have hfstR := Path.Resolve.fst hresolve hbind
              have heq := Path.RuntimeEq.of_reduce hfstR.toReduce
              have hmember' := hmember.convert _
                (Tau.StructConv.replace _ heq.symm)
              cases S with
              | val z =>
                  refine ⟨.val z, ?_, ?_⟩
                  · simpa only [Path.subst] using
                      Path.Resolve.sel_val hresolve hbind
                  · simpa only [Path.subst, Tau.subst, Ty.subst,
                      Tau.open_subst, Def.endpoint] using hmember'
              | type W =>
                  refine ⟨.type W, ?_, ?_⟩
                  · simpa only [Path.subst] using
                      Path.Resolve.sel_type hresolve hbind
                  · simpa only [Path.subst, Tau.subst, Ty.subst,
                      Tau.open_subst, Def.endpoint] using hmember'
  | sel_l hp htail hne ihp ihtail =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      obtain ⟨tailEndpoint, htailResolve, htailRealizes⟩ :=
        ihtail hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | @pair x y b k delta S d hbind hfirst hfirstPossible hmember =>
              refine ⟨tailEndpoint, ?_, htailRealizes⟩
              simpa only [Path.subst] using
                Path.Resolve.sel_miss_fst hresolve hbind hne htailResolve
  | refl =>
      intro m rho Delta sigma hctx hrel henv
      exact .refl
  | trans h1 h2 ih1 ih2 =>
      intro m rho Delta sigma hctx hrel henv
      exact (ih1 hctx hrel henv).comp (ih2 hctx hrel henv)
  | conv hc =>
      intro m rho Delta sigma hctx hrel henv
      exact .conv (hc.subst hrel)
  | bot =>
      intro m rho Delta sigma hctx hrel henv
      simp only [Tau.subst, Ty.subst]
      exact .bot
  | top =>
      intro m rho Delta sigma hctx hrel henv
      simp only [Tau.subst, Ty.subst]
      exact .top
  | widen hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.widen (hp.subst hctx hrel) hresolve hpossible
  | symm hp ih =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ih hctx hrel henv
      cases hrealizes with
      | val hpossible =>
          cases hpossible with
          | single hqresolve =>
              simpa only [Tau.subst, Ty.subst, Path.subst] using
                Tau.SemMap.single_alias
                  (hp.subst hctx hrel) hresolve hqresolve
  | sel_hi hp hbounds ihp ihbounds =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | type hlower hupper =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.sel_hi (hp.subst hctx hrel)
              (hbounds.subst hctx hrel) hresolve hupper
  | sel_lo hp hbounds ihp ihbounds =>
      intro m rho Delta sigma hctx hrel henv
      obtain ⟨endpoint, hresolve, hrealizes⟩ := ihp hctx hrel henv
      cases hrealizes with
      | type hlower hupper =>
          simpa only [Tau.subst, Ty.subst, Path.subst] using
            Tau.SemMap.sel_lo (hp.subst hctx hrel)
              (hbounds.subst hctx hrel) hresolve hlower
  | «fun» hdom hcod ihdom ihcod =>
      intro m rho Delta sigma hctx hrel henv
      simpa only [Tau.subst, Ty.subst] using
        Tau.SemMap.fun (hdom.subst hctx hrel)
          (hcod.subst hctx.lift hrel.scoped)
  | pair_fst hdom ihdom =>
      intro m rho Delta sigma hctx hrel henv
      simpa only [Tau.subst, Ty.subst] using
        Tau.SemMap.pair_fst (hdom.subst hctx hrel)
          (ihdom hctx hrel henv)
  | pair_single_member hp hscoped hopen ihp ihscoped ihopen =>
      intro m rho Delta sigma hctx hrel henv
      have hopen' := hopen.subst hctx hrel
      have hopenMap := ihopen hctx hrel henv
      rw [Tau.open_subst, Tau.open_subst] at hopen' hopenMap
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.SemMap.pair_single_member (hp.subst hctx hrel)
          (hscoped.subst hctx.lift hrel.scoped) hopen' hopenMap
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro m rho Delta sigma hctx hrel henv
      exact Tau.SemMap.bounds
        (hlo.subst hctx hrel) (hhi.subst hctx hrel)
        (hnonempty.subst hctx hrel)
        (ihlo hctx hrel henv) (ihhi hctx hrel henv)

/-! ## Exact-store identity instance -/

private theorem Path.StructSubstitution.mapped_identity
    (Gamma : Ctx n) (sigma : Store n) :
    Path.StructSubstitution Gamma PathSubst.id Gamma
      (Path.RuntimeEq sigma) := by
  intro x T hb
  simpa only [Path.subst_id, Tau.subst, Ty.subst_id] using
    (Path.StructCheck.var (R := Path.RuntimeEq sigma) hb)

private theorem Path.SubstRelHom.mapped_identity
    (sigma : Store n) :
    Path.SubstRelHom (Path.RuntimeEq sigma) (Path.RuntimeEq sigma)
      PathSubst.id := by
  intro p q hpq
  simpa only [Path.subst_id] using hpq

private theorem Store.StructPreciseTy.mapped_identity
    (hstore : Store.StructPreciseTy Gamma sigma) :
    Path.MappedSubstitution Gamma PathSubst.id Gamma sigma := by
  intro x T hb
  refine ⟨.val x, Path.Resolve.var, ?_⟩
  simpa only [Ty.subst_id] using
    (Path.Endpoint.MappedRealizes.val
      (hstore.mappedPossible_of_ctx_binds hb))

/-- Every structurally checked runtime path resolves to an endpoint realizing
its checked generalized type. -/
theorem Path.StructCheck.mapped_resolves
    (hstore : Store.StructPreciseTy Gamma sigma)
    (h : Path.StructCheck Gamma (Path.RuntimeEq sigma) p d) :
    exists endpoint,
      Path.Resolve p sigma endpoint /\
      Path.Endpoint.MappedRealizes Gamma sigma endpoint d := by
  simpa only [Path.subst_id, Tau.subst_id] using
    h.mapped_subst
      (Path.StructSubstitution.mapped_identity Gamma sigma)
      (Path.SubstRelHom.mapped_identity sigma)
      hstore.mapped_identity

/-- Structural runtime subtyping denotes a semantic map in every exact
store. -/
theorem Tau.StructSub.mapped
    (hstore : Store.StructPreciseTy Gamma sigma)
    (h : Tau.StructSub Gamma (Path.RuntimeEq sigma) d1 d2) :
    Tau.SemMap Gamma sigma d1 d2 := by
  simpa only [Tau.subst_id] using
    h.mapped_subst
      (Path.StructSubstitution.mapped_identity Gamma sigma)
      (Path.SubstRelHom.mapped_identity sigma)
      hstore.mapped_identity

end LambdaP
