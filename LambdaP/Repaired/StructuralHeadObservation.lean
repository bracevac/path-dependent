import LambdaP.Repaired.StructuralPreciseCanonical

/-!
A head-observation attempt for exact structural stores.

The source canonical proof uses `Path.Ty.functional`: a singleton or type
selection is interpreted through one precise path type, and any second path
typing derivation has definitionally the same result.  `Path.StructCheck` is
not functional, because it admits subsumption and promotion.  This module
records the exact replacement needed by the same proof: coherence of the
concrete heads admitted by two structural views of one path, together with
coherence under runtime conversion.

Under those two observations, primitive transitivity is harmless: admitted
heads compose by ordinary induction on `Tau.StructSub`.  Thus the remaining
gap is not transitivity inversion.  It is the proof that exact-store path
views are coherent, particularly the two interval views compared in
`sel_hi`.  A direct recursive interpretation of that fact makes the lower
interval map negative, which is the precise positivity obstruction met by
the unindexed realization attempt.
-/

namespace LambdaP.Repaired

/-- Runtime heads distinguished by the evaluator.  Pair observations retain
both the label and the kind of the stored member. -/
inductive Tau.ConcreteHead : Type where
| function
| pair (a : Name) (k : Kind)
deriving DecidableEq

/-- The structural analogue of the source `Tau.MayHead` predicate.  Its
singleton and selection clauses deliberately retain the structural path
view through which the head was exposed. -/
inductive Tau.StructMayHead
    (Gamma : Ctx n) (R : Path n -> Path n -> Prop) :
    Tau n k -> Tau.ConcreteHead -> Prop where
| top : Tau.StructMayHead Gamma R (Tau.ty Ty.Top) h
| function :
    Tau.StructMayHead Gamma R (Tau.ty (Ty.Fun S U)) .function
| pair :
    Tau.StructMayHead Gamma R
      (Tau.ty (Ty.Pair (k := k) S a d)) (.pair a k)
| single :
    Path.StructCheck Gamma R p (Tau.ty T) ->
    Tau.StructMayHead Gamma R (Tau.ty T) h ->
    Tau.StructMayHead Gamma R (Tau.ty (Ty.Single p)) h
| tsel :
    Path.StructCheck Gamma R (p.sel A) (Tau.intv L U) ->
    Tau.StructMayHead Gamma R (Tau.ty U) h ->
    Tau.StructMayHead Gamma R (Tau.ty (Ty.TSel p A)) h
| interval :
    Tau.StructMayHead Gamma R (Tau.ty U) h ->
    Tau.StructMayHead Gamma R (Tau.intv L U) h

/-- The two genuinely semantic observations needed to replay the small
source `MayHead` proof for structural checking.

`check` is used exactly by `widen` and `sel_hi`.  In the latter case `d1`
and `d2` are two interval views of the same selected member.  `conv` is used
only by the structural runtime-conversion rule. -/
structure Tau.StructMayHead.Laws
    (Gamma : Ctx n) (R : Path n -> Path n -> Prop) : Prop where
  check : forall {k : Kind} {p : Path n} {d1 d2 : Tau n k}
      {head : Tau.ConcreteHead},
    Path.StructCheck Gamma R p d1 ->
    Path.StructCheck Gamma R p d2 ->
    Tau.StructMayHead Gamma R d1 head ->
    Tau.StructMayHead Gamma R d2 head
  conv : forall {k : Kind} {d1 d2 : Tau n k}
      {head : Tau.ConcreteHead},
    Tau.StructConv R d1 d2 ->
    Tau.StructMayHead Gamma R d1 head ->
    Tau.StructMayHead Gamma R d2 head

/-- Once structural path views are head-coherent, structural subtyping
preserves every concrete-head observation.  Notice that the transitivity
case is plain composition. -/
theorem Tau.StructSub.structMayHead
    (laws : Tau.StructMayHead.Laws Gamma R)
    (hs : Tau.StructSub Gamma R d1 d2)
    (hh : Tau.StructMayHead Gamma R d1 head) :
    Tau.StructMayHead Gamma R d2 head := by
  induction hs using Tau.StructSub.rec
      (motive_1 := fun _ _ _ _ _ _ => True) with
  | var => trivial
  | sub => trivial
  | promote => trivial
  | fst => trivial
  | sel_r => trivial
  | sel_l => trivial
  | refl => exact hh
  | trans _ _ ih1 ih2 => exact ih2 laws (ih1 laws hh)
  | conv hc => exact laws.conv hc hh
  | bot => cases hh
  | top => exact .top
  | widen hp =>
      cases hh with
      | single hp' hh' => exact laws.check hp' hp hh'
  | symm hp => exact .single hp hh
  | sel_hi hp hbounds ihp ihbounds =>
      cases hh with
      | tsel hp' hh' =>
          cases laws.check hp' hp (Tau.StructMayHead.interval hh') with
          | interval hhTarget => exact hhTarget
  | sel_lo hp hbounds ihp ihbounds =>
      exact .tsel hp (ihbounds laws hh)
  | «fun» hdom hcod ihdom ihcod =>
      cases hh
      exact .function
  | pair_fst hfst ihfst =>
      cases hh
      exact .pair
  | pair_single_member hp hsnd hopen ihp ihsnd ihopen =>
      cases hh
      exact .pair
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      cases hh with
      | interval hh' => exact .interval (ihhi laws hh')

/-! ## Exact-store read-off -/

/-- The outstanding exact-store property, now stated without any reference
to function residues or preservation.  This is the precise head-only
fundamental lemma attempted by the CPS interpretation. -/
def Store.StructPreciseTy.HeadObservation
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  Store.StructPreciseTy Gamma sigma /\
    Tau.StructMayHead.Laws Gamma (Path.RuntimeEq sigma)

private theorem Tau.StructMayHead.function_head
    (h : Tau.StructMayHead Gamma R
      (Tau.ty (Ty.Fun S U)) head) :
    head = .function := by
  cases h
  rfl

private theorem Tau.StructMayHead.pair_head
    {k : Kind} {d : Tau (n + 1) k}
    (h : Tau.StructMayHead Gamma R
      (Tau.ty (Ty.Pair S a d)) head) :
    head = .pair a k := by
  cases h
  rfl

/-- Head coherence is already sufficient for the unconditional operational
shape boundary.  The proof uses only exact store inversion and the small
head-preservation theorem above. -/
theorem Store.StructPreciseTy.singletonHeadPushback_of_headObservation
    (hobs : Store.StructPreciseTy.HeadObservation Gamma sigma) :
    Store.StructPreciseSingletonHeadPushback Gamma sigma where
  function := by
    intro x S U hstore hsub
    obtain ⟨v, P, hbind, hctx, hprecise⟩ := hstore.lookup_exists x
    cases hprecise with
    | abs hbody hwf =>
        exact ⟨_, _, hbind⟩
    | pair hy hz =>
        have hsource : Tau.StructMayHead Gamma (Path.RuntimeEq sigma)
            (Tau.ty (Ty.Single (Path.var x))) (.pair _ .star) :=
          .single (.var hctx) .pair
        have htarget := hsub.structMayHead hobs.2 hsource
        have : Tau.ConcreteHead.pair _ .star = .function :=
          htarget.function_head
        cases this
    | tpair hy hwf =>
        have hsource : Tau.StructMayHead Gamma (Path.RuntimeEq sigma)
            (Tau.ty (Ty.Single (Path.var x))) (.pair _ .iota) :=
          .single (.var hctx) .pair
        have htarget := hsub.structMayHead hobs.2 hsource
        have : Tau.ConcreteHead.pair _ .iota = .function :=
          htarget.function_head
        cases this
  pair := by
    intro x S a k d hstore hsub
    obtain ⟨v, P, hbind, hctx, hprecise⟩ := hstore.lookup_exists x
    cases hprecise with
    | abs hbody hwf =>
        have hsource : Tau.StructMayHead Gamma (Path.RuntimeEq sigma)
            (Tau.ty (Ty.Single (Path.var x))) .function :=
          .single (.var hctx) .function
        have htarget := hsub.structMayHead hobs.2 hsource
        have : Tau.ConcreteHead.function = .pair a k :=
          htarget.pair_head
        cases this
    | pair hy hz =>
        have hsource : Tau.StructMayHead Gamma (Path.RuntimeEq sigma)
            (Tau.ty (Ty.Single (Path.var x))) (.pair _ .star) :=
          .single (.var hctx) .pair
        have htarget := hsub.structMayHead hobs.2 hsource
        have heq : Tau.ConcreteHead.pair _ .star = .pair a k :=
          htarget.pair_head
        injection heq with hlabel hkind
        cases hlabel
        cases hkind
        exact ⟨_, _, hbind⟩
    | tpair hy hwf =>
        have hsource : Tau.StructMayHead Gamma (Path.RuntimeEq sigma)
            (Tau.ty (Ty.Single (Path.var x))) (.pair _ .iota) :=
          .single (.var hctx) .pair
        have htarget := hsub.structMayHead hobs.2 hsource
        have heq : Tau.ConcreteHead.pair _ .iota = .pair a k :=
          htarget.pair_head
        injection heq with hlabel hkind
        cases hlabel
        cases hkind
        exact ⟨_, _, hbind⟩

end LambdaP.Repaired
