import LambdaPHistory.RefinedPathProgress
import LambdaPHistory.StructuralRefinedProgress

/-!
The source-provenance boundary for refined-store path progress.

The counterexamples for `Path.StructCheck` use structural promotion and
singleton symmetry, neither of which belongs to the original precise
`Path.Ty` judgment.  For source paths the useful invariant is much smaller
than arbitrary type preservation: every concrete head of the precise value
reached by evaluation must be admitted by the type synthesized for the
source path.  Pair observations additionally retain the member label and
kind.

This file formalizes that observation-only provenance, proves its atomic
case directly from `Store.RefinedTy`, and proves that the full provenance
property entails `Path.PairTransport`.  Thus the remaining composite-path
obligation is stated without structural reclassification or an untyped
runtime conversion premise.
-/

namespace LambdaPHistory

/-! ## Observation-only source provenance -/

/-- The two source possible-head interpretations of a precise stored type
are preserved by the proper type synthesized for a resolving path. -/
structure Tau.SourceHeadProvenance
    (Gamma : Ctx n) (P T : LambdaPHistory.Ty n) : Prop where
  head : forall {h : Ty.Head},
    Tau.MayHead Gamma (Tau.ty P) h ->
    Tau.MayHead Gamma (Tau.ty T) h
  pair : forall {a : Name} {k : Kind},
    Tau.MayPairHead Gamma (Tau.ty P) a k ->
    Tau.MayPairHead Gamma (Tau.ty T) a k

/-- Ordinary source subtyping supplies observation provenance immediately.
This is the base fact retained at a refined public store location. -/
theorem Tau.Sub.to_sourceHeadProvenance
    (h : Tau.Sub Gamma (Tau.ty P) (Tau.ty T)) :
    Tau.SourceHeadProvenance Gamma P T :=
  ⟨fun hp => h.mayHead hp, fun hp => h.mayPairHead hp⟩

/-- Source-head provenance for every resolving proper path.  The witness is
the actual precise typing derivation of the reached store cell, not a
structural reclassification of its result variable. -/
def Path.RefinedSourceHeadProvenance
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {p : Path n} {x : Fin n} {T : LambdaPHistory.Ty n},
    Path.reduce p sigma x ->
    Path.Ty Gamma p (Tau.ty T) ->
    exists v P,
      Store.Binds sigma x v /\
      Tm.PreciseTy Gamma v P /\
      Tau.SourceHeadProvenance Gamma P T

/-! ## The unconditional atomic case -/

/-- A refined context entry carries exactly the source-subtyping provenance
needed at an atomic path. -/
theorem Store.RefinedTy.variable_sourceHeadProvenance
    (hstore : Store.RefinedTy Gamma sigma)
    (hctx : Ctx.Binds Gamma x T) :
    exists v P,
      Store.Binds sigma x v /\
      Tm.PreciseTy Gamma v P /\
      Tau.SourceHeadProvenance Gamma P T := by
  obtain ⟨v, P, hbind, hprecise, hpublic, hsub⟩ :=
    hstore.of_ctx_binds hctx
  exact ⟨v, P, hbind, hprecise, hsub.to_sourceHeadProvenance⟩

/-- Consequently the full provenance property already holds for every
atomic source path. -/
theorem Store.RefinedTy.sourceHeadProvenance_var
    (hstore : Store.RefinedTy Gamma sigma)
    (hp : Path.Ty Gamma (Path.var x) (Tau.ty T)) :
    exists v P,
      Store.Binds sigma x v /\
      Tm.PreciseTy Gamma v P /\
      Tau.SourceHeadProvenance Gamma P T := by
  cases hp with
  | var hctx => exact hstore.variable_sourceHeadProvenance hctx

/-! ## The first non-atomic observation -/

/-- If an atomic parent exposes a pair whose first component is itself a
pair, refined lookup forces the runtime first component to have the latter
pair's label and member kind.  This is the `fst` case of the desired
provenance induction, proved solely with source `Tau.Sub` observations. -/
theorem Store.RefinedTy.variable_fst_pair_transport
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {x : Fin n}
    {S : LambdaPHistory.Ty n} {a b : Name}
    {k k' : Kind} {d : Tau (n + 1) k} {e : Tau (n + 1) k'}
    (hstore : Store.RefinedTy Gamma sigma)
    (hctx : Ctx.Binds Gamma x
      (Ty.Pair (Ty.Pair S a d) b e)) :
    exists y z, exists delta : Def n k,
      Path.reduce ((Path.var x).fst) sigma y /\
      Store.Binds sigma y (Tm.pair z a delta) := by
  obtain ⟨v, P, hx, hprecise, hpublic, hsub⟩ :=
    hstore.of_ctx_binds hctx
  cases hprecise with
  | abs hbody hA =>
      exact (Tau.Sub.fun_not_pair hsub).elim
  | @pair Gamma y Sy z Sz c hy hz =>
      obtain ⟨w, Q, hyStore, hyPrecise, hyPublic, hySub⟩ :=
        hstore.of_ctx_binds hy
      cases hyPrecise with
      | abs hbody hA =>
          have hY : Tau.MayHead Gamma (Tau.ty Sy) .arrow :=
            hySub.mayHead Tau.MayHead.arrow
          have hFirst : Tau.MayFstHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.ty (Ty.Single (Path.var z).weaken)))) .arrow :=
            Tau.MayFstHead.pair
              (Tau.MayHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstHead hFirst
          cases hout with
          | pair hh => cases hh
      | @pair Gamma u Su z' Sz' c' hu hz' =>
          have hY : Tau.MayPairHead Gamma (Tau.ty Sy) c' .star :=
            hySub.mayPairHead Tau.MayPairHead.pair
          have hFirst : Tau.MayFstPairHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.ty (Ty.Single (Path.var z).weaken)))) c' .star :=
            Tau.MayFstPairHead.pair
              (Tau.MayPairHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstPairHead hFirst
          cases hout with
          | pair hh =>
              cases hh
              exact ⟨y, u, .val z', .fst Path.reduce.var hx, hyStore⟩
      | @tpair Gamma u Su U c' hu hU =>
          have hY : Tau.MayPairHead Gamma (Tau.ty Sy) c' .iota :=
            hySub.mayPairHead Tau.MayPairHead.pair
          have hFirst : Tau.MayFstPairHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.ty (Ty.Single (Path.var z).weaken)))) c' .iota :=
            Tau.MayFstPairHead.pair
              (Tau.MayPairHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstPairHead hFirst
          cases hout with
          | pair hh =>
              cases hh
              exact ⟨y, u, .type U, .fst Path.reduce.var hx, hyStore⟩
  | @tpair Gamma y Sy U c hy hU =>
      obtain ⟨w, Q, hyStore, hyPrecise, hyPublic, hySub⟩ :=
        hstore.of_ctx_binds hy
      cases hyPrecise with
      | abs hbody hA =>
          have hY : Tau.MayHead Gamma (Tau.ty Sy) .arrow :=
            hySub.mayHead Tau.MayHead.arrow
          have hFirst : Tau.MayFstHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.intv U U).weaken)) .arrow :=
            Tau.MayFstHead.pair
              (Tau.MayHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstHead hFirst
          cases hout with
          | pair hh => cases hh
      | @pair Gamma u Su z' Sz' c' hu hz' =>
          have hY : Tau.MayPairHead Gamma (Tau.ty Sy) c' .star :=
            hySub.mayPairHead Tau.MayPairHead.pair
          have hFirst : Tau.MayFstPairHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.intv U U).weaken)) c' .star :=
            Tau.MayFstPairHead.pair
              (Tau.MayPairHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstPairHead hFirst
          cases hout with
          | pair hh =>
              cases hh
              exact ⟨y, u, .val z', .fst Path.reduce.var hx, hyStore⟩
      | @tpair Gamma u Su V c' hu hV =>
          have hY : Tau.MayPairHead Gamma (Tau.ty Sy) c' .iota :=
            hySub.mayPairHead Tau.MayPairHead.pair
          have hFirst : Tau.MayFstPairHead Gamma
              (Tau.ty (Ty.Pair (Ty.Single (Path.var y)) c
                (Tau.intv U U).weaken)) c' .iota :=
            Tau.MayFstPairHead.pair
              (Tau.MayPairHead.single_ty (Path.Ty.var hy) hY)
          have hout := hsub.mayFstPairHead hFirst
          cases hout with
          | pair hh =>
              cases hh
              exact ⟨y, u, .type V, .fst Path.reduce.var hx, hyStore⟩

/-! ## Provenance implies the operational pair contract -/

/-- Observation provenance rules out an abstraction at a path synthesized
as a pair and forces a stored pair's label and member kind to agree with the
synthesized pair type. -/
theorem Path.RefinedSourceHeadProvenance.pairTransport
    (hprov : Path.RefinedSourceHeadProvenance Gamma sigma) :
    Path.PairTransport Gamma sigma := by
  intro p x S a k d hr hp
  obtain ⟨v, P, hbind, hprecise, hheads⟩ := hprov hr hp
  cases hprecise with
  | abs hbody hA =>
      have hout := hheads.head (Tau.MayHead.arrow)
      cases hout
  | pair hy hz =>
      have hout := hheads.pair (Tau.MayPairHead.pair)
      cases hout
      exact ⟨_, .val _, hbind⟩
  | tpair hy hT =>
      have hout := hheads.pair (Tau.MayPairHead.pair)
      cases hout
      exact ⟨_, .type _, hbind⟩

/-- Refined-store path progress is therefore unconditional once the
source-provenance invariant is established for composite paths. -/
theorem Path.reduce_progress_refined_of_sourceProvenance
    (hstore : Store.RefinedTy Gamma sigma)
    (hprov : Path.RefinedSourceHeadProvenance Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    exists x, Path.reduce p sigma x :=
  Path.reduce_progress_refined_of_pairTransport
    hstore hprov.pairTransport hp

/-!
The attempted direct induction now has a precise stopping point.  The
variable case is `variable_sourceHeadProvenance`.  At `fst`, proving the
result clause requires preservation of a first-component observation from
the reached pair's precise type through the source derivation for the
parent path.  At `sel_r`, it requires the analogous dependent-member
observation; `Tau.StructSub.open_precise_member_runtime` solves only the
binder opening after that source provenance has been retained.  Neither
obligation is implied by broad `Path.StructCheck` canonical forms, which are
formally false.
-/

end LambdaPHistory
