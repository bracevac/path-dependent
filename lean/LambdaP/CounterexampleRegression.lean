import LambdaP.Canonical

/-!
Regression showing that the historical closed counterexample is blocked.

The proved syntax distinguishes the abstract selection `q.A` from the
term singleton `{q.A}`.  This file proves more than constructor inequality:
in the critical context containing `q` and an argument `z : q.A`, the old
body subtyping `{q} <: {z}` is not derivable, even using primitive
transitivity and every abstract-bound rule.
-/

namespace LambdaP.CounterexampleRegression

open LambdaP

abbrev label : Name := 0

/-- A pair type with an exact abstract member `A = Top`. -/
abbrev qType0 : Ty 0 :=
  Ty.Pair Ty.Top label (Tau.intv Ty.Top Ty.Top).weaken

abbrev GammaQ : Ctx 1 := Ctx.nil.snoc qType0
abbrev q1 : Fin 1 := 0
abbrev qSelection1 : Path 1 := (Path.var q1).sel label
abbrev argumentType1 : Ty 1 := Ty.TSel (Path.var q1) label

/-- The critical function-body context: `q` followed by `z : q.A`. -/
abbrev GammaZ : Ctx 2 := GammaQ.snoc argumentType1
abbrev z : Fin 2 := 0
abbrev q : Fin 2 := 1
abbrev qSelection : Path 2 := (Path.var q).sel label

abbrev qType : Ty 2 := qType0.weaken.weaken
abbrev argumentType : Ty 2 := argumentType1.weaken

theorem argumentType_eq : argumentType = Ty.TSel (Path.var q) label := by
  rfl

theorem z_binding : Ctx.Binds GammaZ z argumentType := by
  exact Ctx.Binds.here

theorem q_binding : Ctx.Binds GammaZ q qType := by
  exact Ctx.Binds.there Ctx.Binds.here

theorem q_selection_typing :
    Path.Ty GammaZ qSelection (Tau.intv Ty.Top Ty.Top) := by
  have hroot : Path.Ty GammaZ (Path.var q) (Tau.ty qType) :=
    Path.Ty.var q_binding
  have hsel := Path.Ty.sel_r hroot
  simpa only [qSelection, qType, qType0, Ty.weaken, Ty.rename,
    Tau.weaken, Tau.rename, Tau.weaken_open] using hsel

/-! ## A small transitivity-closed interpretation -/

/-- Shape interpretation parameterized by the singleton paths that count as
observable.  Function, pair, `Top`, and abstract-selection heads are marked;
`Bot` is not. -/
def TypeMarked (M : Path n -> Prop) : Ty n -> Prop
| .Top => True
| .Bot => False
| .Fun _ _ => True
| .Pair _ _ _ => True
| .Single p => M p
| .TSel _ _ => True

def SignatureMarked (M : Path n -> Prop) : Tau n k -> Prop
| .ty T => TypeMarked M T
| .intv _ _ => True

def ProperResultsMarked (Gamma : Ctx n) (M : Path n -> Prop) : Prop :=
  forall {p T}, Path.Ty Gamma p (Tau.ty T) -> M p -> TypeMarked M T

def SingletonAliasesMarked (Gamma : Ctx n) (M : Path n -> Prop) : Prop :=
  forall {p r}, Path.Ty Gamma p (Tau.ty (Ty.Single r)) -> M r -> M p

def IntervalUppersMarked (Gamma : Ctx n) (M : Path n -> Prop) : Prop :=
  forall {p L U}, Path.Ty Gamma p (Tau.intv L U) -> TypeMarked M U

/-- Every current subtyping rule preserves the interpretation.  The proof
handles primitive transitivity directly. -/
theorem sub_preserves_mark
    {Gamma : Ctx n} {M : Path n -> Prop} {d1 d2 : Tau n k}
    (hresults : ProperResultsMarked Gamma M)
    (halias : SingletonAliasesMarked Gamma M)
    (huppers : IntervalUppersMarked Gamma M)
    (h : Tau.Sub Gamma d1 d2) :
    SignatureMarked M d1 -> SignatureMarked M d2 := by
  induction h with
  | refl => exact fun hm => hm
  | trans h1 h2 ih1 ih2 =>
      intro hm
      exact ih2 hresults halias huppers
        (ih1 hresults halias huppers hm)
  | bot => exact fun hm => hm.elim
  | top => exact fun _ => trivial
  | widen hp => exact fun hm => hresults hp hm
  | symm hp => exact fun hm => halias hp hm
  | sel_hi hp hbounds ihbounds => exact fun _ => huppers hp
  | sel_lo hp hbounds ihbounds => exact fun _ => trivial
  | «fun» hdom hcod ihdom ihcod => exact fun _ => trivial
  | pair_fst hfst ihfst => exact fun _ => trivial
  | pair_single_member hp hsnd hopen ihsnd ihopen => exact fun _ => trivial
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty => exact fun _ => trivial

/-! ## Complete classification of paths in the critical context -/

inductive KnownPathTy : {k : Kind} -> Path 2 -> Tau 2 k -> Prop where
| z : KnownPathTy (Path.var CounterexampleRegression.z)
    (Tau.ty argumentType)
| q : KnownPathTy (Path.var CounterexampleRegression.q)
    (Tau.ty qType)
| q_fst : KnownPathTy (Path.var CounterexampleRegression.q).fst
    (Tau.ty Ty.Top)
| q_sel : KnownPathTy qSelection (Tau.intv Ty.Top Ty.Top)

private theorem path_typing_known_aux
    {Delta : Ctx 2} {k : Kind} {p : Path 2} {d : Tau 2 k}
    (h : Path.Ty Delta p d) : Delta = GammaZ -> KnownPathTy p d := by
  induction h with
  | var hb =>
      intro hDelta
      cases hDelta
      cases hb with
      | here => exact .z
      | there hb =>
          cases hb with
          | here => exact .q
          | there hb => cases hb
  | fst hp ih =>
      intro hDelta
      cases ih hDelta
      exact .q_fst
  | sel_r hp ih =>
      intro hDelta
      cases ih hDelta
      exact .q_sel
  | sel_l hp htail hne ihp ihtail =>
      intro hDelta
      cases ihtail hDelta

theorem path_typing_known
    {k : Kind} {p : Path 2} {d : Tau 2 k}
    (h : Path.Ty GammaZ p d) : KnownPathTy p d :=
  path_typing_known_aux h rfl

/-- All paths except the argument variable `z` are marked. -/
def PathMarked (p : Path 2) : Prop := p ≠ Path.var z

theorem proper_results_marked : ProperResultsMarked GammaZ PathMarked := by
  intro p T hp hmarked
  cases path_typing_known hp with
  | z => exact (hmarked rfl).elim
  | q => trivial
  | q_fst => trivial

theorem singleton_aliases_marked :
    SingletonAliasesMarked GammaZ PathMarked := by
  intro p r hp hr
  cases path_typing_known hp

theorem interval_uppers_marked :
    IntervalUppersMarked GammaZ PathMarked := by
  intro p L U hp
  cases path_typing_known hp
  trivial

theorem q_singleton_marked :
    SignatureMarked PathMarked (Tau.ty (Ty.Single (Path.var q))) := by
  simp [SignatureMarked, TypeMarked, PathMarked, q, z]

theorem z_singleton_unmarked :
    ¬ SignatureMarked PathMarked (Tau.ty (Ty.Single (Path.var z))) := by
  intro h
  exact h rfl

/-- The critical false alias used to type the historical closure body is no
longer derivable. -/
theorem historical_body_subtyping_blocked :
    ¬ Tau.Sub GammaZ
      (Tau.ty (Ty.Single (Path.var q)))
      (Tau.ty (Ty.Single (Path.var z))) := by
  intro hsub
  exact z_singleton_unmarked
    (sub_preserves_mark proper_results_marked singleton_aliases_marked
      interval_uppers_marked hsub q_singleton_marked)

/-- In particular, the old last edge `q.A <: {z}` is not recoverable through
transitivity either. -/
theorem selection_to_argument_singleton_blocked :
    ¬ Tau.Sub GammaZ
      (Tau.ty (Ty.TSel (Path.var q) label))
      (Tau.ty (Ty.Single (Path.var z))) := by
  intro hsub
  exact z_singleton_unmarked
    (sub_preserves_mark proper_results_marked singleton_aliases_marked
      interval_uppers_marked hsub (by trivial))

end LambdaP.CounterexampleRegression
