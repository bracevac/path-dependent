import LambdaPFC.Typing

/-!
Proof-relevant counterparts of the declarative static semantics.

Each code family follows its proposition-valued judgment constructor for
constructor.  Premises belonging to another static judgment are represented
by the corresponding code, so the complete derivation tree lives in `Type`.
Erasure recovers the declarative judgment; elaboration establishes that every
declarative derivation has a code without attempting to eliminate a proof in
`Prop` directly into `Type`.
-/

namespace LambdaPFC

/-! ## Path typing -/

/-- Proof-relevant path-typing derivations. -/
inductive PathCode :
    {n : Nat} -> Ctx n -> Path n -> {k : Kind} -> Tau n k -> Type where
| var :
    Ctx.Binds Gamma x T ->
    PathCode Gamma (.var x) (.ty T)
| fst :
    PathCode Gamma p (.ty (.Pair S a d)) ->
    PathCode Gamma p.fst (.ty S)
| sel_r :
    PathCode Gamma p (.ty (.Pair S a d)) ->
    PathCode Gamma (p.sel a) (d.open p.fst)
| sel_l :
    PathCode Gamma p (.ty (.Pair S b d')) ->
    PathCode Gamma (p.fst.sel a) d ->
    a ≠ b ->
    PathCode Gamma (p.sel a) d

/-- Forget proof relevance from a path-typing derivation. -/
def PathCode.erase : PathCode Gamma p d -> Path.Ty Gamma p d
| .var binds => .var binds
| .fst receiver => .fst receiver.erase
| .sel_r receiver => .sel_r receiver.erase
| .sel_l receiver member distinct =>
    .sel_l receiver.erase member.erase distinct

/-- Every declarative path-typing derivation has a proof-relevant code. -/
theorem PathCode.nonempty_of_ty
    (typing : Path.Ty Gamma p d) :
    Nonempty (PathCode Gamma p d) := by
  induction typing with
  | var binds => exact ⟨.var binds⟩
  | fst _ ih =>
      obtain ⟨receiver⟩ := ih
      exact ⟨.fst receiver⟩
  | sel_r _ ih =>
      obtain ⟨receiver⟩ := ih
      exact ⟨.sel_r receiver⟩
  | sel_l _ _ distinct ihReceiver ihMember =>
      obtain ⟨receiver⟩ := ihReceiver
      obtain ⟨member⟩ := ihMember
      exact ⟨.sel_l receiver member distinct⟩

/-! ## Subtyping -/

/-- Proof-relevant generalized subtyping derivations. -/
inductive SubCode :
    {n : Nat} -> Ctx n -> {k : Kind} ->
    Tau n k -> Tau n k -> Type where
| refl : SubCode Gamma d d
| trans :
    SubCode Gamma d1 d2 ->
    SubCode Gamma d2 d3 ->
    SubCode Gamma d1 d3
| bot : SubCode Gamma (.ty .Bot) (.ty T)
| top : SubCode Gamma (.ty T) (.ty .Top)
| widen :
    PathCode Gamma p (.ty T) ->
    SubCode Gamma (.ty (.Single p)) (.ty T)
| symm :
    PathCode Gamma p (.ty (.Single q)) ->
    SubCode Gamma (.ty (.Single q)) (.ty (.Single p))
| sel_hi :
    PathCode Gamma (p.sel A) (.intv S T) ->
    SubCode Gamma (.ty S) (.ty T) ->
    SubCode Gamma (.ty (.TSel p A)) (.ty T)
| sel_lo :
    PathCode Gamma (p.sel A) (.intv S T) ->
    SubCode Gamma (.ty S) (.ty T) ->
    SubCode Gamma (.ty S) (.ty (.TSel p A))
| «fun» :
    SubCode Gamma (.ty S') (.ty S) ->
    SubCode (Gamma.snoc S') (.ty T) (.ty T') ->
    SubCode Gamma
      (.ty (.Fun S T)) (.ty (.Fun S' T'))
| pair :
    SubCode Gamma (.ty S) (.ty S') ->
    SubCode (Gamma.snoc S) d d' ->
    SubCode Gamma
      (.ty (.Pair S a d))
      (.ty (.Pair S' a d'))
| bounds :
    SubCode Gamma (.ty S') (.ty S) ->
    SubCode Gamma (.ty T) (.ty T') ->
    SubCode Gamma (.ty S) (.ty T) ->
    SubCode Gamma
      (.intv S T) (.intv S' T')

/-- Forget proof relevance from a subtyping derivation. -/
def SubCode.erase : SubCode Gamma d1 d2 -> Tau.Sub Gamma d1 d2
| .refl => .refl
| .trans first second => .trans first.erase second.erase
| .bot => .bot
| .top => .top
| .widen path => .widen path.erase
| .symm path => .symm path.erase
| .sel_hi path boundCode => .sel_hi path.erase boundCode.erase
| .sel_lo path boundCode => .sel_lo path.erase boundCode.erase
| .fun domain codomain => .fun domain.erase codomain.erase
| .pair first member => .pair first.erase member.erase
| .bounds lower upper nonempty =>
    .bounds lower.erase upper.erase nonempty.erase

/-- Every declarative subtyping derivation has a proof-relevant code. -/
theorem SubCode.nonempty_of_sub
    (sub : Tau.Sub Gamma d1 d2) :
    Nonempty (SubCode Gamma d1 d2) := by
  induction sub with
  | refl => exact ⟨.refl⟩
  | trans _ _ ihFirst ihSecond =>
      obtain ⟨first⟩ := ihFirst
      obtain ⟨second⟩ := ihSecond
      exact ⟨.trans first second⟩
  | bot => exact ⟨.bot⟩
  | top => exact ⟨.top⟩
  | widen path =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      exact ⟨.widen pathCode⟩
  | symm path =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      exact ⟨.symm pathCode⟩
  | sel_hi path _ ihBounds =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      obtain ⟨boundCode⟩ := ihBounds
      exact ⟨.sel_hi pathCode boundCode⟩
  | sel_lo path _ ihBounds =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      obtain ⟨boundCode⟩ := ihBounds
      exact ⟨.sel_lo pathCode boundCode⟩
  | «fun» _ _ ihDomain ihCodomain =>
      obtain ⟨domain⟩ := ihDomain
      obtain ⟨codomain⟩ := ihCodomain
      exact ⟨.fun domain codomain⟩
  | pair _ _ ihFirst ihMember =>
      obtain ⟨first⟩ := ihFirst
      obtain ⟨member⟩ := ihMember
      exact ⟨.pair first member⟩
  | bounds _ _ _ ihLower ihUpper ihNonempty =>
      obtain ⟨lower⟩ := ihLower
      obtain ⟨upper⟩ := ihUpper
      obtain ⟨nonempty⟩ := ihNonempty
      exact ⟨.bounds lower upper nonempty⟩

/-! ## Type well-formedness -/

/-- Proof-relevant generalized-type well-formedness derivations. -/
inductive WfCode :
    {n : Nat} -> Ctx n -> {k : Kind} -> Tau n k -> Type where
| bot : WfCode Gamma (.ty .Bot)
| top : WfCode Gamma (.ty .Top)
| path :
    PathCode Gamma p (.ty T) ->
    WfCode Gamma (.ty (.Single p))
| sel :
    PathCode Gamma p (.ty (.Pair S A (.intv T U))) ->
    WfCode Gamma (.ty (.TSel p A))
| «fun» :
    WfCode Gamma (.ty S) ->
    WfCode (Gamma.snoc S) (.ty T) ->
    WfCode Gamma (.ty (.Fun S T))
| pair :
    WfCode Gamma (.ty S) ->
    WfCode (Gamma.snoc S) d ->
    WfCode Gamma (.ty (.Pair S a d))
| bounds_wf :
    WfCode Gamma (.ty S) ->
    WfCode Gamma (.ty T) ->
    SubCode Gamma (.ty S) (.ty T) ->
    WfCode Gamma (.intv S T)

/-- Forget proof relevance from a well-formedness derivation. -/
def WfCode.erase : WfCode Gamma d -> Tau.Wf Gamma d
| .bot => .bot
| .top => .top
| .path pathCode => .path pathCode.erase
| .sel pathCode => .sel pathCode.erase
| .fun domain codomain => .fun domain.erase codomain.erase
| .pair first member => .pair first.erase member.erase
| .bounds_wf lower upper bounds =>
    .bounds_wf lower.erase upper.erase bounds.erase

/-- Every declarative well-formedness derivation has a proof-relevant code. -/
theorem WfCode.nonempty_of_wf
    (wf : Tau.Wf Gamma d) :
    Nonempty (WfCode Gamma d) := by
  induction wf with
  | bot => exact ⟨.bot⟩
  | top => exact ⟨.top⟩
  | path path =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      exact ⟨.path pathCode⟩
  | sel path =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      exact ⟨.sel pathCode⟩
  | «fun» _ _ ihDomain ihCodomain =>
      obtain ⟨domain⟩ := ihDomain
      obtain ⟨codomain⟩ := ihCodomain
      exact ⟨.fun domain codomain⟩
  | pair _ _ ihFirst ihMember =>
      obtain ⟨first⟩ := ihFirst
      obtain ⟨member⟩ := ihMember
      exact ⟨.pair first member⟩
  | bounds_wf _ _ bounds ihLower ihUpper =>
      obtain ⟨lower⟩ := ihLower
      obtain ⟨upper⟩ := ihUpper
      obtain ⟨boundCode⟩ := SubCode.nonempty_of_sub bounds
      exact ⟨.bounds_wf lower upper boundCode⟩

/-! ## Term typing -/

/-- Proof-relevant term-typing derivations. -/
inductive TermCode :
    {n : Nat} -> Ctx n -> Tm n -> Ty n -> Type where
| path :
    PathCode Gamma p (.ty T) ->
    TermCode Gamma (.path p) (.Single p)
| abs :
    TermCode (Gamma.snoc S) t T ->
    WfCode Gamma (.ty S) ->
    TermCode Gamma (.abs S t) (.Fun S T)
| app :
    TermCode Gamma (.path p) (.Fun S T) ->
    TermCode Gamma (.path q) S ->
    TermCode Gamma (.app p q) (T.open q)
| pair :
    Ctx.Binds Gamma y S ->
    Ctx.Binds Gamma z T ->
    TermCode Gamma (Tm.pair y a (.val z))
      (.Pair (.Single (Path.var y)) a
        (Tau.ty (.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Gamma y S ->
    WfCode Gamma (.ty T) ->
    TermCode Gamma (Tm.pair y A (.type T))
      (.Pair (.Single (Path.var y)) A (Tau.intv T T).weaken)
| «let» :
    TermCode Gamma s S ->
    WfCode Gamma (.ty T) ->
    TermCode (Gamma.snoc S) t T.weaken ->
    TermCode Gamma (.let s t) T
| typed :
    TermCode Gamma t T ->
    WfCode Gamma (.ty T) ->
    TermCode Gamma (.typed t T) T
| sub :
    TermCode Gamma t S ->
    SubCode Gamma (.ty S) (.ty T) ->
    WfCode Gamma (.ty T) ->
    TermCode Gamma t T

/-- Forget proof relevance from a term-typing derivation. -/
def TermCode.erase : TermCode Gamma t T -> Tm.Ty Gamma t T
| .path pathCode => .path pathCode.erase
| .abs body domain => .abs body.erase domain.erase
| .app function argument => .app function.erase argument.erase
| .pair first member => .pair first member
| .tpair first member => .tpair first member.erase
| .let bound result body => .let bound.erase result.erase body.erase
| .typed term wf => .typed term.erase wf.erase
| .sub term subtype wf => .sub term.erase subtype.erase wf.erase

/-- Every declarative term-typing derivation has a proof-relevant code. -/
theorem TermCode.nonempty_of_ty
    (typing : Tm.Ty Gamma t T) :
    Nonempty (TermCode Gamma t T) := by
  induction typing with
  | path path =>
      obtain ⟨pathCode⟩ := PathCode.nonempty_of_ty path
      exact ⟨.path pathCode⟩
  | abs _ domain ihBody =>
      obtain ⟨body⟩ := ihBody
      obtain ⟨domainCode⟩ := WfCode.nonempty_of_wf domain
      exact ⟨.abs body domainCode⟩
  | app _ _ ihFunction ihArgument =>
      obtain ⟨function⟩ := ihFunction
      obtain ⟨argument⟩ := ihArgument
      exact ⟨.app function argument⟩
  | pair first member => exact ⟨.pair first member⟩
  | tpair first member =>
      obtain ⟨memberCode⟩ := WfCode.nonempty_of_wf member
      exact ⟨.tpair first memberCode⟩
  | «let» _ result _ ihBound ihBody =>
      obtain ⟨bound⟩ := ihBound
      obtain ⟨resultCode⟩ := WfCode.nonempty_of_wf result
      obtain ⟨body⟩ := ihBody
      exact ⟨.let bound resultCode body⟩
  | typed _ wf ihTerm =>
      obtain ⟨term⟩ := ihTerm
      obtain ⟨wfCode⟩ := WfCode.nonempty_of_wf wf
      exact ⟨.typed term wfCode⟩
  | sub _ subtype wf ihTerm =>
      obtain ⟨term⟩ := ihTerm
      obtain ⟨subtypeCode⟩ := SubCode.nonempty_of_sub subtype
      obtain ⟨wfCode⟩ := WfCode.nonempty_of_wf wf
      exact ⟨.sub term subtypeCode wfCode⟩

end LambdaPFC
