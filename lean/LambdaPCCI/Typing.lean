import LambdaPCCI.Syntax
import LambdaPCCI.Context

/-!
Static semantics for `lambda_p` with capture checking. Paths synthesize
member signatures, capture sets are ordered by subcapturing, and types
separate capture sets from their underlying shape types.
-/

namespace LambdaPCCI

open Ctx

/-! ## Path typing -/

/-- Precise typing for paths. The kind distinguishes term, type, and capture
members while the path rules themselves remain uniform in the member kind. -/
inductive Path.Ty : Ctx n -> Path n -> Tau n k -> Type where
| var :
    Path.Ty Gamma (.var x) (.term (Gamma.lookup x))
| fst :
    Path.Ty Gamma p (.term (.capt C (.Pair S a tau))) ->
    Path.Ty Gamma p.fst (.term S)
| sel_r :
    Path.Ty Gamma p (.term (.capt C (.Pair S a tau))) ->
    Path.Ty Gamma (p.sel a) (tau.open p.fst)
| sel_l :
    Path.Ty Gamma p (.term (.capt C (.Pair S b tau'))) ->
    Path.Ty Gamma (p.fst.sel a) tau ->
    a ≠ b ->
    Path.Ty Gamma (p.sel a) tau

/-! ## Subcapturing and subtyping -/

/-- Subcapturing. A term path exposes the capture set of its synthesized type;
an abstract capture-set member lies between its declared bounds. -/
inductive CaptureSet.Sub : Ctx n -> CaptureSet n -> CaptureSet n -> Type where
| refl :
    CaptureSet.Sub Gamma C C
| trans :
    CaptureSet.Sub Gamma C D ->
    CaptureSet.Sub Gamma D E ->
    CaptureSet.Sub Gamma C E
| empty :
    CaptureSet.Sub Gamma .empty C
| union_left :
    CaptureSet.Sub Gamma C (.union C D)
| union_right :
    CaptureSet.Sub Gamma D (.union C D)
| union_elim :
    CaptureSet.Sub Gamma C E ->
    CaptureSet.Sub Gamma D E ->
    CaptureSet.Sub Gamma (.union C D) E
| path :
    Path.Ty Gamma p (.term (.capt C S)) ->
    CaptureSet.Sub Gamma (.singleton p) C
| alias :
    Path.Ty Gamma p (.term (.capt C (.Single q))) ->
    CaptureSet.Sub Gamma (.singleton q) (.singleton p)
| fst_root :
    Path.Ty Gamma p.fst (.term T) ->
    CaptureSet.Sub Gamma (.singleton p.fst) (.singleton p)
| sel_root :
    Path.Ty Gamma (p.sel a) (.term T) ->
    CaptureSet.Sub Gamma (.singleton (p.sel a)) (.singleton p)
| select_lower :
    Path.Ty Gamma (p.sel a) (.capture L U) ->
    CaptureSet.Sub Gamma L U ->
    CaptureSet.Sub Gamma L (.select p a)
| select_upper :
    Path.Ty Gamma (p.sel a) (.capture L U) ->
    CaptureSet.Sub Gamma L U ->
    CaptureSet.Sub Gamma (.select p a) U

mutual

/-- Subtyping of capturing types. -/
inductive Ty.Sub : Ctx n -> Ty n -> Ty n -> Type where
| refl :
    Ty.Sub Gamma T T
| trans :
    Ty.Sub Gamma S T ->
    Ty.Sub Gamma T U ->
    Ty.Sub Gamma S U
| capt :
    CaptureSet.Sub Gamma C D ->
    Shape.Sub Gamma S T ->
    Ty.Sub Gamma (.capt C S) (.capt D T)

/-- Subtyping of shape types. -/
inductive Shape.Sub : Ctx n -> Shape n -> Shape n -> Type where
| refl :
    Shape.Sub Gamma S S
| trans :
    Shape.Sub Gamma S T ->
    Shape.Sub Gamma T U ->
    Shape.Sub Gamma S U
| bot :
    Shape.Sub Gamma .Bot S
| top :
    Shape.Sub Gamma S .Top
| singleton_widen :
    Path.Ty Gamma p (.term (.capt C S)) ->
    Shape.Sub Gamma (.Single p) S
| singleton_alias :
    Path.Ty Gamma p (.term (.capt C (.Single q))) ->
    Shape.Sub Gamma (.Single q) (.Single p)
| select_lower :
    Path.Ty Gamma (p.sel a) (.type S T) ->
    Shape.Sub Gamma S T ->
    Shape.Sub Gamma S (.TSel p a)
| select_upper :
    Path.Ty Gamma (p.sel a) (.type S T) ->
    Shape.Sub Gamma S T ->
    Shape.Sub Gamma (.TSel p a) T
| inter :
    Shape.Sub Gamma S T ->
    Shape.Sub Gamma S U ->
    Shape.Sub Gamma S (.Inter T U)
| inter_left :
    Shape.Sub Gamma (.Inter T U) T
| inter_right :
    Shape.Sub Gamma (.Inter T U) U
/-- Merge two views of one term-member slot.  The first-component type,
label, and member capture set must agree, so both views describe the same
stored member with the same capture contract. -/
| pair_inter :
    Shape.Sub Gamma
      (.Inter
        (.Pair S a (.term (.capt C T)))
        (.Pair S a (.term (.capt C U))))
      (.Pair S a (.term (.capt C (.Inter T U))))
/-- Merge two views of one abstract type-member slot.  The first-component
type, label, and lower bound must agree, so both upper bounds constrain the
same stored type. -/
| pair_type_inter :
    Shape.Sub Gamma
      (.Inter
        (.Pair S a (.type L U))
        (.Pair S a (.type L V)))
      (.Pair S a (.type L (.Inter U V)))
| fun :
    Ty.Sub Gamma S' S ->
    Ty.Sub (Gamma.snoc S') T T' ->
    Shape.Sub Gamma (.Fun S T) (.Fun S' T')
| pair :
    Ty.Sub Gamma S S' ->
    Tau.Sub (Gamma.snoc S) tau tau' ->
    Shape.Sub Gamma (.Pair S a tau) (.Pair S' a tau')

/-- Subtyping of member signatures. -/
inductive Tau.Sub : Ctx n -> Tau n k -> Tau n k -> Type where
| refl :
    Tau.Sub Gamma tau tau
| trans :
    Tau.Sub Gamma tau1 tau2 ->
    Tau.Sub Gamma tau2 tau3 ->
    Tau.Sub Gamma tau1 tau3
| term :
    Ty.Sub Gamma S T ->
    Tau.Sub Gamma (.term S) (.term T)
| type :
    Shape.Sub Gamma S' S ->
    Shape.Sub Gamma T T' ->
    Shape.Sub Gamma S T ->
    Tau.Sub Gamma (.type S T) (.type S' T')
| capture :
    CaptureSet.Sub Gamma L' L ->
    CaptureSet.Sub Gamma U U' ->
    CaptureSet.Sub Gamma L U ->
    Tau.Sub Gamma (.capture L U) (.capture L' U')

end

/-! ## Well-formedness -/

/-- Well-formed capture sets. Selection from a capture-set member is admitted
only when the selected interval has consistent bounds. -/
inductive CaptureSet.Wf : Ctx n -> CaptureSet n -> Type where
| empty :
    CaptureSet.Wf Gamma .empty
| union :
    CaptureSet.Wf Gamma C ->
    CaptureSet.Wf Gamma D ->
    CaptureSet.Wf Gamma (.union C D)
| singleton :
    Path.Ty Gamma p (.term T) ->
    CaptureSet.Wf Gamma (.singleton p)
| select :
    Path.Ty Gamma (p.sel a) (.capture L U) ->
    CaptureSet.Sub Gamma L U ->
    CaptureSet.Wf Gamma (.select p a)

mutual

/-- Well-formed capturing types. -/
inductive Ty.Wf : Ctx n -> Ty n -> Type where
| capt :
    CaptureSet.Wf Gamma C ->
    Shape.Wf Gamma S ->
    Ty.Wf Gamma (.capt C S)

/-- Well-formed shapes. -/
inductive Shape.Wf : Ctx n -> Shape n -> Type where
| bot :
    Shape.Wf Gamma .Bot
| top :
    Shape.Wf Gamma .Top
| singleton :
    Path.Ty Gamma p (.term T) ->
    Shape.Wf Gamma (.Single p)
| select :
    Path.Ty Gamma (p.sel a) (.type S T) ->
    Shape.Sub Gamma S T ->
    Shape.Wf Gamma (.TSel p a)
| inter :
    Shape.Wf Gamma S ->
    Shape.Wf Gamma T ->
    Shape.Wf Gamma (.Inter S T)
| fun :
    Ty.Wf Gamma S ->
    Ty.Wf (Gamma.snoc S) T ->
    Shape.Wf Gamma (.Fun S T)
| pair :
    Ty.Wf Gamma S ->
    Tau.Wf (Gamma.snoc S) tau ->
    Shape.Wf Gamma (.Pair S a tau)

/-- Well-formed member signatures. -/
inductive Tau.Wf : Ctx n -> Tau n k -> Type where
| term :
    Ty.Wf Gamma T ->
    Tau.Wf Gamma (.term T)
| type :
    Shape.Wf Gamma S ->
    Shape.Wf Gamma T ->
    Shape.Sub Gamma S T ->
    Tau.Wf Gamma (.type S T)
| capture :
    CaptureSet.Wf Gamma L ->
    CaptureSet.Wf Gamma U ->
    CaptureSet.Sub Gamma L U ->
    Tau.Wf Gamma (.capture L U)

end

/-! ## Term typing -/

/-- Term typing records both a result type and the paths used while evaluating
the term. -/
inductive Tm.Ty : Ctx n -> Tm n -> Ty n -> CaptureSet n -> Type where
| path :
    Path.Ty Gamma p (.term T) ->
    Tm.Ty Gamma (.path p)
      (.capt (.singleton p) (.Single p))
      (.singleton p)
| abs :
    Tm.Ty (Gamma.snoc S) body T
      (.union C.weaken (.singleton (.var 0))) ->
    Ty.Wf Gamma S ->
    CaptureSet.Wf Gamma C ->
    Tm.Ty Gamma (.abs S body) (.capt C (.Fun S T)) .empty
| app :
    Tm.Ty Gamma (.path p) (.capt C (.Fun S T)) Cp ->
    Tm.Ty Gamma (.path q) S Cq ->
    Tm.Ty Gamma (.app p q) (T.open q) (.union Cp Cq)
| pair :
    Tm.Ty Gamma (.pair y a (.val z))
      (.capt
        (.union (.singleton (.var y)) (.singleton (.var z)))
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y)))
          a
          (.term
            (.capt
              (.singleton (Path.var z).weaken)
              (.Single (Path.var z).weaken)))))
      .empty
| type_pair :
    Shape.Wf Gamma T ->
    Tm.Ty Gamma (.pair y a (.type T))
      (.capt
        (.singleton (.var y))
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y)))
          a
          (.type T.weaken T.weaken)))
      .empty
| capture_pair :
    CaptureSet.Wf Gamma C ->
    Tm.Ty Gamma (.pair y a (.capture C))
      (.capt
        (.singleton (.var y))
        (.Pair
          (.capt (.singleton (.var y)) (.Single (.var y)))
          a
          (.capture C.weaken C.weaken)))
      .empty
| let :
    Tm.Ty Gamma bound T C ->
    Tm.Ty (Gamma.snoc T) body U.weaken C.weaken ->
    Ty.Wf Gamma U ->
    CaptureSet.Wf Gamma C ->
    Tm.Ty Gamma (.let bound body) U C
| sub :
    Tm.Ty Gamma term S C ->
    Ty.Sub Gamma S T ->
    CaptureSet.Sub Gamma C D ->
    Ty.Wf Gamma T ->
    CaptureSet.Wf Gamma D ->
    Tm.Ty Gamma term T D

end LambdaPCCI
