import LambdaPCC.CaptureTyping
import LambdaPCC.CaptureWeakening
import LambdaPCC.CaptureInterpretation

/-!
Allocation operations for the capture-aware invariant. Validity supplies the
value evidence and introduction qualifier at every store location. The
internal allocation summary is obtained from that same derivation.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Allocation metadata -/

def Body.toExact
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {term : Tm (n + 1)} {T : Ty (n + 1)}
    {C : CaptureSet (n + 1)}
    (body : Body world S term T C) : ExactBody sigma S term T C := by
  cases body with
  | source environment code => exact .source code

def Value.toExact
    {n : Nat} {sigma : Store n} {world : World sigma}
    {v : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : Value world v T Q) : ExactValue sigma v Q := by
  cases value with
  | abs body suffix => exact .abs body.toExact
  | @pair y z a qualifier suffix =>
      subst Q
      exact .pair
  | @typePair y a W qualifier suffix =>
      subst Q
      exact .typePair
  | @capturePair y a W qualifier suffix =>
      subst Q
      exact .capturePair

/-! ## Valid store entries -/

/-- Joint lookup and value evidence for one location of a valid
world. -/
structure World.Entry
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (x : Fin n) : Type 1 where
  term : Tm n
  introductionQualifier : CaptureSet n
  assignedType : Ty n
  lookup : Lookup world x term introductionQualifier
  value : Value world term assignedType introductionQualifier

noncomputable def World.Valid.entry
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (x : Fin n) : World.Entry valid x := by
  induction valid with
  | empty => exact Fin.elim0 x
  | @val n sigma world v vv T Q exact oldValid value ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact
          { term := v.weaken
            introductionQualifier := Q.weaken
            assignedType := T.weaken
            lookup := .here
            value := value.weaken exact vv }
      · let old := ih y
        exact
          { term := old.term.weaken
            introductionQualifier := old.introductionQualifier.weaken
            assignedType := old.assignedType.weaken
            lookup := .there old.lookup
            value := old.value.weaken exact vv }

/-! ## Realizing stored values -/

private noncomputable def World.Entry.singletonLocation
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {x : Fin n}
    (entry : World.Entry valid x) :
    LocationEvidence world x
      (.capt (.singleton (.var x)) (.Single (.var x))) :=
  .single entry.lookup .var (.fold .var entry.lookup)

/-- A stored joint value realizes its assigned type at the lookup location. -/
noncomputable def Value.atLookup
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {v : Tm n} {T : Ty n}
    {Q : CaptureSet n} (value : Value world v T Q)
    {x : Fin n} (lookup : Lookup world x v Q) : LocationEvidence world x T := by
  cases value with
  | abs body suffix =>
      apply suffix.actionLocation
      exact .fun lookup body .refl .refl .refl
  | pair qualifier suffix =>
      rename_i a y z
      cases qualifier
      apply suffix.actionLocation
      let first := (valid.entry y).singletonLocation
      let second := (valid.entry z).singletonLocation
      apply LocationEvidence.pair lookup first
      · simpa only [Tau.weaken_open] using Realizes.loc second
      · exact .refl
  | typePair qualifier suffix =>
      rename_i a y W
      cases qualifier
      apply suffix.actionLocation
      apply LocationEvidence.pair lookup (valid.entry y).singletonLocation
      · change Realizes world (.type W)
          ((Tau.type W W).weaken.open (.var y))
        simpa only [Tau.weaken_open] using
          Realizes.type
            (ShapeCoercion.refl (world := world) (S := W))
            (ShapeCoercion.refl (world := world) (S := W))
      · exact .refl
  | capturePair qualifier suffix =>
      rename_i a y W
      cases qualifier
      apply suffix.actionLocation
      apply LocationEvidence.pair lookup (valid.entry y).singletonLocation
      · change Realizes world (.capture W)
          ((Tau.capture W W).weaken.open (.var y))
        simpa only [Tau.weaken_open] using
          Realizes.capture
            (Relation.refl (world := world) (C := W))
            (Relation.refl (world := world) (C := W))
      · exact .refl

/-- A typed runtime path realizes its assigned type at any location to
which it resolves. -/
noncomputable def TermEvidence.pathLocationAt
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {p : Path n} {T : Ty n}
    {C : CaptureSet n} (term : TermEvidence valid (.path p) T C)
    {x : Fin n} (resolution : Path.Resolve p sigma (.loc x)) :
    LocationEvidence world x T :=
  term.pathView.suffix.actionLocation
    (.single (valid.entry x).lookup resolution
      (.fold resolution (valid.entry x).lookup))

/-! ## Continuations and suspended bodies -/

noncomputable def ContEvidence.weaken
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S T : Ty n} {E C : CaptureSet n}
    {cont : Tm.Cont n}
    (continuation : ContEvidence valid S E cont T C)
    {v : Tm n} {A : Ty n} {Q : CaptureSet n}
    (value : Value world v A Q) (vv : v.IsValue) :
    ContEvidence
      (valid.extend value (exact := value.toExact) (vv := vv))
      S.weaken E.weaken cont.weaken T.weaken C.weaken := by
  induction continuation with
  | hole suffix coverage =>
      exact .hole (suffix.weaken value.toExact vv)
        (coverage.weaken value.toExact vv)
  | cons tail body suffix current bodyCoverage ih =>
      apply ContEvidence.cons ih
      · simpa only [← Ty.weaken_rename,
          ← CaptureSet.weaken_rename] using
          body.weaken value.toExact vv
      · exact suffix.weaken value.toExact vv
      · exact current.weaken value.toExact vv
      · exact bodyCoverage.weaken value.toExact vv

private theorem FinFun.capture_weaken_ext_comp_openAt_zero {n : Nat} :
    (FinFun.weaken (n := n)).ext.comp
      (FinFun.openAt (0 : Fin (n + 1))) = FinFun.id := by
  apply FinFun.funext
  intro x
  refine Fin.cases ?_ (fun _ => ?_) x <;> rfl

/-- Allocate a value consumed by a let frame and instantiate the suspended
body at the fresh location. -/
noncomputable def Body.allocate
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S : Ty n} {body : Tm (n + 1)}
    {T : Ty (n + 1)} {C : CaptureSet (n + 1)}
    (closure : Body world S body T C)
    {v : Tm n} {Q : CaptureSet n}
    (argument : Value world v S Q) (vv : v.IsValue) :
    TermEvidence
      (valid.extend argument (exact := argument.toExact) (vv := vv))
      body T C := by
  let exact := argument.toExact
  let newValid := valid.extend argument (exact := exact) (vv := vv)
  have weakenedArgument := argument.weaken exact vv
  have possible :
    LocationEvidence (World.val world exact (vv := vv)) 0 S.weaken :=
    weakenedArgument.atLookup
      (valid := newValid) (.here)
  have applied := (closure.weaken exact vv).apply
    (valid := newValid) possible
  simpa only [Tm.open, Tm.rename_rename,
    FinFun.capture_weaken_ext_comp_openAt_zero, Tm.rename_id,
    ← Ty.rename_openAt_eq_open_var, Ty.rename_rename, Ty.rename_id,
    ← CaptureSet.rename_openAt_eq_open_var,
    CaptureSet.rename_rename, CaptureSet.rename_id] using applied

end
end Cap
end LambdaPCC
