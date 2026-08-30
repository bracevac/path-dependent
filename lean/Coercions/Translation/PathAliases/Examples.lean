import Coercions.Translation.PathAliases.Realizability
import Coercions.Translation.PathAliases.OperationalCorrespondence
import Coercions.Translation.RecursiveObjects.Examples
import Coercions.DOT.TraceablePaths.Source.Examples

/-!
# Traceable path-alias end-to-end regressions

The finite layout below allocates both members of the two-member recursive
object translation at each of two syntactically different source paths:

* the nested transparent path `r.a.b`;
* its singleton alias `q`, represented by the distinct stable path `s.b`.

Both paths resolve to `t`.  Their member keys nevertheless receive four
different FCsub names.  Equality and bound transport are explicit checked
coercions, while source alias reduction compiles to a target runtime stutter.
-/

namespace DotToFCsub.PathAliases.Examples

open DotFCRP.Source
open DotFCRP.Source.NestedExample

/-! ## Nested path and singleton alias -/

/-- A syntactically distinct suffix path resolving to the same `t` anchor as
`r.a.b`.  This is the stable path named `q` by the regression. -/
def q : Path Scope := .select sPath b

def qTrace : Traceable store q t :=
  .select (.var) sLookup (.var)

def qReducesToT : PathStep store q tPath :=
  .field (.var) sLookup (.var)

def rabEqualsQ : CoResolved store rab q :=
  ⟨t, rabTrace, qTrace⟩

def qEqualsT : CoResolved store q tPath :=
  ⟨t, qTrace, .var⟩

/-- A second proof tree with the same endpoints, used to exercise target
certificate coherence rather than proof-tree identity. -/
def rabEqualsQAlternative : CoResolved store rab q :=
  rabEqualsT.trans qEqualsT.symm

theorem rab_and_q_are_syntactically_distinct : rab ≠ q := by
  native_decide

/-! ## A complete four-slot target layout -/

abbrev Definitions := DotToFCsub.RecursiveObjects.Examples.Definitions

def encoding : DotToFCsub.RecursiveObjects.Encoding (target := []) Definitions :=
  DotToFCsub.RecursiveObjects.Examples.encoding

def firstMember : Fin Definitions.length :=
  DotToFCsub.RecursiveObjects.Examples.firstPosition

def secondMember : Fin Definitions.length :=
  DotToFCsub.RecursiveObjects.Examples.secondPosition

def firstLabel : Name := (Definitions.get firstMember).label
def secondLabel : Name := (Definitions.get secondMember).label

/-! ## Source binding to the same two-member recursive object -/

abbrev PrefixScope : DotFC.Sig := ([] ▹ .term) ▹ .term

/-- Embed the closed recursive object type below the `r` and `s` binders;
the final context extension below binds `t` at this type. -/
def recursiveBound : Ty PrefixScope :=
  (Legacy.ty DotFCR.Source.MutualExample.objectType).weaken.weaken

def recursiveType : Ty Scope := recursiveBound.weaken

def recursiveContext : Ctx Scope :=
  ((Ctx.nil.snoc (.top : Ty []))
    |>.snoc (.top : Ty ([] ▹ .term)))
    |>.snoc recursiveBound

def tRecursiveLookup : Lookup recursiveContext t recursiveType :=
  .here

def rabRecursiveBinding :
    PathBinding store recursiveContext rab recursiveType :=
  ⟨t, rabTrace, tRecursiveLookup⟩

def qRecursiveBinding :
    PathBinding store recursiveContext q recursiveType :=
  ⟨t, qTrace, tRecursiveLookup⟩

/-- The singleton is formed at the same recursive object binding used by all
four member selections. -/
def qSingletonWf : Wf store recursiveContext (.singleton q) :=
  .singleton qRecursiveBinding

def singletonSubtyping :
    Sub store recursiveContext (.singleton rab) (.singleton q) :=
  .singletonEq rabEqualsQ

/-- `r.a.b.A` and `r.a.b.B` expose the left and right members of the embedded
exact recursive body. -/
def rabFirstSelectionWf :
    Wf store recursiveContext (.sel rab firstLabel) := by
  apply Wf.sel
  apply Handle.recursive rabRecursiveBinding
  · exact .inter .member .member
  · exact .left .here

def rabSecondSelectionWf :
    Wf store recursiveContext (.sel rab secondLabel) := by
  apply Wf.sel
  apply Handle.recursive rabRecursiveBinding
  · exact .inter .member .member
  · exact .right .here

/-- The singleton alias `q` exposes the same two source members through its
independent trace certificate. -/
def qFirstSelectionWf :
    Wf store recursiveContext (.sel q firstLabel) := by
  apply Wf.sel
  apply Handle.recursive qRecursiveBinding
  · exact .inter .member .member
  · exact .left .here

def qSecondSelectionWf :
    Wf store recursiveContext (.sel q secondLabel) := by
  apply Wf.sel
  apply Handle.recursive qRecursiveBinding
  · exact .inter .member .member
  · exact .right .here

def rabA : MemberKey Scope := ⟨rab, firstLabel⟩
def rabB : MemberKey Scope := ⟨rab, secondLabel⟩
def qA : MemberKey Scope := ⟨q, firstLabel⟩
def qB : MemberKey Scope := ⟨q, secondLabel⟩

def rabASlot : Fin 4 := ⟨0, by omega⟩
def rabBSlot : Fin 4 := ⟨1, by omega⟩
def qASlot : Fin 4 := ⟨2, by omega⟩
def qBSlot : Fin 4 := ⟨3, by omega⟩

/-- Slots zero and one belong to `r.a.b`; slots two and three belong to `q`. -/
def pathAt (index : Fin 4) : Path Scope :=
  if index.val < 2 then rab else q

/-- Even slots select the first recursive member; odd slots select the
second. -/
def memberAt (index : Fin 4) : Fin Definitions.length :=
  if index.val % 2 = 0 then firstMember else secondMember

def keyAt (index : Fin 4) : MemberKey Scope :=
  ⟨pathAt index, (Definitions.get (memberAt index)).label⟩

def traceAt (index : Fin 4) :
    Traceable store (keyAt index).path t := by
  by_cases nested : index.val < 2
  · simpa [keyAt, pathAt, nested] using rabTrace
  · simpa [keyAt, pathAt, nested] using qTrace

def index? (key : MemberKey Scope) : Option (Fin 4) :=
  if key = rabA then some rabASlot
  else if key = rabB then some rabBSlot
  else if key = qA then some qASlot
  else if key = qB then some qBSlot
  else none

def anchorType (index : Fin 4) : FCsub.Ty [] :=
  recursiveAnchor encoding (memberAt index)

theorem memberAt_eq_of_label_eq (first second : Fin 4)
    (labelsEqual :
      (Definitions.get (memberAt first)).label =
        (Definitions.get (memberAt second)).label) :
    memberAt first = memberAt second := by
  native_decide +revert

/-- Executable allocation for both public members at both source paths. -/
def layout : PathLayout store [] where
  count := 4
  keyAt := keyAt
  anchorAt := fun _ => t
  traceAt := traceAt
  anchorType := anchorType
  index? := index?
  owns := by native_decide
  sound := by
    intro key index found
    by_cases isRabA : key = rabA
    · have indexEqual : rabASlot = index := by
        simpa [index?, isRabA] using found
      subst index
      calc
        keyAt rabASlot = rabA := by native_decide
        _ = key := isRabA.symm
    · by_cases isRabB : key = rabB
      · have indexEqual : rabBSlot = index := by
          simpa [index?, isRabA, isRabB,
            show rabB ≠ rabA by native_decide] using found
        subst index
        calc
          keyAt rabBSlot = rabB := by native_decide
          _ = key := isRabB.symm
      · by_cases isQA : key = qA
        · have indexEqual : qASlot = index := by
            simpa [index?, isRabA, isRabB, isQA,
              show qA ≠ rabA by native_decide,
              show qA ≠ rabB by native_decide] using found
          subst index
          calc
            keyAt qASlot = qA := by native_decide
            _ = key := isQA.symm
        · by_cases isQB : key = qB
          · have indexEqual : qBSlot = index := by
              simpa [index?, isRabA, isRabB, isQA, isQB,
                show qB ≠ rabA by native_decide,
                show qB ≠ rabB by native_decide,
                show qB ≠ qA by native_decide] using found
            subst index
            calc
              keyAt qBSlot = qB := by native_decide
              _ = key := isQB.symm
          · simp [index?, isRabA, isRabB, isQA, isQB] at found
  anchorType_coherent := by
    intro first second _ labelsEqual
    change (Definitions.get (memberAt first)).label =
      (Definitions.get (memberAt second)).label at labelsEqual
    have positionsEqual := memberAt_eq_of_label_eq first second labelsEqual
    simp only [anchorType]
    rw [positionsEqual]

abbrev RabAImage := layout.ownedImage rabASlot
abbrev RabBImage := layout.ownedImage rabBSlot
abbrev QAImage := layout.ownedImage qASlot
abbrev QBImage := layout.ownedImage qBSlot

/-- Every one of the four allocated keys is realized by its corresponding
member of the concrete two-member recursive interface. -/
def recursiveLayout : RecursiveLayoutRealization layout encoding where
  memberAt := fun index =>
    { memberIndex := memberAt index
      label_eq := rfl
      anchorType_eq := rfl }

/-- Every exact key in the executable layout has a source recursive
selection derivation in the context that binds `t` to the embedded recursive object
type.  This closes the source/target gap at the finite-layout boundary. -/
def sourceSelectionAt (index : Fin 4) :
    Wf store recursiveContext
      (.sel (layout.keyAt index).path (layout.keyAt index).label) := by
  by_cases isRabA : index = rabASlot
  · subst index
    simpa [layout, keyAt, pathAt, memberAt, rabASlot, firstLabel] using
      rabFirstSelectionWf
  · by_cases isRabB : index = rabBSlot
    · subst index
      simpa [layout, keyAt, pathAt, memberAt, rabBSlot, secondLabel] using
        rabSecondSelectionWf
    · by_cases isQA : index = qASlot
      · subst index
        simpa [layout, keyAt, pathAt, memberAt, qASlot, firstLabel] using
          qFirstSelectionWf
      · have isQB : index = qBSlot := by
          have notZero : index.val ≠ 0 := by
            intro equal
            apply isRabA
            apply Fin.ext
            simpa [rabASlot] using equal
          have notOne : index.val ≠ 1 := by
            intro equal
            apply isRabB
            apply Fin.ext
            simpa [rabBSlot] using equal
          have notTwo : index.val ≠ 2 := by
            intro equal
            apply isQA
            apply Fin.ext
            simpa [qASlot] using equal
          apply Fin.ext
          change index.val = 3
          omega
        subst index
        simpa [layout, keyAt, pathAt, memberAt, qBSlot, secondLabel] using
          qSecondSelectionWf

/-- Concrete end-to-end realization: source recursive selections and target
recursive member images share the same four syntactic layout positions. -/
structure EndToEndLayoutRealization : Type where
  sourceSelection : forall index : Fin 4,
    Wf store recursiveContext
      (.sel (layout.keyAt index).path (layout.keyAt index).label)
  targetMembers : RecursiveLayoutRealization layout encoding

def endToEndLayout : EndToEndLayoutRealization where
  sourceSelection := sourceSelectionAt
  targetMembers := recursiveLayout

def rabARealization : RecursiveMemberAt encoding
    (layout.ownedImage rabASlot) :=
  recursiveLayout.memberAt rabASlot

def rabBRealization : RecursiveMemberAt encoding
    (layout.ownedImage rabBSlot) :=
  recursiveLayout.memberAt rabBSlot

def qARealization : RecursiveMemberAt encoding
    (layout.ownedImage qASlot) :=
  recursiveLayout.memberAt qASlot

def qBRealization : RecursiveMemberAt encoding
    (layout.ownedImage qBSlot) :=
  recursiveLayout.memberAt qBSlot

theorem layout_covers_two_recursive_members :
    rabARealization.memberIndex = firstMember ∧
    rabBRealization.memberIndex = secondMember ∧
    qARealization.memberIndex = firstMember ∧
    qBRealization.memberIndex = secondMember := by
  native_decide

/-- The complete concrete layout packages the original recursive object
under all four generative alias pairs. -/
noncomputable def aliasedObjectRealization :
    AliasedRecursiveObjectRealization layout encoding .nil :=
  realizeAliasedRecursiveObject recursiveLayout .nil

theorem aliased_object_checks :
    FCsub.checkTerm .nil (aliasedRecursiveObject layout encoding)
      encoding.objectType = true :=
  aliasedObjectRealization.checkerAccepts

theorem aliased_object_erases_to_unit :
    (aliasedRecursiveObject layout encoding).erase =
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm []) :=
  aliasedObjectRealization.erasesToUnit

theorem aliased_object_runtime_reaches_unit :
    FCsub.Runtime.Steps (aliasedRecursiveObject layout encoding).erase
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm []) :=
  aliasedObjectRealization.reachesUnit

/-! ## Explicit equality and directed transport -/

def singletonMemberEquality : MemberPathEq
    (layout.ownedImage rabASlot) (layout.ownedImage qASlot) where
  paths := by simpa [layout, keyAt, pathAt, rabASlot, qASlot] using rabEqualsQ
  label_eq := by native_decide

def singletonMemberEqualityAlternative : MemberPathEq
    (layout.ownedImage rabASlot) (layout.ownedImage qASlot) where
  paths := by
    simpa [layout, keyAt, pathAt, rabASlot, qASlot] using
      rabEqualsQAlternative
  label_eq := by native_decide

/-- Co-resolved keys remain different allocation slots and target BVars. -/
theorem singleton_slots_distinct : rabASlot ≠ qASlot := by decide

theorem singleton_names_distinct :
    AliasScope.name (scope := []) layout.count rabASlot ≠
      AliasScope.name layout.count qASlot :=
  AliasScope.name_ne singleton_slots_distinct

theorem singleton_alias_types_distinct :
    (layout.ownedImage rabASlot).aliasType ≠
      (layout.ownedImage qASlot).aliasType := by
  apply MemberImage.aliasType_ne_of_key_ne
  native_decide

/-- Alternative source resolution proof trees produce identical explicit
target certificate syntax and hence identical checked endpoints. -/
theorem singleton_evidence_coherent :
    singletonMemberEquality.evidence =
      singletonMemberEqualityAlternative.evidence :=
  MemberPathEq.evidence_coherent _ _

abbrev TargetContext : FCsub.Ctx (AliasScope.Scope [] layout.count) :=
  AliasScope.extend .nil layout.anchorType

theorem singleton_equality_checks :
    FCsub.checkEquality TargetContext singletonMemberEquality.evidence
      (layout.ownedImage rabASlot).aliasType
      (layout.ownedImage qASlot).aliasType = true := by
  native_decide

noncomputable def singletonRealization : SingletonMemberRealization
    rabARealization qARealization singletonMemberEquality .nil :=
  realizeSingletonMember rabARealization qARealization
    singletonMemberEquality .nil

abbrev FirstExact : FCsub.Ty (AliasScope.Scope [] layout.count) :=
  (recursiveExact encoding firstMember).rename
    (AliasScope.weaken layout.count)

/-- Lower transport is directed from the exact recursive witness through the left
alias equality to the right alias. -/
theorem singleton_lower_transport_checks :
    FCsub.checkEvidence TargetContext
      (singletonMemberEquality.transportLower rabARealization.lower)
      FirstExact (layout.ownedImage qASlot).aliasType = true := by
  native_decide

/-- Upper transport reverses the singleton equality before exposing the same
exact recursive witness. -/
theorem singleton_upper_transport_checks :
    FCsub.checkEvidence TargetContext
      (singletonMemberEquality.transportUpper rabARealization.upper)
      (layout.ownedImage qASlot).aliasType FirstExact = true := by
  native_decide

/-! ## Path reduction and erasure correspondence -/

def runtime : AnchorRuntime Scope [] where
  term := fun _ => .unit

def rabSourceRuntimeStep : DotFCRP.Source.Runtime.Step store
    (DotFCRP.Source.Runtime.Tm.ofPath rab)
    (DotFCRP.Source.Runtime.Tm.ofPath tPath) :=
  pathStep_source_runtime rabReducesToT

def qSourceRuntimeStep : DotFCRP.Source.Runtime.Step store
    (DotFCRP.Source.Runtime.Tm.ofPath q)
    (DotFCRP.Source.Runtime.Tm.ofPath tPath) :=
  pathStep_source_runtime qReducesToT

/-- Both distinct source aliases take a real source field step and compile to
the same target unit by zero target runtime steps. -/
theorem rab_target_stutters :
    FCsub.Runtime.Steps
      (compilePathRuntime runtime rabTrace)
      (compilePathRuntime runtime
        (rabReducesToT.traceForward rabTrace)) :=
  pathStep_runtime_stutters runtime rabReducesToT rabTrace

theorem q_target_stutters :
    FCsub.Runtime.Steps
      (compilePathRuntime runtime qTrace)
      (compilePathRuntime runtime
        (qReducesToT.traceForward qTrace)) :=
  pathStep_runtime_stutters runtime qReducesToT qTrace

def nested_step_preserves_t :
    Traceable store tPath t :=
  pathStep_preserves_anchor rabReducesToT rabTrace

/-- Concrete generated `newtype` pairs, equality coercions, and casts erase
to the unchanged payload.  Typing of the nonescaping general construction is
provided by `closePathEqualityRoundTrip_hasType`. -/
def closedAdministrativeTerm : FCsub.Tm [] :=
  DotToFCsub.PathAliases.closePathEqualityRoundTrip singletonMemberEquality
    (.unit : FCsub.Tm (AliasScope.Scope [] layout.count))

theorem closed_administration_erases :
    closedAdministrativeTerm.erase = FCsub.Runtime.Tm.unit := by
  simpa [closedAdministrativeTerm, layout, AliasScope.eraseAliases] using
    (DotToFCsub.PathAliases.erase_closePathEqualityRoundTrip
      singletonMemberEquality
      (.unit : FCsub.Tm (AliasScope.Scope [] layout.count)))

/-! ## Rejected boundaries -/

/-- Equality transport is label-sensitive even when the paths co-resolve. -/
theorem different_labels_rejected :
    MemberPathEq (layout.ownedImage rabASlot)
      (layout.ownedImage qBSlot) -> False :=
  MemberPathEq.different_label_rejected (by native_decide)

/-- The missing source field cannot be upgraded to a finite path image. -/
theorem unresolved_path_rejected :
    PathImage layout unresolved -> False :=
  unresolved_not_pathImage (fun anchor => unresolved_not_traceable anchor)

def unresolvedKey : MemberKey Scope := ⟨unresolved, firstLabel⟩

theorem unresolved_key_is_unallocated :
    translateMember? layout unresolvedKey = none := by
  native_decide

theorem unresolved_key_has_no_member_image :
    MemberImage layout unresolvedKey -> False :=
  unallocated_not_translatable unresolved_key_is_unallocated

/-- Opaque values and dynamically computed applications are both outside the
certified receiver boundary. -/
theorem opaque_receiver_rejected :
    DotFCRP.Source.Runtime.TraceableReceiver store
      (.dynamic (.unit : DotFCRP.Source.Runtime.Tm Scope)) -> False :=
  dynamic_receiver_untranslatable store _

theorem dynamic_receiver_rejected :
    DotFCRP.Source.Runtime.TraceableReceiver store
      (.dynamic
        (DotFCRP.Source.Runtime.Tm.app (.var r) (.var s))) -> False :=
  dynamic_receiver_untranslatable store _

/-- A new term binder cannot be identified with any weakened ambient alias. -/
theorem fresh_binder_rejected :
    CoResolved (store.weaken (kind := .term))
      rab.weaken (.var .here) -> False :=
  weakened_path_not_fresh rabTrace

end DotToFCsub.PathAliases.Examples
