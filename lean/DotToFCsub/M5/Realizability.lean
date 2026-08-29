import DotToFCsub.M5.OperationalCorrespondence

/-!
# Realizability and preservation for the recursive-object slice

This file states the result at exactly the strength implemented by M5.  It
does not claim a global consistency theorem for arbitrary DOT.  For a closed,
source-valid, type-member-only recursive object equipped with a successful
witness translation, it constructs a closed FCsub package whose complete
interface evidence and inhabitant are derivable in the empty ambient context.
-/

namespace DotToFCsub.M5

open DotFCR.Source

/-- Type-translation relation for the closed recursive-object boundary. -/
inductive TranslatesObjectType
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    Ty [] → FCsub.Ty [] → Prop where
  | recursive : TranslatesObjectType encoding
      (.mu (TypeDefs.exact definitions)) encoding.objectType

/-- Term-translation relation for the closed recursive-object boundary. -/
inductive TranslatesObject
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    Tm [] → FCsub.Tm [] → Prop where
  | recursive : TranslatesObject encoding (.recObj definitions) encoding.object

/-- A preservation witness retains the source derivation, both translation
relations, and the target derivation.  In particular, the target type is the
translation related to the exact source recursive self type. -/
structure RecursivePreservation
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : Type where
  sourceTyping : HasTy Ctx.nil (.recObj definitions)
    (.mu (TypeDefs.exact definitions))
  termTranslation : TranslatesObject encoding (.recObj definitions)
    encoding.object
  typeTranslation : TranslatesObjectType encoding
    (.mu (TypeDefs.exact definitions)) encoding.objectType
  targetTyping : FCsub.Tm.HasType FCsub.Ctx.nil encoding.object
    encoding.objectType

/-- Type and term preservation for a checked recursive object. -/
noncomputable def preserveRecursiveObject
    {definitions : List (TypeDef ClosedSelfScope)}
    (valid : TypeDefs.RecValid Ctx.nil definitions)
    (encoding : Encoding (target := []) definitions) :
    RecursivePreservation encoding where
  sourceTyping := .recObj valid
  termTranslation := .recursive
  typeTranslation := .recursive
  targetTyping := encoding.object_typed

/-- Exact-witness factorization for one member.  The public abstract name is
realized by a recursive projection; canonical unfolding gives equality with
the instantiated translated witness, and its two directed views are exactly
the lower and upper certificates emitted into the package. -/
structure ExactWitnessFactorization
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions)
    (index : Fin definitions.length) : Type where
  emitted : EmittedPairAt encoding.translation.witness
    encoding.order.positions index
  equality : FCsub.EqCo.HasType FCsub.Ctx.nil
    (.unfoldRec encoding.block (memberIndex index))
    (.recProj encoding.block (memberIndex index))
    ((encoding.translation.witness index).instantiateNames
      encoding.witnesses)
  lower : FCsub.LeCo.HasType FCsub.Ctx.nil
    (.eqToLe (.symm (.unfoldRec encoding.block (memberIndex index))))
    ((encoding.translation.witness index).instantiateNames
      encoding.witnesses)
    (.recProj encoding.block (memberIndex index))
  upper : FCsub.LeCo.HasType FCsub.Ctx.nil
    (.eqToLe (.unfoldRec encoding.block (memberIndex index)))
    (.recProj encoding.block (memberIndex index))
    ((encoding.translation.witness index).instantiateNames
      encoding.witnesses)
  roundTrip : FCsub.LeCo.HasType FCsub.Ctx.nil
    (.trans
      (.eqToLe (.symm (.unfoldRec encoding.block (memberIndex index))))
      (.eqToLe (.unfoldRec encoding.block (memberIndex index))))
    ((encoding.translation.witness index).instantiateNames
      encoding.witnesses)
    ((encoding.translation.witness index).instantiateNames
      encoding.witnesses)

noncomputable def factorExactWitness
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions)
    (index : Fin definitions.length) :
    ExactWitnessFactorization encoding index := by
  let emitted := Classical.choice
    (emittedPairAt_of_mem encoding.translation.witness
      encoding.order.positions index (encoding.order.complete index))
  have equality : FCsub.EqCo.HasType FCsub.Ctx.nil
      (.unfoldRec encoding.block (memberIndex index))
      (.recProj encoding.block (memberIndex index))
      ((encoding.translation.witness index).instantiateNames
        encoding.witnesses) := by
    unfold Encoding.witnesses
    rw [← encoding.unfolds index]
    exact .unfoldRec encoding.guarded
  exact
    { emitted := emitted
      equality := equality
      lower := .eqToLe (.symm equality)
      upper := .eqToLe equality
      roundTrip := .trans (.eqToLe (.symm equality)) (.eqToLe equality) }

/-- Concrete bad-bounds condition for an exact translated member.  Because
both public bounds factor through one exact witness, a bad member in this
slice would force that very same instantiated witness to be both `Top` and
`Bot`. -/
def BadBoundsAt
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions)
    (index : Fin definitions.length) : Prop :=
  let exact := (encoding.translation.witness index).instantiateNames
    encoding.witnesses
  exact = FCsub.Ty.top ∧ exact = FCsub.Ty.bot

/-- Exact-witness factorization rules out the slice's concrete bad-bounds
condition.  This is deliberately not advertised as global FCsub consistency. -/
theorem noBadBoundsAt
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions)
    (index : Fin definitions.length) :
    ¬ BadBoundsAt encoding index := by
  intro bad
  rcases bad with ⟨top, bottom⟩
  rw [top] at bottom
  cases bottom

/-- Runtime realizability is constructive: the translated closed package is
already a value, erases to unit, and its erased runtime reaches unit (in zero
steps). -/
structure ReachableRuntime
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : Prop where
  annotatedValue : FCsub.Tm.IsRuntimeValue encoding.object
  erasesToUnit : encoding.object.erase = FCsub.Runtime.Tm.unit
  reachesUnit : FCsub.Runtime.Steps encoding.object.erase
    FCsub.Runtime.Tm.unit

theorem reachableRuntime
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    ReachableRuntime encoding := by
  refine
    { annotatedValue := target_recursive_object_is_value encoding
      erasesToUnit := erase_target_recursive_object encoding
      reachesUnit := ?_ }
  rw [erase_target_recursive_object]
  exact .refl

/-- Full M5 realization: source/target preservation, exact-witness
factorization for every public name, and a reachable erased runtime. -/
structure RecursiveObjectRealization
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : Type where
  preservation : RecursivePreservation encoding
  exactWitness : ∀ index, ExactWitnessFactorization encoding index
  runtime : ReachableRuntime encoding

noncomputable def realizeRecursiveObject
    {definitions : List (TypeDef ClosedSelfScope)}
    (valid : TypeDefs.RecValid Ctx.nil definitions)
    (encoding : Encoding (target := []) definitions) :
    RecursiveObjectRealization encoding where
  preservation := preserveRecursiveObject valid encoding
  exactWitness := factorExactWitness encoding
  runtime := reachableRuntime encoding

/-- Existential realizability form of the full construction. -/
theorem recursiveObject_realizable
    {definitions : List (TypeDef ClosedSelfScope)}
    (valid : TypeDefs.RecValid Ctx.nil definitions)
    (encoding : Encoding (target := []) definitions) :
    Nonempty (RecursiveObjectRealization encoding) :=
  ⟨realizeRecursiveObject valid encoding⟩

/-- Honest closed consistency statement for this slice: every public
constraint has evidence in the empty ambient context and the resulting
existential interface has a closed inhabitant.  This is interface
realizability, not a claim about arbitrary source subtyping derivations. -/
structure ClosedExactInterfaceConsistent
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : Prop where
  constraints : Nonempty (FCsub.LeArgs.HasType FCsub.Ctx.nil
    encoding.telescope encoding.witnesses encoding.evidence)
  inhabited : Nonempty (FCsub.Tm.HasType FCsub.Ctx.nil encoding.object
    encoding.objectType)
  exactWitnesses : ∀ index,
    Nonempty (ExactWitnessFactorization encoding index)
  noBadBounds : ∀ index, ¬ BadBoundsAt encoding index
  runtime : ReachableRuntime encoding

/-- Closed consistency follows constructively from recursive-object
realizability; the source-validity premise prevents the rejected direct-alias
block from entering the theorem. -/
theorem closed_exact_interface_consistency
    {definitions : List (TypeDef ClosedSelfScope)}
    (valid : TypeDefs.RecValid Ctx.nil definitions)
    (encoding : Encoding (target := []) definitions) :
    ClosedExactInterfaceConsistent encoding := by
  let preservation := preserveRecursiveObject valid encoding
  exact
    { constraints := encoding.evidence_is_ambient
      inhabited := ⟨preservation.targetTyping⟩
      exactWitnesses := fun index => ⟨factorExactWitness encoding index⟩
      noBadBounds := noBadBoundsAt encoding
      runtime := reachableRuntime encoding }

end DotToFCsub.M5
