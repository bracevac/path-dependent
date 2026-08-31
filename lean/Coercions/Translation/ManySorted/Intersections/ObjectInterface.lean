import Coercions.Translation.ManySorted.Intersections.Encoding
import Coercions.Translation.ManySorted.Acyclic.NegativeObjectInterface
import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.Erasure

/-!
# One-payload objects over arbitrary normalized theories

M11 changes the shape of the static theory, not the runtime representation
discipline.  This module packages the generic positive existential and open
operations for any names-first theory.  There is exactly one runtime payload
binder regardless of the number of static members or retained constraints.
-/

namespace DOTCaptureToManySortedFC.Intersections.ObjectInterface

open ManySortedFC

/-- Positive existential shape of an object before its ambient capture is
recorded. -/
def existentialShape {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations)) : Ty scope :=
  .existsT theory representation

/-- Positive object type: one local theory, one representation, and one
ambient retained capture. -/
def objectType {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations))
    (outerCapture : Capture scope) : Ty scope :=
  .capturing outerCapture (existentialShape theory representation)

/-- A checked canonical object value.  Its model is established entirely in
the ambient context; assumptions exported by `theory` are unavailable while
the model evidence is proved. -/
structure Literal {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations))
    (outerCapture : Capture scope) where
  model : Theory.Model context theory
  payload : Tm scope
  payloadValue : Tm.IsValue payload
  payloadTyping : Tm.HasType context payload .empty
    (representation.instantiateStatic model.symbols)
  captures : Evidence (.inclusion .capture) scope
  capturesTyping : Evidence.Proves context captures
    (.inclusion
      (.capture
        (representation.instantiateStatic model.symbols).outerCapture)
      (.capture outerCapture))

namespace Literal

/-- Package the model and its single runtime payload. -/
def term {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {outerCapture : Capture scope}
    (literal : Literal context theory representation outerCapture) : Tm scope :=
  .pack theory representation outerCapture literal.model.symbols
    literal.model.evidence literal.payload literal.captures

def isValue {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {outerCapture : Capture scope}
    (literal : Literal context theory representation outerCapture) :
    Tm.IsValue literal.term :=
  .pack literal.payloadValue

def typing {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {outerCapture : Capture scope}
    (literal : Literal context theory representation outerCapture) :
    Tm.HasType context literal.term .empty
      (objectType theory representation outerCapture) := by
  exact .pack literal.model.satisfies literal.payloadValue
    literal.payloadTyping literal.capturesTyping

/-- Static witnesses, evidence, and the package marker erase literally. -/
@[simp]
theorem erase_term {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {outerCapture : Capture scope}
    (literal : Literal context theory representation outerCapture) :
    literal.term.erase = literal.payload.erase := rfl

/-- The standalone term checker accepts every generated literal artifact. -/
theorem checker_accepts {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {outerCapture : Capture scope}
    (literal : Literal context theory representation outerCapture) :
    (Tm.check context literal.term).isSome = true :=
  by
    have complete := Tm.synth_complete literal.typing
    unfold Tm.synth at complete
    cases checked : Tm.check context literal.term with
    | none => simp [checked] at complete
    | some _ => rfl

end Literal

/-! ## Explicit opening -/

/-- The body and capture certificate required after opening one object. -/
structure OpenBody {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations))
    (result : Ty scope) (bodyOuterUse : Capture scope) where
  body : Tm (PayloadScope scope symbols relations)
  bodyUse : Capture (PayloadScope scope symbols relations)
  bodyTyping : Tm.HasType
    ((context.extendTheory theory).extendTerm representation)
    body bodyUse
    ((result.rename (Rename.weakenStatic symbols relations)).weaken)
  discharge : Evidence (.inclusion .capture)
    (PayloadScope scope symbols relations)
  dischargeTyping : Evidence.Proves
    ((context.extendTheory theory).extendTerm representation)
    discharge
    (.inclusion (.capture bodyUse)
      (.capture
        (.union
          ((bodyOuterUse.rename
            (Rename.weakenStatic symbols relations)).weaken)
          (.singleton .here))))

namespace OpenBody

/-- Open an arbitrary package-producing computation once. -/
def term {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {result : Ty scope} {bodyOuterUse packageUse : Capture scope}
    {packageType : Ty scope} {package : Tm scope}
    (_packageTyping : Tm.HasType context package packageUse packageType)
    (_packageShape : packageType.stripCapture =
      existentialShape theory representation)
    (opened : OpenBody context theory representation result bodyOuterUse) :
    Tm scope :=
  .«open» theory representation result bodyOuterUse package opened.body
    opened.discharge

def typing {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {result : Ty scope} {bodyOuterUse packageUse : Capture scope}
    {packageType : Ty scope} {package : Tm scope}
    (packageTyping : Tm.HasType context package packageUse packageType)
    (packageShape : packageType.stripCapture =
      existentialShape theory representation)
    (opened : OpenBody context theory representation result bodyOuterUse) :
    Tm.HasType context
      (opened.term packageTyping packageShape)
      (packageUse.sequence (.union packageType.outerCapture bodyOuterUse))
      result := by
  exact .«open» packageTyping packageShape opened.bodyTyping
    opened.dischargeTyping

/-- Opening is exactly one runtime binding; the package computation is not
duplicated or reordered. -/
@[simp]
theorem erase_term {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation : Ty (StaticScope scope symbols relations)}
    {result : Ty scope} {bodyOuterUse packageUse : Capture scope}
    {packageType : Ty scope} {package : Tm scope}
    (packageTyping : Tm.HasType context package packageUse packageType)
    (packageShape : packageType.stripCapture =
      existentialShape theory representation)
    (opened : OpenBody context theory representation result bodyOuterUse) :
    (opened.term packageTyping packageShape).erase =
      .let' package.erase
        (opened.body.eraseWith
          ((Erasure.Renaming.identity scope).liftPayload symbols relations)) :=
  rfl

end OpenBody

/-! ## Scope facts -/

/-- Every opened object adds one ordinary payload binder, independent of the
number of static members and constraints. -/
theorem payload_term_count {scope : Sig} (symbols : List StaticSort)
    (relations : List Relation) :
    (PayloadScope scope symbols relations).termCount = scope.termCount + 1 := by
  simp [PayloadScope, StaticScope, SymbolScope]

end DOTCaptureToManySortedFC.Intersections.ObjectInterface
