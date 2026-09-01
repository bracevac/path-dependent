import Coercions.Translation.ManySorted.Intersections.ObjectPreparation

/-!
# Multi-member one-payload object regressions
-/

namespace DOTCaptureToManySortedFC.Intersections.ObjectInterfaceExamples

open DOTCapture.Intersections.Source
open DOTCaptureToManySortedFC.Intersections
open ManySortedFC

/-! ## Four labels, with repeated type and capture declarations -/

def multiInterface : Interface 0 :=
  .inter
    (.inter
      (.typeMember 0 .one .one)
      (.typeMember 0 .one .one))
    (.inter
      (.inter
        (.captureMember 1 .empty .empty)
        (.captureMember 1 .empty .empty))
      (.inter
        (.typeMember 2 .one .one)
        (.captureMember 3 .empty .empty)))

/-- The representation is one runtime unit payload; the four abstract names
remain available statically through `multiInterface`. -/
def multiObject : ObjectType 0 :=
  .mk multiInterface .one .empty

def preparedMulti? : Option
    (ObjectPreparation.PreparedObject ([] : ManySortedFC.Sig)) :=
  (ObjectPreparation.prepareObject
    (Preparation.emptyLayout []) multiObject).toOption

theorem preparedMulti_isSome : preparedMulti?.isSome = true := by
  rfl

theorem preparedMulti_has_four_names :
    preparedMulti?.map (fun object => object.encoding.symbols.length) =
      some 4 := by
  rfl

theorem preparedMulti_retains_six_occurrences :
    preparedMulti?.map
      (fun object => object.encoding.openedOccurrences.length) = some 6 := by
  rfl

theorem preparedMulti_has_twelve_constraints :
    preparedMulti?.map (fun object => object.encoding.relations.length) =
      some 12 := by
  rfl

noncomputable abbrev preparedMulti :
    ObjectPreparation.PreparedObject ([] : ManySortedFC.Sig) :=
  preparedMulti?.get preparedMulti_isSome

/-! ## A closed exact model -/

/-- Choose unit for every type name and empty for every capture name. -/
def exactSymbols : (symbols : List ManySortedFC.StaticSort) ->
    SymbolArgs [] symbols
  | [] => .nil
  | .type :: remaining => .cons (.type .one) (exactSymbols remaining)
  | .capture :: remaining =>
      .cons (.capture .empty) (exactSymbols remaining)
  | .classifier :: remaining =>
      .cons (.classifier (.ground .empty)) (exactSymbols remaining)

/-- Reflexivity evidence at the same canonical witnesses.  Generated M11
theories contain inclusions only. -/
def exactEvidence : (relations : List Relation) -> EvidenceArgs [] relations
  | [] => .nil
  | .inclusion .type :: remaining =>
      .cons (.inclusionRefl (.type .one)) (exactEvidence remaining)
  | .inclusion .capture :: remaining =>
      .cons (.inclusionRefl (.capture .empty)) (exactEvidence remaining)
  | .inclusion .classifier :: remaining =>
      .cons (.classifierGroundInclusion .empty .empty)
        (exactEvidence remaining)
  | .equality .type :: remaining =>
      .cons (.equalityRefl (.type .one)) (exactEvidence remaining)
  | .equality .capture :: remaining =>
      .cons (.equalityRefl (.capture .empty)) (exactEvidence remaining)
  | .equality .classifier :: remaining =>
      .cons (.classifierGroundEquality .empty .empty)
        (exactEvidence remaining)
  | .mode mode :: remaining =>
      .cons (.modeEmpty mode) (exactEvidence remaining)
  | .separate :: remaining =>
      .cons (.separateEmpty .empty) (exactEvidence remaining)
  | .disjoint :: remaining =>
      .cons (.disjointEmpty .empty) (exactEvidence remaining)
  | .classifierDisjoint :: remaining =>
      .cons (.classifierGroundDisjoint .empty .empty)
        (exactEvidence remaining)
  | .captureHasKind :: remaining =>
      .cons (.captureHasKindEmpty (.ground .empty))
        (exactEvidence remaining)

/-- The exact witnesses satisfy every retained interval directly.  Building
this derivation structurally avoids re-evaluating the complete source
preparation pipeline inside a native decision procedure. -/
noncomputable def exactModel :
    Theory.Model Ctx.nil preparedMulti.encoding.theory where
  symbols := exactSymbols preparedMulti.encoding.symbols
  evidence := exactEvidence preparedMulti.encoding.relations
  satisfies := by
    repeat' constructor

structure CheckedMulti where
  object : ObjectPreparation.PreparedObject ([] : ManySortedFC.Sig)
  model : Theory.Model Ctx.nil object.encoding.theory
  payloadTyping : Tm.HasType Ctx.nil .unit .empty
    (object.representation.instantiateStatic model.symbols)
  capturesTyping : Evidence.Proves Ctx.nil
    (.inclusionRefl (.capture .empty))
    (.inclusion (.capture .empty) (.capture object.outerCapture))

noncomputable def checkedMulti : CheckedMulti where
  object := preparedMulti
  model := exactModel
  payloadTyping := by
    exact .unit
  capturesTyping := .inclusionRefl (.capture .empty)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev multiLiteral :
    ObjectInterface.Literal Ctx.nil checkedMulti.object.encoding.theory
      checkedMulti.object.representation checkedMulti.object.outerCapture where
  model := checkedMulti.model
  payload := .unit
  payloadValue := .unit
  payloadTyping := checkedMulti.payloadTyping
  captures := .inclusionRefl (.capture .empty)
  capturesTyping := checkedMulti.capturesTyping

theorem multiLiteral_checker_accepts :
    (Tm.check Ctx.nil multiLiteral.term).isSome = true :=
  multiLiteral.checker_accepts

theorem multiLiteral_erases_to_unit :
    multiLiteral.term.erase = .unit := rfl

theorem multiLiteral_has_one_runtime_payload :
    (PayloadScope ([] : Sig) checkedMulti.object.encoding.symbols
      checkedMulti.object.encoding.relations).termCount = 1 := by
  simp

end DOTCaptureToManySortedFC.Intersections.ObjectInterfaceExamples
