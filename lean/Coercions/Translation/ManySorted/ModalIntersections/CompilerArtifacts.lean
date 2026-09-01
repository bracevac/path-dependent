import Coercions.DOT.Captures.ModalIntersections.Typing
import Coercions.ManySortedFC.Administrative
import Coercions.ManySortedFC.TermChecker
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext

/-!
# Checked compiler artifacts

This module is the output boundary for the cumulative compiler.  A compiled
artifact retains its source derivation, the exact partial translations of its
indices, the standalone target check that accepted its term, and its relation
to the independently defined source erasure.

Structural adapters can eta-expand values, so the general runtime statement
is `Runtime.AdministrativeEq`.  Compiler cases that erase literally enter this
boundary through `finishValueExact?` and `finishTermExact?` below.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev ValueTyping {scope : Sig} :=
  @DOTCapture.ModalIntersections.Value.HasType scope
abbrev TermTyping {scope : Sig} :=
  @DOTCapture.ModalIntersections.Term.HasType scope

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev Tm := ManySortedFC.Tm

end Target

/-- A source value and the independently accepted target value produced for
it.  The target checker result is retained, rather than reconstructed from a
compiler-internal typing derivation. -/
structure CompiledValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceValue : Source.Value sourceScope)
    (sourceType : Source.Ty sourceScope) where
  sourceTyping : Source.ValueTyping environment sourceValue sourceType
  targetType : Target.Ty targetScope
  typePrepared :
    Preparation.translateType core.layout sourceType = .ok targetType
  term : Target.Tm targetScope
  valueChecked : ManySortedFC.Tm.ValueChecked term
  valueAccepted : ManySortedFC.Tm.checkValue term = some valueChecked
  isValue : ManySortedFC.Tm.IsValue term
  checked : ManySortedFC.Tm.Checked core.target term
  accepted : ManySortedFC.Tm.check core.target term = some checked
  useMatches : checked.use = .empty
  typeMatches : checked.type = targetType
  erasure : ManySortedFC.Runtime.AdministrativeEq term.erase
    (core.eraseValue sourceValue)

/-- A source computation and the independently accepted target computation
produced for it. -/
structure CompiledTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceTerm : Source.Term sourceScope)
    (sourceUse : Source.Capture sourceScope)
    (sourceType : Source.Ty sourceScope) where
  sourceTyping : Source.TermTyping environment sourceTerm sourceUse sourceType
  targetUse : Target.Capture targetScope
  targetType : Target.Ty targetScope
  usePrepared :
    Preparation.translateCapture core.layout sourceUse = .ok targetUse
  typePrepared :
    Preparation.translateType core.layout sourceType = .ok targetType
  term : Target.Tm targetScope
  checked : ManySortedFC.Tm.Checked core.target term
  accepted : ManySortedFC.Tm.check core.target term = some checked
  useMatches : checked.use = targetUse
  typeMatches : checked.type = targetType
  erasure : ManySortedFC.Runtime.AdministrativeEq term.erase
    (core.eraseTerm sourceTerm)

namespace CompiledValue

/-- Declarative target typing recovered from the retained checker result. -/
def targetTyping {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue core sourceValue sourceType) :
    ManySortedFC.Tm.HasType core.target compiled.term .empty
      compiled.targetType := by
  simpa only [compiled.useMatches, compiled.typeMatches] using
    compiled.checked.typing

/-- Public checker projection for a compiled value. -/
theorem checkerAccepts {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue core sourceValue sourceType) :
    ManySortedFC.Tm.synth core.target compiled.term =
      some (.empty, compiled.targetType) := by
  unfold ManySortedFC.Tm.synth
  rw [compiled.accepted]
  simp only [Option.map_some]
  rw [compiled.useMatches, compiled.typeMatches]

/-- The standalone value-side checker also accepts the emitted syntax. -/
theorem valueCheckerAccepts {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue core sourceValue sourceType) :
    (ManySortedFC.Tm.checkValue compiled.term).isSome = true := by
  rw [compiled.valueAccepted]
  rfl

end CompiledValue

namespace CompiledTerm

/-- Declarative target typing recovered from the retained checker result. -/
def targetTyping {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledTerm core sourceTerm sourceUse sourceType) :
    ManySortedFC.Tm.HasType core.target compiled.term
      compiled.targetUse compiled.targetType := by
  simpa only [compiled.useMatches, compiled.typeMatches] using
    compiled.checked.typing

/-- Public checker projection for a compiled computation. -/
theorem checkerAccepts {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledTerm core sourceTerm sourceUse sourceType) :
    ManySortedFC.Tm.synth core.target compiled.term =
      some (compiled.targetUse, compiled.targetType) := by
  unfold ManySortedFC.Tm.synth
  rw [compiled.accepted]
  simp only [Option.map_some]
  rw [compiled.useMatches, compiled.typeMatches]

end CompiledTerm

/-- Close a value artifact only after both the value-side condition and the
standalone term checker accept it at the independently prepared source type. -/
def finishValue? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : Source.ValueTyping environment sourceValue sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : ManySortedFC.Runtime.AdministrativeEq candidate.erase
      (core.eraseValue sourceValue)) :
    Option (CompiledValue core sourceValue sourceType) :=
  match typePrepared : Preparation.translateType core.layout sourceType with
  | .error _ => none
  | .ok targetType =>
      match valueAccepted : ManySortedFC.Tm.checkValue candidate with
      | none => none
      | some valueChecked =>
          match accepted : ManySortedFC.Tm.check core.target candidate with
          | none => none
          | some checked =>
              if useMatches : checked.use =
                  (.empty : Target.Capture targetScope) then
                if typeMatches : checked.type = targetType then
                  some
                    { sourceTyping := sourceTyping
                      targetType := targetType
                      typePrepared := typePrepared
                      term := candidate
                      valueChecked := valueChecked
                      valueAccepted := valueAccepted
                      isValue := valueChecked.typing
                      checked := checked
                      accepted := accepted
                      useMatches := useMatches
                      typeMatches := typeMatches
                      erasure := candidateErasure }
                else
                  none
              else
                none

/-- Close a computation artifact only after the standalone checker reproduces
both independently prepared source indices. -/
def finishTerm? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : Source.TermTyping environment sourceTerm sourceUse
      sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : ManySortedFC.Runtime.AdministrativeEq candidate.erase
      (core.eraseTerm sourceTerm)) :
    Option (CompiledTerm core sourceTerm sourceUse sourceType) :=
  match usePrepared :
      Preparation.translateCapture core.layout sourceUse with
  | .error _ => none
  | .ok targetUse =>
      match typePrepared :
          Preparation.translateType core.layout sourceType with
      | .error _ => none
      | .ok targetType =>
          match accepted : ManySortedFC.Tm.check core.target candidate with
          | none => none
          | some checked =>
              if useMatches : checked.use = targetUse then
                if typeMatches : checked.type = targetType then
                  some
                    { sourceTyping := sourceTyping
                      targetUse := targetUse
                      targetType := targetType
                      usePrepared := usePrepared
                      typePrepared := typePrepared
                      term := candidate
                      checked := checked
                      accepted := accepted
                      useMatches := useMatches
                      typeMatches := typeMatches
                      erasure := candidateErasure }
                else
                  none
              else
                none

/-- Literal erasure is the common compiler case; inject it into the general
administrative boundary without changing the target artifact. -/
def finishValueExact? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : Source.ValueTyping environment sourceValue sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : candidate.erase = core.eraseValue sourceValue) :
    Option (CompiledValue core sourceValue sourceType) :=
  finishValue? core sourceTyping candidate (candidateErasure ▸ .refl)

/-- Literal computation erasure enters the same checked output boundary. -/
def finishTermExact? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : Source.TermTyping environment sourceTerm sourceUse
      sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : candidate.erase = core.eraseTerm sourceTerm) :
    Option (CompiledTerm core sourceTerm sourceUse sourceType) :=
  finishTerm? core sourceTyping candidate (candidateErasure ▸ .refl)

end DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
