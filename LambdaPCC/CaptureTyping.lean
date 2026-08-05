import LambdaPCC.CaptureCoercion

/-!
Store-local typing and use evidence for the capture-aware CK invariant.  A
runtime term carries its result type and a use set; a valid world connects
stored introduction qualifiers with the values that introduced them.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Values and terms -/

def Value.isValue : Value world v T Q -> v.IsValue
| .abs _ _ => .abs
| .pair _ _ => .pair
| .typePair _ _ => .pair
| .capturePair _ _ => .pair

def Value.cast
    (value : Value world v S Q)
    (suffix : TyCoercion world S T) : Value world v T Q :=
  match value with
  | .abs body old => .abs body (old.comp suffix)
  | .pair exact old => .pair exact (old.comp suffix)
  | .typePair exact old => .typePair exact (old.comp suffix)
  | .capturePair exact old => .capturePair exact (old.comp suffix)

/-- Runtime term evidence, indexed jointly by result type and predicted use
set.  Subsumption is retained as a suffix at the outer term constructor. -/
inductive TermEvidence :
    {n : Nat} -> {sigma : Store n} -> {world : World sigma} ->
      (valid : World.Valid world) -> Tm n -> Ty n -> CaptureSet n -> Type 1 where
| path {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {p : Path n} {x : Fin n}
    {T : Ty n} {C : CaptureSet n} :
    Path.Resolve p sigma (.loc x) ->
    TyCoercion world (.capt (.singleton p) (.Single p)) T ->
    Relation world (.singleton p) C ->
    TermEvidence valid (.path p) T C
| value {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {v : Tm n} {T : Ty n}
    {Q C : CaptureSet n} :
    Value world v T Q -> Relation world .empty C ->
    TermEvidence valid v T C
| app {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {p q : Path n}
    {Cf Cp Cq C : CaptureSet n} {S T : Ty n} {U : Ty (n + 1)} :
    TermEvidence valid (.path p) (.capt Cf (.Fun S U)) Cp ->
    TermEvidence valid (.path q) S Cq ->
    TyCoercion world (U.open q) T ->
    Relation world (.union Cp Cq) C ->
    TermEvidence valid (.app p q) T C
| «let» {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {s : Tm n} {body : Tm (n + 1)}
    {S T U : Ty n} {C D : CaptureSet n} :
    TermEvidence valid s S C ->
    Body world S body U.weaken C.weaken ->
    TyCoercion world U T -> Relation world C D ->
    TermEvidence valid (.let s body) T D

def TermEvidence.castType
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {t : Tm n} {S T : Ty n}
    {C : CaptureSet n}
    (term : TermEvidence valid t S C)
    (suffix : TyCoercion world S T) : TermEvidence valid t T C :=
  match term with
  | .path resolution old uses => .path resolution (old.comp suffix) uses
  | .value valueEvidence uses => .value (valueEvidence.cast suffix) uses
  | .app function argument old uses =>
      .app function argument (old.comp suffix) uses
  | .let bound body old uses => .let bound body (old.comp suffix) uses

def TermEvidence.castUse
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {t : Tm n} {T : Ty n}
    {C D : CaptureSet n}
    (term : TermEvidence valid t T C)
    (coverage : Relation world C D) : TermEvidence valid t T D :=
  match term with
  | .path resolution suffix old =>
      .path resolution suffix (old.comp coverage)
  | .value valueEvidence old => .value valueEvidence (old.comp coverage)
  | .app function argument suffix old =>
      .app function argument suffix (old.comp coverage)
  | .let bound body suffix old =>
      .let bound body suffix (old.comp coverage)

/-! ## Syntax-directed views -/

structure PathEvidenceView
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (p : Path n) (T : Ty n)
    (C : CaptureSet n) : Type 1 where
  location : Fin n
  resolution : Path.Resolve p sigma (.loc location)
  suffix : TyCoercion world (.capt (.singleton p) (.Single p)) T
  coverage : Relation world (.singleton p) C

def TermEvidence.pathView
    (term : TermEvidence valid (.path p) T C) :
    PathEvidenceView valid p T C := by
  cases term with
  | path resolution suffix coverage =>
      exact ⟨_, resolution, suffix, coverage⟩
  | value value coverage => cases value

structure AppEvidenceView
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (p q : Path n) (T : Ty n)
    (C : CaptureSet n) : Type 1 where
  functionCaptures : CaptureSet n
  functionUse : CaptureSet n
  argumentUse : CaptureSet n
  argumentType : Ty n
  codomain : Ty (n + 1)
  function : TermEvidence valid (.path p)
    (.capt functionCaptures (.Fun argumentType codomain)) functionUse
  argument : TermEvidence valid (.path q) argumentType argumentUse
  suffix : TyCoercion world (codomain.open q) T
  coverage : Relation world (.union functionUse argumentUse) C

def TermEvidence.appView
    (term : TermEvidence valid (.app p q) T C) :
    AppEvidenceView valid p q T C := by
  cases term with
  | value value coverage => cases value
  | app function argument suffix coverage =>
      exact ⟨_, _, _, _, _, function, argument, suffix, coverage⟩

structure LetEvidenceView
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (s : Tm n) (body : Tm (n + 1))
    (T : Ty n) (D : CaptureSet n) : Type 1 where
  boundType : Ty n
  resultType : Ty n
  localUse : CaptureSet n
  bound : TermEvidence valid s boundType localUse
  closure : Body world boundType body resultType.weaken localUse.weaken
  suffix : TyCoercion world resultType T
  coverage : Relation world localUse D

def TermEvidence.letView
    (term : TermEvidence valid (.let s body) T D) :
    LetEvidenceView valid s body T D := by
  cases term with
  | value value coverage => cases value
  | «let» bound closure suffix coverage =>
      exact ⟨_, _, _, bound, closure, suffix, coverage⟩

structure ValueEvidenceView
    {n : Nat} {sigma : Store n} (world : World sigma)
    (v : Tm n) (T : Ty n) : Type 1 where
  introductionQualifier : CaptureSet n
  value : Value world v T introductionQualifier

theorem TermEvidence.nonemptyValueView
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {v : Tm n} {T : Ty n}
    {C : CaptureSet n}
    (term : TermEvidence valid v T C) (isValue : v.IsValue) :
    Nonempty (ValueEvidenceView world v T) := by
  cases term with
  | path resolution suffix coverage => cases isValue
  | value value coverage => exact ⟨⟨_, value⟩⟩
  | app function argument suffix coverage => cases isValue
  | «let» bound closure suffix coverage => cases isValue

/-! ## Continuations and states -/

/-- A continuation maps the current result type and use set to a final type
and a use set covering the remainder of the run. -/
inductive ContEvidence :
    {n : Nat} -> {sigma : Store n} -> {world : World sigma} ->
      (valid : World.Valid world) -> Ty n -> CaptureSet n ->
      Tm.Cont n -> Ty n -> CaptureSet n -> Type 1 where
| hole {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S T : Ty n} {E C : CaptureSet n} :
    TyCoercion world S T -> Relation world E C ->
    ContEvidence valid S E [] T C
| cons {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S U V T : Ty n}
    {E F D C : CaptureSet n} {body : Tm (n + 1)}
    {cont : Tm.Cont n} :
    ContEvidence valid U D cont T C ->
    Body world S body V.weaken F.weaken ->
    TyCoercion world V U ->
    Relation world E C -> Relation world F D ->
    ContEvidence valid S E (body :: cont) T C

def ContEvidence.inputCoverage
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {S T : Ty n} {E C : CaptureSet n}
    {cont : Tm.Cont n}
    (continuation : ContEvidence valid S E cont T C) :
    Relation world E C :=
  match continuation with
  | .hole _ coverage => coverage
  | .cons _ _ _ coverage _ => coverage

/-- Joint machine invariant for a valid capture-aware world. -/
inductive StateEvidence :
    {n : Nat} -> {sigma : Store n} -> {world : World sigma} ->
      (valid : World.Valid world) -> State n -> Ty n ->
      CaptureSet n -> Type 1 where
| ok {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {cont : Tm.Cont n} {term : Tm n}
    {S T : Ty n} {E C : CaptureSet n} :
    ContEvidence valid S E cont T C ->
    TermEvidence valid term S E ->
    StateEvidence valid (State.mk sigma cont term) T C

end
end Cap
end LambdaPCC
