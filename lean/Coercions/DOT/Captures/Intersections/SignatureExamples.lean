import Coercions.DOT.Captures.Intersections.SignatureMetatheory

/-!
# Normalized-signature regressions

These examples instantiate the generic bound-expression family independently
at the type and capture sorts.  They exercise shared identity, conjunction by
interval accumulation, sorted allocation, and explicit cross-sort failure.
-/

namespace DOTCapture.Intersections.Examples

inductive TypeBound where
  | bottom
  | atom (name : Nat)
  | top
deriving DecidableEq, Repr

inductive CaptureBound where
  | empty
  | singleton (name : Nat)
  | universal
deriving DecidableEq, Repr

def BoundExpr : StaticSort -> Type
  | .type => TypeBound
  | .capture => CaptureBound

open Signature

def typeLeft : Signature BoundExpr :=
  singletonType 3 .bottom (.atom 0)

def typeRight : Signature BoundExpr :=
  singletonType 3 (.atom 1) .top

theorem typeLeft_normalized : typeLeft.Normalized := by
  simpa [typeLeft] using
    (singletonType_normalized (Expr := BoundExpr) 3
      TypeBound.bottom (TypeBound.atom 0))

theorem typeRight_normalized : typeRight.Normalized := by
  simpa [typeRight] using
    (singletonType_normalized (Expr := BoundExpr) 3
      (TypeBound.atom 1) TypeBound.top)

def typeMerged : Signature BoundExpr :=
  ⟨[.type 3 [⟨.bottom, .atom 0⟩, ⟨.atom 1, .top⟩]]⟩

/-- Same-label type members allocate one identity and retain both intervals. -/
example : merge? typeLeft typeRight = .ok typeMerged := rfl

example : typeMerged.entries.length = 1 := rfl

example : typeMerged.occurrenceCount = 2 := rfl

example : typeMerged.lookup 3 = typeMerged.entries.head? := rfl

example : typeMerged.constraintsAt 3 =
    [.type 3 ⟨.bottom, .atom 0⟩, .type 3 ⟨.atom 1, .top⟩] := rfl

example : typeMerged.Normalized :=
  merge?_normalized typeLeft typeRight typeMerged
    typeLeft_normalized typeRight_normalized rfl

def captureLeft : Signature BoundExpr :=
  singletonCapture 5 .empty (.singleton 0)

def captureRight : Signature BoundExpr :=
  singletonCapture 5 (.singleton 1) .universal

theorem captureLeft_normalized : captureLeft.Normalized := by
  simpa [captureLeft] using
    (singletonCapture_normalized (Expr := BoundExpr) 5
      CaptureBound.empty (CaptureBound.singleton 0))

theorem captureRight_normalized : captureRight.Normalized := by
  simpa [captureRight] using
    (singletonCapture_normalized (Expr := BoundExpr) 5
      (CaptureBound.singleton 1) CaptureBound.universal)

def captureMerged : Signature BoundExpr :=
  ⟨[.capture 5 [⟨.empty, .singleton 0⟩,
    ⟨.singleton 1, .universal⟩]]⟩

/-- Capture constraints use the same label-first merge without crossing sorts. -/
example : merge? captureLeft captureRight = .ok captureMerged := rfl

example : captureMerged.entries.length = 1 := rfl

example : captureMerged.occurrenceCount = 2 := rfl

example : captureMerged.constraintsAt 5 =
    [.capture 5 ⟨.empty, .singleton 0⟩,
      .capture 5 ⟨.singleton 1, .universal⟩] := rfl

example : captureMerged.Normalized :=
  merge?_normalized captureLeft captureRight captureMerged
    captureLeft_normalized captureRight_normalized rfl

def laterCapture : Signature BoundExpr :=
  singletonCapture 8 .empty .universal

def earlierType : Signature BoundExpr :=
  singletonType 2 .bottom .top

theorem laterCapture_normalized : laterCapture.Normalized := by
  simpa [laterCapture] using
    (singletonCapture_normalized (Expr := BoundExpr) 8
      CaptureBound.empty CaptureBound.universal)

theorem earlierType_normalized : earlierType.Normalized := by
  simpa [earlierType] using
    (singletonType_normalized (Expr := BoundExpr) 2
      TypeBound.bottom TypeBound.top)

def sortedMixed : Signature BoundExpr :=
  ⟨[.type 2 [⟨.bottom, .top⟩],
    .capture 8 [⟨.empty, .universal⟩]]⟩

/-- Different labels retain their distinct sorts and normalize by label first. -/
example : merge? laterCapture earlierType = .ok sortedMixed := rfl

example : sortedMixed.Normalized :=
  merge?_normalized laterCapture earlierType sortedMixed
    laterCapture_normalized earlierType_normalized rfl

def conflictingType : Signature BoundExpr :=
  singletonType 9 .bottom .top

def conflictingCapture : Signature BoundExpr :=
  singletonCapture 9 .empty .universal

/-- A shared label cannot be allocated once at each static sort. -/
example : merge? conflictingType conflictingCapture =
    .error ⟨9, .type, .capture⟩ := rfl

example : merge? conflictingCapture conflictingType =
    .error ⟨9, .capture, .type⟩ := rfl

/-- The executable result satisfies the independent merge specification. -/
example : LawfulMerge typeLeft typeRight typeMerged :=
  merge?_lawful typeLeft typeRight typeMerged
    typeLeft_normalized typeRight_normalized rfl

/-- Reversing the conjuncts preserves the constraint multiset. -/
example : ConstraintEquivalent typeMerged
    ⟨[.type 3 [⟨.atom 1, .top⟩, ⟨.bottom, .atom 0⟩]]⟩ :=
  merge?_comm_equivalent typeLeft typeRight typeMerged
    ⟨[.type 3 [⟨.atom 1, .top⟩, ⟨.bottom, .atom 0⟩]]⟩ rfl rfl

end DOTCapture.Intersections.Examples
