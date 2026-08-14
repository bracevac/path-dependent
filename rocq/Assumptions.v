(** Central trust audit for published safety and regression results.

    This file intentionally contains only imports and [Print Assumptions]
    commands.  [make rocq-audit] rejects its output if any command reports an
    axiom. *)

Set Warnings "-already-declared-rewrite-hint-db".

From PathDependent Require Import LambdaP LambdaPFC LambdaPCC.

Print Assumptions
  PathDependent.LambdaP.Safety.Tm_Ty_closed_type_safety.

Print Assumptions
  PathDependent.LambdaPFC.SemanticSafety.tm_ty_closed_type_safety.
Print Assumptions
  PathDependent.LambdaPFC.GeneralPairRegression.term_type_safety.

Print Assumptions
  PathDependent.LambdaP.CounterexampleRegression.CounterexampleRegression.historical_body_subtyping_blocked.
Print Assumptions
  PathDependent.LambdaP.CounterexampleRegression.CounterexampleRegression.selection_to_argument_singleton_blocked.

Print Assumptions
  PathDependent.LambdaPCC.CaptureSafety.tm_ty_closed_progress.
Print Assumptions
  PathDependent.LambdaPCC.CaptureSafety.tm_ty_closed_finite_preservation.
Print Assumptions
  PathDependent.LambdaPCC.CaptureSafety.tm_ty_closed_type_safety.
Print Assumptions
  PathDependent.LambdaPCC.CaptureBounds.tm_ty_closed_finite_application_coverage.
Print Assumptions
  PathDependent.LambdaPCC.CaptureBounds.tm_ty_closed_finite_returned_capture_bound.

Print Assumptions
  PathDependent.LambdaPCC.CaptureRegression.exact_capture_member.
Print Assumptions
  PathDependent.LambdaPCC.CaptureRegression.application_opens_capture.

Print Assumptions
  PathDependent.LambdaPCC.GeneralPairRegression.term_type_safety.
Print Assumptions
  PathDependent.LambdaPCC.GeneralPairRegression.allocated_type_pair_progress.
Print Assumptions
  PathDependent.LambdaPCC.GeneralPairRegression.capture_term_type_safety.
Print Assumptions
  PathDependent.LambdaPCC.GeneralPairRegression.allocated_capture_pair_progress.
Print Assumptions
  PathDependent.LambdaPCC.GeneralPairRegression.selected_capture_member_progress.
