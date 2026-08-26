import SystemFSub.ElaborationRegression
import SystemFSub.ElaborationAllRegression
import SystemFSub.ElaborationSafety

/-!
# Source-safety regression

These corollaries exercise the completed operational bridge: they concern the
original System F<: programs, not merely their compiled target expressions.
-/

namespace SystemFSub.ElaborationSafetyRegression

theorem bounded_identity_source_sound :
    Not (SystemFSub.Tm.GoesWrong
      SystemFSub.ElaborationRegression.program) :=
  SystemFSub.Elaboration.source_not_goesWrong
    SystemFSub.ElaborationRegression.program_typing

theorem full_all_source_sound :
    Not (SystemFSub.Tm.GoesWrong
      SystemFSub.ElaborationAllRegression.program) :=
  SystemFSub.Elaboration.source_not_goesWrong
    SystemFSub.ElaborationAllRegression.program_typing

end SystemFSub.ElaborationSafetyRegression
