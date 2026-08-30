import DotToFCsub.M7.Surface
import DotToFCsub.M6.Realizability

/-!
# Proof-directed M7 elaboration boundary

The front end receives, rather than searches for, source validity, finite path
resolution, recursive-member realization, and singleton equality.  Every field
below is an existing M5 or M6 certificate.  In particular, this module does not
define a second source typing relation and does not claim a total compiler for
`DotFCRP` terms.
-/

namespace DotToFCsub.M7

open DotFCRP.Source

namespace Surface.Program

/-- Syntactic allocation key for the method argument `leftPath.A`. -/
def leftKey (program : Surface.Program) :
    M6.MemberKey program.pathScope :=
  ⟨program.leftPath, program.selectedLabel⟩

/-- Syntactic allocation key for the method result `rightPath.A`. -/
def rightKey (program : Surface.Program) :
    M6.MemberKey program.pathScope :=
  ⟨program.rightPath, program.selectedLabel⟩

end Surface.Program

/-- All proof-relevant input supplied by the source checker and the existing
M5/M6 bridge.

`pathContext`, `leftEndpointWf`, and `rightEndpointWf` are validation premises:
the source checker has established that both endpoints of `rekeySignature` are
meaningful.  They are deliberately not presented as a source term-typing or
source-to-target theorem.  The target compiler consumes only the finite images
and their `MemberPathEq`; it never attempts to reconstruct source path equality.
-/
structure Certificate (program : Surface.Program) : Type where
  sourceValid : DotFCR.Source.TypeDefs.RecValid
    DotFCR.Source.Ctx.nil program.definitions
  pathContext : DotFCRP.Source.Ctx program.pathScope
  leftEndpointWf : DotFCRP.Source.Wf program.aliases pathContext
    program.leftSelection
  rightEndpointWf : DotFCRP.Source.Wf program.aliases pathContext
    program.rightSelection
  encoding : M5.Encoding (target := []) program.definitions
  layout : M6.PathLayout program.aliases []
  recursiveLayout : M6.RecursiveLayoutRealization layout encoding
  leftImage : M6.MemberImage layout program.leftKey
  rightImage : M6.MemberImage layout program.rightKey
  leftMember : M6.RecursiveMemberAt encoding leftImage
  rightMember : M6.RecursiveMemberAt encoding rightImage
  memberEquality : M6.MemberPathEq leftImage rightImage

namespace Certificate

/-- The validation premises for the two endpoints advertised by the surface
method signature.  This states well-formedness only, not source term typing. -/
def signatureEndpointsWf {program : Surface.Program}
    (certificate : Certificate program) :
    DotFCRP.Source.Wf program.aliases certificate.pathContext
        program.leftSelection ×
      DotFCRP.Source.Wf program.aliases certificate.pathContext
        program.rightSelection :=
  ⟨certificate.leftEndpointWf, certificate.rightEndpointWf⟩

/-- Reuse the exact M5 source-to-target preservation theorem for the closed
recursive object.  This is the complete source claim made by M7. -/
noncomputable def sourcePreservation {program : Surface.Program}
    (certificate : Certificate program) :
    M5.RecursivePreservation certificate.encoding :=
  M5.preserveRecursiveObject certificate.sourceValid certificate.encoding

/-- The supplied complete path layout realizes the aliased recursive object
using the existing M6 theorem. -/
noncomputable def aliasedObjectRealization {program : Surface.Program}
    (certificate : Certificate program) :
    M6.AliasedRecursiveObjectRealization certificate.layout
      certificate.encoding FCsub.Ctx.nil :=
  M6.realizeAliasedRecursiveObject certificate.recursiveLayout FCsub.Ctx.nil

/-- The selected source singleton equality is realized at the same exact M5
member on both paths, with both directed transports checked by FCsub. -/
noncomputable def singletonRealization {program : Surface.Program}
    (certificate : Certificate program) :
    M6.SingletonMemberRealization certificate.leftMember
      certificate.rightMember certificate.memberEquality FCsub.Ctx.nil :=
  M6.realizeSingletonMember certificate.leftMember certificate.rightMember
    certificate.memberEquality FCsub.Ctx.nil

/-- Co-resolved selected paths expose the same exact recursive member. -/
theorem selected_member_coherent {program : Surface.Program}
    (certificate : Certificate program) :
    certificate.leftMember.memberIndex =
      certificate.rightMember.memberIndex :=
  certificate.leftMember.memberIndex_eq_of_pathEq certificate.rightMember
    certificate.memberEquality

end Certificate

end DotToFCsub.M7
