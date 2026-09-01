import Coercions.ManySortedFC.StaticDomainClassifier

/-!
# Ground static-domain checks for classifier kinds

The examples use the generic certificate boundary, not the target evidence
checker.  They demonstrate that the classifier instance exposes the existing
ground algorithms without suggesting that target sorts are dynamically
extensible.
-/

namespace ManySortedFC.StaticDomainExamples

open GroundStaticDomain

def shared : Classifier := .child 0 .top
def control : Classifier := .child 0 shared
def io : Classifier := .child 1 shared

def onlyShared : Classifier.Kind := Classifier.Kind.classifier shared
def onlyControl : Classifier.Kind := Classifier.Kind.classifier control
def onlyIO : Classifier.Kind := Classifier.Kind.classifier io

theorem io_below_shared : io ≤ shared := by
  exact .child .refl

theorem control_below_shared : control ≤ shared := by
  exact .child .refl

theorem io_control_disjoint : Classifier.Disjoint io control := by
  native_decide

def inclusionCertificate :
    GroundStaticDomain.Certificate classifierKindGroundDomain where
  relation := .inclusion
  left := onlyIO
  right := onlyShared

def disjointCertificate :
    GroundStaticDomain.Certificate classifierKindGroundDomain where
  relation := .disjoint
  left := onlyIO
  right := onlyControl

def rejectedReverseCertificate :
    GroundStaticDomain.Certificate classifierKindGroundDomain where
  relation := .inclusion
  left := onlyShared
  right := onlyIO

example : inclusionCertificate.Holds := by
  exact Classifier.Kind.Subkind.semantics.mpr (by
    intro point inIO
    exact Classifier.Kind.Contains.classifier
      (Classifier.le_trans (Classifier.Kind.Contains.classifier_iff.mp inIO)
        io_below_shared))

example : disjointCertificate.Holds :=
  Classifier.Kind.Disjoint.classifiers io_control_disjoint

example : inclusionCertificate.accepts = true := by native_decide
example : disjointCertificate.accepts = true := by native_decide
example : rejectedReverseCertificate.accepts = false := by native_decide

example : ∃ checked, inclusionCertificate.check = some checked :=
  GroundStaticDomain.Certificate.check_complete (by
    exact Classifier.Kind.Subkind.semantics.mpr (by
      intro point inIO
      exact Classifier.Kind.Contains.classifier
        (Classifier.le_trans (Classifier.Kind.Contains.classifier_iff.mp inIO)
          io_below_shared)))

example : inclusionCertificate.erase = () := rfl

end ManySortedFC.StaticDomainExamples
