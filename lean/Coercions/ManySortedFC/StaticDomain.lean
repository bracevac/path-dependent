/-!
# Contracts for decidable ground static domains

`GroundStaticDomain` packages the part of a static theory that can be checked
without variables or hypotheses: a ground syntax, a semantic observation
space, decidable equality/inclusion/disjointness judgments, and proofs that
those judgments have their expected extensional meanings.

This is deliberately not a plugin interface for `ManySortedFC`.  The closed
kernel still fixes its static sorts, expressions, propositions, and evidence
constructors.  The contract only factors the common obligations of a ground
decision procedure so that a kernel extension can reuse and audit them.
-/

namespace ManySortedFC

universe u v

/-- A decidable ground static domain, presented through observations.

`Ground` is closed syntax and `Point` is the semantic observation space.
`Contains ground point` interprets a ground expression.  The three logical
relations and their decision procedures are domain-specific, but their
semantic characterizations are fixed here. -/
structure GroundStaticDomain where
  Ground : Type u
  Point : Type v
  Contains : Ground -> Point -> Prop
  Equivalent : Ground -> Ground -> Prop
  Includes : Ground -> Ground -> Prop
  Disjoint : Ground -> Ground -> Prop
  groundDecidableEq : DecidableEq Ground
  containsDecision : (ground : Ground) -> (point : Point) ->
    Decidable (Contains ground point)
  equivalentDecision : (left right : Ground) ->
    Decidable (Equivalent left right)
  includesDecision : (source target : Ground) ->
    Decidable (Includes source target)
  disjointDecision : (left right : Ground) ->
    Decidable (Disjoint left right)
  equivalent_semantics : forall left right,
    Equivalent left right <->
      forall point, Contains left point <-> Contains right point
  includes_semantics : forall source target,
    Includes source target <->
      forall point, Contains source point -> Contains target point
  disjoint_semantics : forall left right,
    Disjoint left right <->
      forall point, Contains left point -> Contains right point -> False

namespace GroundStaticDomain

/-- The extensional interpretation of one ground expression. -/
def Interpretation (domain : GroundStaticDomain) := domain.Point -> Prop

/-- Interpret a ground expression by its observable members. -/
def interpret (domain : GroundStaticDomain) (ground : domain.Ground) :
    domain.Interpretation :=
  fun point => domain.Contains ground point

instance (domain : GroundStaticDomain) : DecidableEq domain.Ground :=
  domain.groundDecidableEq

instance (domain : GroundStaticDomain) (ground : domain.Ground)
    (point : domain.Point) : Decidable (domain.Contains ground point) :=
  domain.containsDecision ground point

instance (domain : GroundStaticDomain) (left right : domain.Ground) :
    Decidable (domain.Equivalent left right) :=
  domain.equivalentDecision left right

instance (domain : GroundStaticDomain) (source target : domain.Ground) :
    Decidable (domain.Includes source target) :=
  domain.includesDecision source target

instance (domain : GroundStaticDomain) (left right : domain.Ground) :
    Decidable (domain.Disjoint left right) :=
  domain.disjointDecision left right

/-! ## Laws derived once from the semantic characterizations -/

theorem equivalent_refl (domain : GroundStaticDomain)
    (ground : domain.Ground) : domain.Equivalent ground ground := by
  apply (domain.equivalent_semantics ground ground).mpr
  intro _
  exact Iff.rfl

theorem equivalent_symm (domain : GroundStaticDomain)
    {left right : domain.Ground} (equivalent : domain.Equivalent left right) :
    domain.Equivalent right left := by
  apply (domain.equivalent_semantics right left).mpr
  intro point
  exact ((domain.equivalent_semantics left right).mp equivalent point).symm

theorem equivalent_trans (domain : GroundStaticDomain)
    {first second third : domain.Ground}
    (firstStep : domain.Equivalent first second)
    (secondStep : domain.Equivalent second third) :
    domain.Equivalent first third := by
  apply (domain.equivalent_semantics first third).mpr
  intro point
  exact Iff.trans
    ((domain.equivalent_semantics first second).mp firstStep point)
    ((domain.equivalent_semantics second third).mp secondStep point)

theorem includes_refl (domain : GroundStaticDomain)
    (ground : domain.Ground) : domain.Includes ground ground := by
  apply (domain.includes_semantics ground ground).mpr
  intro _ contained
  exact contained

theorem includes_trans (domain : GroundStaticDomain)
    {first second third : domain.Ground}
    (firstStep : domain.Includes first second)
    (secondStep : domain.Includes second third) :
    domain.Includes first third := by
  apply (domain.includes_semantics first third).mpr
  intro point contained
  exact (domain.includes_semantics second third).mp secondStep point
    ((domain.includes_semantics first second).mp firstStep point contained)

theorem equivalent_includes_left (domain : GroundStaticDomain)
    {left right : domain.Ground} (equivalent : domain.Equivalent left right) :
    domain.Includes left right := by
  apply (domain.includes_semantics left right).mpr
  intro point contained
  exact ((domain.equivalent_semantics left right).mp equivalent point).mp contained

theorem equivalent_includes_right (domain : GroundStaticDomain)
    {left right : domain.Ground} (equivalent : domain.Equivalent left right) :
    domain.Includes right left :=
  domain.equivalent_includes_left (domain.equivalent_symm equivalent)

theorem includes_antisymm (domain : GroundStaticDomain)
    {left right : domain.Ground}
    (forward : domain.Includes left right)
    (backward : domain.Includes right left) :
    domain.Equivalent left right := by
  apply (domain.equivalent_semantics left right).mpr
  intro point
  exact ⟨
    (domain.includes_semantics left right).mp forward point,
    (domain.includes_semantics right left).mp backward point⟩

theorem disjoint_symm (domain : GroundStaticDomain)
    {left right : domain.Ground} (disjoint : domain.Disjoint left right) :
    domain.Disjoint right left := by
  apply (domain.disjoint_semantics right left).mpr
  intro point inRight inLeft
  exact (domain.disjoint_semantics left right).mp disjoint point inLeft inRight

theorem disjoint_mono_left (domain : GroundStaticDomain)
    {smaller larger other : domain.Ground}
    (included : domain.Includes smaller larger)
    (disjoint : domain.Disjoint larger other) :
    domain.Disjoint smaller other := by
  apply (domain.disjoint_semantics smaller other).mpr
  intro point inSmaller inOther
  have inLarger :=
    (domain.includes_semantics smaller larger).mp included point inSmaller
  exact (domain.disjoint_semantics larger other).mp disjoint point inLarger inOther

theorem disjoint_mono_right (domain : GroundStaticDomain)
    {other smaller larger : domain.Ground}
    (included : domain.Includes smaller larger)
    (disjoint : domain.Disjoint other larger) :
    domain.Disjoint other smaller :=
  domain.disjoint_symm
    (domain.disjoint_mono_left included (domain.disjoint_symm disjoint))

theorem disjoint_transport_left (domain : GroundStaticDomain)
    {source target other : domain.Ground}
    (equivalent : domain.Equivalent source target)
    (disjoint : domain.Disjoint source other) :
    domain.Disjoint target other :=
  domain.disjoint_mono_left
    (domain.equivalent_includes_right equivalent) disjoint

theorem disjoint_transport_right (domain : GroundStaticDomain)
    {other source target : domain.Ground}
    (equivalent : domain.Equivalent source target)
    (disjoint : domain.Disjoint other source) :
    domain.Disjoint other target :=
  domain.disjoint_mono_right
    (domain.equivalent_includes_right equivalent) disjoint

/-! ## A generic boundary for ground certificates -/

/-- The three ground relations certified by the contract. -/
inductive CertificateRelation where
  | equality
  | inclusion
  | disjoint
deriving DecidableEq, Repr

/-- A fully annotated ground certificate.  It carries no proof: the checker
recomputes the selected relation from the two ground endpoints. -/
structure Certificate (domain : GroundStaticDomain) where
  relation : CertificateRelation
  left : domain.Ground
  right : domain.Ground

namespace Certificate

/-- Declarative meaning of a ground certificate. -/
def Holds {domain : GroundStaticDomain} (certificate : Certificate domain) : Prop :=
  match certificate.relation with
  | .equality => domain.Equivalent certificate.left certificate.right
  | .inclusion => domain.Includes certificate.left certificate.right
  | .disjoint => domain.Disjoint certificate.left certificate.right

/-- The checker invokes exactly the decision procedure named by the
certificate. -/
def holdsDecision {domain : GroundStaticDomain} :
    (certificate : Certificate domain) -> Decidable certificate.Holds
  | ⟨.equality, left, right⟩ => domain.equivalentDecision left right
  | ⟨.inclusion, left, right⟩ => domain.includesDecision left right
  | ⟨.disjoint, left, right⟩ => domain.disjointDecision left right

/-- Successful checking retains the independently recomputed proposition. -/
structure Checked {domain : GroundStaticDomain}
    (certificate : Certificate domain) : Type where
  proof : certificate.Holds

/-- Check a fully annotated ground certificate without proof search. -/
def check {domain : GroundStaticDomain} (certificate : Certificate domain) :
    Option (Checked certificate) :=
  match certificate.holdsDecision with
  | isTrue proof => some ⟨proof⟩
  | isFalse _ => none

/-- Boolean acceptance is useful for executable regression tests. -/
def accepts {domain : GroundStaticDomain} (certificate : Certificate domain) : Bool :=
  match certificate.holdsDecision with
  | isTrue _ => true
  | isFalse _ => false

/-- Certificate checking is sound by construction. -/
theorem check_sound {domain : GroundStaticDomain}
    {certificate : Certificate domain} (checked : Checked certificate) :
    certificate.Holds :=
  checked.proof

/-- Every true fully ground claim is accepted. -/
theorem check_complete {domain : GroundStaticDomain}
    {certificate : Certificate domain} (holds : certificate.Holds) :
    ∃ checked, certificate.check = some checked := by
  unfold check
  cases certificate.holdsDecision with
  | isTrue proof => exact ⟨⟨proof⟩, rfl⟩
  | isFalse refutation => exact (refutation holds).elim

/-- Executable acceptance is equivalent to the declarative ground relation. -/
theorem accepts_iff {domain : GroundStaticDomain}
    {certificate : Certificate domain} :
    certificate.accepts = true ↔ certificate.Holds := by
  unfold accepts
  cases certificate.holdsDecision with
  | isTrue proof => simp [proof]
  | isFalse refutation => simp [refutation]

/-- A ground certificate is proof-only at the runtime boundary. -/
def erase {domain : GroundStaticDomain} (_ : Certificate domain) : Unit := ()

/-- A checked certificate is equally runtime-free. -/
def Checked.erase {domain : GroundStaticDomain} {certificate : Certificate domain}
    (_ : Checked certificate) : Unit := ()

@[simp] theorem erase_eq {domain : GroundStaticDomain}
    (certificate : Certificate domain) : certificate.erase = () := rfl

@[simp] theorem Checked.erase_eq {domain : GroundStaticDomain}
    {certificate : Certificate domain} (checked : Checked certificate) :
    checked.erase = () := rfl

end Certificate

end GroundStaticDomain

end ManySortedFC
