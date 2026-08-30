import Coercions.DOT.Captures.BinderOnly.StaticJudgments

/-!
# Ambient realization of source intervals

An interval is realized by choosing a same-sort static expression between
each endpoint that is present.  Crucially, `SatisfiedBy` is indexed by an
outer `Ctx scope`, and both the witness and interval also inhabit `scope`.
The static binder governed by the interval would live in
`scope ▹ .static sort`; it therefore cannot occur in any evidence used to
realize its own interval.  This is the source no-self-discharge boundary.
-/

namespace DOTCapture.BinderOnly.Interval

/-- Proof-relevant realization of an interval by an ambient witness.

There is one constructor for each endpoint shape.  Present lower endpoints
must include into the witness, and the witness must include into present upper
endpoints.  All inclusions are checked in `context`, before the interval's
static binder is introduced. -/
inductive SatisfiedBy {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (witness : StaticExpr sort scope) :
    Interval sort scope -> Type where
  | unbounded :
      SatisfiedBy context witness (.bounds .none .none)
  | lower {lower : StaticExpr sort scope}
      (evidence : Includes context lower witness) :
      SatisfiedBy context witness (.bounds (.some lower) .none)
  | upper {upper : StaticExpr sort scope}
      (evidence : Includes context witness upper) :
      SatisfiedBy context witness (.bounds .none (.some upper))
  | between {lower upper : StaticExpr sort scope}
      (lowerEvidence : Includes context lower witness)
      (upperEvidence : Includes context witness upper) :
      SatisfiedBy context witness
        (.bounds (.some lower) (.some upper))

namespace SatisfiedBy

/-- Extract the lower-bound evidence whenever a lower endpoint is present,
independently of the upper endpoint's shape. -/
def lowerEvidence {scope : Sig} {context : Ctx scope}
    {sort : StaticSort} {witness lower : StaticExpr sort scope}
    {upper : Endpoint sort scope}
    (satisfaction : SatisfiedBy context witness
      (.bounds (.some lower) upper)) :
    Includes context lower witness :=
  match upper, satisfaction with
  | .none, .lower evidence => evidence
  | .some _, .between evidence _ => evidence

/-- Extract the upper-bound evidence whenever an upper endpoint is present,
independently of the lower endpoint's shape. -/
def upperEvidence {scope : Sig} {context : Ctx scope}
    {sort : StaticSort} {witness upper : StaticExpr sort scope}
    {lower : Endpoint sort scope}
    (satisfaction : SatisfiedBy context witness
      (.bounds lower (.some upper))) :
    Includes context witness upper :=
  match lower, satisfaction with
  | .none, .upper evidence => evidence
  | .some _, .between _ evidence => evidence

/-- Extract both obligations of a two-sided realization. -/
def betweenEvidence {scope : Sig} {context : Ctx scope}
    {sort : StaticSort} {witness lower upper : StaticExpr sort scope}
    (satisfaction : SatisfiedBy context witness
      (.bounds (.some lower) (.some upper))) :
    Includes context lower witness × Includes context witness upper :=
  ⟨satisfaction.lowerEvidence, satisfaction.upperEvidence⟩

end SatisfiedBy

namespace Examples

/-- The exact `One` type interval is realized by `One` using reflexivity in
the empty outer context. -/
def exactOne :
    SatisfiedBy Ctx.nil (.type .one)
      (Interval.exact (.type .one)) :=
  .between .refl .refl

/-- The exact empty-capture interval is realized by the empty capture using
reflexivity in the empty outer context. -/
def exactEmptyCapture :
    SatisfiedBy Ctx.nil (.capture .empty)
      (Interval.exact (.capture .empty)) :=
  .between .refl .refl

/-- An unbounded capture interval accepts every ambient capture witness and
requires no inclusion evidence. -/
def unboundedCapture {scope : Sig} (context : Ctx scope)
    (witness : Capture scope) :
    SatisfiedBy context (.capture witness)
      (Interval.unbounded (sort := .capture)) :=
  .unbounded

end Examples

end DOTCapture.BinderOnly.Interval
