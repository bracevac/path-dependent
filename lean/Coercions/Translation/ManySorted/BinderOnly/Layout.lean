import Coercions.DOT.Captures.BinderOnly.Context
import Coercions.ManySortedFC.IntervalElaboration
import Coercions.Translation.ManySorted.StaticSlot

/-!
# Layout of binder-only DOT captures in many-sorted FC

This is the first bridge from the DOT-with-captures source family to the
standalone target.  A source term binder occupies one target term slot.  A
source static binder expands to one generated symbol followed by the lower
and upper assumptions that are actually present in its interval.

The lookup result for a static variable is a reusable `StaticSlot`.  Later
object paths `x.A` and `x.C` will use a `(path, label)` lookup to produce this
same structure; the translation of types and captures below is independent of
which kind of source lookup produced the slot.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- The source and target agree on the two initial static sorts without
sharing their syntax definitions. -/
def translateSort : DOTCapture.BinderOnly.StaticSort →
    ManySortedFC.StaticSort
  | .type => .type
  | .capture => .capture

/-- The evidence-binder shape contributed by a source interval. -/
def intervalRelations {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort} :
    DOTCapture.BinderOnly.Interval sort scope →
      List ManySortedFC.Relation
  | .bounds .none .none => []
  | .bounds (.some _) .none => [.inclusion (translateSort sort)]
  | .bounds .none (.some _) => [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- Target signature induced by a source context.  Static declarations expand
to names-first one-symbol theories, whereas source syntax never sees the
target's proof-only evidence binders. -/
def sig : {scope : DOTCapture.BinderOnly.Sig} →
    DOTCapture.BinderOnly.Ctx scope → ManySortedFC.Sig
  | _, .nil => []
  | _, .extend outer binding =>
      match binding with
      | .term _ => ManySortedFC.Sig.extend (sig outer) .term
      | @DOTCapture.BinderOnly.Binding.static _ sort interval =>
          ManySortedFC.StaticScope (sig outer) [translateSort sort]
            (intervalRelations interval)

/-- Weakening of the compiled target scope induced by one source-context
extension. -/
def extendRename {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (outer : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind) :
    ManySortedFC.Rename (sig outer) (sig (.extend outer binding)) :=
  match binding with
  | .term _ => ManySortedFC.Rename.succ
  | @DOTCapture.BinderOnly.Binding.static _ sort interval =>
      ManySortedFC.Rename.weakenStatic [translateSort sort]
        (intervalRelations interval)

/-- Canonical coordinates allocated by the newest source static binder.

Only the endpoint *shape* matters here.  Endpoint expressions are translated
separately when the target theory is built. -/
def newestStaticSlot {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (outer : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope) :
    ManySortedTranslation.StaticSlot
      (sig (outer.extendStatic interval)) (translateSort sort) :=
  match interval with
  | .bounds .none .none =>
      ManySortedTranslation.StaticSlot.unconstrained
        (sig outer) (translateSort sort)
  | .bounds (.some _) .none =>
      { name := .there .here, lower := some .here, upper := none }
  | .bounds .none (.some _) =>
      { name := .there .here, lower := none, upper := some .here }
  | .bounds (.some _) (.some _) =>
      { name := .there (.there .here)
        lower := some .here
        upper := some (.there .here) }

/-- Map a source term variable to its unique target runtime coordinate. -/
def termVar : {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) →
    DOTCapture.BinderOnly.BVar scope .term →
      ManySortedFC.BVar (sig context) .term
  | _, .extend _ (.term _), .here => .here
  | _, .extend outer binding, .there older =>
      (extendRename outer binding).var (termVar outer older)

/-- Map a source static variable to its generated target name and exact
optional evidence coordinates. -/
def staticSlot : {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) →
    {sort : DOTCapture.BinderOnly.StaticSort} →
    DOTCapture.BinderOnly.BVar scope (.static sort) →
      ManySortedTranslation.StaticSlot (sig context) (translateSort sort)
  | _, .extend outer (.static interval), _, .here =>
      newestStaticSlot outer interval
  | _, .extend outer binding, _, .there older =>
      (staticSlot outer older).rename (extendRename outer binding)

/-- Translate a variable-only stable path. -/
def translatePath {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (path : DOTCapture.BinderOnly.Path scope) :
    ManySortedFC.BVar (sig context) .term :=
  match path with
  | .var name => termVar context name

/-- Translate a sorted static reference through its reusable slot. -/
def translateRef {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (reference : DOTCapture.BinderOnly.StaticRef sort scope) :
    ManySortedFC.StaticExpr (translateSort sort) (sig context) :=
  match reference with
  | .bound name => (staticSlot context name).expression

/-- The exact target theory assigned to a source interval.  This is an
abbreviation, rather than an existential result carrier, so clients cannot
replace the translated endpoints while retaining only the relation shape. -/
abbrev CompiledInterval {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope) :=
  ManySortedFC.Theory (sig context) [translateSort sort]
    (intervalRelations interval)

mutual

/-- Translate source capture expressions. -/
def translateCapture {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    DOTCapture.BinderOnly.Capture scope → ManySortedFC.Capture (sig context)
  | .empty => .empty
  | .union left right =>
      .union (translateCapture context left) (translateCapture context right)
  | .singleton path => .singleton (translatePath context path)
  | .ref reference =>
      match translateRef context reference with
      | .capture capture => capture

/-- Translate source types.  Each source static quantifier becomes a target
constrained quantifier over the independently compiled true interval. -/
def translateTy {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    DOTCapture.BinderOnly.Ty scope → ManySortedFC.Ty (sig context)
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference =>
      match translateRef context reference with
      | .type type => type
  | .capturing captures shape =>
      .capturing (translateCapture context captures)
        (translateTy context shape)
  | .arr domain codomain =>
      .arr (translateTy context domain) (translateTy context codomain)
  | .forallI interval body =>
      .forallT (translateInterval context interval)
        (translateTy (context.extendStatic interval) body)
  | .existsI interval body =>
      .existsT (translateInterval context interval)
        (translateTy (context.extendStatic interval) body)

/-- Translate a sorted source expression. -/
def translateExpr {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    DOTCapture.BinderOnly.StaticExpr sort scope →
      ManySortedFC.StaticExpr (translateSort sort) (sig context)
  | .type type => .type (translateTy context type)
  | .capture capture => .capture (translateCapture context capture)

/-- Compile one source true interval.  No branch requests evidence relating
its two endpoints. -/
def translateInterval {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope) :
    CompiledInterval context interval :=
  match interval with
  | .bounds .none .none =>
      ManySortedFC.Interval.unconstrained (translateSort sort)
  | .bounds (.some lower) .none =>
      ManySortedFC.Interval.lowerBounded (translateExpr context lower)
  | .bounds .none (.some upper) =>
      ManySortedFC.Interval.upperBounded (translateExpr context upper)
  | .bounds (.some lower) (.some upper) =>
      ManySortedFC.Interval.between (translateExpr context lower)
        (translateExpr context upper)

end

/-- Compile the payloads of a source context into the induced target scope. -/
def translateContext : {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) → ManySortedFC.Ctx (sig context)
  | _, .nil => .nil
  | _, .extend outer binding =>
      match binding with
      | .term type =>
          (translateContext outer).extendTerm (translateTy outer type)
      | .static interval =>
          (translateContext outer).extendTheory
            (translateInterval outer interval)

@[simp]
theorem sig_nil : sig (.nil : DOTCapture.BinderOnly.Ctx []) = [] := rfl

@[simp]
theorem sig_extendTerm {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (type : DOTCapture.BinderOnly.Ty scope) :
    sig (context.extendTerm type) =
      ManySortedFC.Sig.extend (sig context) .term := rfl

@[simp]
theorem translateContext_extendTerm
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (type : DOTCapture.BinderOnly.Ty scope) :
    translateContext (context.extendTerm type) =
      (translateContext context).extendTerm (translateTy context type) := rfl

@[simp]
theorem translateContext_extendStatic
    {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope) :
    translateContext (context.extendStatic interval) =
      (translateContext context).extendTheory
        (translateInterval context interval) := rfl

end DOTCaptureToManySortedFC.BinderOnly
