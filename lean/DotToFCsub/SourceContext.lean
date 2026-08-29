import DotToFCsub.Layout
import DotFC.Explicit.SourceContext

/-!
# Executable DOT source-context translation to standalone FCsub

Plain source declarations add one FCsub term binder.  A direct member
declaration opens its complete static telescope and then adds its separate
unit payload binder.
-/

namespace DotToFCsub.SourceContext

/-- Translate a source context when all of its types satisfy the executable
stable-layout boundary. -/
def translate? : {source : DotFC.Sig} →
    (context : DotFC.Source.Ctx source) →
    Option (FCsub.Ctx (Layout.sig (DotFC.Explicit.Ctx.ofSource context)))
  | _, .nil => some .nil
  | _, .snoc outer (.member _ lower upper) => do
      let target ← translate? outer
      let lower' ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource outer) lower
      let upper' ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource outer) upper
      pure (target.extendPayload (MemberEncoding.telescope lower' upper') .one)
  | _, .snoc outer .top => do
      let target ← translate? outer
      pure (target.extendTerm .top)
  | _, .snoc outer .bot => do
      let target ← translate? outer
      pure (target.extendTerm .bot)
  | _, .snoc outer (.all domain codomain) => do
      let target ← translate? outer
      let type ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource outer)
        (.all domain codomain)
      pure (target.extendTerm type)
  | _, .snoc outer (.sel path label) => do
      let target ← translate? outer
      let type ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource outer)
        (.sel path label)
      pure (target.extendTerm type)

/-- Proof-relevant graph of context translation. -/
def Translates {source : DotFC.Sig} (sourceContext : DotFC.Source.Ctx source)
    (targetContext :
      FCsub.Ctx (Layout.sig (DotFC.Explicit.Ctx.ofSource sourceContext))) :
    Prop :=
  translate? sourceContext = some targetContext

/-- Exact executable context boundary admitted by the bridge. -/
def Ready {source : DotFC.Sig} (context : DotFC.Source.Ctx source) : Prop :=
  ∃ target, Translates context target

theorem Translates.functional {source : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {first second :
      FCsub.Ctx (Layout.sig (DotFC.Explicit.Ctx.ofSource sourceContext))}
    (left : Translates sourceContext first)
    (right : Translates sourceContext second) : first = second := by
  unfold Translates at left right
  rw [left] at right
  exact Option.some.inj right

@[simp]
theorem translate_nil :
    translate? DotFC.Source.Ctx.nil = some FCsub.Ctx.nil := rfl

end DotToFCsub.SourceContext
