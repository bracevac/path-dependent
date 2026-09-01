import Coercions.DOT.Captures.ModalIntersections.ModalJudgments

/-!
# Typing environments for modal captured intersections

Typing keeps ordinary term/static bindings separate from the stack of active
modal assumptions.  Extending the heterogeneous source scope weakens every
active lock frame along the same source renaming; entering a lock changes only
the assumption stack.
-/

namespace DOTCapture.ModalIntersections

namespace Rename

/-- Weaken an ambient source scope below an existential's hidden static name
and its runtime payload, in that order. -/
def weakenPayload {scope : Sig} (sort : StaticSort) :
    Rename scope (PayloadScope scope sort) :=
  (DOTCapture.BinderOnly.Rename.succ
      (scope := scope) (kind := .static sort)).comp
    (DOTCapture.BinderOnly.Rename.succ
      (scope := scope ▹ .static sort) (kind := .term))

@[simp]
theorem weakenPayload_var {scope : Sig} (sort : StaticSort)
    {kind : BinderKind} (index : BVar scope kind) :
    (weakenPayload sort).var index = .there (.there index) :=
  rfl

end Rename

/-- The complete source environment used by term typing. -/
structure TypingEnv (scope : Sig) where
  bindings : Ctx scope
  locks : ModalAssumptions scope

namespace TypingEnv

/-- The empty source environment. -/
def nil : TypingEnv [] :=
  ⟨Ctx.nil, ModalAssumptions.nil⟩

/-- Add an ordinary runtime variable and weaken every active lock frame below
the same term binder. -/
def extendTerm {scope : Sig} (environment : TypingEnv scope)
    (type : Ty scope) : TypingEnv (scope ▹ .term) :=
  ⟨environment.bindings.extendTerm type,
    environment.locks.rename DOTCapture.BinderOnly.Rename.succ⟩

/-- Add a lexical static variable and weaken every active lock frame below the
same sorted binder. -/
def extendStatic {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope) :
    TypingEnv (scope ▹ .static sort) :=
  ⟨environment.bindings.extendStatic interval,
    environment.locks.rename DOTCapture.BinderOnly.Rename.succ⟩

/-- Add an existential's hidden static variable followed by its runtime
payload.  Defining this as the two primitive extensions keeps the binding and
lock scopes synchronized by construction. -/
def extendPayload {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort)) :
    TypingEnv (PayloadScope scope sort) :=
  (environment.extendStatic interval).extendTerm payloadType

/-- Enter one modal lock frame without changing the source variable scope or
ordinary bindings. -/
def push {scope : Sig} {separationCount : Nat} {modes : List CaptureMode}
    (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope) :
    TypingEnv scope :=
  ⟨environment.bindings, .push environment.locks requirements⟩

@[simp]
theorem nil_bindings : nil.bindings = Ctx.nil := rfl

@[simp]
theorem nil_locks : nil.locks = ModalAssumptions.nil := rfl

@[simp]
theorem extendTerm_bindings {scope : Sig}
    (environment : TypingEnv scope) (type : Ty scope) :
    (environment.extendTerm type).bindings =
      environment.bindings.extendTerm type :=
  rfl

@[simp]
theorem extendTerm_locks {scope : Sig}
    (environment : TypingEnv scope) (type : Ty scope) :
    (environment.extendTerm type).locks =
      environment.locks.rename DOTCapture.BinderOnly.Rename.succ :=
  rfl

@[simp]
theorem extendStatic_bindings {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope) :
    (environment.extendStatic interval).bindings =
      environment.bindings.extendStatic interval :=
  rfl

@[simp]
theorem extendStatic_locks {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope) :
    (environment.extendStatic interval).locks =
      environment.locks.rename DOTCapture.BinderOnly.Rename.succ :=
  rfl

@[simp]
theorem extendPayload_bindings {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort)) :
    (environment.extendPayload interval payloadType).bindings =
      (environment.bindings.extendStatic interval).extendTerm payloadType :=
  rfl

@[simp]
theorem extendPayload_locks {scope : Sig} {sort : StaticSort}
    (environment : TypingEnv scope) (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort)) :
    (environment.extendPayload interval payloadType).locks =
      environment.locks.rename (Rename.weakenPayload sort) := by
  simp only [extendPayload, extendStatic, extendTerm,
    ModalAssumptions.rename_comp, Rename.weakenPayload]

@[simp]
theorem push_bindings {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode} (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope) :
    (environment.push requirements).bindings = environment.bindings :=
  rfl

@[simp]
theorem push_locks {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode} (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope) :
    (environment.push requirements).locks =
      .push environment.locks requirements :=
  rfl

/-- Pushing a lock frame commutes with a term extension after weakening the
frame below that term binder. -/
@[simp]
theorem push_extendTerm {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode} (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope)
    (type : Ty scope) :
    (environment.push requirements).extendTerm type =
      (environment.extendTerm type).push requirements.weaken :=
  rfl

/-- Pushing a lock frame commutes with a static extension after weakening the
frame below that sorted binder. -/
@[simp]
theorem push_extendStatic {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode}
    (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope)
    (interval : Interval sort scope) :
    (environment.push requirements).extendStatic interval =
      (environment.extendStatic interval).push requirements.weaken :=
  rfl

/-- Pushing a lock frame commutes with an existential payload extension after
weakening the frame below both source binders. -/
@[simp]
theorem push_extendPayload {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode}
    (environment : TypingEnv scope)
    (requirements : ModalRequirements separationCount modes scope)
    (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort)) :
    (environment.push requirements).extendPayload interval payloadType =
      (environment.extendPayload interval payloadType).push
        ((requirements.weaken (kind := .static sort)).weaken
          (kind := .term)) :=
  rfl

end TypingEnv

end DOTCapture.ModalIntersections
