import LambdaPToFCo.Full.ValueModel

/-!
# Opened stable-identity value interfaces

`ValuePlan` describes the fields hidden by a compiled value package.  A
`ValueInterface` supplies those fields in a target context.  Keeping the
hidden identity and its payload available as projections is the low-level
bridge used by paths, dependent application, and identity-preserving
adapters.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

/-- A fully instantiated value plan in `context`.  The fields mirror the
mandatory `I, i : I` prefix of `ValuePlan.telescope`; spelling the prefix out
makes stable identity preservation available without inspecting a dependent
`Telescope.Args` value at every use site. -/
structure ValueInterface {sig : Sig} (context : Ctx sig) where
  plan : ValuePlan sig
  identity : Ty sig
  payload : Exp sig
  payloadTyping : Exp.HasType context payload identity
  observations : Telescope.Args context
    ((plan.observations.subst ((Subst.openTVar identity).lift .var)).subst
      (Subst.openVar payload))

namespace ValueInterface

/-- The complete mixed argument spine represented by an opened interface. -/
def arguments {sig : Sig} {context : Ctx sig}
    (interface : ValueInterface context) :
    Telescope.Args context interface.plan.telescope :=
  .tvar interface.identity
    (.var interface.payload interface.payloadTyping interface.observations)

/-- Recover the explicit prefix representation from an arbitrary complete
argument spine for a value plan. -/
def ofArguments {sig : Sig} {context : Ctx sig} (plan : ValuePlan sig)
    (arguments : Telescope.Args context plan.telescope) :
    ValueInterface context := by
  cases arguments with
  | tvar identity rest =>
      cases rest with
      | var payload payloadTyping observations =>
          exact
            { plan
              identity
              payload
              payloadTyping
              observations }

@[simp] theorem ofArguments_arguments {sig : Sig} {context : Ctx sig}
    (interface : ValueInterface context) :
    ofArguments interface.plan interface.arguments = interface := by
  cases interface
  rfl

/-- Repackage an opened interface at its public existential type. -/
noncomputable def package {sig : Sig} {context : Ctx sig}
    (interface : ValueInterface context) : Exp sig :=
  interface.plan.pack interface.arguments

noncomputable def package_hasType {sig : Sig} {context : Ctx sig}
    (interface : ValueInterface context) :
    Exp.HasType context interface.package interface.plan.inputTy :=
  interface.plan.pack_hasType interface.arguments

/-- Renaming an opened interface renames its plan and all supplied fields. -/
noncomputable def rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    ValueInterface targetContext :=
  ofArguments (interface.plan.rename mapping)
    (interface.arguments.rename mapping typed)

end ValueInterface

end LambdaPToFCo.Full
