import SystemFCoExt.TelescopeInstances

namespace SystemFCoExt.TelescopeInstancesRegression

open Telescope

/-- A closed telescope with a type field, a term field depending on that
type, and a proper coercion field. -/
def mixed : Telescope [] :=
  .tvar (.var (.tvar .here) (.cvar .top .top .nil))

def mixedSuffix : Telescope mixed.scope := .tvar .nil

example : (mixed.append mixedSuffix).scope = mixedSuffix.scope :=
  mixed.append_scope mixedSuffix

example :
    cast (congrArg Ctx (mixed.appendScopeEq mixedSuffix))
        ((mixed.append mixedSuffix).context Ctx.empty) =
      mixedSuffix.context (mixed.context Ctx.empty) :=
  mixed.append_context_cast mixedSuffix Ctx.empty

example :
    cast (congrArg (Rename []) (mixed.appendScopeEq mixedSuffix))
        (mixed.append mixedSuffix).weaken =
      mixed.weaken.comp mixedSuffix.weaken :=
  mixed.append_weaken mixedSuffix

noncomputable def fields :
    Args (mixed.context Ctx.empty) (mixed.rename mixed.weaken) :=
  Telescope.Args.identity mixed Ctx.empty

noncomputable def repackage : Exp mixed.scope := Telescope.pack fields

noncomputable def repackageTyping :
    Exp.HasType (mixed.context Ctx.empty) repackage
      (mixed.rename mixed.weaken).existsTy :=
  Telescope.pack_hasType fields

def suffix : Telescope (mixed.rename mixed.weaken).scope := .tvar .nil

noncomputable def suffixFields :
    Args (mixed.context Ctx.empty) (suffix.subst fields.substitution) := by
  change Args (mixed.context Ctx.empty) (.tvar .nil)
  exact .tvar .top .nil

noncomputable def combined :
    Args (mixed.context Ctx.empty)
      ((mixed.rename mixed.weaken).append suffix) :=
  fields.append suffix suffixFields

def combinedTele : Telescope mixed.scope :=
  (mixed.rename mixed.weaken).append suffix

def identityFunction : Exp mixed.scope := .abs .top (.var .here)

example : combined.apply identityFunction =
    suffixFields.apply (fields.apply identityFunction) :=
  Telescope.Args.append_apply fields suffix suffixFields identityFunction

example : combined.substitution =
    Telescope.Args.appendSubstitution fields suffix suffixFields :=
  Telescope.Args.append_substitution fields suffix suffixFields

example : combined.instantiate (.top : Ty combinedTele.scope) =
    (.top : Ty combinedTele.scope).subst
      (Telescope.Args.appendSubstitution fields suffix suffixFields) :=
  Telescope.Args.append_instantiate fields suffix suffixFields .top

end SystemFCoExt.TelescopeInstancesRegression
