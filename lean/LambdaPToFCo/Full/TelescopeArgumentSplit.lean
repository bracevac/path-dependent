import SystemFCoExt.TelescopeInstances

/-!
# Splitting arguments for an appended target telescope

This target-generic helper is the inverse-shaped eliminator needed when a
Church pair representation is opened as one appended telescope.  It returns
the exact first argument spine and indexes the suffix spine by that first
spine's proof-relevant substitution.  It deliberately states no equality of
argument records or typing derivations.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace TargetArguments

/-- Binder count used only as a recursion measure.  Substitution changes
indices and field syntax but preserves this count. -/
def telescopeBinderCount : Telescope sig -> Nat
  | .nil => 0
  | .var _ tail => telescopeBinderCount tail + 1
  | .tvar tail => telescopeBinderCount tail + 1
  | .cvar _ _ tail => telescopeBinderCount tail + 1

@[simp] theorem telescopeBinderCount_subst (tele : Telescope source)
    (substitution : Subst source target) :
    telescopeBinderCount (tele.subst substitution) =
      telescopeBinderCount tele := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [Telescope.subst, telescopeBinderCount, ih]
  | tvar tail ih =>
      simp only [Telescope.subst, telescopeBinderCount, ih]
  | cvar source target tail ih =>
      simp only [Telescope.subst, telescopeBinderCount, ih]

/-- Split arguments for `first.append second`.  The suffix arguments retain
the literal substitution determined by the returned first arguments. -/
noncomputable def splitAppend :
    {first : Telescope sig} -> (second : Telescope first.scope) ->
    Telescope.Args base (first.append second) ->
    Sigma fun firstArguments : Telescope.Args base first =>
      Telescope.Args base (second.subst firstArguments.substitution)
  | .nil, second, arguments =>
      ⟨.nil, second.subst_id.symm ▸ arguments⟩
  | .var type tail, second, .var argument argumentTyping rest => by
      let opening := tail.liftSubst (Subst.openVar argument)
      let openedTail := tail.subst (Subst.openVar argument)
      let openedSecond := second.subst opening
      have openedRest : Telescope.Args base
          (openedTail.append openedSecond) :=
        (tail.append_subst second (Subst.openVar argument)) ▸ rest
      let result := splitAppend openedSecond openedRest
      let firstArguments : Telescope.Args base (.var type tail) :=
        .var argument argumentTyping result.1
      refine ⟨firstArguments, ?_⟩
      change Telescope.Args base
        (second.subst (opening.comp result.1.substitution))
      exact second.subst_comp opening result.1.substitution ▸ result.2
  | .tvar tail, second, .tvar argument rest => by
      let opening := tail.liftSubst (Subst.openTVar argument)
      let openedTail := tail.subst (Subst.openTVar argument)
      let openedSecond := second.subst opening
      have openedRest : Telescope.Args base
          (openedTail.append openedSecond) :=
        (tail.append_subst second (Subst.openTVar argument)) ▸ rest
      let result := splitAppend openedSecond openedRest
      let firstArguments : Telescope.Args base (.tvar tail) :=
        .tvar argument result.1
      refine ⟨firstArguments, ?_⟩
      change Telescope.Args base
        (second.subst (opening.comp result.1.substitution))
      exact second.subst_comp opening result.1.substitution ▸ result.2
  | .cvar source target tail, second,
      .cvar argument argumentTyping rest => by
      let opening := tail.liftSubst (Subst.openCVar argument)
      let openedTail := tail.subst (Subst.openCVar argument)
      let openedSecond := second.subst opening
      have openedRest : Telescope.Args base
          (openedTail.append openedSecond) :=
        (tail.append_subst second (Subst.openCVar argument)) ▸ rest
      let result := splitAppend openedSecond openedRest
      let firstArguments : Telescope.Args base (.cvar source target tail) :=
        .cvar argument argumentTyping result.1
      refine ⟨firstArguments, ?_⟩
      change Telescope.Args base
        (second.subst (opening.comp result.1.substitution))
      exact second.subst_comp opening result.1.substitution ▸ result.2
termination_by first => telescopeBinderCount first
decreasing_by
  all_goals simp [telescopeBinderCount]

end TargetArguments

end LambdaPToFCo.Full
