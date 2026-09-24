import Lean
import Coercions.FCdotR
import Coercions.Oopsla16

/-!
# Axiom audit of `FCdotR` and `Oopsla16`

This file belongs to no library, so `lake build` does not compile it.  After
`lake build FCdotR Oopsla16`, run it from the repository root:

```sh
lake env lean lean/Coercions/FCdotR/audit/AxiomAudit.lean
```

It visits every constant of the environment that is defined in a module under
`Coercions.FCdotR` or `Coercions.Oopsla16`, auxiliary and private constants
included, and collects the axioms each one depends on (`Lean.collectAxioms`,
which also reports `sorryAx`).  It prints the number of constants checked and
the number that depend on an axiom other than `propext` and `Quot.sound`,
followed by each such constant with its axioms.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut n := 0
  for (name, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`Coercions.FCdotR).isPrefixOf mod || (`Coercions.Oopsla16).isPrefixOf mod then
        n := n + 1
        let axs ← liftCoreM <| Lean.collectAxioms name
        let extra := axs.filter (fun a => a != ``propext && a != ``Quot.sound)
        if !extra.isEmpty then bad := bad.push (name, extra)
  logInfo m!"checked {n} constants; offending: {bad.size}"
  for (nm, ax) in bad do logInfo m!"  {nm}: {ax}"
