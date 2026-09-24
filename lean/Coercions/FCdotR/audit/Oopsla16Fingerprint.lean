import Lean
import Coercions.Oopsla16

/-!
# Fingerprint of the `Oopsla16` library

This file belongs to no library, so `lake build` does not compile it.  After
`lake build Oopsla16`, run it from the repository root:

```sh
lake env lean lean/Coercions/FCdotR/audit/Oopsla16Fingerprint.lean
```

It prints one row for every constant defined in a module under
`Coercions.Oopsla16`: the name, the kind, a hash of the type and, for a
definition, a hash of the value.  The rows are sorted.  Two lines end the
output: the number of rows, and a digest of all of them.

Comments and doc strings do not enter, so a documentation edit leaves the
output unchanged; a change to a statement, a rule, a type or a definition
changes a row, and a new or removed constant changes the count.  The hashes are
those of the pinned toolchain.  `STATUS.md` records the count and the digest
of the `Oopsla16` the safety theorems are about, and says at which commits they
were taken.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (name, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`Coercions.Oopsla16).isPrefixOf mod then
        let kind := match ci with
          | .defnInfo _ => "def" | .thmInfo _ => "thm" | .inductInfo _ => "ind"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
        let v := match ci with
          | .defnInfo d => toString (hash d.value) | _ => "-"
        rows := rows.push s!"{name} {kind} {hash ci.type} {v}"
  let sorted := rows.qsort (· < ·)
  for r in sorted do IO.println r
  IO.println s!"total {sorted.size}"
  IO.println s!"digest {sorted.foldl (fun h r => mixHash h (hash r)) 7}"
