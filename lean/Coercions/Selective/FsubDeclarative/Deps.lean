import Lean
import Coercions.Selective.FsubDeclarative
/-!
Dependency check for the headline theorems: the transitive closure of the constants
their types and proofs mention, restricted to namespace `SelFsub`, grouped by the module
that declares them, and tested against the certificate layer's typing, operations and
results.
-/
open Lean Elab Command

/-- Every constant reachable from `roots` through types and values. -/
def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | c :: rest =>
      todo := rest
      if !seen.contains c then
        seen := seen.insert c
        if let some ci := env.find? c then
          let extra := match ci with
            | .inductInfo v => v.ctors
            | .ctorInfo v => [v.induct]
            | _ => []
          todo := ci.type.getUsedConstants.toList ++
            (ci.value?.map (·.getUsedConstants.toList)).getD [] ++ extra ++ todo
  return seen

/-- Constants of the certificate layer that the declarative proof must not reach. -/
def forbidden : List Name :=
  [``SelFsub.Prim, ``SelFsub.PrimAt, ``SelFsub.prim?, ``SelFsub.CTy, ``SelFsub.Cert.subst,
   ``SelFsub.Cert.ofPrim, ``SelFsub.Cert.narrow, ``SelFsub.Cert.inst, ``SelFsub.Cert.arrInv,
   ``SelFsub.Cert.allInv, ``SelFsub.Cert.allBound, ``SelFsub.CSub, ``SelFsub.CTy.subst,
   ``SelFsub.CTy.narrow, ``SelFsub.CTy.inst, ``SelFsub.CTy.arr_inv, ``SelFsub.CTy.all_inv,
   ``SelFsub.HTy, ``SelFsub.synthC, ``SelFsub.synthTm, ``SelFsub.preservation,
   ``SelFsub.progress, ``SelFsub.safety, ``SelFsub.Sub.toCert, ``SelFsub.Sub.toCert_typed,
   ``SelFsub.primitive_sound, ``SelFsub.coercion_sound, ``SelFsub.elaboration_typed,
   ``SelFsub.elaboration_complete, ``SelFsub.typability_iff, ``SelFsub.fsub_safety]

/-- Compiler and equation auxiliaries are reported only by count. -/
def isAux (n : Name) : Bool :=
  n.isInternal || n.isImplementationDetail ||
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
   "noConfusionType", "sizeOf_spec", "ctorIdx", "ctorElim", "ctorElimType"].any
    (fun s => n.getString! == s || (toString n).endsWith s!".{s}") ||
  [".match_", ".eq_", "_sunfold", "._", ".proof_", ".brecOn.go", ".elim"].any (fun s => ((toString n).splitOn s).length > 1)

elab "#deps " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.toList.map (·.getId)
  let cl := closure env roots
  let sel := cl.toList.filter (fun n => (`SelFsub).isPrefixOf n)
  let bad := forbidden.filter cl.contains
  logInfo m!"roots: {roots}"
  logInfo m!"constants reached: {cl.size}; in namespace SelFsub: {sel.length}"
  let mods := sel.foldl (fun (acc : Std.HashMap Name (Array Name)) n =>
    let m := (env.getModuleIdxFor? n).map (env.header.moduleNames[·]!) |>.getD `this
    acc.insert m ((acc.getD m #[]).push n)) {}
  for (m, ns) in mods.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let main := ns.filter (!isAux ·) |>.qsort (fun a b => a.toString < b.toString)
    let shown := main.toList.map (fun n => (n.replacePrefix `SelFsub .anonymous).toString)
    logInfo m!"{m}: {", ".intercalate shown} (+{ns.size - main.size} auxiliary)"
  logInfo m!"forbidden constants reached: {bad}"

#deps SelFsub.fsub_progress
#deps SelFsub.fsub_preservation
#deps SelFsub.fsub_safety_direct

/-- The same test on a theorem of the certificate route, as a control of the check. -/
elab "#forbidden " id:ident : command => do
  let cl := closure (← getEnv) [id.getId]
  logInfo m!"control {id.getId}: forbidden constants reached: {forbidden.filter cl.contains}"

#forbidden SelFsub.fsub_safety

/-! The constants of namespace `SelFsub` that the certificate route's `safety` reaches,
by module; the matched line comparison counts these declarations. -/
#deps SelFsub.safety
