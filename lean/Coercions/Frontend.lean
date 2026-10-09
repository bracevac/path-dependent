import Coercions.Frontend.Surface
import Coercions.Frontend.Notation
import Coercions.Frontend.Ann
import Coercions.Frontend.Resolve
import Coercions.Frontend.Decide
import Coercions.Frontend.Fuel
import Coercions.Frontend.Reason
import Coercions.Frontend.Look
import Coercions.Frontend.Sub
import Coercions.Frontend.Alg
import Coercions.Frontend.Limit
import Coercions.Frontend.Avoid
import Coercions.Frontend.Typer
import Coercions.Frontend.Elab
import Coercions.Frontend.Step
import Coercions.Frontend.StepFC
import Coercions.Frontend.Pipeline
import Coercions.Frontend.Pretty
import Coercions.Frontend.Examples

/-!
# The vanilla front end

The root of the `Frontend` library.  It imports the modules of
`lean/Coercions/Frontend/`.  The typer follows the Scala 3 compiler on DOT-MNF,
and the frozen trees it builds on are unchanged.

* `Surface` is the named syntax the elaborator produces, with the label table
  that interns names as labels, and the command `#assert_no_wf`, which fails if
  a namespace uses well-founded recursion.
* `Notation` is the syntax of the paper's notation: the entry points `dotTy%`,
  `dot%` and `dotDefs%`.  A type member is written `{type A = T}`.  Importing it
  makes `type` a keyword.
* `Ann` is `ATm` and `ADefs`, DOT-MNF terms with the self type of an object
  literal and the optional result type of a `let`.  Erasure to `DotMNF.Tm`
  drops exactly those two.
* `Resolve` is the resolvers from surface syntax to `ATm`, total on scoped,
  well labelled programs.  Let insertion has no semantic statement.
* `Decide` is the side conditions the typer computes: distinct labels of a
  definition block, and strengthening, the inverse of `DotMNF.Ty.weaken`.
* `Fuel` is the tank, the one fuel of a typing.  A goal that finds it short
  marks it, and a marked tank is the recursion limit (the compiler's
  `RecursionOverflow`), never a rejection by the rules.  The run fails a goal
  that repeats a pending one.  For a step that is framed and dominated, a run
  that ends unmarked gives the same answer with more fuel (`run_frame`) and a
  larger index (`run_index`), and the cut loses no success (`cut_complete`).
* `Reason` is why a program is rejected: a missing parameter type, a cyclic
  reference, a definition that needs a written type, candidates with no least
  type, a reason of the typer, a mismatch, or the recursion limit.  It is
  generic in the label type and in the typer's reasons, and imports only
  Lean core.  `Reason.top` picks the one a rejection reports.
* `Look` is the cost of a goal, `cost k = k + 1`, `defaultFuel = 2 ^ 15`, and
  member lookup on demand, after `Types.findMember`.  It returns every member
  it finds, each with its derivation, since DOT-MNF cannot merge two members.
  A key that repeats along a branch has no answer.
* `Sub` is the subtyping algorithm.  Its goals are `S <: T` and a variable seen
  at `V` having type `T`.  The alternatives follow `TypeComparer`, and each
  emits the DOT-MNF derivation.  An answer stays at more fuel (`sub?_mono`,
  `var?_mono`).
* `Alg` is the judgment `Alg`, one constructor per alternative, with no fuel.
  Completeness holds up to the recursion limit (`sub?_complete`,
  `var?_complete`), so an unmarked rejection means `Alg` derives no such goal
  (`sub?_reject`, `var?_reject`).  The form "some fuel suffices" is false,
  since an alternative that never ends, tried first, marks every tank
  (`LP_alg`).
* `Limit` is the goals that end at the recursion limit, checked at
  `defaultFuel`.
* `Avoid` approximates the type of a `let` body by one free of the binder, as
  `TypeOps.avoid` does.  A type that does not mention the binder comes back
  strengthened (`avoidLet_strengthen`).
* `Typer` is the typer.  It threads one tank through every goal, returns a list
  of candidates with their derivations, and keeps every choice.  A typing that
  ends unmarked gives the same verdict at more fuel (`synthTop?_mono`,
  `synthTop?_stable`).  It has no completeness theorem.
* `Elab` is the elaborator in front of the typer.  It fills the empty slots of
  a partial term: a lambda's domain from the function part of its goal, or
  from the callee of a body `g x` when the goal has none, a call argument's
  goal from the dominant formal of the callee, a literal's self type from a
  `μ` goal.  A term with no empty slot goes to the typer as it is, so a
  program with every slot written is the typer's, at the same fuel
  (`elabF_toI`, `elabChkF_toI`).  The elaborator is framed (`elabF_framed`),
  and a lambda whose body has no empty slot is the typer's check of the filled
  lambda (`lam_fill_full`).
* `Step` is the DOT-MNF machine as a structural function, with agreement with
  the frozen step relation in both directions.
* `StepFC` is the FCdot machine as a function.  It takes the fuel of the frozen
  head form normalizer, and agreement with the relation is soundness at every
  fuel, monotonicity in the fuel, and completeness for some fuel.
* `Pipeline` is `compile`, which resolves and types a program at the fuel of a
  `Budget`, and `compileAndRun`, which then runs the machine.  Five theorems
  say what a compiled program is worth: the target checker accepts the
  translation of the derivation, the translation erases to the source term,
  every reachable state is final or steps, none is stuck, and the driver never
  answers at a stuck state.  `compile_checks_get` restates the first for a
  program that compiles.
* `Pretty` is an unparser into the paper's notation for surface, annotated and
  frozen syntax and for machine states.  The frozen inductives have no `Repr`,
  so this is how a type, a term or a state is read.  It has no theorem.
* `Examples` takes the programs through the front end at `defaultFuel`, each
  verdict a `decide +kernel` theorem.  Accepted programs have `Ek_type` and
  `Ek_checks`.  Rejected programs have `Ek_rejected`, and `Ek_not_alg` where the
  rejection is at one subtyping goal.  Programs at the recursion limit have
  `Ek_limit`.
-/

#assert_no_wf Frontend
