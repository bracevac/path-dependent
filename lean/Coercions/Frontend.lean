import Coercions.Frontend.Surface
import Coercions.Frontend.Notation
import Coercions.Frontend.Ann
import Coercions.Frontend.Resolve
import Coercions.Frontend.Decide
import Coercions.Frontend.Fuel
import Coercions.Frontend.Look
import Coercions.Frontend.Sub
import Coercions.Frontend.Alg
import Coercions.Frontend.Limit
import Coercions.Frontend.Avoid
import Coercions.Frontend.Typer
import Coercions.Frontend.Step
import Coercions.Frontend.StepFC
import Coercions.Frontend.Pipeline
import Coercions.Frontend.Pretty
import Coercions.Frontend.Examples

/-!
# The vanilla front end

The root of the `Frontend` library.  It imports the modules of
`lean/Coercions/Frontend/` and changes nothing in the frozen trees it consumes.

`Surface.lean` holds the named abstract syntax the elaborator produces, the
label table that interns surface names as target labels, the scoping and
labelling predicates under which resolution is total, the `expect` helper for
checks run as compiled code, and the command `#assert_no_wf`, which fails if a
definition of a namespace uses well-founded recursion.

`Notation.lean` holds the three syntax categories `dotTy`, `dotTm` and
`dotDefs` that hold the paper's notation, and the three term level entry
points `dotTy%`, `dot%` and `dotDefs%` whose macros expand a piece of that
notation into a surface value.  One departure from the paper: a type member
definition is written `{type A = T}`.  A dotted surface name is a single
token that the macro takes apart.  Importing this module makes the bare word
`type` a keyword, so no later module uses it as an identifier.

`Ann.lean` defines `ATm` and `ADefs`, the terms of DOT-MNF with the two
annotations a front end needs: the self type of an object literal and the
optional result type of a `let`.  Their erasure to `DotMNF.Tm` and
`DotMNF.Defs` drops exactly those two fields.  The module also carries the
renaming, the lemma that erasure commutes with it, and a size measure of
terms.

`Resolve.lean` defines name environments, the spine of inserted bindings,
`atomize`, and the three resolvers from the surface syntax to `ATm`.
Resolution is total on scoped, well labelled programs, which is proved here.
It is structural, so the ten example programs at the end of the module are
checked against hand written terms by `rfl`.  Let insertion has no semantic
statement attached.  A direct style calculus with its own type preservation
theorem would be a separate development.

`Decide.lean` holds the side conditions the typer discharges by computation:
distinctness of the labels of a definition block, and strengthening, the
inverse of `DotMNF.Ty.weaken`.  Each is a decision procedure with an `iff`.
Strengthening is the target's own partial renaming, reused from
`lean/Coercions/FCdot/Checker.lean`, over a traversal of `DotMNF.Ty`.

`Fuel.lean` holds the tank, the one fuel of a typing.  The tank is threaded
from each goal to the next, so it counts the work of the whole run.  A goal
that finds it short marks it, and a marked tank is the recursion limit, the
compiler's `RecursionOverflow`, never a rejection by the rules.  The run keeps
the goals pending along a branch and fails a goal that repeats one of them
exactly, as the compiler does.  Three facts hold for any step that is framed
and dominated, which the combinators of the module give.  A run that ends unmarked gives the same answer
with more fuel (`run_frame`) and with a larger index (`run_index`), and the
cut never loses a success of the run without it (`cut_complete`).  The module
imports only Lean core, so the other front ends share it.

`Look.lean` fixes the cost of a goal, `cost k = k + 1` at `k` pending goals,
and `defaultFuel = 2 ^ 15`.  It holds member lookup on demand, after the
compiler's `findMember`: a recursive type is opened at the variable, both
operands of an intersection are searched, and a selection continues in the
upper bounds of its members.  The lookup returns every member it finds, each
with its derivation, since DOT-MNF has no rule that merges two members of
one name.  A key that repeats along a branch has no answer, the compiler's
cyclic reference.

`Sub.lean` holds the subtyping algorithm.  Its two goals ask `S <: T` and
whether a variable seen at `V` has the type `T`.  Each goal tries its
alternatives in the order of the compiler's `TypeComparer`, and each
alternative emits the DOT-MNF derivation.  The middle of every transitivity
step is a bound of a member or an operand of an intersection, read off a
type the algorithm already holds, so no middle is chosen from the context.
The step is framed and dominated, so the facts of `Fuel.lean` hold, and an
answer stays at more fuel (`sub?_mono`, `var?_mono`).

`Alg.lean` states the algorithmic judgment `Alg`, one constructor per
alternative, with no fuel and no pending goals.  Completeness holds up to the
recursion limit: a goal `Alg` derives is answered at every fuel at which the
run ends unmarked (`sub?_complete`, `var?_complete`).  So a rejection with the
tank unmarked means `Alg` derives no such goal (`sub?_reject`,
`var?_reject`).  The form that some fuel suffices is false.  The alternatives
share the tank, and an alternative that never ends, tried first, marks every
tank (`LP_alg`).  `Alg.answer` builds the derivation each constructor emits,
and `Alg.sound` is its corollary for subtyping.

`Limit.lean` states the goals that end at the recursion limit: a loop through
`∀` bodies, Pierce's divergence of bounded quantification written with type
members, and an alias chain whose work doubles per link.  The kernel checks
each at `defaultFuel`.

`Avoid.lean` approximates the type of a `let` body by a type free of the
binder, as the compiler's `avoid` does.  A selection on the binder at a
covariant position becomes the meet of the avoided upper bounds of all its
members, and at a contravariant position the avoided lower bound of the
first.  Each step returns its `DotMNF.Sub` derivation.  A type that does not
mention the binder comes back strengthened (`avoidLet_strengthen`).

`Typer.lean` holds the typer, structural on the term and threading one tank
through every subtyping goal, lookup and avoidance it asks.  Synthesis
returns a list of candidates, each a type with its derivation.  An
application tries every function type the lookup finds, a projection returns
every field, and an unannotated `let` keeps every pair of candidates.  A
written `let` annotation binds.  The derivation is a field of the result, so
soundness is the result type.  A typing that ends unmarked gives the same
verdict at more fuel (`synthTop?_mono`, `synthTop?_stable`).  The typer as a
whole has no completeness theorem.

`Step.lean` defines the DOT-MNF machine as a function.  The source machine
needs no search, because every side condition of a rule is a pattern match on
a total lookup, so `step?` is fuel free and structural, and one step is a
sigma type over signatures, with `alloc` the rule that allocates.  It comes
with a decided finality test, agreement with the frozen step relation in both
directions, completeness as the full converse since the relation is
deterministic, a constructive classification of the states with no step into
final and stuck, and a driver whose result the relation reaches.  Everything
here reduces in the kernel, so the ten states that probe the ten branches of
the function are checked by `rfl`.

`StepFC.lean` defines the FCdot machine as a function.  The target machine
has one side condition that is not a shape, the head form of an atom's chain
of casts, which the frozen normalizer computes with fuel.  So this step
function takes that fuel, the driver takes it beside a step budget, and
agreement with the frozen relation is three statements: soundness at every
fuel, monotonicity in the fuel, and completeness up to the existence of a
fuel, witnessed by the fuel the derivation used.  Ten concrete states probe
the ten rules.  Nine of them, and the stuck and the final shapes, reduce in
the kernel by `rfl`.  The one that reaches its head form through the
composition of forms needs the kernel's own transparency, because the frozen
composition is defined by well-founded recursion.

`Pipeline.lean` puts the front end together end to end.  `compile` resolves a
surface program and types it at the fuel of a `Budget`, and returns the
annotated term beside the synthesized type and its derivation.
`compileAndRun` follows with the source machine at a step budget.  Five
theorems say what a compiled program is worth, and not one of them is about
the calculus: the target checker accepts the translation of the derivation,
the translation erases to the source term, every reachable state is final or
steps, no reachable state is stuck, and the driver never answers at a state
the machine is stuck at.  The first four are the frozen results of
`lean/Coercions/FCdot/CheckerCompleteness.lean` and
`lean/Coercions/DotToFCdot/` applied to the derivation the typer returned.
The fifth adds the step function's agreement with the step relation, proved
in `Step.lean`.  `compile_checks_get` restates the first for a `compile`
that succeeds, so that an example needs no hypothesis.

`Pretty.lean` is the way back out.  The frozen inductives carry no `Repr`
instance and cannot gain one, so an unparser into the paper's notation is the
only way to read a type, a term or a state of a run as text.  It prints the
surface syntax, the annotated syntax of `Ann.lean`, the frozen syntax of
`DotMNF`, and the store, the continuation and the term of a machine state.  A
label becomes a name through a label table, an index becomes a name through a
name environment, and a binder, which carries neither, is given a short name
the environment does not already hold.  The module carries no theorem.  Its
checks are the printer output on the programs of `Resolve.lean`, and they
reduce in the kernel.

`Examples.lean` takes the programs through the whole front end at
`defaultFuel`, each verdict a `decide +kernel` theorem.  An accepted program
has its type and the tank left (`Ek_type`) and the checker's acceptance of
its translation (`Ek_checks`).  It is compared with the hand written
derivation of `lean/Coercions/DotMNF/Examples.lean` where there is one.  A
rejected program has no type at any budget (`Ek_rejected`).  Where it fails
at one goal of the subtyping core, `Alg` does not derive that goal
(`Ek_not_alg`).  E1, E3 and E4 need a middle type the program does not write,
and scalac rejects them too.  E1s and E3s write that middle type and
compile.  LP, PF and the doubled alias chain end at the recursion limit
(`Ek_limit`).  The file closes with three runs of `compileAndRun`, printed by
the unparser and pinned at the step count each needs.
-/

#assert_no_wf Frontend
