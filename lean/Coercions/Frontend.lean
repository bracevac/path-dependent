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
import Coercions.Frontend.Search
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
labelling predicates under which resolution is total, and the `expect` helper
that later tests use in place of `by decide`.

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
renaming, the lemma that erasure commutes with it, and the size measure the
typer recurses on.

`Resolve.lean` defines name environments, the spine of inserted bindings,
`atomize`, and the three resolvers from the surface syntax to `ATm`.
Resolution is total on scoped, well labelled programs, which is proved here,
and it is structural, so the ten example programs of `Examples.lean` are
checked against hand written terms by `rfl` at the end of the module.  Let
insertion has no semantic statement attached: a direct style calculus and its
type preservation theorem would be a separate development, not covered here.

`Decide.lean` holds the side conditions the typer discharges by computation.
`DotMNF.Ty.Decl` is already decided in the frozen tree, so three more are
added here.  Well-formedness of a type and distinctness of the labels of a
definition block are decision procedures, each with an `iff` and a
`Decidable` instance.  Strengthening, the inverse of `DotMNF.Ty.weaken`, is
the action of the target's own partial renaming, reused verbatim from
`lean/Coercions/FCdot/Checker.lean`, over a new traversal of `DotMNF.Ty`.  The
module also holds the variables of a context, which the subtyping search
walks.  Everything here is structural and reduces in the kernel.

`Search.lean` holds views of a context variable, the declaration table of a
context, and the subtyping search.  A view and a declaration each carry the
derivation that justifies them, so the search returns evidence rather than an
answer and has no separate soundness theorem to prove.  Four counters live in
`Budget`: two for the rounds of the two closures, one for the fuel of the
search, and one for the typer.  The closures drop duplicates after every
round, by type for views and by the four data fields for declarations, and
two monotonicity theorems say that more rounds lose neither.  The search
tries eleven rules in a fixed order, the last three of them the type
selections and one family of transitivity middles, and then retries itself at
the previous fuel, which is what makes fuel monotonicity an induction rather
than a walk through the eleven rules.
The search is well-founded, so unlike everything before it in this library it
does not reduce in the kernel: its six probes run compiled code through
`expect` at measured budgets.

`Typer.lean` holds the typer that replaces the hand assembly of
`lean/Coercions/DotMNF/Examples.lean`.  Four mutually recursive functions
synthesize a type for a term, check a term against a type, check a variable
against a type, and check a definition list against a type in lockstep.  Each
returns the `DotMNF` derivation, so soundness is the result type and there is
no separate soundness theorem; incompleteness is necessary, since DOT
subtyping is undecidable, and what the typer will not find is written out as
a list in the module and not as a theorem.  The `let` rule is where a typer
for a dependently typed language makes its one ad hoc choice, made by a
ladder of three rungs: the surface annotation, the strengthening of the
body's type, and `⊤`.  The typer uses well-founded recursion on the fuel, the
size of the term and a tag, and it ends its fuel level with a retry that
makes fuel monotonicity an induction.  Its eight checks run `synthTop?` on
eight example surface programs and compare the result against the type the
hand written derivation concludes, in compiled code, at a budget measured per
example.

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
fuel, which is the honest statement and is witnessed by the fuel the
derivation used.  Ten concrete states probe the ten rules.  Nine of them, and
the stuck and the final shapes, reduce in the kernel by `rfl`.  The one that
reaches its head form through the composition of forms needs the kernel's own
transparency, because the frozen composition is defined by well-founded
recursion.

`Pipeline.lean` puts the front end together end to end.  `compile` resolves a
surface program and types it, and returns the annotated term beside the
synthesized type and its derivation.  `compileAndRun` follows with the source
machine at a step budget.  Five theorems say what a compiled program is
worth, and not one of them is about the calculus: the target checker accepts
the translation of the derivation, the translation erases to the source
term, every reachable state is final or steps, no reachable state is stuck,
and the driver never answers at a state the machine is stuck at.  The first
four are the frozen results of
`lean/Coercions/FCdot/CheckerCompleteness.lean` and
`lean/Coercions/DotToFCdot/` applied to the derivation the typer returned.
The fifth adds the step function's agreement with the step relation, proved
in `Step.lean`, which is what makes safety executable.

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

`Examples.lean` takes the ten surface programs of `Resolve.lean` through the
whole front end and compares them against the hand written derivations of
`lean/Coercions/DotMNF/Examples.lean`.  Three things are compared, all of
them decidable: the term the resolver returns, the type the typer
synthesizes, and the verdict of the target checker on the translation of the
derivation.  Derivations themselves are not, since `DotMNF.HasTy` is `Type`
valued with no decidable equality, and the typer reaches the same judgment by
another route in three places.  Each program carries four checks, one
decided by the kernel, two run as compiled code through `expect` at a budget
measured per program, and one the pipeline theorem at that program.  Two
further programs are the file's own.  E10t is E10 at a function type, which
is what carries an inserted binding through the typer and the checker, and
E11 is E10t applied to the identity, which is what carries one through the
machine.  The file closes with three runs of `compileAndRun`, printed by the
unparser and pinned at the step count each needs.
-/
