import Coercions.Frontend.Surface
import Coercions.Frontend.Notation
import Coercions.Frontend.Ann
import Coercions.Frontend.Resolve

/-!
# The vanilla front end

The root of the `Frontend` library (plan-5e-frontend-stages.md).  It imports the
modules of `lean/Coercions/Frontend/` as the stages add them and changes nothing
in the frozen trees it consumes.

`Surface.lean` is stage F0.1: the named abstract syntax the elaborator produces,
the label table that interns surface names as target labels, the scoping and
labelling predicates under which resolution is total, and the `expect` helper
that F1's tests use in place of `by decide`.

`Notation.lean` is stages F0.2 and F0.3: the three syntax categories `dotTy`,
`dotTm` and `dotDefs` that hold the paper's notation, and the three term level
entry points `dotTy%`, `dot%` and `dotDefs%` whose macros expand a piece of that
notation into a surface value.  One departure from the paper, a type member
definition is written `{type A = T}`, and one measured fact, a dotted surface
name is a single token that the macro takes apart.  Importing this module makes
the bare word `type` a keyword, so no later module uses it as an identifier.

`Ann.lean` is stage F0.4: `ATm` and `ADefs`, the terms of DOT-MNF with the two
annotations a front end needs, the self type of an object literal and the
optional result type of a `let`.  Their erasure to `DotMNF.Tm` and `DotMNF.Defs`
drops exactly those two fields.  The module also carries the renaming, the
lemma that erasure commutes with it, and the size measure F1's typer recurses
on.

`Resolve.lean` is stages F0.5 to F0.7: name environments, the spine of inserted
bindings, `atomize`, and the three resolvers from the surface syntax to `ATm`.
Resolution is total on scoped well labelled programs, which is proved here, and
it is structural, so the ten example programs of the plan's F3.3 are checked
against hand written terms by `rfl` at the end of the module.  Let insertion has
no semantic statement attached: the direct style calculus and its type
preservation theorem are a separate development, parked by `plan-5-extensions.md`
§7.
-/
