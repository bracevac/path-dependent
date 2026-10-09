# Paths

Scala selects types through paths of any length, as in `global.typer.Type` or
`pcore.types.TypeRef`. WadlerFest DOT allows only a variable before a type selection, so it cannot
type the module structure of a real program. This development adds the paths `x.a.b`, stable `val`
fields and singleton types `p.type` of pDOT (Rapoport and Lhoták, OOPSLA 2019) to DOT-MNF, DOT in
monadic normal form. It translates them into FCdot, where every use of a path is explicit evidence
that erases. Source type safety still follows from the target's, and the source passes the two
acceptance tests of gDOT (Giarrusso et al., ICFP 2020).

## What is proved

- `HasTy.translate_typed`: every source typing derivation in a well-formed context (`Ctx.Wf`), in
  particular every closed one, translates to a typed FCdot term.
- `PathTy.translatePath_typed`: every path typing in a well-formed context translates to path
  evidence at the same path.
- `HasTy.translate_erase`: the image erases to the source term, so behaviour is unchanged.
- `dot_safety`: a closed well-typed source program never gets stuck.
- `reachable_consistent`: every store a closed translated program reaches is typed, with no closed
  `⊤ ≤ ⊥`.
- `Store.Typed.pathView`: over a typed store, every typed path has a view of its object, typed at
  every object type that the path's type resolves to.
- `acceptance_fig2`: a copy of gDOT's Fig. 2 with four changes (listed in `DotMNF/Examples.lean`),
  typed at `⊤`, translates to a term the checker accepts.
- `acceptance_gdot3_any`: in the empty context, no object literal has gDOT's bad-bounds type
  `μ(x. {A : ⊤..⊥})`.

## What it leaves out

- A `val` field must hold an object literal. A field holding a variable or a lambda is a plain
  field, and its declared type has no stable member. So `Fld-E` cannot step through it from the
  receiver. A binder assumed at the singleton of such a field can still make it a path, through the
  singleton rules.
- No replacement of a path by its alias: `p.type <: q.type` is not derivable, nor `p.A <: q.A`
  at an abstract member.
- A variable of singleton type cannot be used at a non-singleton type of its alias.
- A `let` binds at a singleton only when the field is declared at a singleton.
- No union types, no later modality, and none of pDOT's precise or invertible typing.
- The body of a recursive type must be a declaration type.

The first four restrictions have one reason: the target has no evidence for the lost forms. The
directory READMEs give the details.

## Layout

`DotMNF/` is the source calculus. Paths appear in types only, and terms stay in monadic normal
form, so the machine and the erasure are those of the base. Path typing is a judgment of its own,
`PathTy`, with pDOT's singleton rules. The examples include the example of Sec. 2.2 of the pDOT
paper and the source of gDOT's Fig. 2.

`FCdot/` is the target. The binder of an object literal carries a forest of blocks, one node per
stable field, and an alias is a forwarding node. Path evidence types a path at the precise type of
its node. The checker, preservation, progress and canonical forms keep the base's statements.

`DotToFCdot/` is the translation, its typedness and erasure theorems, the safety and consistency
corollaries, and the two gDOT acceptance tests. Every translation function is structurally
recursive, so the kernel evaluates translations and the examples are decided by `decide +kernel`.

`Runtime.lean` is the untyped runtime both calculi erase into, unchanged from the base.

## Building

`lake build Paths` builds the namespace `Paths`, and `Paths` is a default target. Every theorem
depends on `propext` and `Quot.sound` at most, with no `sorry`, `axiom` or `native_decide`.

The tree is a copy of the vanilla line (`DotMNF`, `FCdot`, `DotToFCdot`, `Runtime.lean`) at the
commit recorded in `BASE`, and it keeps every theorem of that base. Later changes to the vanilla
line are not carried over.
