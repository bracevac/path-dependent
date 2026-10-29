# The pdot corpus against scalac

Written by `lake env lean --run scripts/scala/Agree.lean pdot scala/pdot`.  Do not edit it by hand.
CI runs the same command and fails when the file it writes differs from this one.

- scalac 3.8.4, default flags, 120 s per run.
- Files: 78.  pos 33, neg 15, disagree 8, outside 22.
- Classes (plan S-21): agree-accept 33, ours-stricter 5, ours-looser 3, agree-reject 15, refuse-differently 0, agree-giveup 0, broken 0, outside 22.
- Fills of the pos files (F): 32.  agree-accept 25, ours-stricter 5, agree-reject 2.  19 have a cause of plan XI XS3.  F-L: the fill drops every written self type, so a lambda field prints with no declared type.  F-W: a `let` the elaborator inserted prints as a `val` with no written type, which scalac widens.  F admits a fill of another class than agree-accept only with a cause, and its row names it.
- Round trips (R): 57 files the reader takes, same 57.  28 example programs, same 1, gap 25, differs 2.

## Files

| file | folder | scalac | warnings | ours | ours in Scala | class | cause or rule | fill | round trip |
|---|---|---|---|---|---|---|---|---|---|
| AliasObj | pos | ok |  | ok : ∀(x : ⊥) ⊤ | Nothing => Any | agree-accept |  | agree-accept | same |
| AliasSngl | pos | ok |  | ok : ∀(x : {B : ⊥..⊤}) ∀(y : x.B) x.B | (x0: { type B }) => x0.B => x0.B | agree-accept |  | agree-accept | same |
| BlockAliasSngl | pos | ok |  | ok : ∀(x : ⊥) ⊤ | Nothing => Any | agree-accept |  | agree-accept | same |
| Chain | pos | ok |  | ok : ⊤ | Any | agree-accept |  | ours-stricter (F-L, F-W): scalac ok, ours rejected: Type mismatch | same |
| Curried | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| DefInfer | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| DepDomain | pos | ok |  | ok : {types : {T : ⊥..⊤}} | { val types: { type T } } | agree-accept |  | agree-accept | same |
| E3m | pos | ok |  | ok : ⊤ ∧ {symb : {tpe : ⊤}} | Any & { val symb: { val tpe: Any } } | agree-accept |  | ours-stricter (F-L): scalac ok, ours rejected: recursive value types needs type (scalac E044) | same |
| E5Obj | pos | ok |  | ok : ⊤ | Any | agree-accept |  | ours-stricter (F-L): scalac ok, ours rejected: Type mismatch | same |
| E5m | pos | ok | no code at 6, no code at 7 | ok : ⊤ | Any | agree-accept |  | ours-stricter (F-L, F-W): scalac ok, ours rejected: the candidates of d have no least type | same |
| E7Obj | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| E8Obj | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| Fig1 | pos | ok |  | ok : ∀(x : ⊤ ∧ {symb : {tpe : ⊤}}) ⊤ | Any & { val symb: { val tpe: Any } } => Any | agree-accept |  | agree-accept | same |
| KeepNestedObj | pos | ok |  | ok : ∀(x : ⊥) ⊤ | Nothing => Any | agree-accept |  | agree-accept | same |
| LamExpected | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| LamResultModule | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| ModAlias | pos | ok |  | ok : ∀(x : {tpe : {Name : ⊥..⊤}}) ∀(y : {Name : ⊥..⊤}) ∀(z : y.type) ∀(w : z.Name) y.Name | { val tpe: { type Name } } => (x1: { type Name }) => (x2: x1.type) => x2.Name => x1.Name | agree-accept |  | agree-accept | same |
| NestedBare | pos | ok |  | ok : ∀(x : μ(x. {A : ⊥..⊤} ∧ {x : {y : x.A}})) x.A | (x0: { type A; val x: { val y: A } }) => x0.A | agree-accept |  | agree-accept | same |
| ObjAgainstAlias | pos | ok |  | ok : {a : {B : ⊥..⊤}} | { val a: { type B } } | agree-accept |  | agree-accept | same |
| ObjAsVal | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| ObjForward | pos | ok |  | ok : ∀(x : {v : ⊤}) ⊤ | { val v: Any } => Any | agree-accept |  | agree-accept | same |
| ObjInLit | pos | ok |  | ok : {a : {A : ⊥..⊤}} | { val a: { type A } } | agree-accept |  | agree-accept | same |
| ObjSibling | pos | ok |  | ok : ∀(x : {tpe : ⊤}) ⊤ | { val tpe: Any } => Any | agree-accept |  | agree-accept | same |
| R7Direct | pos | ok |  | ok : ∀(x : μ(x. {B : ⊥..⊤} ∧ {b : x.B})) ∀(y : {a : x.type}) ∀(z : ∀(z : y.a.B) ⊤) ⊤ | (x0: { type B; val b: B }) => (x1: { val a: x0.type }) => (x1.a.B => Any) => Any | agree-accept |  | ours-stricter (F-W): scalac ok, ours rejected: Type mismatch | same |
| Recursion | pos | ok | no code at 6 | ok : ⊤ | Any | agree-accept |  | agree-reject (F-L): scalac error: E045 at 5, ours rejected: recursive value go needs type (scalac E044) | same |
| RefValSngl | pos | ok |  | ok : ∀(x : {B : ⊥..⊤}) ∀(y : {a : x.type}) ∀(z : y.a.B) x.B | (x0: { type B }) => (x1: { val a: x0.type }) => x1.a.B => x0.B | agree-accept |  | agree-accept | same |
| ReplPQ | pos | ok |  | ok : ∀(x : {B : ⊥..⊤}) ∀(y : x.type) ∀(z : y.B) x.B | (x0: { type B }) => (x1: x0.type) => x1.B => x0.B | agree-accept |  | agree-accept | same |
| ReplPrefix | pos | ok |  | ok : ⊤ | Any | agree-accept |  | no fill: reader: scalac 3.8.4 crashes in the pickler on this shape (orphan parameter reference) | same |
| ReplQP | pos | ok |  | ok : ∀(x : {B : ⊥..⊤}) ∀(y : x.type) ∀(z : x.B) y.B | (x0: { type B }) => (x1: x0.type) => x0.B => x1.B | agree-accept |  | agree-accept | same |
| ThisBody | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| ThisVal | pos | ok |  | ok : ⊤ | Any | agree-accept |  | agree-accept | same |
| UnstableSngl | pos | ok |  | ok : ∀(x : μ(x. {a : {A : ⊥..⊤}} ∧ {g : ∀(y : x.a.type) ⊤})) ∀(y : x.type) ⊤ | (x0: { val a: { type A }; val g: a.type => Any }) => x0.type => Any | agree-accept |  | agree-reject (F-W): scalac error: E007 at 15, ours rejected: Type mismatch | same |
| ViewThroughAnd | pos | ok |  | ok : ∀(x : μ(x. {C : {incr : ⊤}..{incr : ⊤}} ∧ {D : x.C ∧ {decr : ⊤}..x.C ∧ {decr : ⊤}})) ∀(y : x.D) ⊤ | (x0: { type C = { val incr: Any }; type D = C & { val decr: Any } }) => x0.D => Any | agree-accept |  | agree-accept | same |
| AliasWiden | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| AliasWrongTarget | neg | error: E007 at 17 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| BareInRefine | neg | error: E007 at 10 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| KeepLitSelf | neg | error: E007 at 10 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| LamNoType | neg | error: E081 at 7 |  | rejected: missing parameter type (scalac E081) |  | agree-reject |  |  | same |
| N1Lam | neg | error: E007 at 7 |  | rejected: the field b holds a lambda at a type that is no function type |  | agree-reject |  |  | same |
| NestedBareInner | neg | error: E007 at 6 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| ObjWrongPath | neg | error: E007 at 12 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| ParamAlias | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| R7Let | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| RecNoType | neg | error: E044 at 7 |  | rejected: recursive value go needs type (scalac E044) |  | agree-reject |  |  | same |
| SnglInfer | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| TreeMix | neg | error: E007 at 7 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| UnstableArg | neg | error: E007 at 7 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| WidenChain | neg | error: E007 at 8 |  | rejected: Type mismatch |  | agree-reject |  |  | same |
| DefThisInfer | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | an inferred def result of this is widened in the elaborator rounds, where the object binder is a fresh variable and not a module path, so core.me(core) has no type at core.type (ours-stricter) |  | same |
| DepCo | disagree | error: E007 at 10 |  | ok : ∀(x : ∀(x : {A : ⊥..⊤}) x.A) ∀(y : {A : ⊥..⊤} ∧ {a : ⊤}) y.A | ((x0: { type A }) => x0.A) => (x1: { type A; val a: Any }) => x1.A | ours-looser | scalac compares the domain of a dependent function type by equality, pDOT contravariantly (subtyp_all, vanilla DepCo) |  | same |
| Mid | disagree | error: E007 at 8 |  | ok : ∀(x : {A : {a : ⊤}..{b : ⊤}}) ∀(y : {a : ⊤}) ∀(z : (∀(z : ∀(z : ⊤) x.A) ⊤) ∧ (∀(z : ∀(z : ⊤) {b : ⊤}) ⊤)) ⊤ | (x0: { type A >: { val a: Any } <: { val b: Any } }) => { val a: Any } => ((Any => x0.A) => Any) & ((Any => { val b: Any }) => Any) => Any | ours-looser | the vanilla cause: scalac checks the argument against one function type of the intersection, DOT against the other (Gaps, d2 Mid) |  | same |
| ReflSngl | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | pDOT has no rule x : x.type, here through def id(x: Any): x.type = x (pDOT N4) |  | same |
| SnglInFn | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | pDOT subtyping widens no singleton, so Any => q.type is no subtype of Any => { type B } |  | same |
| SnglRefl | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | pDOT has no rule x : x.type, so a parameter is not at its own singleton (pDOT N4) |  | same |
| TS | disagree | ok |  | rejected: Type mismatch |  | ours-stricter | q : p.type needs q : q.type first (pDOT N4), scalac relates p.type and q.type both ways |  | same |
| X3 | disagree | error: E007 at 10 |  | ok : ∀(x : {A : ∀(x : {a : ⊤}) {a : ⊤}..⊤}) (∀(y : {a : ⊤}) ⊤) ∧ x.A | (x0: { type A >: { val a: Any } => { val a: Any } }) => ({ val a: Any } => Any) & x0.A | ours-looser | the vanilla cause: scalac types the closure at the function part of the expected type, DOT at the lower bound of y.A (Gaps, d2 X3) |  | same |
| CycFn | outside | error: E140 at 8 |  | outside 8:10: illegal cyclic type reference: the alias of `T` refers back to `T` (scalac E140) |  | outside | R-Y, illegal cyclic type reference (scalac E140) |  |  |
| CycObj1 | outside | error: E140 at 8 |  | outside 8:10: illegal cyclic type reference: the alias of `T` refers back to `T` (scalac E140) |  | outside | R-Y, illegal cyclic type reference (scalac E140) |  |  |
| DefArity3 | outside | error: E007 at 7 |  | outside 7:23: a def takes one parameter per list, and a refinement declares no def |  | outside | R-P, a def takes one parameter per list, and a refinement declares no def |  |  |
| DefSnglParam | outside | error: E007 at 10 |  | outside 9:16: a def takes one parameter per list, and a refinement declares no def |  | outside | R-P, a def takes one parameter per list, and a refinement declares no def |  |  |
| E13s | outside | error: E046 at 8 |  | outside 8:9: cyclic reference involving val a (scalac E046) |  | outside | R-C, cyclic reference involving val a (scalac E046) |  |  |
| E2m | outside | error: E140 at 8 |  | outside 8:21: illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140) |  | outside | R-Y, illegal cyclic type reference (scalac E140) |  |  |
| KeepNestedLit | outside | error: E007 at 14 |  | outside 8:9: a member that holds an object literal is a nested `object` |  | outside | R-L, a member that holds an object literal is a nested `object` |  |  |
| N3s | outside | error: E008 at 8, E008 at 8 |  | outside 8:14: value zz is not a member of the object literal (scalac E008) |  | outside | R-M, zz is not a member of the type of x (scalac E008) |  |  |
| ObjAbstract | outside | ok |  | outside 8:10: a type member of an object is an alias in pDOT |  | outside | R-A, a type member of an object is an alias in pDOT |  |  |
| ObjArgVal | outside | error: E007 at 9 |  | outside 8:26: a name is a method everywhere or a value everywhere |  | outside | R-D, a name is a method everywhere or a value everywhere |  |  |
| ObjInBlock | outside | ok |  | outside 8:5: an object is a member of the wrapper, an object or a literal |  | outside | R-O, an object is a member of the wrapper, an object or a literal |  |  |
| ObjPathFieldWiden | outside | error: E007 at 11 |  | outside 9:9: a field that holds a path is an alias in pDOT: write `val a: p.type = p` |  | outside | R-V, a field that holds a path is an alias in pDOT: write `val a: p.type = p` |  |  |
| ObjUndeclared | outside | error: E008 at 12 |  | outside 12:25: type B is not a member of the type of o.a (scalac E008) |  | outside | R-M, type B is not a member of the type of o.a (scalac E008) |  | same |
| ObjVal | outside | error: E007 at 10 |  | outside 8:9: a member that holds an object literal is a nested `object` |  | outside | R-L, a member that holds an object literal is a nested `object` |  |  |
| PaperXaB | outside | error: E008 at 13 |  | outside 8:13: an object literal needs a written type: scalac types it as Object |  | outside | plan IX rule 10, an object literal stands under a written type (S-12) |  |  |
| Paramless | outside | ok |  | outside 8:9: a def takes one parameter per list, and a refinement declares no def |  | outside | R-P, a def takes one parameter per list, and a refinement declares no def |  |  |
| RefValUnstable | outside | error: E083 at 7 |  | outside 7:53: `p.a` is not a valid type prefix, since it is not an immutable path (scalac E083) |  | outside | R-S, `p.a` is not a valid type prefix, since it is not an immutable path (scalac E083) |  |  |
| Tree | outside | ok |  | outside 7:3: classes and traits are outside the subset |  | outside | R-T, traits, classes and `extends` are outside the subset (plan IX's message) |  |  |
| UnstableAlias | outside | error: E083 at 8 |  | outside 8:22: `x.a` is not a valid type prefix, since it is not an immutable path (scalac E083) |  | outside | R-S, `x.a` is not a valid type prefix, since it is not an immutable path (scalac E083) |  |  |
| UnstableSnglMember | outside | error: E083 at 7 |  | outside 7:97: `q.b` is not a valid type prefix, since it is not an immutable path (scalac E083) |  | outside | R-S, `q.b` is not a valid type prefix, since it is not an immutable path (scalac E083) |  |  |
| ValCycle | outside | error: E046 at 9 |  | outside 8:9: cyclic reference involving val a (scalac E046) |  | outside | R-C, cyclic reference involving val a (scalac E046) |  |  |
| WrapperVal | outside | ok |  | outside 8:7: a field holds a path or a value in pDOT: move the computation into `program` |  | outside | R-R, a field holds a path or a value in pDOT: move the computation into `program` |  |  |

## Example programs

- gap, an object literal needs a written type: scalac types it as Object (plan IX S-12) (22): E1, E2, E3, E4, E5, E6, E7, E8, E13, N1, N2, N3, E1I, E2I, E3I, E4I, E5I, E6I, E7I, E8I, E13I, E7w
- differs: an application that is a lambda body reads back with the widening bind of D-13 (1): R2
- same (1): PQ
- gap, reader: `x.a` is not a valid type prefix, since it is not an immutable path (scalac E083) (1): R7
- gap, reader: `x.b` is not a valid type prefix, since it is not an immutable path (scalac E083) (1): E9l
- gap, `let x : U = t in u` with `u` not `x` has no Scala form (plan IX S-11) (1): E10
- differs: a μ whose binder does not occur prints as its body (plan IX S-15) (1): E11
