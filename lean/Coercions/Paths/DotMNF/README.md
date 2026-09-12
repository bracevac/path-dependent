# DotMNF, at stage P0 of paths

WadlerFest DOT in monadic normal form, the source of the translation in `../DotToFCdot`.

**P0 is the stage that gives the source paths** (`plan-5g-paths-stages.md` §P0).  A path is a
variable followed by field selections, paths live in types, and term position stays in monadic
normal form: `Tm.path` carries a variable, and a deep path in term position is written with a `let`.
That is decision 2, and it is Fact 1 of the plan: a deep path is never a running term, so the
machine and the erasure keep their statements word for word.  Path typing becomes a judgment of its
own, `PathTy`, and the four rules that used to be stated on variables inside term typing move there.
Eliminating at a path asks for a stable member, which is Fact 2's answer and what replaces pDOT's
`tight_bounds`.  The declared type of a literal is exact on type members (T9) and on stable fields
(T10), and the abstract view of a declaration is `SubDecl`, reached by `Typ-Abs`.

| module | contents |
|---|---|
| `Syntax` | paths with `root`, `depth`, `substVar`, `substPath` and the parallel `PathSubst`; types (`⊤ ⊥ {A:S..T} {a:T} {val a:T} p.type p.A μ ∀ ∧`) with `substPath`; the three declaration readers `lookupTypDecl`, `lookupFldDecl`, `lookupVfldDecl`; terms, values, definitions; `Decl` and its decision procedure `isDecl`, `Wf`, `Distinct` |
| `Typing` | contexts (`cons`, `consSelf`); `Sub`, `PathTy`, `HasTy`, `DefsTy`, `SelfFree` and `SubDecl` as one mutual block (Type-valued); `HasTy.path` the bridge and `HasTy.toPathTy` its inverse; `Ty.ReplOne` with its decision procedure; the two exactness theorems `DefsTy.typ_exact` and `DefsTy.vfld_exact`; intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise); `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`, `Sub.mu`); `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Erasure` | erasure to `Runtime`; `erase_step`, `erase_reflect`.  `final_erase` and `final_reflect` are named by T11 as well and live in `../DotToFCdot/Safety.lean`, not here |
| `Examples` | E1 to E8 as `HasTy` derivations, unchanged; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation.  X1 to X4 are the path pages, below |

## What P0 changed

| where | what P0 changed |
|---|---|
| paths | `Path.sel`, so a path is a variable followed by field selections.  `Path.root` recurses, `Path.depth` counts the field steps, `Path.substPath` replaces the root and keeps the suffix, and `Path.replPrefix` rewrites a prefix.  `PathSubst` is the parallel substitution, the shape of `Rename` with paths in place of variables, and `Ty.substPath T q` is `T.subst (PathSubst.one q)`, which reads as `Path.substPath` at every binder-free shape and lifts under a binder |
| types | `Ty.vfld`, the stable field declaration `{val a : T}`; `Ty.sngl`, the singleton `p.type`; and `Ty.sel` on a path, so `p.A` is a type at any path.  The three declaration readers descend an intersection with the right conjunct winning, which is the convention of `Defs.lookupTyp` |
| terms | `Tm.path` carries a `BVar`, not a `Path`.  Fact 1: the erasure of a term is a runtime term, a runtime projection takes a variable, and a deep path in term position would make `erase_reflect` false |
| judgments | `PathTy` as a fourth member of the mutual block, with `HasTy.path` the one bridge rule; `Sub.vfld`, `Sub.vfldToFld`, `Sub.repl`, `Sub.replSym` and `Sub.mu`; `SelfFree` and `SubDecl`, the abstract view; `DefsTy.trmObj`, `trmLam` and `trmSngl`, the three stable fields; `HasTy.letSngl`, the `let` over a stable path |
| machine, erasure | nothing, except that the two `.path (.var x)` patterns read `.path x` |

## `PathTy`

pDOT's `Γ ⊢ p : T` for the fragment plan V §4 keeps.  Eleven rules, `Type`-valued like the other
three judgments, in the same mutual block.

```
var       : PathTy Γ (.var x) (Γ.lookup x)
sel       : PathTy Γ p (.vfld a T) → PathTy Γ (.sel p a) T
recI      : PathTy Γ p (T.substPath p) → Ty.Decl T → PathTy Γ p (.mu T)
recE      : PathTy Γ p (.mu T) → Ty.Decl T → PathTy Γ p (T.substPath p)
andI      : PathTy Γ p T → PathTy Γ p U → PathTy Γ p (.and T U)
sub       : PathTy Γ p T → Sub Γ T U → PathTy Γ p U
snglRefl  : PathTy Γ p T → PathTy Γ p (.sngl p)
snglTrans : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ p T
snglSym   : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ q (.sngl p)
snglInv   : PathTy Γ p (.sngl q) → PathTy Γ q .top
snglSel   : PathTy Γ p (.sngl q) → PathTy Γ p (.vfld a T) →
              PathTy Γ (.sel p a) (.sngl (.sel q a))
```

`sel` is the rule Fact 2 shapes.  It reads a *stable* member, `{val a : T}`, and a stable member is
one whose definition is an object literal, a lambda or a variable (T10).  A computation member is
not a prefix, which is X2.  Term typing reaches all of this through the one bridge rule
`HasTy.path`, and `HasTy.toPathTy` reads the bridge backwards: only `path` and `sub` conclude at a
`.path` term.  The base's `T-Var`, `Rec-I`, `Rec-E` and `And-I` are restated after the block as
`HasTy.var`, `HasTy.recI`, `HasTy.recE` and `HasTy.andI`, with the base's premises and no premise
added.

`snglSym` is stated and not derived: the four-rule derivation gDOT gives needs `Sngl-<:-Self`, which
this line does not have.

## Theorems

`DefsTy.typ_exact` (T9) says the declared type of a literal is exact on type members: `{}-I` never
introduces an abstract member, so no derivation inside a literal uses an abstract bound of its own
self.  It is the statement that replaces pDOT's `tight_bounds`.

`DefsTy.vfld_exact` (T10) reads the three shapes a stable field can have off the declared type: an
object literal with its own declared type, a singleton, or a lambda.  It carries the premise
`Defs.Distinct d`, which the table below explains.

`HasTy.toPathTy` is the reflection lemma that makes the four base rules derivable exactly where they
were.  `erase_step` and `erase_reflect` keep their statements (T11), as does every lemma of
`Machine`.

`#print axioms` of every theorem named here, and of X1 to X4, is inside `[propext, Quot.sound]`.

## Statements whose form changed

The table of P0.9, with the sentence that says why each restatement has the meaning it had.  No
statement of the copied base gained a hypothesis.

| statement | change | why the meaning is the same |
|---|---|---|
| `Tm.path` | the argument is a `BVar`, not a `Path` | the base's `Path` has the single constructor `var`, so the two sets of terms are in bijection, and `.path (.var x)` reads `.path x` throughout |
| `Path.root` | recursive | on a `.var` path it is the base's identity clause, and no other clause exists on the copy |
| `Path.root_rename` | statement kept, the proof becomes an induction | `Path` is recursive now, so `cases p <;> rfl` no longer closes it |
| `HasTy.var`, `recI`, `recE`, `andI` | they move to `PathTy` and reach `HasTy` through the bridge rule `HasTy.path` | `HasTy.toPathTy` makes each composite derivable exactly where the base's rule was, with the same premises and no premise added.  At a variable path `Ty.substPath_var` turns `T.substPath (.var x)` into the base's `T.substVar x` |
| `Sub.selUpper`, `selLower` | the premise is `PathTy Γ p _` for a general path | at `p = .var x` the premise is the base's premise through `HasTy.toPathTy`, so every base derivation is a derivation |
| `Ty` | three constructors, `vfld`, `sngl`, and `sel` taking a path | additive, and `.sel (.var x) A` is the base's type selection, so every base type is a type |
| `Ty.Decl`, `Ty.isDecl`, `Ty.isDecl_iff`, `Ty.Wf` | two clauses each | additive, and no base shape changes its verdict |
| `DefsTy` | three constructors, `trmObj`, `trmLam` and `trmSngl` | additive, `DefsTy.trm` still types a value field at `{a : T}`, so every base derivation stands, and the new rules give a stronger type to the same definition |
| `HasTy.let` | nothing, and `letSngl` is stated beside it | additive: a `let` over a projection may still bind opaquely |
| `Path.substVar` | nothing, and `substPath` is stated beside it, with `substPath_var` the bridge | `Ty.substVar` and `Path.substVar` stay renamings, which is what `RenameLemmas` is stated over |
| `erase_step`, `erase_reflect`, `final_erase`, `final_reflect` | nothing, except that the two `.path (.var x)` patterns read `.path x` | decision 2: the constructor's argument changed, the case analysis did not.  `Tm.erase (.path x) = .var x`, where the base wrote `.var p.root` and the base's `root` on a `var` path is the identity |
| `DefsTy.vfld_exact` (T10, new) | the premise `Defs.Distinct d`, and `Defs.lookupTrm` for the plan's `d.get?` | a new theorem of this stage, not a base statement, and false without the premise: `DefsTy` puts no condition on the labels of an intersection, so `{a = ν(t. {A = ⊤})} ∧ {a = z}` types at `{val a : μ(t. {A : ⊤..⊤})} ∧ {a : ⊤}`, where the reader of the type and the reader of the definitions answer about two different definitions.  That is decision 21, and every use has the premise to hand: `HasTy.obj` carries it for the literal and `DefsTy.trmObj` for the nested one |
| `E1src`, `E3src`, `E4src` of `../FCdot/Examples.lean` | five occurrences of `.path (.var .here)` read `.path .here` | the first row of this table, in the one target file that writes source terms of its own, so that `Coercions.Paths.FCdot` builds at the end of P0 |

## The examples

E1 to E8 are the regression, and the extension weakens nothing: each keeps its name, its statement
and its derivation, repaired only as far as the two rows above force, `.path (.var x)` reading
`.path x` and a `PathTy` premise for `Sub.selUpper` and `Sub.selLower` through `HasTy.toPathTy`.
Four pages are added.

**X1, pDOT Sec. 2.2.**  `ν(z. {val c = ν(w. {A = z.B})} ∧ {B = z.c.A})`, the shape the pDOT paper
names as the one WadlerFest DOT cannot write.  The field `c` is stable by `DefsTy.trmObj`, so
`Fld-E` reads a member at the path `x.c` of length two, and the two selections `x.c.A` and `x.B` are
then below one another by two independent routes.  The `Ty.Decl` premises of the two `Rec-E` steps
are by `decide`.

**X2, E10.**  `ν(x. {a = x.a})`, the literal Fact 2 machine checks, typed by `DefsTy.trm` at
`μ(x. {a : {A : ⊤..⊥}})`.  The refutation is by inversion, twice.  `X2_defsShape` inverts definition
typing: the three stable rules ask for an object literal, a lambda or a variable body, the body is a
projection, so every derivation of these definitions types `a` as a computation member and
`Ty.lookupVfldDecl` answers `none`.  `X2_noSubDecl` inverts the abstract view, so `Typ-Abs` does not
manufacture a stable member at `a` either.  Left unproved is the unqualified sentence that no
`PathTy Γ x.a T` exists at all: its remaining cases go through `PathTy.sub` and `PathTy.snglInv`,
and refuting those is an inversion of `Sub`, which P0 does not have.

**X3, the two-hop program.**  `let y = x.a in y.b`, typed by `HasTy.letSngl`: the binder `y` is
bound at the singleton of the path it names, `Sngl-Trans` carries `x.a`'s stable member to `y`, and
`PathTy.sel` reads `y.b` under the singleton.  `X3_opaque` types the same term with the plain
`HasTy.let`, which stands beside `letSngl`.

**X4, gDOT Fig. 2.**  The `types` literal of the Dotty fragment, with the enclosing module `pcore` a
context binder, since nothing here eliminates a member of `pcore`.  `pcore.symbols.Symbol` is the
length-two selection, both lambda fields are stable by `DefsTy.trmLam`, and `newTypeRef` allocates
`ν(_. {symb = s})`, binds it with a `let` and lets it out at `types.TypeRef`.  T9 is then applied to
the literal's declared type, and the three type members are found by `decide` through
`Ty.lookupTypDecl`, each with equal bounds.  `X4_abs` and `X4_muAbs` are the other half: Fig. 2's
abstract reading, `TypeRef >: ⊥ <: …`, derived from the exact declaration by `Typ-Abs`, which is the
step pDOT's precise self types refuse.
