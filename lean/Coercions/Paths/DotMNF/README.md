# DotMNF, at stage P2 of paths

WadlerFest DOT in monadic normal form, the source of the translation in `../DotToFCdot`.

**P0 is the stage that gives the source paths** (`plan-5g-paths-stages.md` §P0).  A path is a
variable followed by field selections, paths live in types, and term position stays in monadic
normal form: `Tm.path` carries a variable, and a deep path in term position is written with a `let`.
That is decision 2, and it is Fact 1 of the plan: a deep path is never a running term, so the
machine and the erasure keep their statements word for word.  Path typing becomes a judgment of its
own, `PathTy`, which states the base's variable rules at a path and carries the singleton rules.
Eliminating at a path asks for a stable member, which is Fact 2's answer and what replaces pDOT's
`tight_bounds`.  The declared type of a literal is exact on type members (T9) and on stable fields
(T10), and the abstract view of a declaration is `SubDecl`, reached by `Typ-Abs`.

**P2 restricts four of P0's rules** (`plan-5g-paths-stages.md` §P2.0), so that every source
derivation has an image in the target of `../FCdot`.  Term typing keeps the base's variable rules,
and the bridge from path typing is at a singleton only.  The subtyping rules `repl` and `replSym` are
removed.
`letSngl`, `trmLam` and `trmSngl` are derived forms, and `trmObj` is the only rule that declares a
stable field.  Each restriction and what it loses is the section "What P2 restricted" below.

| module | contents |
|---|---|
| `Syntax` | paths with `root`, `depth`, `substVar`, `substPath` and the parallel `PathSubst`; types (`⊤ ⊥ {A:S..T} {a:T} {val a:T} p.type p.A μ ∀ ∧`) with `substPath`; the three declaration readers `lookupTypDecl`, `lookupFldDecl`, `lookupVfldDecl`; terms, values, definitions; `Decl` and its decision procedure `isDecl`, `Wf`, `Distinct` |
| `Typing` | contexts (`cons`, `consSelf`).  `Sub`, `PathTy`, `HasTy`, `DefsTy`, `SelfFree` and `SubDecl` as one mutual block (Type-valued).  `HasTy.sngl` the bridge at a singleton, `HasTy.projP` the projection from a path typing, and `HasTy.toPathTy` from term typing at a variable to path typing.  The derived forms `HasTy.letSngl`, `HasTy.letSnglVal`, `DefsTy.trmSngl` and `DefsTy.trmLam`.  `Ty.ReplOne` with its decision procedure, unused since P2.  The exactness theorems `DefsTy.typ_exact`, `DefsTy.vfld_exact` and `DefsTy.vfld_exact_obj`.  Intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise).  `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`, `Sub.mu`).  `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Erasure` | erasure to `Runtime`; `erase_step`, `erase_reflect`.  `final_erase` and `final_reflect` are named by T11 as well and live in `../DotToFCdot/Safety.lean`, not here |
| `Examples` | E1 to E8 as `HasTy` derivations, unchanged; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation.  X1 to X4 are the path pages, below |

## What P0 changed

| where | what P0 changed |
|---|---|
| paths | `Path.sel`, so a path is a variable followed by field selections.  `Path.root` recurses, `Path.depth` counts the field steps, `Path.substPath` replaces the root and keeps the suffix, and `Path.replPrefix` rewrites a prefix.  `PathSubst` is the parallel substitution, the shape of `Rename` with paths in place of variables, and `Ty.substPath T q` is `T.subst (PathSubst.one q)`, which reads as `Path.substPath` at every binder-free shape and lifts under a binder |
| types | `Ty.vfld`, the stable field declaration `{val a : T}`; `Ty.sngl`, the singleton `p.type`; and `Ty.sel` on a path, so `p.A` is a type at any path.  The three declaration readers descend an intersection with the right conjunct winning, which is the convention of `Defs.lookupTyp` |
| terms | `Tm.path` carries a `BVar`, not a `Path`.  Fact 1: the erasure of a term is a runtime term, a runtime projection takes a variable, and a deep path in term position would make `erase_reflect` false |
| judgments | `PathTy` as a fourth member of the mutual block, with the bridge rule `path` of `HasTy`.  `Sub.vfld`, `Sub.vfldToFld`, `repl`, `replSym` and `Sub.mu`.  `SelfFree` and `SubDecl`, the abstract view.  `DefsTy.trmObj`, `trmLam` and `trmSngl`, the three stable fields.  `HasTy.letSngl`, the `let` over a stable path.  P2 replaced the bridge and removed or derived five of these rules, as the next section says |
| machine, erasure | nothing, except that the two `.path (.var x)` patterns read `.path x` |

## What P2 restricted

Four rules of P0 have no image in the target of `../FCdot`, and P2 restricts each of them
(`plan-5g-paths-stages.md` §P2.0, decisions 23, 27, 28 and 29).  The machine, the erasure and
`PathTy` do not change.

**R1, the `let` at a singleton (decision 23).**  `HasTy.letSngl` is a derived `def` over
`HasTy.let` and `HasTy.projP`.  Its premise is `PathTy Γ (.var x) (.fld a (.sngl q))`, a field
declared at a singleton, and it binds `y` at `.sngl q`.  `HasTy.letSnglVal` is the instance at
`{val a : q.type}`, which after R2 only a binder's declared type can have.  Lost: a `let` over a
field that is not declared at a singleton, with the binder at the singleton of the field's path.
The same program still types with the opaque binder, as X3 does.

**R2, the stable fields (decision 27).**  `DefsTy.trmSngl` and `DefsTy.trmLam` are derived forms
at a plain field `{a : _}`, both by `DefsTy.trm`.  `trmObj` is the only rule that gives a literal a
`{val a : _}` member.  The target lists a stable label only when the field's body is an object
literal under table-only casts, so a variable or a lambda body has no stable image.  Lost:
`{val a = y}` at `{val a : y.type}`, `{val f = λ…}` at `{val f : ∀…}`, and every path typing at
`x.a` and below for such a field.  `PathTy.sel`, `snglSel` and `snglTrans` keep their text, and a
binder's declared `{val a : T}` still feeds them.

**R3, term typing at a variable (decision 28).**  P0's bridge `path` from every path typing at a
variable is gone.  `HasTy.var`, `recI`, `recE` and `andI` are constructors again with the base's
statements.  `HasTy.sngl` types a variable at a singleton from a path typing, and `HasTy.projP`
projects a field out of a receiver typed as a path, beside the base's `HasTy.proj`.  The image of a
term at a variable is an atom rooted there, and the target reads nothing but an alias out of a
singleton.  Lost: a variable of singleton type used as a term at a type of its alias that is not a
singleton, as a value, as an operand of an application, as the bound term of a `let`, or as the
body of a field.  Projection and the bounds of type members through such a variable are kept.

**R4, replacement (decision 29).**  The subtyping rules `repl` and `replSym` are removed.  The translation types
its images in an open context, where the target has no coercion between the types of two names
that a singleton relates.  `Ty.ReplOne` and its decision procedure stay, unused.  `p.A <: q.A` for
`p` aliased to `q` still holds when the member of `q` is exact, by `snglTrans`, `Sel-<:` and
`<:-Sel`, and a literal's members are exact (T9).  Lost: pDOT's `Sngl-<:` and `<:-Sngl`, that is
`p.type <: q.type`, and `p.A <: q.A` at an abstract member.

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

`sel` is the rule Fact 2 shapes.  It reads a *stable* member, `{val a : T}`.  In a literal a stable
member is one whose definition is an object literal, since after P2 `trmObj` is the only rule that
declares one (T10).  A binder's declared type may carry any stable member.  A computation member is
not a prefix, which is X2.  Term typing reaches path typing through two rules only, the bridge
`HasTy.sngl` at a singleton and the projection `HasTy.projP`.  `HasTy.toPathTy` goes the other way.
Every term typing at a variable is a path typing, with one case per rule that concludes at a
`.path` term.

`snglSym` is stated and not derived: the four-rule derivation gDOT gives needs `Sngl-<:-Self`, which
this line does not have.

## `HasTy` and `DefsTy`

Term typing has twelve rules after P2.

```
var    : HasTy Γ (.path x) (Γ.lookup x)
recI   : HasTy Γ (.path x) (T.substVar x) → Ty.Decl T → HasTy Γ (.path x) (.mu T)
recE   : HasTy Γ (.path x) (.mu T) → Ty.Decl T → HasTy Γ (.path x) (T.substVar x)
andI   : HasTy Γ (.path x) T → HasTy Γ (.path x) U → HasTy Γ (.path x) (.and T U)
sngl   : PathTy Γ (.var x) (.sngl q) → HasTy Γ (.path x) (.sngl q)
lam    : HasTy (Γ.cons S) t T → Ty.Wf S → HasTy Γ (.val (.lam S t)) (.all S T)
app    : HasTy Γ (.path x) (.all S T) → HasTy Γ (.path y) S → HasTy Γ (.app x y) (T.substVar y)
obj    : DefsTy (Γ.consSelf d T) d T → Defs.Distinct d → HasTy Γ (.val (.obj d)) (.mu T)
proj   : HasTy Γ (.path x) (.fld a T) → HasTy Γ (.proj x a) T
projP  : PathTy Γ (.var x) (.fld a T) → HasTy Γ (.proj x a) T
let    : HasTy Γ t T → HasTy (Γ.cons T) u U.weaken → Ty.Wf U → HasTy Γ (.let t u) U
sub    : HasTy Γ t T → Sub Γ T U → HasTy Γ t U
```

`var`, `recI`, `recE` and `andI` are the base's `T-Var`, `Rec-I`, `Rec-E` and `And-I`, statements
verbatim.  `sngl` is the bridge from path typing, at a singleton only.  `projP` is `{}-E` with the
receiver typed as a path, and it is to `proj` what `memberP` is to `member` in the target.
`proj` keeps the base's premise, so the base's projections keep their derivations.

Definition typing has four rules, `typ`, `trm`, `trmObj` and `and`.  After the mutual block stand
the derived forms `HasTy.letSngl`, `HasTy.letSnglVal`, `DefsTy.trmSngl` and `DefsTy.trmLam`, each
one line over the rules above.

## Theorems

`DefsTy.typ_exact` (T9) says the declared type of a literal is exact on type members: `{}-I` never
introduces an abstract member, so no derivation inside a literal uses an abstract bound of its own
self.  It is the statement that replaces pDOT's `tight_bounds`.

`DefsTy.vfld_exact` (T10) reads the three shapes a stable field could have at P0 off the declared
type: an object literal with its own declared type, a singleton, or a lambda.  It carries the
premise `Defs.Distinct d`, which the table below explains.  P2 keeps its statement.  Its second and
third disjuncts are no longer inhabited, and `DefsTy.vfld_exact_obj` states the first alone beside
it.

`HasTy.toPathTy` maps every term typing at a variable to a path typing.  `erase_step` and `erase_reflect` keep their statements (T11), as does every lemma of
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
| `HasTy.var`, `recI`, `recE`, `andI` | at P0 they move to `PathTy` and reach `HasTy` through the bridge rule `path`.  Amended at P2 (decision 28): they are constructors of `HasTy` again with the base's statements, the bridge is `HasTy.sngl` at a singleton only, and `HasTy.projP` stands beside `HasTy.proj` | at P0 `HasTy.toPathTy` makes each composite derivable exactly where the base's rule was, with the same premises and no premise added.  After P2 they are the base's rules verbatim, and `HasTy.toPathTy` still maps every term typing at a variable to a path typing |
| `Sub.selUpper`, `selLower` | the premise is `PathTy Γ p _` for a general path | at `p = .var x` the premise is the base's premise through `HasTy.toPathTy`, so every base derivation is a derivation |
| `Ty` | three constructors, `vfld`, `sngl`, and `sel` taking a path | additive, and `.sel (.var x) A` is the base's type selection, so every base type is a type |
| `Ty.Decl`, `Ty.isDecl`, `Ty.isDecl_iff`, `Ty.Wf` | two clauses each | additive, and no base shape changes its verdict |
| `DefsTy` | three constructors at P0, `trmObj`, `trmLam` and `trmSngl`.  Amended at P2 (decision 27): `trmObj` only, and `trmLam` and `trmSngl` are derived forms at a plain field `{a : T}` | additive, `DefsTy.trm` still types a value field at `{a : T}`, so every base derivation stands, and the new rule gives a stronger type to the same definition |
| `HasTy.let` | nothing, and `letSngl` is stated beside it.  Amended at P2 (decisions 23 and 27): `letSngl` is a derived form over `HasTy.let` and `HasTy.projP`, premise `PathTy Γ (.var x) (.fld a (.sngl q))`, binder `.sngl q` | additive: a `let` over a projection may still bind opaquely |
| `Path.substVar` | nothing, and `substPath` is stated beside it, with `substPath_var` the bridge | `Ty.substVar` and `Path.substVar` stay renamings, which is what `RenameLemmas` is stated over |
| `erase_step`, `erase_reflect`, `final_erase`, `final_reflect` | nothing, except that the two `.path (.var x)` patterns read `.path x` | decision 2: the constructor's argument changed, the case analysis did not.  `Tm.erase (.path x) = .var x`, where the base wrote `.var p.root` and the base's `root` on a `var` path is the identity |
| `DefsTy.vfld_exact` (T10, new) | the premise `Defs.Distinct d`, and `Defs.lookupTrm` for the plan's `d.get?`.  Amended at P2 (decision 27): the statement is kept, its second and third disjuncts are no longer inhabited, and `DefsTy.vfld_exact_obj` states the first alone beside it | a new theorem of this stage, not a base statement, and false without the premise: `DefsTy` puts no condition on the labels of an intersection, so `{a = ν(t. {A = ⊤})} ∧ {a = z}` types at `{val a : μ(t. {A : ⊤..⊤})} ∧ {a : ⊤}`, where the reader of the type and the reader of the definitions answer about two different definitions.  That is decision 21, and every use has the premise to hand: `HasTy.obj` carries it for the literal and `DefsTy.trmObj` for the nested one |
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
typing: the one stable rule, `trmObj`, asks for an object literal body, the body is a projection, so every derivation of these definitions types `a` as a computation member and
`Ty.lookupVfldDecl` answers `none`.  `X2_noSubDecl` inverts the abstract view, so `Typ-Abs` does not
manufacture a stable member at `a` either.  Left unproved is the unqualified sentence that no
`PathTy Γ x.a T` exists at all: its remaining cases go through `PathTy.sub` and `PathTy.snglInv`,
and refuting those is an inversion of `Sub`, which P0 does not have.

**X3, the two-hop program.**  `let y = x.a in y.b`.  After P2 `X3` is the former `X3_opaque`: the
field `a` is declared at `{val b : ⊤}` and not at a singleton, so the derived `letSngl` does not
apply, and the plain `HasTy.let` types the program with both projections by `HasTy.projP`.
`X3_body` keeps the body's derivation under the singleton binder: `y` is bound at `(x.a).type`,
`Sngl-Trans` carries `x.a`'s stable member to `y`, and `PathTy.sel` reads `y.b` (`X3_yb`).

**X4, gDOT Fig. 2.**  The `types` literal of the Dotty fragment, with the enclosing module `pcore` a
context binder, since nothing here eliminates a member of `pcore`.  `pcore.symbols.Symbol` is the
length-two selection, both lambda fields are plain, by `DefsTy.trm` (decision 27), and `newTypeRef` allocates
`ν(_. {symb = s})`, binds it with a `let` and lets it out at `types.TypeRef`.  T9 is then applied to
the literal's declared type, and the three type members are found by `decide` through
`Ty.lookupTypDecl`, each with equal bounds.  `X4_abs` and `X4_muAbs` are the other half: Fig. 2's
abstract reading, `TypeRef >: ⊥ <: …`, derived from the exact declaration by `Typ-Abs`, which is the
step pDOT's precise self types refuse.
