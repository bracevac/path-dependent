# DotMNF with paths

WadlerFest DOT in monadic normal form, extended with pDOT's paths. A path is a variable followed by
field selections, `x.a.b`. Paths appear in types, as `p.A` and as the singleton `p.type`. A term
still names only a variable, and a deep path is reached through a `let`. So the machine and the
erasure keep the base's statements, and only typing grows: a stable field declaration
`{val a : T}`, and a path typing judgment `PathTy` with pDOT's singleton rules.

| module | contents |
|---|---|
| `Syntax` | paths with `root`, `depth` and path substitution (`substPath`, `PathSubst`). Types with `vfld`, `sngl` and `sel` at a path. The declaration readers `lookupTypDecl`, `lookupFldDecl`, `lookupVfldDecl`. Terms, values, definitions, `Ty.Decl`, `Ty.Wf`, `Defs.Distinct` |
| `Typing` | contexts. `Sub`, `PathTy`, `HasTy`, `DefsTy`, `SelfFree`, `SubDecl` as one mutual `Type`-valued block. `HasTy.toPathTy`, the derived forms `HasTy.letSngl`, `DefsTy.trmSngl`, `DefsTy.trmLam`, and the exactness theorems |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck`, unchanged from the base |
| `Erasure` | erasure to the shared runtime, `erase_step`, `erase_reflect` |
| `Examples` | the base examples E1 to E8, the path examples X1 to X4, E1p to E8p, E9, E11, P3e, and the gDOT programs `Fig2_prog` and `Fig1_prog` |

## New syntax

| | |
|---|---|
| `{val a : T}` (`Ty.vfld`) | a stable field: its value is an object literal, so `x.a` is a path |
| `p.type` (`Ty.sngl`) | the singleton type of the path `p` |
| `p.A` (`Ty.sel`) | a type selection, now at any path |
| `PathTy Γ p T` | the path `p` has type `T` |

## Path typing

```
var       : PathTy Γ (.var x) (Γ.lookup x)
sel       : PathTy Γ p (.vfld a T) → PathTy Γ (.sel p a) T
recI, recE, andI, sub                       -- the base's variable rules, at a path
snglRefl  : PathTy Γ p T → PathTy Γ p (.sngl p)
snglTrans : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ p T
snglSym   : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ q (.sngl p)
snglInv   : PathTy Γ p (.sngl q) → PathTy Γ q .top
snglSel   : PathTy Γ p (.sngl q) → PathTy Γ p (.vfld a T) → PathTy Γ (.sel p a) (.sngl (.sel q a))
```

A path extends only through a stable field (`sel`). A field computed by a term, such as
`{a = x.a}`, never becomes a path prefix.
Term typing keeps the base's rules for a variable. It reads path typing in two places only:
`HasTy.sngl` types a variable at a singleton, and `HasTy.projP` projects a field from a receiver
typed as a path. `Sub.selUpper` and `Sub.selLower` take a path typing premise.

## Restrictions

The target has no evidence for four of pDOT's forms, so the source leaves them out.

- **Stable fields hold literals.** `DefsTy.trmObj` is the only rule that declares `{val a : _}`,
  and its body is an object literal. A variable or lambda body is a plain field
  (`DefsTy.trmSngl`, `DefsTy.trmLam`).
- **`let` at a singleton.** In `let y = x.a in u`, `HasTy.letSngl` binds `y` at `q.type` only
  when the field `a` is declared at `q.type`. Otherwise `y` gets an ordinary type, not the
  singleton of `x.a`.
- **Singleton variables.** A variable of type `q.type` cannot be used at a non-singleton type
  of `q`. Projections and type members through it still work.
- **No replacement.** pDOT's `Sngl-<:` and `<:-Sngl` are absent. `p.A <: q.A` for an alias
  still holds when the member is exact, which every literal member is.

The body of a recursive type must be a declaration type (`Ty.Decl`).

## Main theorems

- `DefsTy.typ_exact`: the declared type of a literal is exact on type members. It replaces
  pDOT's `tight_bounds`.
- `DefsTy.vfld_exact_obj`: a stable field of a literal holds an object literal typed at the
  field's declared type. It needs `Defs.Distinct d`.
- `HasTy.toPathTy`: every term typing of a variable is a path typing.
- `erase_step`, `erase_reflect`: the machine and the runtime are in lockstep, as in the base.

Base statements whose form changed: `Tm.path` takes a variable, not a path. `Sub.selUpper` and
`Sub.selLower` take a `PathTy` premise. Every base derivation is still a derivation.

## Examples

E1 to E8 keep their names, statements and derivations. X1 is the example of Sec. 2.2 of the pDOT
paper, a selection `x.c.A` through a stable field, which WadlerFest DOT cannot write. X2 shows
that a field computed by a projection is not a path (`X2_noVfld`, `X2_noSubDecl`). X3 is the
two-hop program `let y = x.a in y.b`. X4 is the `types` literal of gDOT's Fig. 2, with exact
members (`X4_exact`) and their abstract reading (`X4_abs`).

E1p to E8p move the receiver of each base example one stable field deeper. The hop changes no
runtime term, since erasure drops types. E9 is a `let` at a singleton, E11 a stable field next
to a forwarding field, and P3e pDOT's bad bounds through a computation field. `Fig2_prog` is
gDOT's Fig. 2 with the `Option` encoding, and `Fig1_prog` the same program in pDOT's Fig. 1 form,
with a path of length two in a field type. `Nat` is a closed stand-in, since the calculus has no base types.
