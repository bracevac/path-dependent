# DotMNF with captures

DOT in monadic normal form with Scala 3 capture sets, the source of the translation in
`../DotToFCdot`.  A type is a shape with a capture set beside it, `S ^ C`, where the shapes are the
vanilla types plus a capture member `{C : c₁..c₂}` and a box `□ T`.  Term typing carries a use set
as its first index, `U; Γ ⊢ t : T`: the capabilities `t` may read when it runs.  The calculus has a
machine and an erasure but no metatheory of its own, since safety and capture prediction are
borrowed from the target through the translation.

A value is pure, and the capture set of its type is the use set of its body without the binder.
`Var` types `x` at `{x}`, and `sc-var` reads the declared set back off the context.  Type-member
bounds are shapes, so a capturing type enters a type member through a box.

## Modules

| module | contents |
|---|---|
| `Syntax` | capture atoms `{x}`, `{κ}`, `{x.C}`, `any`, and capture sets with union and decided inclusion. Shapes, types, terms with `C ⊸ x`, values with `□ x`, definitions with `{C = c}`. `Shape.Decl`, `Ty.Wf`, `Defs.Distinct`. The expansion of `any` (`Ty.expand`, `Ty.expandWith`, `Ty.AnyOk`, `Ty.NoAny`) |
| `Typing` | contexts, with `Ctx.consC` for a platform capture binder. `Subcap`, `SubShape`, `Sub`, `HasTy`, `DefsTy`, Type-valued and mutual. Derived rules `Subcap.ofVar`, `HasTy.widen` |
| `Machine` | store with data-free capture slots, continuations, `Step` with the `unbox` step, `State.inspects`, the platform prefix `Platform` and its store |
| `Erasure` | erasure to `Runtime`, a box to the runtime's box and an unboxing to its `unbox`. `erase_step`, `erase_reflect` |
| `Examples` | the vanilla E1 to E8 at pure types and empty use sets, and capture examples S1, S2, S3, C2, C5, C7 over a platform of two capabilities |

## Notation

| | |
|---|---|
| `S ^ C` | the type with shape `S` and capture set `C` |
| `{C : c₁..c₂}`, `{C = c}` | a capture member with lower and upper bound, and its definition in a literal |
| `□ T`, `□ x`, `C ⊸ x` | the box shape, boxing a variable, unboxing `x` at the boxed set `C` |
| `{x}`, `{κ}`, `{x.C}` | capture atoms: a term variable, a platform capability, a capture member |
| `U; Γ ⊢ t : T` | term typing with use set `U` (`HasTy U Γ t T`) |
| `Γ ⊢ C <:ᶜ D` | subcapturing (`Subcap Γ C D`) |
| `any` | a capture atom no rule reads, given its meaning by `Ty.expand` |

## New rules

```text
sc-var       Γ ⊢ {x} <:ᶜ (Γ(x)).captureSet
sc-sel-lower U; Γ ⊢ x : {C : c₁..c₂} ^ D  ⟹  Γ ⊢ c₁ <:ᶜ {x.C}
sc-sel-upper U; Γ ⊢ x : {C : c₁..c₂} ^ D  ⟹  Γ ⊢ {x.C} <:ᶜ c₂
Cap          Γ ⊢ c₁' <:ᶜ c₁,  Γ ⊢ c₂ <:ᶜ c₂'  ⟹  Γ ⊢ {C : c₁..c₂} <: {C : c₁'..c₂'}
Boxed        Γ ⊢ T <: T'  ⟹  Γ ⊢ □ T <: □ T'
Capt         Γ ⊢ S <: S',  Γ ⊢ C <:ᶜ C'  ⟹  Γ ⊢ S ^ C <: S' ^ C'
Var          {x}; Γ ⊢ x : (Γ(x)).shape ^ {x}
All-I        U↑ ∪ {x}; Γ, x : T₁ ⊢ t : T₂  ⟹  {}; Γ ⊢ λ(x : T₁) t : (∀(x : T₁) T₂) ^ U
{}-I         U↑ ∪ {x}; Γ, x : (μ(x. S)) ^ U ⊢ d : S  ⟹  {}; Γ ⊢ ν(x. d) : (μ(x. S)) ^ U
Box          U; Γ ⊢ x : T  ⟹  {}; Γ ⊢ □ x : (□ T) ^ {}
Unbox        U; Γ ⊢ x : (□ (S ^ C)) ^ D,  Γ ⊢ C <:ᶜ U  ⟹  U; Γ ⊢ C ⊸ x : S ^ C
Sub          U; Γ ⊢ t : T,  Γ ⊢ T <: T',  Γ ⊢ U <:ᶜ U'  ⟹  U'; Γ ⊢ t : T'
```

The other rules are the vanilla ones with the use set passed through.  The body of a `μ` must be a
declaration (`Shape.Decl`), unlike in the vanilla source today.

## Reading `any`

`any` is the universal capture atom.  Here it is a notation: `Ty.expand` replaces it by a
concrete set before typing.  In the result of a function type it reads as the function's
own set plus the parameter.  In a field type or a capture-member upper bound it reads as the
object's set plus the self.  At the top of a program it reads as the platform set.  Each former
resets the reading for what is under it, so no levels are needed.  `Ty.AnyOk` decides that `any`
occurs only in these positions.  It rejects `any` in the outer set of a parameter type, in a type-member
bound, in a capture-member lower bound and under a box.

## Main theorems

- `erase_step`, `erase_reflect`: source steps and runtime steps match, with no side condition.
- `Tm.inspects_erase`, `State.inspects_erase`: erasure keeps the root a state reads next.
- `Subcap.ofVar`: from any typing of `x` at `S ^ C`, `{x} <:ᶜ C`.  It is derived, because `sc-var`
  reads the context instead.
- `Ty.noAny_expand`: every type expands, at a set with no `any`, to a type with no `any`.
- `Ty.expandWith_of_anyOk`: what `AnyOk` secures, that no `any` is read as `{}`.  `Ty.expandWith D E`
  is `Ty.expand D` with `E` given to the four positions that `expand` reads as `{}`.  For an `AnyOk`
  type it equals `Ty.expand D` for every `E`.  For `□ (⊤ ^ {any})`, which is not `AnyOk`, it differs from `Ty.expand D` at `E = {κ}`.
- `Ty.expand_of_noAny`, `Ty.expand_rename`: expansion is the identity without `any` and commutes
  with renaming.
- `S1_typed`: `withFile` with an explicit capture parameter, its result `any` read as `{fs, cp, op}`
  (`S1_expand`).
- `S2_typed`, `C5_typed`: an iterator class with a capture member, and a caller that reaches `{fs}`
  only through the member's upper bound.
- `S3_typed`, `C2_typed`, `C7_typed`: a boxed capability in a type member, explicit capture
  polymorphism, and a container of boxed capabilities.

Axioms: `propext` and `Quot.sound` at most.  No `sorry`, `axiom` or `native_decide`.
