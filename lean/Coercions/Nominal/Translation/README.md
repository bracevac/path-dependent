# PDot.Translation: pDOT into FCp, and the transport

The translation of the source `PDot.Source` into FCp (plan X, Part TR), and the transport of FCp's
safety to pDOT.  A derivation maps to a term, a path typing to path evidence, and a subtyping to
inclusion evidence, one equation per source rule.  Both replacement rules become `lift` along the
alias, `tight_bounds` is read at `ty_def_new`, and a recursive type is folded after it is unfolded.
Related contexts `G ≈ Δ` (`Ctx.Rel`) pair every source binder with a target binder at its translated
type, the self binder of a literal included.  Every function is structural recursion on its source
object, so the kernel runs the translation of a whole derivation.  A function or theorem about a
source object is declared in `PDot.Source`, a helper about a target object in `PDot.Translation`,
and the claim in `PDot`.

## What is proved

- `HasTy.translate_typed`: for `d : HasTy G t T` and `G ≈ Δ`, the image is typed, `Δ ⊢ ⟦d⟧ : ⟦T⟧`.
- `HasTy.translatePath_typed`: for `d : HasTy G (path p) T` and `G ≈ Δ`, `Δ ⊢ᵖ ⟦d⟧ : ⟦T⟧` and the
  path of `⟦d⟧` is `p`.
- `Sub.translate_typed`: for `d : Sub G S T` and `G ≈ Δ`, `Δ ⊢ ⟦d⟧ : ⟦S⟧ ≤ ⟦T⟧`.
- `DefsTy.translate_typed`: for `d : DefsTy G r ds T`, `G ≈ Δ` and an annotation `T₀` with
  `T₀⟨r⟩ = T` and `T₀.tight = true`, the image is typed against `tel T₀` at `r`.  The tightness
  premise is needed: without it the image of N5's definitions is untyped (`N5_image_untyped`).
- `HasTy.translate_erase`: the image erases to the source's erasure of the term.
- `PDot.safety`: let `d : HasTy .nil t T` and `Reds ⟨[], .nil, t⟩ c`.  Then the term of `c` is a
  normal form or `c` steps, and a path in focus has a safe lookup in the store of `c`.
- `PDot.reachable_typed`: under the same hypotheses, the erasure of `c` is the erasure of an FCp
  state typed at `⟦T⟧` renamed into the signature of `c`, and every typing of its store proves no
  `⊤ ≤ ⊥`.
- `PDot.reachable_run`: under the same hypotheses, the machine runs the image of `d` to a state with
  the erasure of `c`.

The transport carries the invariant `Simulated c`, a typed FCp state over the signature of `c` with
the erasure of `c`.  It holds at the start by `translate_typed` and `translate_erase`.  A source
step erases to a runtime step (`Source.erase_step`), which `erase_reflect'` matches by a run of the
machine (`lockstep`).  `progress`, `path_safe` and the source's `erase_reflect`, `erase_normForm`
and `erase_pathSafe` read it off.  The consistency in `reachable_typed` is FCp's
`reachable_consistent`, whose premise is the typing of the image, `translate_typed d .nil`.

The examples, decided in the kernel:

- `E1_checks` to `E11_checks` and `E13_checks`: the FCp checker accepts the image of each of X0's derivations of E1
  to E11 and E13 at the translated type, E9 to E11 in the translated context and E11 at `T = ⊤`.
  `E12_three`: the lookup of `x.a.c` reaches `λ(z : ⊤) z` in the source store, on its erasure, and
  on the erasure of X3's typed FCp store of E12.
- `Pages.E5`, `Pages.E7`, `Pages.E8`: each program runs on the source (`Source.runFuel`) and its
  image on the machine (`Translation.runOf`) to one runtime configuration, the source to a normal
  form and the machine to a final state.  E5 ends at `path o.incr.decr` after four source steps and
  seven machine steps, E7 at `path core` after two and three, E8 at `path o` after nine and sixteen.
  `counts` on each page makes the counts exact: one source step fewer ends at another erasure, and
  one machine step fewer at a state that is not final.
- `N1_both` to `N3_both`: in the empty context the source types none of the literals of N1 to N3
  (X0), and no FCp literal at `tel` of the same annotation with definitions of the image's shape is
  typed, whatever its evidence.  `N1_image_erase` to `N3_image_erase`: with the evidence at the
  source's paths, and for N1 a function value that erases to the source's lambda, that literal
  erases to the source literal.  N3's FCp side is proved by `path_safe`: the lookup of `x.zz` is
  stuck.
- `N4_both`: in the context `x : {A : ⊤..⊤}` the source does not type `x : x.type`, and FCp types
  it in the translated context by `PA-Sngl` over `PE-Refl` (plan X, decision 21).
- `N5_both`: `ty_def_new`'s third premise holds where `tight_bounds` fails, and the image of those
  definitions is typed against the opened annotation and not against the one that is not tight.

## What it leaves out

The translation is a function on derivations, not on terms.  A term with two derivations has two
images, with one erasure.  The examples' derivations are written by hand in `Source/`.  E11 is
checked by the kernel at `T = ⊤` only, and holds for every `T` by `E11_image_typed`.  The negative
examples refute the images of one shape of definitions, the shape the translation builds.  An FCp
literal with another annotation and the same erasure may be typed.

## Modules

| module | contents |
|---|---|
| `Types` | the type translation `⟦·⟧`, the telescopes `tel⁺` and `tel` |
| `TypesLemmas` | its laws under renaming and path substitution, the fold `Ty.tel_fold`, the kernel checks on E3's types |
| `Hole` | the translated hole of a replacement |
| `Rel` | related contexts `G ≈ Δ`, `Ctx.translate` |
| `Evidence` | the images of path typings (TR.3) and of subtyping (TR.4) |
| `EvidenceTyped` | `HasTy.translatePath_typed`, `Sub.translate_typed`, the examples E9 to E11 |
| `Defs` | helpers of the definition translation and the opening inversions |
| `Terms` | the images of terms (TR.6) and of definitions (TR.5) |
| `DefsTyped` | label lemmas and the inversions of FCp's typing that `TermsTyped` reads |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translate_typed`, the examples E3, E8, E13 and N5 |
| `Erasure` | `HasTy.translate_erase` |
| `Safety` | the invariant `Simulated`, `lockstep`, `PDot.reachable_run`, `PDot.reachable_typed`, `PDot.safety` |
| `Examples` | the evaluators `Source.runFuel` and `Translation.runOf`, the checker on E1 to E11 and E13, E12's lookup at three levels, N1 to N5 on both sides |
| `Pages` | the runs of E5, E7 and E8 on the source and on the machine with their step counts, one namespace each |
