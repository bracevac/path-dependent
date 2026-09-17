# DOT-MNF to FCdot presentation

Sixty-three main slides and six reference slides (69 pages). The deck gives
full grammars for the source and target calculi, proof terms, head forms,
and object entries. It develops concrete projection and object translations,
then compares the safety argument with the direct proof of Rapoport et al.
(2017), including allocation, application, projection, narrowing, and
transitivity.

The source now includes arbitrary recursive bodies. The annotated WadlerFest
frontend has opened-self assumptions and distinct label categories. The final
part defines retained-let reduction and readback, states exact finite-answer
and stuckness correspondence with the store machine, and proves safety for
every retained reduction order through FCdot. The scope slide records the
intrinsic-scoping boundary and the absence of recursive subtyping and field
paths.

The rendered deck is [dot-mnf-fcdot.pdf](../output/pdf/dot-mnf-fcdot.pdf).
The [LaTeX source](dot-mnf-fcdot.tex) contains only slide content.
[Speaker cues and Lean references](speaker-notes.md) are separate.

Build from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error dot-mnf-fcdot.tex
```

The presentation follows `DotMNF/`, `DotMNF/WadlerFest/`, `FCdot/`, and
`DotToFCdot/`. The retained-let safety theorem is in
`DotToFCdot/RetainedSafety.lean`; the public label-sorted interface is in
`DotMNF/WadlerFest/Sorted.lean`, with its public safety theorem in
`DotToFCdot/SortedSafety.lean`. Source entities remain blue inside translation
brackets. Calligraphic letters followed by `::` name derivations; proof-term
definitions and typing judgments are displayed separately.
