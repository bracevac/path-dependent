# Deviations of `Oopsla16` from `dot.v`

The itemized list behind the overview in [`README.md`](README.md).

Every place where this port says something other than the reference, as found
by a line-by-line audit against `dot.v`, `dot_soundness.v` and `dot_exs.v` at
the pinned commit. Lean lines are in this directory unless a path is given; Coq
lines are in `dot.v` unless another file is named. Each item has a status:

* **PROVED**: the named theorem proves the claim, in Lean or in Coq;
* **ARGUED**: comments argue the claim, and nothing proves it;
* **NEITHER**: nothing supports it; the item records a gap.

That a Lean definition and a Coq definition say the same thing can never be
proved here, since the two live in different proof assistants. Every
correspondence claim below is therefore at best ARGUED, even where a Coq
theorem proves a fact about the reference.

## Representation changes

The reference's content, written differently. The claim for each item is that
the rewriting is faithful.

1. **Variables.** Absolute positions (`TVar b x`), locally nameless binders
   (`TVarB`) and the `closed` predicate become intrinsically scoped de Bruijn
   indices in two scopes, store and local. `open 0 v` becomes `substVr`, and
   the 25 closedness premises and 10 `open` equations of the judgment block
   disappear as premises (`README.md`, *Design*).
   Lean `Syntax.lean:57-119`, `Structural.lean:61-63`, `Structural.lean:115`.
   Coq `dot.v:20-57`, `dot.v:89-145`. **ARGUED** (`Syntax.lean:11-18`,
   `README.md`, *Design*).
2. **The self and the method parameter are binders.** `tobj` binds its self,
   and `dfun` binds its parameter once, for the result annotation and the body
   together. The reference has no binder here: the self is "the next slot" of
   the abstract context, and the parameter is written `TVarB 0` in the result
   annotation but as an absolute abstract position in the body (as in `ex1`,
   `dot_exs.v:184-185`).
   Lean `Syntax.lean:97`, `Syntax.lean:108`. Coq `dot.v:43`, `dot.v:48`,
   `dot.v:274-277`. **ARGUED** (the doc comments of `tobj` and `dfun`).
3. **Explicit weakening.** The three non-dependence premises (`T_App`, `D_Fun`,
   `stp_bind1`) become `.weaken`, and so does `stp_fun`'s pushed domain.
   `renameNil` and `renameUpTo` move a type out of the empty context or out of
   a prefix; absolute positions need neither.
   Lean `Typing.lean:63, 65, 79, 105, 121, 132, 137, 143, 147, 152`. Coq
   `dot.v:249, 276, 298, 308, 313, 316-322, 332`. **ARGUED** (each rule's doc
   comment).
4. **`htp`'s truncated context is a prefix scope.** `GH = GU ++ GL` with
   `length GL = S x` becomes the scope `scopeUpTo x`, and `Htp` is typed at
   `Ty σ (scopeUpTo x)`. That is faithful only because every type the
   reference's `htp` assigns to `x` is closed at `S x`, a fact the reference
   does not prove (`README.md`, *The context truncation of `htp_sub` becomes
   scoping*).
   Lean `Typing.lean:173-186`, `Context.lean:52-95`. Coq `dot.v:375-393`,
   `dot.v:781-789`. The closedness fact is **PROVED** on the reference's
   definitions (`htp_closed_Sx`,
   `../../../coq/oopsla16/deviations/ctx_restriction.v`); that `Htp` and `htp`
   derive the same judgments is **ARGUED**.
5. **The size index is dropped, and the judgments are `Type`-valued.** No rule
   constrains the index, and the reference quantifies it away wherever it
   states a result (`has_typed`, `stpd`, `htpd`, `type_safety`).
   Lean `Typing.lean:56, 93, 112, 173`. Coq `dot.v:219, 263, 285, 375,
   395-399`. **ARGUED** (`README.md`, *Design*).
6. **Reduction bookkeeping.** `Step` carries a `Grows` index recording the `G'`
   of `G' ++ G`; `ST_Obj` weakens the old store, and `ST_App1`/`ST_App2` rename
   the operand they do not reduce.
   Lean `Semantics.lean:30-77`. Coq `dot.v:197-212`, `dot_soundness.v:1134`.
   **ARGUED** (`Semantics.lean:16-19`). It was also tested, not proved:
   `../../../coq/oopsla16/deviations/step_differential.py` transcribes both
   step relations to Python and runs them side by side on random
   configurations, and on seeds 0 to 7, 160,000 configurations, they agree at
   every step (that directory's README says how to run it).
7. **Lookup and answers.** The `vobj` wrapper is gone, store and context lookup
   are total, `Dms.get?` is the recursion of `index l (dms_to_list ds)`, and
   the answer condition `∃ ds, index x G = Some ds` holds automatically.
   Lean `Syntax.lean:139-141`, `Syntax.lean:173-177`, `Structural.lean:136-138`,
   `Semantics.lean:89-91`. Coq `dot.v:65-67`, `dot.v:77-81`,
   `dot_soundness.v:1133`. **ARGUED** (by comparing the definitions).

## Restrictions: Lean admits less

8. **Contexts are indexed by prefixes.** A `Ctx` entry may mention only its own
   variable and older ones. Coq's `tenv` is any list, and `T_Varz` accepts an
   entry that mentions a newer variable.
   Lean `Context.lean:76-80`. Coq `dot.v:70`, `dot.v:227-230`. That this loses
   nothing from a prefix-closed context, the empty one included, is **PROVED**
   on the reference's rules (`restriction_harmless`,
   `restriction_harmless_empty`), and that the restriction is real is
   **PROVED** there too (`ctx_restriction_is_real`), both in
   `../../../coq/oopsla16/deviations/ctx_restriction.v`. That prefix-closed Coq
   contexts are exactly the Lean `Ctx` values is **ARGUED**.
9. **Stored objects have every variable in range.** A store entry is a
   `Dms σ []`: it mentions no abstract variable, no dangling `TVarB` and no
   unallocated location. Coq's `venv` is unconstrained, the reference types
   closed terms over stores that break this, and its `type_safety` covers
   them.
   Lean `Syntax.lean:173-177`. Coq `dot.v:69`, `dot_soundness.v:1131`. That
   the reference derives judgments over such stores is **PROVED**
   (`store_restriction_is_real`,
   `../../../coq/oopsla16/deviations/store_restriction.v`). That the
   restriction costs the empty-store theorems nothing, because every store the
   reference reaches from the empty store has all variables in range, is
   **ARGUED** (`Syntax.lean:143-169`).
10. **Out-of-range syntax cannot be written.** Terms and types with
    out-of-range variables do not exist here, and `Step` is defined only on
    configurations where everything is in range. Coq's `step` also fires on
    the others: an out-of-range argument in `ST_AppAbs`, an out-of-range
    receiver in `ST_App2`, free abstract variables in `ST_Obj`. No Coq typing
    rule accepts such syntax.
    Lean `Semantics.lean:50-51`. Coq `dot.v:197-211`, `dot.v:221`, `dot.v:228`.
    That this is harmless for typed terms, since `has_type [] G t T` forces
    every variable into range, is **ARGUED** here and nowhere proved.

## Extensions: Lean admits more

11. **None found.** The four judgments have the reference's 32 rules
    (8 + 3 + 18 + 3), with its names and in its order, and `Step` has its 4
    rules; each rule matches the Coq rule up to items 1-7.
    `PackingCounterexample` is an isolated experiment with its own judgments,
    used only in counterexamples. **ARGUED**, rule by rule
    (`Typing.lean`, `Semantics.lean`).

## Theorem gaps: Lean proves less

The reference's theorem is `type_safety` (`dot_soundness.v:1131-1134`): for any
store `G`, a closed term typed at `T` is a location or steps to a term typed at
`T` over an extended store. The Lean theorems are `Oopsla16.oopsla16_safety`,
`oopsla16_not_stuck`, `oopsla16_safety_honest` and `oopsla16_not_stuck_honest`
(`../FCdotR/SourceSafety.lean:193`, `:208`, `:227`, `:238`).

12. **No preservation.** No Lean theorem says that a reached source term, or
    the final answer, has type `T`. The nearest is `Oopsla16.reachable_related`
    (`../FCdotR/Deliverables.lean:327`), which types a related *target* state,
    and only up to evidence. Coq `dot_soundness.v:1134`. **NEITHER**.
13. **Starting stores.** The Lean theorems start from the empty store, or from
    a store whose every location has a `T_Vary` witness in `FCdotR.DmsFrag`
    (both method annotations present, variable operands only). The reference
    allows any store. Not covered: a location with no `T_Vary` typing, and a
    location typable only through a method without annotations or through a
    general application in a method body. Lean
    `../FCdotR/SourceSafety.lean:227` (`oopsla16_safety_honest`),
    `../FCdotR/StoreTyping.lean:501` (`Store.Honest`),
    `../FCdotR/Elaboration.lean:247` (`DmsFrag`). Coq `dot_soundness.v:1131`.
    **NEITHER**, for the stores not covered.
14. **Every run versus one step.** The Lean theorems cover every configuration
    of every run; the reference gives one step from any typed configuration.
    Iterating the reference yields the Lean form only if `step` is
    deterministic. It is, by inspection of `dot.v:197-212`, but neither
    artifact proves it. The converse fails because of items 12 and 13.
    **ARGUED**.
15. **An any-store statement would still be restricted.** Even a Lean theorem
    for every store could range only over stores whose objects have every
    variable in range (item 9). **NEITHER**: no Lean statement can mention the
    other stores.
16. **Reference lemmas not restated for the source.** Substitution, narrowing,
    canonical forms and transitivity pushback (`dot_soundness.v:201-1129`,
    `dot.v:2049`) have no source-level Lean statement. **NEITHER**.
    `dot_exs.v`'s `ex0` is `Examples.ex0`; `ex1`, `ex2` and `paper_lst` are
    derivations in `../FCdotR/CheckerExamples.lean` (namespaces
    `FCdotR.CheckerExamples.DotExs` and `FCdotR.CheckerExamples.PaperLst`),
    outside this library, whose constants are kept fixed. That they state the
    reference's examples, through the translation of items 1 and 2, is
    **ARGUED**; the Lean derivations themselves are checked by Lean, and
    their elaborations by the kernel. `Oopsla16.stp_consistent` (`../FCdotR/Deliverables.lean:346`)
    is an extra result with no reference counterpart.
