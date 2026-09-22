# FCdotR — status

State of the `Coercions.FCdotR` library as integrated on branch
`fcdot-recursive-subtyping`.  FCdotR is the explicit-evidence **target** for
the `Coercions.Oopsla16` source (Rompf–Amin OOPSLA'16 DOT, which has
recursive subtyping).  It is a *second* target: the WadlerFest→FCdot chain in
`DotMNF`/`DotToFCdot`/`FCdot` is not reused, only imitated.

`lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR` completes in **104 jobs**.
No `sorry`, `admit`, `axiom`, `native_decide` or `partial` anywhere in
`FCdotR/` or `Oopsla16/` outside doc comments.  Every result named below
depends on at most `propext` and `Quot.sound`.

## Modules

| Module | What it establishes |
| --- | --- |
| `PLAN.md` | The design: substitution via prefix restriction, the elaboration of 32 source rules, the metatheory order, and the open questions.  Not code. |
| `Prefix.lean` | The prefix apparatus at a two-zone variable: `scopeAt`, `renameAt`, `selfAt`, `ctxAt`, `Zone`, and the `upTo`/`renameUpTo` transport laws (`lookupAt_upTo`, `upTo_upTo`, `scopeUpTo_renameUpTo`). |
| `Syntax.lean` | The five grammars — inclusion evidence `Le`, observation evidence `Vc` (indexed at its subject's prefix scope), `Atom`, `Tm`, `Defs` — plus `Atom.root` and `Defs.length`. |
| `Typing.lean` | `StoreTy`/`tyOf` and the two evidence judgments `LeTy` (inclusion) and `VcTy` (observation).  No term typing here. |
| `Structural.lean` | `MonoAt`/`Mono`: a substitution carrying a per-variable image and restriction satisfying the star law; `id`, `lift`, `comp`, `oneConc`.  Its own closing note records that `Mono` is *not* closed under restriction, so no substitution action can be defined against it. |
| `Locality.lean` | Lemma 0, the locality of observation evidence: `VcTy.strengthen` and `VcTy.ofLoc`. |
| `Examples.lean` | The `FunctionField` example elaborated by hand: a closed `bindx` derivation whose method body uses a `selL` under the enclosing self.  This is the judgment `DotToFCdot/RecursiveSubtypingSeparation` shows current FCdot cannot express. |
| `Subst.lean` | `MonoSyn`, the **inductive syntax** of generated substitutions (`id`, `weaken`, `ofStore`, `atNil`, `lift`, `comp`, `oneConc`), which *is* closed under restriction (`resSyn`) — the thing `Mono` could not be.  The substitution action on all five sorts (`Le.subst`, `Vc.subst`, `Atom.subst`, `Tm.subst`, `Defs.subst`), the star laws, `toMono`, and `restrict_unique`: the restriction is the only substitution satisfying the star law. |
| `SubstTyping.lean` | `MonoSyn.Ev` (agreement of a substitution with store, store typing and context) with `refl`/`lift`/`atNil`; `VcTy.toFull`, `VcTy.weakenVar`.  The substitution theorem `LeTy.substEv`/`VcTy.substEv` — every clause of both judgments discharged — **conditional on an explicit hypothesis `LemmaR`**, reduced by `LemmaR.ofVc` to its variable field `LemmaRVc`.  Nothing inhabits `LemmaRVc`. |
| `StoreTyping.lean` | `Conjunct` (a right-nested intersection with a named conjunct) and `DmsHasType.conjunct`; `Store.Honest`, the invariant that every location holds a literal typed at its store type; `Honest.vary` (source `T_Vary`), `Honest.member`, `Honest.obs` (the definition-side half of concrete `selL`/`selR`), `Honest.alloc` (honesty survives allocation).  Store renaming for all four source judgments (`HasType`/`DmsHasType`/`Stp`/`Htp`).  `TwoObjectStore`: the invariant instantiated at `Oopsla16.PackingCounterexample`'s store. |
| `TermTyping.lean` | The three term-level judgments `AtomTy` (5 rules), `TmTy` (4), `DefsTy` (3); `TmTy.appWeaken`, `AtomTy.toVc`; `FunctionFieldObject`, an object literal typed at a recursive self type. |
| `Machine.lean` | The runtime: `Inst` (the one substitution the machine performs — a location for the oldest local binder — closed under restriction), its action on all five sorts, the target `Store`, `Frame`/`Cont`/`State`, and `Step`/`Steps` indexed by the source's own `Oopsla16.Grows`.  Six rules: `let`, `castPush`, `castAtom`, `rename`, `alloc`, `app`. |
| `Erasure.lean` | `Tm.erase`/`Defs.erase`/`Store.erase` into `Oopsla16` itself (the type translation is the identity), the commutation laws with instantiation and store renaming, and `Step.simulate`/`Steps.simulate`: a machine step erases to zero or one source step.  `Counterexample.badRun`: a closed program that allocates the packing counterexample's store and gets stuck, with the endpoint equal to the source's stuck configuration by `rfl`. |

## Road to a WadlerFest-style safety theorem

In dependency order.

1. **Substitution theorem** — *partial.*  `LeTy.substEv`/`VcTy.substEv` discharge
   every clause of both evidence judgments, but take `LemmaR` as an explicit
   hypothesis, and **no inhabitant of `LemmaR` exists**.  `LemmaR.ofVc` reduces
   it to one field, `LemmaRVc`: the coherence of iterated restriction at an
   abstract subject, a heterogeneous equality in both the domain and the
   codomain scope.  `restrict_unique` is the stated route (it makes the
   coherence provable without induction over generators), and is done.  Until
   `LemmaRVc` is inhabited the substitution theorem is vacuous, and nothing
   downstream may use it.  There is also **no** substitution theorem for
   `AtomTy`/`TmTy`/`DefsTy` — not started.
2. **Canonical forms** — *not started.*  `le_canon`/`vc_canon`/`atom_canon`, one
   mutual induction with `Vc` as a third sort.  `PLAN.md` §I flags the
   termination measure for `vc_canon` as the one genuinely open question in the
   design.  Also needed here: `obs_conc_admissible`, whose easy half is
   `Store.Honest.obs` and whose converse needs canonical forms.
3. **Preservation** — *not started.*  Blocked on 1 and 2.  Two further
   obstacles are already visible: `Machine.lean`'s `rename` and `app` rules
   substitute an atom's *root* and drop its coercions, which is sound at
   runtime but not type-preserving (`FCdot.Machine` keeps them via
   `Tm.adjust`); and `Store.Honest` is an invariant of an `Oopsla16.Store`,
   whereas preservation needs honesty of the *machine's* store or of its
   erasure.
4. **Progress** — *not started.*  Blocked on 2.
5. **Elaboration from `Oopsla16.Stp`/`HasType`** — *not started.*  `PLAN.md` §E
   lists the 32 source rules.  The input side exists: all four source
   judgments now survive store renaming (`StoreTyping.lean`), and
   `Store.Honest.vary` shows the target's `AtomTy.varConc` is exactly the
   source's `T_Vary`.  `Examples.lean` and `FunctionFieldObject` are two
   worked instances done by hand.
6. **Erasure equality** — *partial.*  `Step.simulate` holds under
   `Cont.Evidential` (no `let` frame) and `Steps.simulate` on the let-free
   fragment.  The gap is structural, not incidental: `let` erases by an
   object encoding, so the step that consumes a `let` frame erases to a
   configuration that must first allocate the encoding's object and the store
   scopes diverge.  Closing it means either a source-side `let` or a
   simulation up to store extension.
7. **Safety transport** — *not started.*  The `DotToFCdot/Safety.lean` shape
   (`Simulated`, `final_erase`/`final_reflect`, `dot_safety`,
   `dot_not_stuck`) needs 3, 4, 5 and 6.

## Integration notes

* **`Store` is overloaded.**  `Machine.lean` declares `FCdotR.Store` (the
  target machine store, holding `Defs σ []`) while `Typing.lean`,
  `Locality.lean`, `StoreTyping.lean`, `SubstTyping.lean`, `TermTyping.lean`
  and `Examples.lean` all write `open Oopsla16 (… Store …)` inside
  `namespace FCdotR`.  Nothing breaks today, because no module imports both.
  But in a module that does, the enclosing namespace wins over the `open`
  **silently**: bare `Store` becomes `FCdotR.Store`, with no ambiguity error.
  A preservation module needs both stores at once and will hit this.  The
  finished line's convention (`DotToFCdot`) is to qualify at use sites and not
  `open` the clashing name.  Deciding whether `Store.Honest` should attach to
  the source store or the machine store is a design question, so it is
  recorded here rather than patched.
* **Two unconnected substitution machineries.**  `Machine.lean` does not import
  `Subst.lean`; its `Inst`/`Le.inst` duplicates `MonoSyn`/`Le.subst` for the
  one case the machine needs.  `Inst` should eventually be an instance of
  `MonoSyn`; there is no bridge yet.
* **`Structural.lean`'s closing note is superseded.**  It says the substitution
  action "is not yet provable" against `Mono`.  That is still true of `Mono`,
  but `Subst.lean`'s `MonoSyn` is the answer, and `MonoSyn.toMono` embeds it.
* **`Ctx.renameStore` is in the wrong namespace.**  It lives in `FCdotR`
  because `Oopsla16/Context.lean` was off-limits, so it is written applied
  (`Ctx.renameStore Γ ρ`), not by dot notation.  It belongs in `Oopsla16`.
* `Oopsla16/SubstLemmas.lean` gained 15 `@[simp]` lemmas, which changes the
  global simp set for everything downstream.  All five libraries were rebuilt;
  nothing regressed.
