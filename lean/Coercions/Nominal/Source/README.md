# PDot.Source: pDOT as its Coq formalization states it

This directory transcribes pDOT, the calculus of paths of any length, from its Coq formalization
(`git.io/dotpaths`, the files `Definitions.v`, `Lookup.v`, `Reduction.v` and `Safety.v`).  Each
constructor of a Coq judgment or relation is one Lean constructor with the Coq name, and its premises
come in Coq's order.  The syntax constructors have Lean names, `Ty.sel` for `typ_path`, `Dec.typ` for
`dec_typ`, and so on, in Coq's order.  The
binders are de Bruijn binders of the Paths target: a family is indexed by a signature `s`, and
`(s,x)` adds one variable, `.here`.  Plan X (`plan-10-pdot.md`, Part S) states the design, and its
section S.6 lists the changes of form.

The syntax (`Syntax.lean`, `Binding.lean`) has the constructors of `Definitions.v:59-115` in their
order.  Paths, signatures, labels, renamings and path substitutions are the Paths target's, imported
and not copied.  A path is a variable followed by field selections in the order they are selected.
Coq's `p_sel x bs` keeps its fields newest first, so Coq's `p••bs` is `p.ext` of the reversed list,
and `rpath` and `rsngl` range over the same paths.  Coq's two label sorts `typ_label` and
`trm_label` are the two sorts `Label.typ` and `Label.trm` of the tree's one type `Label`
(`Paths/FCdot/Debruijn.lean:16-19`).  `Ty.sel`, `Dec.typ`, `Dec.trm`, `Def.typ`, `Def.trm` and
`Path.sel` take a `Label` and do not check its sort, and `Def.label`, `Defs.get` and `Defs.hasnt`
compare labels without their sort.  So the Lean syntax holds ill-sorted terms that Coq has not, such
as a type member selected at a term label, and the judgments type some of them.  The correspondence
of the table below is on the well-sorted fragment.  A context binds a variable at a type of the outer signature, `G.cons T`, or at a type
that mentions the variable itself, `G.consSelf T`, which is the self of a literal.

The judgments (`Repl.lean`, `Typing.lean`) are `Type`-valued.  Replacement `Repl p q T T'` is
`repl_typ` with `repl_dec`, one occurrence of the prefix `p` at a time.  `tight_bounds` is the
Boolean `Ty.tight`.  `HasTy`, `DefTy`, `DefsTy` and `Sub` are `ty_trm`, `ty_def`, `ty_defs` and
`subtyp` in one mutual block, 13, 4, 2 and 14 constructors.  Definition typing is indexed by a path
`r`, which is Coq's pair of a variable `x` and a field list `bs`.  `Derived.lean` inverts the
judgments and adds derived rules for the examples.  A definition typing has no subsumption, so a
path field is declared at its singleton and nothing else (`DefTy.path_decl`).

pDOT-C, the source of plan XII (`plan-12-nominal.md:463-499`), adds one definition and two rules to
these judgments, so `DefTy` has 5 constructors and `Sub` 15.  `Def.cls C T` is a class definition
`{class C = T}` (`Syntax.lean:57`).  `DefTy.ty_def_cls` declares it at `{C : ⊥..T}` when
`T.clsBody`, that is when `T` is `⊤`, a record, an intersection or a `μ` (`Typing.lean:73`,
`Binding.lean:442`).  `Sub.subtyp_seal` gives `T <: p.C` when `G.selfCls p C = some T`
(`Typing.lean:111`).  `Ctx.selfCls` is the class reading of a self binder: `p` is a self variable
followed by fields of nested objects, and the self type at `p` declares `{C : ⊥..T}` with `T` a
class body (`Binding.lean:497-503`).  A let-bound path has no class reading, so a value is sealed at
`p.C` only inside the literal that defines `C`.  `ty_def_new` reads `Ty.tightC` in place of
`Ty.tight`, which also passes `{C : ⊥..U}` with `U` a class body (`Repl.lean:74`).  In a class-free
context every typing of a class-free term is plain, it uses neither new rule
(`HasTy.plain_of_clsFree`, `Derived.lean:322`), so plan X's pDOT is the class-free restriction of
pDOT-C, and a class-free context has no class reading (`Ctx.selfCls_none_of_classFree`,
`Binding.lean:693`).  `Nominal.lean` defines the nominal vocabulary, `IsView`, `Up`, `Factor` and
`ClassReach`, and proves its three theorems: `Factor.sub` (a factorization through `p.C` is a
subtyping), `Ty.Structural.not_factor` (no structural type factors through a class type) and
`class_order` (between class types, a factorization is the class order).  `Programs.lean` types the
class program E14 of plan XII, with two class definitions and three seals.

Lookup and reduction (`Lookup.lean`, `Reduction.lean`) are `Prop`-valued, as in Coq.  `LStep` is
`lookup_step`, and `lookup_sel_v` reads the newest definition at a label (`Defs.get`).  `Red` is
`red` on configurations `⟨s, γ, t⟩`, indexed by the renaming of the step's signature, the identity
or `succ` when `red_let_val` allocates.  `NormForm` is `norm_form`, `ExtRed` is `extended_red` of
`Safety.v`.  `Lookups` and `Reds` are the reflexive transitive closures, and `CyclicPath`,
`Diverges` and `Diverges'` are infinite sequences given by a function.  Lookup is deterministic
(`LStep.det`), and so is reduction (`Red.det`).

The examples check the transcription from both sides.  `Programs.lean` types the programs E1 to E8
of plan X, among them the three example lemmas of the Coq development under their Coq names:
`compiler_typecheck` (`CompilerExample.v:71`), `list_typing` (`ListExample.v:49`) and `typecheck`
(`SingletonTypeExample.v:32`).  `Examples.lean` types E9 to E11 and E13, and `Lookup.lean` runs the
lookup E12.  A replay cannot see a rule transcribed too strongly.  The negative examples N1 to N5 of
`Examples.lean` can: a reflexive singleton rule, a symmetric one, or a `ty_def_path` with
subsumption each makes one of them false.  `Model.lean` holds the path models that refute N3 and N4.

## The fidelity table

The last column names the changes of form of plan S.6 that apply to the row, by these tags.

- **Type**: the judgment is `Type`-valued, and its `Prop` reading is `Nonempty`.
- **dB**: de Bruijn signatures in place of locally nameless terms.  A cofinite premise
  `∀ z ∉ L, G & z ~ T ⊢ J^z` is one premise in `G.cons T`, a type free of the fresh name is weakened
  (`U.weaken`), and `open_*_p p` is `substPath p`.
- **self**: the self `z ~ open_typ z T` of a literal is the binder `G.consSelf T`.
- **path index**: `ty_def x bs` and `ty_defs x bs` are indexed by the path `r = x.bs`, so the premise
  `p = p_sel (avar_f x) bs` of `ty_def_new` is the index itself.
- **shift**: under the binder of `rbnd` and `rall2` both paths are weakened, `p↑ ↦ q↑`.
- **get**: `defs_has ds {a := t}` is `ds.get a = some {a = r}`, the newest definition at `a`.
- **tight**: `tight_bounds T : Prop` is `T.tight = true` with `T.tight : Bool`.  plan XII weakens `ty_def_new`'s premise to `T.tightC =
  true`, which also passes `{A : ⊥..U}` with `U` a class body.
- **conf**: `red` on `sta * trm` with a fresh name is `Red` on configurations with the store
  renaming `ρ`, and `red_let_tgt` renames the continuation by `ρ.lift`.
- **total**: `binds x v γ` is the total `γ.get x`.

| Coq | line | Lean | change of form |
|---|---|---|---|
| `ty_var` | `Definitions.v:593` | `HasTy.ty_var` | Type, dB, self (`binds x T G` is `G.lookup x = T`, at a self binder too) |
| `ty_all_intro` | `Definitions.v:604` | `HasTy.ty_all_intro` | Type, dB |
| `ty_all_elim` | `Definitions.v:616` | `HasTy.ty_all_elim` | Type, dB |
| `ty_new_intro` | `Definitions.v:628` | `HasTy.ty_new_intro` | Type, dB, self, path index |
| `ty_new_elim` | `Definitions.v:639` | `HasTy.ty_new_elim` | Type |
| `ty_rcd_intro` | `Definitions.v:649` | `HasTy.ty_rcd_intro` | Type |
| `ty_let` | `Definitions.v:661` | `HasTy.ty_let` | Type, dB |
| `ty_sngl` | `Definitions.v:674` | `HasTy.ty_sngl` | Type |
| `ty_path_elim` | `Definitions.v:686` | `HasTy.ty_path_elim` | Type |
| `ty_rec_intro` | `Definitions.v:697` | `HasTy.ty_rec_intro` | Type, dB |
| `ty_rec_elim` | `Definitions.v:707` | `HasTy.ty_rec_elim` | Type, dB |
| `ty_and_intro` | `Definitions.v:718` | `HasTy.ty_and_intro` | Type |
| `ty_sub` | `Definitions.v:730` | `HasTy.ty_sub` | Type |
| `ty_def_typ` | `Definitions.v:742` | `DefTy.ty_def_typ` | Type, path index |
| `ty_def_all` | `Definitions.v:751` | `DefTy.ty_def_all` | Type, path index |
| `ty_def_new` | `Definitions.v:761` | `DefTy.ty_def_new` | Type, path index, `tightC` (plan XII), dB |
| `ty_def_path` | `Definitions.v:773` | `DefTy.ty_def_path` | Type, path index |
| `ty_defs_one` | `Definitions.v:790` | `DefsTy.ty_defs_one` | Type, path index |
| `ty_defs_cons` | `Definitions.v:802` | `DefsTy.ty_defs_cons` | Type, path index |
| `subtyp_top` | `Definitions.v:816` | `Sub.subtyp_top` | Type |
| `subtyp_bot` | `Definitions.v:823` | `Sub.subtyp_bot` | Type |
| `subtyp_refl` | `Definitions.v:830` | `Sub.subtyp_refl` | Type |
| `subtyp_trans` | `Definitions.v:840` | `Sub.subtyp_trans` | Type |
| `subtyp_and11` | `Definitions.v:849` | `Sub.subtyp_and11` | Type |
| `subtyp_and12` | `Definitions.v:853` | `Sub.subtyp_and12` | Type |
| `subtyp_and2` | `Definitions.v:863` | `Sub.subtyp_and2` | Type |
| `subtyp_fld` | `Definitions.v:874` | `Sub.subtyp_fld` | Type |
| `subtyp_typ` | `Definitions.v:885` | `Sub.subtyp_typ` | Type |
| `subtyp_sngl_pq` | `Definitions.v:897` | `Sub.subtyp_sngl_pq` | Type |
| `subtyp_sngl_qp` | `Definitions.v:910` | `Sub.subtyp_sngl_qp` | Type |
| `subtyp_sel2` | `Definitions.v:922` | `Sub.subtyp_sel2` | Type |
| `subtyp_sel1` | `Definitions.v:932` | `Sub.subtyp_sel1` | Type |
| `subtyp_all` | `Definitions.v:944` | `Sub.subtyp_all` | Type, dB |
| `rrcd` | `Definitions.v:380` | `Repl.rrcd` | Type |
| `rand1` | `Definitions.v:383` | `Repl.rand1` | Type |
| `rand2` | `Definitions.v:386` | `Repl.rand2` | Type |
| `rpath` | `Definitions.v:389` | `Repl.rpath` | Type |
| `rbnd` | `Definitions.v:391` | `Repl.rbnd` | Type, shift |
| `rall1` | `Definitions.v:394` | `Repl.rall1` | Type |
| `rall2` | `Definitions.v:397` | `Repl.rall2` | Type, shift |
| `rsngl` | `Definitions.v:400` | `Repl.rsngl` | Type |
| `rdtyp1` | `Definitions.v:403` | `ReplDec.rdtyp1` | Type |
| `rdtyp2` | `Definitions.v:406` | `ReplDec.rdtyp2` | Type |
| `rdtrm` | `Definitions.v:409` | `ReplDec.rdtrm` | Type |
| `lookup_var` | `Lookup.v:22` | `LStep.lookup_var` | total |
| `lookup_sel_p` | `Lookup.v:29` | `LStep.lookup_sel_p` | none |
| `lookup_sel_v` | `Lookup.v:36` | `LStep.lookup_sel_v` | get, dB |
| `red_app` | `Reduction.v:16` | `Red.red_app` | conf, dB |
| `red_let_val` | `Reduction.v:21` | `Red.red_let_val` | conf |
| `red_let_path` | `Reduction.v:26` | `Red.red_let_path` | conf, dB |
| `red_let_tgt` | `Reduction.v:32` | `Red.red_let_tgt` | conf |
| `nf_path` | `Reduction.v:45` | `NormForm.nf_path` | none |
| `nf_val` | `Reduction.v:46` | `NormForm.nf_val` | none |
| `er_red` | `Safety.v:469` | `ExtRed.er_red` | conf |
| `er_lookup` | `Safety.v:472` | `ExtRed.er_lookup` | conf |
| none (pDOT-C) | plan XII | `Def.cls` | addition: a class definition `{class C = T}` |
| none (pDOT-C) | plan XII | `DefTy.ty_def_cls` | addition: Type, path index, premise `T.clsBody` |
| none (pDOT-C) | plan XII | `Sub.subtyp_seal` | addition: Type, premise `G.selfCls p C = some T` |

That is 33 typing rows, 11 replacement rows, 3 lookup rows, 4 reduction rows, 2 normal-form rows,
2 extended-reduction rows, and 3 rows that pDOT-C adds, which Coq's pDOT has not.

Two notes on plan S.6.

First, the label sorts of the paragraph on the syntax are a change of form that S.6 does not list.
Coq's `dec_typ`, `def_typ` and `typ_path` take a `typ_label`, and `dec_trm`, `def_trm` and
`sel_field` take a `trm_label`.  Here each takes a `Label` of either sort.  The images of Coq's terms
are the well-sorted Lean terms, and the table pairs the rules on them.  The Lean source types a
superset of pDOT's programs.  That the typing of well-sorted terms is pDOT's is argued by a map that
keeps the two sorts apart, and it is not proved.

Second, S.6 calls the function form of Coq's `infseq` "the same relation".  It is not, without
choice.  The function form `∃ f : Nat → _` implies Coq's coinductive `infseq`
(`infseq_from_function`, `Sequences.v:193-194`), and the converse needs dependent choice, which is
why Coq defines `infseq` coinductively (`Sequences.v:95-102`).  X0 only defines `CyclicPath`,
`Diverges` and `Diverges'` in the function form, and no X0 theorem crosses that gap.

## Definitions with no Coq row

| Lean | what it is |
|---|---|
| `PathSafe` (`Lookup.lean`) | `PathSafe γ p`: every lookup sequence from `p` ends at a value or can take a step.  It is the predicate of `PDot.safety` (`plan-10-pdot.md:43,52`), which X1 uses (`plan-10-pdot.md:337`).  It takes the place of the conclusion of `path_safety` (`Safety.v:442-447`), as `plan-10-pdot.md:52-55` says |

## Coq definitions not ported

None of these is a rule of the calculus.  Each is a device of Coq's safety proof, and plan X replaces
each by a device of the target.  Because `inert`, `wf` and `well_typed` are not ported, the source
cannot state the typed conclusion of Coq's `safety`, `G ⊢ u : T` with `γ ⫶ G`, `wf G` and `inert G`
(`Safety.v:416-424`), nor the general `path_safety` for every typed path of a well-typed store
(`Safety.v:442-447`).  `PDot.safety` states progress and the safety of the path in focus, which is
the use Coq's own theorem makes of the lemma (`Safety.v:534`), and `PDot.reachable_typed` types the
reached configuration in FCp instead.

| Coq | line | replaced by |
|---|---|---|
| `record_dec` | `Definitions.v:494` | store typing (I2) and (I3), plan X, "The store invariant" (`plan-10-pdot.md:835-850`) |
| `record_typ` | `Definitions.v:503` | the same (I2) and (I3).  Distinct labels are `ds.hasnt` of `ty_defs_cons` at the source |
| `inert_typ` | `Definitions.v:529` | store typing (I1) and (I2), plan X, "pDOT's proof devices" (`plan-10-pdot.md:917`) |
| `record_has` | `Definitions.v:537` | the object view along the evidence from a location's annotation, plan X, "pDOT's proof devices" (`plan-10-pdot.md:920`) |
| `inert` | `Definitions.v:552` | store typing `⊢ σ : Γ` of FCp, plan X, T.3 (`ST-Nil`, `ST-Lam`, `ST-Obj`, `plan-10-pdot.md:512-514`) and "pDOT's proof devices" (`plan-10-pdot.md:917`) |
| `well_typed` | `Definitions.v:967` | store typing `⊢ σ : Γ` of FCp and `PDot.reachable_typed`, plan X, "Goal and the claim" (`plan-10-pdot.md:40-55`) and "The store invariant" (`plan-10-pdot.md:835-850`) |
| `wf` | `PreciseTyping.v:734` | the forward `PA-Alias`, `DF-Path`'s typing of a path field's body and `lookup_step_typed`, plan X, "pDOT's proof devices" (`plan-10-pdot.md:918`) |

## Modules

| module | content |
|---|---|
| `Syntax.lean` | types, declarations, terms, values, definitions, contexts, stores, configurations, `Path.ext`, `Defs.get` |
| `Binding.lean` | renaming, path substitution, weakening and opening for every family, their laws, `Ctx.lookup`, `Store.get`, the class reading `Ctx.selfCls` with `Ty.clsBody`, `Ty.findCls`, `Ty.findNest`, and the class-free predicates `clsFree` with `Ctx.selfCls_none_of_classFree` |
| `Repl.lean` | replacement, its hole, `Repl.swap`, `Repl.subst`, the decision `Ty.isRepl`, `Ty.tight`, `Ty.tightC` of plan XII |
| `Typing.lean` | the four typing judgments in one mutual block |
| `Derived.lean` | inversion lemmas and derived rules, `DefTy.tightC`, and the class-free restriction `HasTy.plain_of_clsFree` |
| `Nominal.lean` | the nominal vocabulary `IsView`, `Up`, `Factor`, `ClassReach`, and `Factor.sub`, `not_factor`, `class_order` |
| `Lookup.lean` | lookup, its closure, `CyclicPath`, `PathSafe`, determinism, E12 |
| `Reduction.lean` | reduction, normal forms, extended reduction, divergence, determinism |
| `Model.lean` | path models of a fixed context and their soundness |
| `Examples.lean` | E9 to E11, E13, and the negative examples N1 to N5 |
| `Programs.lean` | the programs E1 to E8, with the Coq lemmas `compiler_typecheck`, `list_typing`, `typecheck` |
| `Erasure.lean` | erasure into the untyped runtime `../Runtime.lean`, with nested literals addressed by path, and the lockstep theorems `erase_lookup`, `erase_step`, `erase_reflect`, `erase_pathSafe` |
