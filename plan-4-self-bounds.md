# Plan IV: self-bound propositions in FCdot, lifting the intersection restriction of DOT-MNF

Repository: /Users/mario/projects/path-dependent2 (build from the repo root with `~/.elan/bin/lake build <module>`; the
default targets are all of `lake build`).  Base commit: 6449b58 (branch `choice-free`).  Library: `lean/Coercions/`.
Read `lean/Coercions/README.md`, `FCdot/README.md`, `DotMNF/README.md`, `DotToFCdot/README.md` first.

Hard constraints: no `sorry`, `axiom`, `native_decide`, `partial`, `unsafe`; no Mathlib; `#print axioms` of every theorem
named in the READMEs must stay `[propext, Quot.sound]`; no existing theorem may be weakened (a statement may be
restated in the new representation with the same meaning; nothing may gain a hypothesis); all notations keep working.
Vocabulary: write "self-alias restriction"/"alias-tolerant resolution"; never use the word beginning with "guard" in
any form, in code, comments, commit messages or reports.  Commit nothing to any real branch: work in your worktree,
build, and write `git diff` patches to the paths you are given.

## 1. What changes and why

DOT-MNF restricts intersections `S ∧ T` (and the bodies of `μ`) to declaration-shaped types (`Ty.Decl`): the
translation turns a declaration-shaped type into an object type `μ Tel` and an intersection into the concatenation of
two telescopes, and a type selection `x.A` or a function type is not a telescope.  We lift the restriction on `∧` by
adding a *self-bound proposition* to FCdot telescopes:

    Proposition.bnd (T : Ty s)          written  ⊑ T   ("the object itself is included in T")

so that a non-declaration operand `B` of an intersection translates to the one-proposition telescope `[⊑ ⟦B⟧↑]`.
The restriction on the bodies of `μ` stays (`Wf.mu`, `Rec-I`, `Rec-E` keep their `Decl` premise); the premises of
`And₁`, `And₂`, `And`, `And-I` and of `Wf.and` are dropped, so `S ∧ T` is well formed for all well-formed `S`, `T`.
The refinement of an abstract type, `x.A ∧ {a : T}`, is the acceptance test (E8 below).

Closedness convention.  A bound proposition in a telescope over `(s,x)` is always a weakened closed type: every typing
rule below matches the pattern `bnd T↑` (`Proposition.bnd (Ty.weaken T)`, `T : Ty s`).  Bounds never mention the self.
(Opening a telescope at a root, `Tel⟦r⟧↑`, therefore leaves bound propositions unchanged; what changes is how the
typedness judgments *read* a bound, see §4.)

## 2. FCdot syntax and typing (Syntax.lean, Typing.lean, Checker*.lean, Rename/Subst/Transparency lemmas)

New constructors (add renaming, substitution, `DecidableEq`, and every lemma the existing constructors have):

    Proposition.bnd : Ty s → Proposition s                          -- rename pointwise
    LeCo.bound : Telescope (s,x) → Nat → LeCo s                      -- "the object type is below its i-th bound"
    LeCo.intoBnd : LeCo s → LeCo s                                  -- "an S below T is in μ [⊑ T↑]"
    Morphism.bnd : Morphism s → LeCo s → Morphism s                 -- a template for a target bound

Typing (Typing.lean), in the notation of the file:

    Γ ⊢ .bound Tel i : μ Tel ≤ T                     if  Tel ∋ (i ↦ .bnd T↑)
    Γ ⊢ .intoBnd e : S ≤ μ (.nil ▹ .bnd T↑)           if  Γ ⊢ e : S ≤ T
    Γ ⊢ .bnd m e : src ⇒ Tel ▹ .bnd T↑               if  Γ ⊢ m : src ⇒ Tel  and  Γ ⊢ e : μ src ≤ T

`member` is unchanged (it eliminates `le`, `eq`, `has` propositions only; there is no atom-level elimination of a bound:
one casts the atom by `bound`).  `Value.HasType.obj`, `Telescope.ofLiteral`, `Witnesses.eqEntries` are unchanged: a
literal's precise telescope never contains a bound.

Checker: `synthLeCore` gets the two cases (for `bound`, read `Tel.getAt? i`, require a `bnd` proposition and strengthen
its type with `Ty.strengthenW?`, which already exists in Checker.lean; for `intoBnd`, synthesise `e`), `synthMorCore`
gets the `bnd` case (synthesise `e`, require its source to be `μ src`), and CheckerCompleteness gets the matching cases.
`checkTm_iff` and friends keep their statements.

## 3. Normal forms and the normalizer (Normalizer.lean)

New forms and entries:

    Form.bnd  : Nat → Form s → Form s        -- "bound i, then F":  bnd i F : S ≤ U  when S resolves to μ Tel, Tel ∋ (i ↦ bnd T↑), F : T ≤ U
    Form.into : Entries s → Form s           -- "into a bounds-only object type": into Es : S ≤ μ [bnd T₁↑, …, bnd Tₙ↑]
                                             --   where Es = [bnd F₁, …, bnd Fₙ] and Fₖ : S ≤ Tₖ  (only bnd entries)
    Entry.bnd : Form s → Entry s             -- a bound entry of an object form: bnd G with G : μ Tel₁ ≤ T
    PropForm.bnd : Form s → PropForm s       -- the view entry for a bound: a form typed at the root, see §4

Normalizer clauses (fuel as everywhere):

    hnf (bound Tel i)     = bnd i id
    hnf (intoBnd e)       = into (nil ▹ bnd (hnf e))
    entries (bnd m e)     = entries m ▹ bnd (hnf e)

Composition `F ∘ G` (`Form.combine`), new clauses, placed before the catch-all `F, _ => some F` and after the `id`, `bot`,
`top` clauses that exist now (keep the existing order for the existing clauses):

    F ∘ into Es               = into (map Es: bnd G ↦ bnd (F ∘ G))            for every F (after the bot/top clauses)
    bnd i F ∘ G               = bnd i (F ∘ G)
    obj Es ∘ bnd i F          = G ∘ F      where Es.get? i = some (bnd G);  none otherwise
    into Es ∘ bnd i F         = G ∘ F      where Es.get? i = some (bnd G);  none otherwise
    obj Es₁ ∘ obj Es₂         = obj (Es₂ routed through Es₁)   as now; a bnd G entry of Es₂ routes to bnd (obj Es₁ ∘ G)
    into Es₁ ∘ obj Es₂        = into (Es₂ routed through into Es₁): every entry of Es₂ must be bnd G, becoming bnd (into Es₁ ∘ G); none otherwise
    eqv φ ∘ bnd i F = bnd i F ;  eqv φ ∘ into Es = into Es ;  into Es ∘ eqv φ = into Es

Adjust the `termination_by` measures of the mutual block (`Entry.through` needs `sizeOf Es₁ + sizeOf E + 1` or
similar) so that the calls into `Form.combine` from bound entries decrease.

Pairing `Form.pair Tel₁ Tel₂ F G`: bot rules as now; `top`/`top` as now; if both components are `into`/`top`, the result is
`into (es F ++ es G)` with `es top = nil`, `es (into Es) = Es`; otherwise `obj (toEntries' Tel₁ F ++ toEntries' Tel₂ G)`
where `toEntries' Tel (into Es) = some Es` and the other cases are `Form.toEntries` as now.  `Telescope.identityEntries`
gets the clause `identityEntries (Tel ▹ bnd _) = identityEntries Tel ▹ bnd (Form.bnd Tel.length id)`.

Views.  Move `closedAtomForm` into the mutual normalizer block.  `Entry.at` takes the chain form `C` of the atom whose
view is being computed: `Entry.at C V (bnd G) = some (PropForm.bnd (C ∘ G))`, the other entries ignore `C`.
`entriesAt C V Es` likewise.  `viewThrough σ (n+1) F a`:

    id / eqv φ     : view σ n a
    obj Es         : do V ← view σ n a; (_, C) ← closedAtomForm σ n a; entriesAt C V Es
    into Es        : the same (only bnd entries occur; V is not consulted)
    bnd i F        : do V ← view σ n a; some (.bnd G) ← V.get? i; viewThrough σ n (G ∘ F) (.var a.root)
    pi / top / bot : some .nil

`view`, `hasView`, `member` as now.  The precise view of a literal is unchanged (no bound entries).

## 4. Typedness of forms (FormTyping.lean, FormAlgebra.lean)

Reintroduce a root mode: `FormTyped (Γ : Ctx s) (ρ : Option (BVar s .var)) : Form s → Ty s → Ty s → Prop`, with shapes
read through `Ctx.resolveAt? Γ ρ T := match ρ with | none => Γ.resolve T | some r => Γ.resolveAt r T` (`resolveAt r T =
(Γ.resolve T).unfoldAt r` as now; `unfoldAt` stays syntactic and leaves bound propositions untouched).  Plain typedness
is mode `none`, chain typedness is mode `some r`:

    Γ ⊨ F : S ≤ T      :=  FormTyped Γ none F S T           Γ ⊨[r] F : S ≤ T  :=  FormTyped Γ (some r) F S T

so `ChainTyped` becomes the `some r` mode of the one inductive (keep both notations and all existing lemma names).
Every existing rule is stated once with `resolveAt? ρ` in place of `resolve`.  The `obj` rule types entries at mode ρ:
`EntriesTyped Γ ρ Tel₁ Es Tel₂`, where for ρ = some r the telescopes are the opened ones (this is exactly what
`FormTyped.atRoot` produces today).  New rules:

    FormTyped.bnd   : resolveAt? ρ S = μ Tel → Tel ∋ (i ↦ bnd T↑) → FormTyped Γ ρ F T U → FormTyped Γ ρ (bnd i F) S U
    FormTyped.into  : resolveAt? ρ T = μ Tel → BndsTyped Γ ρ S Es Tel → FormTyped Γ ρ (into Es) S T
        with  BndsTyped Γ ρ S .nil .nil   and   BndsTyped Γ ρ S Es Tel → FormTyped Γ ρ F S T → BndsTyped Γ ρ S (Es ▹ bnd F) (Tel ▹ bnd T↑)
    EntriesTyped.bnd: EntriesTyped Γ ρ Tel₁ Es Tel₂ → FormTyped Γ ρ G (μ Tel₁) T → EntriesTyped Γ ρ Tel₁ (Es ▹ bnd G) (Tel₂ ▹ bnd T↑)
    ViewTyped.bnd   : Γ ⊨[r, σ] V : Tel → FormTyped Γ (some r) G (Γ.lookupTy r) T → Γ ⊨[r, σ] V ▹ .bnd G : Tel ▹ bnd T↑

(The `le` view rule keeps typing its form at mode `none` at the instantiated types, as now.)  Lemmas, all mode-generic
where they were plain: `FormTyped.srcRes`, `tgtRes`, `FormTyped.atRoot : Γ ⊨ F : S ≤ T → Γ ⊨[r] F : S ≤ T` (by mutual
induction with `EntriesTyped.open`; the bound cases are the induction hypothesis on the sub-form), `Form.combine_typed`
(one proof, mode-generic, with the new cases), `EntriesTyped.through`, `Form.pair_typed`, `entriesAt_typed` (now with the
chain `C` typed `Γ ⊨[r] C : Γ.lookupTy r ≤ S` as a hypothesis), `viewThrough_typed` (obtains `C` from the new
`closedAtomForm` in the same fuel), `normalizer_succ`/monotonicity/determinism with the new clauses.

## 5. Canonical forms and corollaries (CanonicalForms.lean, Progress.lean, Consistency.lean, Preservation.lean)

`atom_canon` and `closedAtomForm_typed` are proven together (the view of a cast atom needs the chain of the atom).  New
cases: `bound` (form `bnd i id`), `intoBnd` (form `into [bnd F]`), `Morphism.bnd` (entry `bnd F`), `viewThrough` for
`bnd`/`into`.  Keep the statements of `le_canon`, `eq_canon`, `has_canon`, `mor_canon`, `atom_canon`,
`closedAtomForm_typed`, `preservation'`, `progress`, `not_stuck`, `erase_step`, `erase_reflect'`,
`reachable_consistent`, `checkTm_iff`, `Store.Typed.no_top_le_bot`, `closed_pi_inversion`, `closed_has_field`,
`Store.Typed.realized` exactly.  `closed_le_shapes` gains two disjuncts (the source resolves to an object type with a
bound whose type is below the target; the target resolves to a bounds-only object type); `no_obj_le_pi` becomes "from an
object type without bound propositions"; `no_pi_le_obj` becomes "into an object type with a proposition that is not a
bound".  `closedAtomForm_pi` keeps its statement: the root's type is the precise type of a literal or a function type,
neither has a bound, so the chain of a function atom is still `id`, a conversion, or `pi`.

## 6. DOT-MNF and the translation (DotMNF/*, DotToFCdot/*)

Source: drop the `Ty.Decl` premises of `Sub.and1`, `Sub.and2`, `Sub.and`, `HasTy.andI`, and of `Ty.Wf.and`.  Keep
`Ty.Decl` (it stays the premise of `Wf.mu`, `Rec-I`, `Rec-E`) and add a decidable `Ty.isDecl : Ty s → Bool` agreeing
with it.  Update the docstrings that describe the fragment.

Translation.  `Ty.tel` of a non-declaration operand: `tel B = .nil ▹ .bnd B.translate↑` for `B` a selection, a function
type, or `⊥` (so `tel` is total: declaration-shaped types as now, everything else a single bound).  `Ty.telSelf` likewise
with `.bnd B.translate` (no weakening: `B : Ty (s,x)`; `Wf.mu` keeps such bodies out, but the function is total).
`Ty.translate (.and S T) = μ (tel S ++ tel T)` as now.  Note `⟦B⟧ ≠ μ (tel B)` for a non-declaration `B`; the lemma
`Ty.translate_decl` stays as it is, and a new lemma states `tel B = .nil ▹ .bnd ⟦B⟧↑` for the other shapes.

Evidence (`Sub.translate`), with `into T d := if T.isDecl then d else .intoBnd d` for `d : ⟦S⟧ ≤ ⟦T⟧`:

    And₁ : S ∧ T <: S   ↦  if S.isDecl then obj (tel (S ∧ T)) (idMor 0 (tel S))  (as now, idMor extended: a bound at
                           position j of the source is copied by `Morphism.bnd _ (bound src j)`, so idMor takes `src`)
                           else bound (tel (S ∧ T)) 0
    And₂                ↦  symmetric, offset (tel S).length
    And d₁ d₂ : S <: T ∧ U ↦  pair (tel T) (tel U) (into T d₁) (into U d₂)
    And-I h₁ h₂         ↦  both (tel T) (tel U) (into' T h₁) (into' U h₂)   with into' T a := if T.isDecl then a else cast a (intoBnd (refl ⟦T⟧))

`Rec-I`, `Rec-E`, `Sel-<:`, `<:-Sel`, `Typ`, `Fld`, `All`, `Var`, terms, literals: unchanged.  Typedness proofs
(`Sub.translate_typed`, `HasTy.translateAtom_typed` with its root conjunct, `HasTy.translate_typed`), erasure
(`HasTy.translate_erase`, `coherence`), `dot_safety`, `reachable_consistent`, `reachable_realized` keep their statements.

## 7. Examples

E8, on both sides, the acceptance test: the refinement of an abstract type and a selection through it.

    λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a        typed at  ∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : ⊤}) ⊤

DOT-MNF: `y : x.A ∧ {a : ⊤}` by Var, `y : {a : ⊤}` by And₂, then {}-E.  Also a second derivation of the same term that
goes the other way: `y : x.A` by And₁, `x.A <: {a : ⊤}` by Sel-<:, so `y : {a : ⊤}` by Sub, then {}-E.  And-I: from
`y : x.A` and `y : {a : ⊤}` derive `y : x.A ∧ {a : ⊤}` (a derivation, not necessarily a closed program).
FCdot: the translations of both derivations as terms, `checkTm … = true` by `decide +kernel`, `HasType` via
`checkTm_sound`, and `E8_erase : E8.erase = E8src.erase := rfl`.  Register E8 in both README module tables.

## 8. Deliverables

Green `lake build` of all default targets; `#print axioms` on the theorems named in the READMEs (report the exact
lists); a patch of the whole change; a report of every statement whose shape changed and why, every new lemma, and
anything in this spec that turned out wrong (say what you did instead).  Update the four READMEs (`Coercions`, `FCdot`,
`DotMNF`, `DotToFCdot`) and the plan's §13 decision log (`plan-3-dot-mnf-to-fcdot.md`) in the same patch.
