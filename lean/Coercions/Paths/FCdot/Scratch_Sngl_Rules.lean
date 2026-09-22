import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.FCdot.Preservation
import Coercions.Paths.FCdot.FormTyping

namespace Paths

/-!
# Scratch 3: the repaired rules, as this refutation would keep them

Outside the import graph, against the g6 tree.  The g6 inductives cannot gain
constructors from here, so each new rule is a standalone judgment over the g6
terms, as write-up A's `Scratch_A_Rules` did.  What is new against that file:

* `sngl_chain_typed`: the chain form of a `sngl` step is `into [aliasTo P.path q]`,
  typed from any source at the root `P.path` by the block equality.  Closed.
  `Entry.aliasTo`, `EntryTyped.aliasTo`, `BndsTyped.aliasTo` and
  `EntriesTyped.aliasTo` therefore stay (write-up A deletes them).
* `atom_sngl_block_of_T2`: the canonical fact reduces to T2 at one alias.  Closed.
* `preservation_rename_letPath`: the `rename` case of preservation under the
  `letPath` frame, closed from the substitution lemma `substAtom_fwd`.
* `preservation_alloc_letPath`: the `alloc` case, closed from `value_not_sngl`.
* The statements a later group proves carry `-- SORRY:` marks: `alias_blocks`
  (T2 over a typed store), `substAtom_fwd`, `value_not_sngl`, `lookupBlock_sel`.
  Section 6 of write-up A is *not* prototyped: scratch 2 refutes its budget claim.
-/

namespace FCdot
namespace ScratchSnglRules

/-- The singleton object type of a path: `μ [≈ q↑]`. -/
def Ty.snglOf (q : Path s) : Ty s := .obj (.nil ▹ .alias q.weaken)

/-! ## (1) Introduction at a path and at an atom -/

/-- `PathCo.HasType.sngl`, in place of `LeCo.HasType.intoSngl`. -/
inductive SnglPath : Ctx s → PathCo s → Path s → AliasCo s → Ty s → Prop where
  | sngl : Γ ⊢ᵖ P : S → Γ ⊢ α : P.path ≋ q → SnglPath Γ P q α (Ty.snglOf q)

/-- `Atom.HasType.sngl`. -/
inductive SnglAtom : Ctx s → Atom s → Path s → AliasCo s → Ty s → Prop where
  | sngl : Γ ⊢ₐ a : S → Γ ⊢ α : (Path.var a.root) ≋ q → SnglAtom Γ a q α (Ty.snglOf q)

/-- The alias a singleton licenses, read off the type by `AliasCo.member`. -/
theorem alias_of_sngl {Γ : Ctx s} {P : PathCo s} {q : Path s}
    (hP : Γ ⊢ᵖ P : Ty.snglOf q) :
    Γ ⊢ .member P (.refl (Ty.snglOf q)) 0 : P.path ≋ q := by
  have h := AliasCo.HasType.member hP (LeCo.HasType.refl (T := Ty.snglOf q))
    (Telescope.At.here (Tel := .nil) (P := .alias q.weaken))
  simpa [Telescope.length, Path.weaken_substPath] using h

/-- The checker clause, as a function: both annotations are checked against
the synthesised alias. -/
def synthSngl (Γ : Ctx s) (P : PathCo s) (q : Path s) (α : AliasCo s) :
    Option {T : Ty s // SnglPath Γ P q α T} := do
  let cP ← synthPathCore Γ P
  let cα ← synthAliasCore Γ α
  if h1 : cα.source = P.path then
    if h2 : cα.target = q then
      some ⟨Ty.snglOf q, .sngl cP.typing (by rw [← h1, ← h2]; exact cα.typing)⟩
    else none
  else none

/-! ## (2) The chain form of a `sngl` step: `aliasTo` stays -/

/-- The view of `sngl P q α`, typed at the root against the singleton telescope,
from the block equality. -/
theorem sngl_view_typed {σ : Store s} {Γ : Ctx s} {P : PathCo s} {q : Path s}
    (h2 : Γ.lookupBlock P.path = Γ.lookupBlock q) :
    ViewTyped Γ P.path σ (.nil ▹ .alias q) (.nil ▹ .alias q.weaken) := by
  have h := ViewTyped.alias (q := q.weaken) (ViewTyped.nil (Γ := Γ) (r := P.path) (σ := σ))
    (by rw [Path.weaken_substPath]; exact h2)
  simpa [Path.weaken_substPath] using h

/-- The chain form of a `sngl` step: `into [aliasTo P.path q]`, typed at the
root from any source type, by `FormTyped.into` and `BndsTyped.aliasTo`.  This
is what `closedAtomForm`/`pathChainForm` compose in at a `sngl` wrapper
(scratch 1 shows the identity is wrong there). -/
theorem sngl_chain_typed {Γ : Ctx s} {P : PathCo s} {q : Path s} {S : Ty s}
    (h : Γ.lookupBlock P.path = Γ.lookupBlock q) :
    FormTyped Γ (some P.path) (.into (.nil ▹ .aliasTo P.path q)) S (Ty.snglOf q) := by
  refine FormTyped.into ?_ (BndsTyped.aliasTo .nil h)
  simp only [Ctx.resolveAt?, Ctx.resolveAt, Ty.snglOf, Ctx.resolve_obj, Ty.unfoldAt_obj,
    Telescope.substPath_cons, Proposition.substPath_alias, Path.weaken_substPath,
    Telescope.weaken_cons, Proposition.weaken_alias]
  rfl

/-! ## (3) T2 over a typed store, and the canonical fact -/

/-- T2, over a typed store.  Without `hσ` it is false (`ScratchA.t2_without_store_false`). -/
theorem alias_blocks {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) {α : AliasCo s} {p q : Path s}
    (h : Γ ⊢ α : p ≋ q) : Γ.lookupBlock p = Γ.lookupBlock q := by
  sorry -- SORRY: g8, by induction on `h`, mutual with T1 at the `member` case

/-- The two table cases of T2, closed. -/
theorem alias_blocks_fwd {Γ : Ctx s} {p q : Path s} {B : Block s}
    (hp : Γ.lookupBlock p = some B) (hq : Γ.lookupBlock q = some B) :
    Γ.lookupBlock p = Γ.lookupBlock q := hp.trans hq.symm

/-- The `sel` case of T2 needs the walk to commute with one field step.  Its
forwarding case is `blockFuel_budget` one way and the gap argument the other. -/
theorem lookupBlock_sel (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.lookupBlock (.sel p a) =
      ((Γ.lookupBlock p).bind fun B => B.childAt? a).bind fun b =>
        match b with
        | .fwd r => Γ.lookupBlock r
        | b => some b := by
  sorry -- SORRY: g8, `Context.lean`, beside `blockFuel_eq_lookupBlock`

/-- **The canonical fact reduces to T2.**  Over a typed store, an atom typed at
the singleton of `q` is rooted at the block of `q`.  Closed from T2 at the one
alias `member a.toPathCo (refl _) 0`. -/
theorem atom_sngl_block_of_T2 {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    (hT2 : ∀ {α : AliasCo s} {p q : Path s}, Γ ⊢ α : p ≋ q → Γ.lookupBlock p = Γ.lookupBlock q)
    {a : Atom s} {q : Path s} (h : Γ ⊢ₐ a : Ty.snglOf q) :
    Γ.lookupBlock (.var a.root) = Γ.lookupBlock q := by
  have hα := alias_of_sngl (PathCo.HasType.ofAtom h)
  rw [Atom.path_toPathCo] at hα
  exact hT2 hα

/-! ## (4) The let over a path -/

/-- The forwarding binder of a let over a path, typed at the singleton. -/
def Binding.fwdAt (q : Path s) : Binding s := .transparent (Ty.snglOf q) (.fwd q.weaken)

theorem fwdAt_not_transparent (Γ : Ctx s) (q : Path s) :
    ¬ (Γ.cons (Binding.fwdAt q)).IsTransparent .here := by
  simp [Ctx.IsTransparent, Binding.fwdAt]

/-- `Tm.HasType.letPath`. -/
inductive LetPath : Ctx s → Tm s → Ty s → Prop where
  | letPath :
      Γ ⊢ t : Ty.snglOf q →
      Γ.cons (Binding.fwdAt q) ⊢ u : U↑ →
      LetPath Γ (.let t u) U

/-- `Cont.Typed.letPath`, the singleton as the incoming type. -/
inductive ContLetPath : Ctx s → Cont s → Ty s → Ty s → Prop where
  | letPath :
      Γ.cons (Binding.fwdAt q) ⊢ u : U↑ →
      Γ ⊢ₖ K : U ⇒ V →
      ContLetPath Γ (K ▹ .let u) (Ty.snglOf q) V

/-- The let over a field declared at a singleton. -/
theorem letPath_of_field {Γ : Ctx s} {x : BVar s .var} {a : Label} {h : Has s}
    {q : Path s} {u : Tm (s,x)} {U : Ty s}
    (hx : Γ ⊢ₐ .var x : Γ.lookupTy x) (hh : Γ ⊢ h : (Path.var x) ∋ a)
    (hdef : Γ.lookupDefP (.var x) a = some (Ty.snglOf q))
    (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U↑) :
    LetPath Γ (.let (.cast (.proj (.var x) a h) (.eqToLe (.defP (.var x) a))) u) U :=
  .letPath (.cast (.proj hx hh) (.eqToLe (.defP hdef))) hu

/-- The substitution lemma at a forwarding binder, over a typed store, with the
incoming type the singleton.  (g6 refuted the version with the incoming type
free, `forwarding_subst_false`.) -/
theorem substAtom_fwd {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) {q : Path s} {u : Tm (s,x)}
    {U : Ty (s,x)} {a : Atom s}
    (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U) (ha : Γ ⊢ₐ a : Ty.snglOf q) :
    Γ ⊢ u.substAtom a : U⟦a.root⟧ := by
  sorry -- SORRY: g7/g8, `Tm.HasType.subst` over a `Subst.Typed` whose block field is `lookupB`

/-- No value is typed at a singleton, over a typed store. -/
theorem value_not_sngl {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) {v : Value s} {q : Path s}
    (hv : Γ ⊢ᵥ v : Ty.snglOf q) : False := by
  sorry -- SORRY: g8, `coreDecomp`, `le_canon`, and: `hnf` never produces `aliasTo`, and no
        -- closed form out of an alias-free telescope reaches an alias entry

/-- The `rename` case of preservation under a `letPath` frame, closed from the
substitution lemma. -/
theorem preservation_rename_letPath {σ : Store s} {Γ : Ctx s} {K : Cont s} {u : Tm (s,x)}
    {q : Path s} {T V : Ty s} {a : Atom s}
    (hσ : ⊢ σ : Γ) (ha : Γ ⊢ₐ a : Ty.snglOf q) (hK : ContLetPath Γ (K ▹ .let u) T V)
    (hT : T = Ty.snglOf q)
    (hsub : ∀ {u : Tm (s,x)} {U : Ty (s,x)},
      Γ.cons (Binding.fwdAt q) ⊢ u : U → Γ ⊢ u.substAtom a : U⟦a.root⟧) :
    ∃ T, Γ ⊢ u.substAtom a : T ∧ Γ ⊢ₖ K : T ⇒ V := by
  cases hK with
  | @letPath _ _ _ _ _ q' hu hK' =>
      have hq : q' = q := by
        have h1 : q'.weaken (k := .var) = q.weaken (k := .var) := by
          simp only [Ty.snglOf, Ty.obj.injEq, Telescope.cons.injEq, Proposition.alias.injEq,
            true_and] at hT
          exact hT
        have h2 := congrArg (fun p : Path (s,x) => p.substPath q) h1
        simpa [Path.weaken_substPath] using h2
      subst hq
      exact ⟨_, by simpa using hsub hu, hK'⟩

/-- The `alloc` case of preservation under a `letPath` frame is vacuous. -/
theorem preservation_alloc_letPath {σ : Store s} {Γ : Ctx s} {K : Cont s} {u : Tm (s,x)}
    {q : Path s} {V : Ty s} {v : Value s}
    (hσ : ⊢ σ : Γ) (hv : Γ ⊢ᵥ v : Ty.snglOf q) (hK : ContLetPath Γ (K ▹ .let u) (Ty.snglOf q) V)
    (hns : ∀ {v : Value s}, Γ ⊢ᵥ v : Ty.snglOf q → False) :
    State.Typed ⟨.cons σ v.core, K↑, u.adjust v⟩ V↑ :=
  absurd hv hns

/-! ## (5) Images of the seven source rules (as write-up A gives them, re-elaborated) -/

theorem sngl_refl {Γ : Ctx s} {P : PathCo s} {S : Ty s} (hP : Γ ⊢ᵖ P : S) :
    SnglPath Γ P P.path (.refl P.path) (Ty.snglOf P.path) :=
  .sngl hP .refl

theorem snglTrans_image {Γ : Ctx s} {P Q : PathCo s} {q : Path s} {T : Ty s}
    (hP : Γ ⊢ᵖ P : Ty.snglOf q) (hQ : Γ ⊢ᵖ Q : T) (hq : Q.path = q) :
    Γ ⊢ᵖ .alias (.member P (.refl (Ty.snglOf q)) 0) P.path Q : T :=
  .alias (by rw [hq]; exact alias_of_sngl hP) hQ

theorem snglSym_image {Γ : Ctx s} {P Q : PathCo s} {q : Path s} {T : Ty s}
    (hP : Γ ⊢ᵖ P : Ty.snglOf q) (hQ : Γ ⊢ᵖ Q : T) (hq : Q.path = q) :
    SnglPath Γ Q P.path (.symm (.member P (.refl (Ty.snglOf q)) 0)) (Ty.snglOf P.path) :=
  .sngl hQ (by rw [hq]; exact .symm (alias_of_sngl hP))

/-- `snglInv`: the second premise of write-up A's image is the first. -/
theorem snglInv_image {Γ : Ctx s} {P : PathCo s} {q : Path s}
    (hPs : Γ ⊢ᵖ P : Ty.snglOf q) :
    Γ ⊢ᵖ .cast (.alias (.symm (.member P (.refl (Ty.snglOf q)) 0)) q P) (.top (Ty.snglOf q)) : ⊤ :=
  .cast (.alias (.symm (alias_of_sngl hPs)) hPs) .top

theorem snglSel_image {Γ : Ctx s} {P : PathCo s} {q : Path s} {Tel : Telescope (s,x)}
    {a : Label} {i : Nat}
    (hPs : Γ ⊢ᵖ P : Ty.snglOf q) (hP : Γ ⊢ᵖ P : μ Tel) (hAt : Tel ∋ (i ↦ ∋ᵛ a)) :
    SnglPath Γ (.sel P a i) (.sel q a) (.sel (.member P (.refl (Ty.snglOf q)) 0) a)
      (Ty.snglOf (.sel q a)) :=
  .sngl (.sel hP hAt) (.sel (alias_of_sngl hPs))

theorem trmSngl_image {Γ : Ctx (s,x)} {y : BVar (s,x) .var} {a : Label}
    (hdef : Γ.lookupDef .here a = some (Ty.snglOf (.var y))) :
    SnglAtom Γ (.var y) (.var y) (.refl (.var y)) (Ty.snglOf (.var y)) ∧
    Γ ⊢ .eqToLe (.symm (.def .here a)) : Ty.snglOf (.var y) ≤ (Path.var .here) ∙ a :=
  ⟨.sngl .var .refl, .eqToLe (.symm (.def hdef))⟩

#print axioms alias_of_sngl
#print axioms sngl_view_typed
#print axioms sngl_chain_typed
#print axioms alias_blocks_fwd
#print axioms atom_sngl_block_of_T2
#print axioms fwdAt_not_transparent
#print axioms letPath_of_field
#print axioms preservation_rename_letPath
#print axioms preservation_alloc_letPath
#print axioms sngl_refl
#print axioms snglTrans_image
#print axioms snglSym_image
#print axioms snglInv_image
#print axioms snglSel_image
#print axioms trmSngl_image

end ScratchSnglRules
end FCdot

end Paths
