import Coercions.Paths.FCdot.CheckerCompleteness
import Coercions.Paths.FCdot.Preservation
import Coercions.Paths.FCdot.FormTyping

namespace Paths

/-!
# Refutation of write-up A, scratch 1: the chain form of `sngl` is not the identity

Outside the import graph, against the g6 tree.

Write-up A (section 1.4) says that `closedAtomForm` and `pathChainForm` treat
`.sngl` as they treat `.foldSelf`, "the wrapper is invisible to the chain", and
that "no bound entry is ever read at a singleton telescope, so the chain form is
never consulted there".  Section 1.2 deletes `Entry.aliasTo` and its three
typing clauses.

Both claims fail on one atom.  A bound entry *out of* the singleton type is
produced by `Morphism.bnd m e` with `e : μ [≈ q↑] ≤ T` (`Typing.lean:158-159`),
and the view of the cast atom then carries `bnd (C.combine G)` where `C` is the
chain of the atom under the cast (`Normalizer.lean:619`, the `.bnd` clause of
`Entry.at`).  If the chain of a `sngl` atom is the identity, the view entry is
`bnd G` with `G` typed from the singleton, and `ViewTyped.bnd`
(`FormTyping.lean:328-330`) asks for it to be typed from `Γ.lookupTy root`.  It
is not: the root's type is a literal's type, and the singleton is not
resolution-equal to it at the root.

In the g6 tree the same atom is written with `intoSngl`, whose head form is
`into [aliasTo x x]` (`Normalizer.lean:678`), the chain composes it in
(`Form.combine`, `:424,:436`), and the view entry `bnd (into [aliasTo x x])` is
typed by `FormTyped.into` and `BndsTyped.aliasTo` (`FormTyping.lean:265`).
So `aliasTo` is exactly the chain form the `sngl` step needs, and deleting it
leaves `atom_canon` (T1's `cast` case) with no proof at this atom.

Checked here:
* `aB_typed`: the atom is typed in the g6 tree.
* `g6_view_typed`: the view the g6 normalizer gives it, `[bnd (into [aliasTo x x])]`,
  is typed against `[⊑ (μ [≈ x↑])↑]` at the root.
* `writeup_view_not_typed`: the view write-up A's clauses give it,
  `[bnd (eqv (refl _))]`, is not.
* `sngl_chain_typed`: the general fact that `into [aliasTo P.path q]` is the typed
  chain form of a `sngl` step, from the block equality T2 gives.
-/

namespace FCdot
namespace ScratchSnglChain

/-- The store: one literal `ν(x. {})`, whose type is `⊤ = μ .nil`. -/
def vE : Value [] := .obj .nil .nil
def TE : Ty [] := μ (Telescope.ofLiteral (Witnesses.nil (s := ([],x))) [] [])
def σE : Store ([],x) := .cons .nil vE
def ΓE : Ctx ([],x) := Ctx.nil.cons (.transparent TE (vE.weaken.blocksAt (.var .here)))

theorem vE_typed : Ctx.nil ⊢ᵥ vE : TE := Value.HasType.obj .nil
theorem σE_typed : ⊢ σE : ΓE := Store.Typed.cons .nil trivial vE_typed

def xv : BVar ([],x) .var := .here
def xP : Path ([],x) := .var xv

/-- The singleton of `x`, `μ [≈ x↑]`. -/
def sx : Ty ([],x) := .obj (.nil ▹ .alias xP.weaken)

/-- The atom `x` at its singleton.  In the g6 tree this is written with
`intoSngl`; under write-up A it is `Atom.sngl (.var x) x (.refl x)`, with the
same type. -/
def aS : Atom ([],x) := .cast (.var xv) (.intoSngl (.var xv) xP (.refl xP))

example : synthAtom ΓE aS = some sx := by decide +kernel

/-- A coercion out of the singleton into a bounds-only object type, whose one
bound is proven by `refl` at the singleton: `μ [≈ x↑] ≤ μ [⊑ (μ [≈ x↑])↑]`. -/
def eB : LeCo ([],x) := .obj (.nil ▹ .alias xP.weaken) (.bnd .nil (.refl sx))

/-- The bounds-only target. -/
def TB : Ty ([],x) := .obj (.nil ▹ .bnd sx.weaken)

example : synthLe ΓE eB = some (sx, TB) := by decide +kernel

/-- The atom whose view reads a bound entry produced *from* the singleton. -/
def aB : Atom ([],x) := .cast aS eB

theorem aB_typed : ΓE ⊢ₐ aB : TB := checkAtom_sound (by decide +kernel)

/-! ## The g6 tree: the chain carries `into [aliasTo x x]`, and the view is typed -/

/-- The chain of `aS` in the g6 tree is the `into` form of the `intoSngl` step. -/
theorem aS_chain : closedAtomForm σE 4 aS = some (aS, .into (.nil ▹ .aliasTo xP xP)) := by
  simp [closedAtomForm, hnf, Form.combine, aS, PathCo.path, xP]

/-- The view of `aB` in the g6 tree. -/
theorem aB_view :
    view σE 6 aB
      = some (View.nil ▹ PropForm.bnd (Form.into (Entries.nil ▹ Entry.aliasTo xP xP))) := by
  simp [view, viewThrough, hnf, entries, closedAtomForm, Form.combine, entriesAt, Entry.at, aB, aS,
    eB, sx, σE, Store.lookup, vE, Value.weaken, Value.rename, Value.precView, Witnesses.eqForms,
    Fields.hasForms, Fields.hasValForms, Fields.labels, Fields.valLabels, Witnesses.rename,
    Fields.rename, PathCo.path, xP, Atom.root, xv]

/-- That view is typed at the root against the bounds-only telescope: the bound
entry is `FormTyped.into` with `BndsTyped.aliasTo`, whose condition is the
block equality `lookupBlock x = lookupBlock x`. -/
theorem g6_view_typed :
    ViewTyped ΓE xP σE (View.nil ▹ PropForm.bnd (Form.into (Entries.nil ▹ Entry.aliasTo xP xP)))
      (Telescope.nil ▹ Proposition.bnd sx.weaken) := by
  refine .bnd .nil ?_
  refine FormTyped.into ?_ (BndsTyped.aliasTo .nil rfl)
  decide +kernel

/-! ## Write-up A: the chain is `id`, the view entry is `bnd (eqv (refl sx))`, untyped

Trace of write-up A's clauses (section 1.4) on `aB` with `aS` read as
`Atom.sngl (.var x) x (.refl x)`:

* `closedAtomForm (.sngl a q α)` "as `.foldSelf`": the chain is that of `a`,
  and `closedAtomForm (.var x) = (.var x, .id)` (`Normalizer.lean:768`).
* `view (.sngl _ q _) = [.alias q]` (write-up A, 1.4).
* `viewThrough (.obj Es) a` (`Normalizer.lean:725-728`): `entriesAt` with `C = .id`
  over `Es = [.bnd (.eqv (.refl sx))]`, since `hnf eB = .obj [.bnd (hnf (.refl sx))]`
  and `hnf (.refl T) = .eqv (.refl T)` (`:648`).
* `Entry.at _ _ C _ (.bnd G) = (C.combine G).map .bnd` (`:619`) with
  `Form.combine .id G = G` (`:424`): the entry is `.bnd (.eqv (.refl sx))`.

So write-up A's view of `aB` is `[.bnd (.eqv (.refl sx))]`.  It is not typed. -/

theorem writeup_view_not_typed :
    ¬ ViewTyped ΓE xP σE (View.nil ▹ PropForm.bnd (Form.eqv (.refl sx)))
      (Telescope.nil ▹ Proposition.bnd sx.weaken) := by
  intro h
  cases h with
  | bnd _ hF =>
      cases hF with
      | eqv heq =>
          revert heq
          decide +kernel

/-- The two facts in one line: the view the g6 normalizer computes is typed and
the view write-up A's clauses compute is not, at one typed atom over one typed
store. -/
theorem chain_form_matters :
    (ViewTyped ΓE xP σE (View.nil ▹ PropForm.bnd (Form.into (Entries.nil ▹ Entry.aliasTo xP xP)))
      (Telescope.nil ▹ Proposition.bnd sx.weaken)) ∧
    ¬ ViewTyped ΓE xP σE (View.nil ▹ PropForm.bnd (Form.eqv (.refl sx)))
      (Telescope.nil ▹ Proposition.bnd sx.weaken) :=
  ⟨g6_view_typed, writeup_view_not_typed⟩

/-! ## The repair: keep `aliasTo` as the chain form of a `sngl` step -/

/-- The singleton object type of a path. -/
def Ty.snglOf (q : Path s) : Ty s := .obj (.nil ▹ .alias q.weaken)

/-- The chain form of `sngl P q α`, typed at the root `P.path` from any source
type, given the block equality that T2 provides for `α`.  This is what
`closedAtomForm`/`pathChainForm` must compose in at a `sngl` wrapper, and it
is `Entry.aliasTo` with `BndsTyped.aliasTo`, the two things write-up A
deletes. -/
theorem sngl_chain_typed {Γ : Ctx s} {P : PathCo s} {q : Path s} {S : Ty s}
    (h : Γ.lookupBlock P.path = Γ.lookupBlock q) :
    FormTyped Γ (some P.path) (.into (.nil ▹ .aliasTo P.path q)) S (Ty.snglOf q) := by
  refine FormTyped.into ?_ (BndsTyped.aliasTo .nil h)
  simp only [Ctx.resolveAt?, Ctx.resolveAt, Ty.snglOf, Ctx.resolve_obj, Ty.unfoldAt_obj,
    Telescope.substPath_cons, Proposition.substPath_alias, Path.weaken_substPath,
    Telescope.weaken_cons, Proposition.weaken_alias]
  rfl

/-! ## A side remark on write-up A's proof sketch 2.3

The sketch says `unfoldSelf` gives `[≈ q↑]` only from `[≈ q↑]`, "the telescope
opened at the root is the telescope".  It does not: `unfoldSelf` gives the
closed singleton `μ [≈ x↑]` from the self-mentioning `μ [≈ self]`, so the
canonical fact cannot be proved by an induction on the closed shape alone and
must go through `atom_canon`'s typed view at every resolved telescope.  A
proof-shape defect, not a falsity. -/

/-- `μ [≈ self]`. -/
def TelSelf : Telescope (([],x),x) := .nil ▹ .alias (.var .here)

def aFold : Atom ([],x) := .foldSelf TelSelf aS
def aUnfold : Atom ([],x) := .unfoldSelf aFold

example : synthAtom ΓE aFold = some (.obj TelSelf) := by decide +kernel
example : synthAtom ΓE aUnfold = some sx := by decide +kernel

#print axioms aB_typed
#print axioms aS_chain
#print axioms aB_view
#print axioms g6_view_typed
#print axioms writeup_view_not_typed
#print axioms chain_form_matters
#print axioms sngl_chain_typed

end ScratchSnglChain
end FCdot

end Paths
