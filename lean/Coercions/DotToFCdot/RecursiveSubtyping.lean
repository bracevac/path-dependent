import Coercions.DotToFCdot.EvidenceTyped
import Coercions.DotMNF.WadlerFest.LabelSorted
import Coercions.FCdot.Checker
import Coercions.FCdot.Normalizer

/-!
# Experimental coercions for recursive subtyping

Two bounded recursive-subtyping principles already have evidence in FCdot:

* project a self-independent component out of a recursive intersection;
* retain a declaration-shaped component under its recursive binder.

These are explicit target coercions, not new constructors of source `Sub`.
The final example uses finite composition of source-fact templates to
translate a recursive coercion whose opened-self premise composes two
facts about the same receiver. It also checks the resulting view at a
closed, allocated object. This does not establish general BINDX.
-/

namespace DotMNF.RecursiveSubtyping

open FCdot (Sig LeCo EqCo Side Morphism Atom Telescope Proposition)
open scoped FCdot

/-- Evidence for `mu z. (T & U(z)) <= T`, where `T` does not mention `z`.
An object-shaped result copies its telescope; any other result is recovered
through the recursive source's first bound. -/
def project (T : Ty s) (U : Ty (s,x)) : FCdot.LeCo s :=
  let src := (Ty.and T.weaken U).telSelf
  if T.isObj then .obj src (identityMorphism src 0 T.tel)
  else .bound src 0

theorem project_typed {Γ : FCdot.Ctx s} (T : Ty s) (U : Ty (s,x)) :
    Γ ⊢ project T U : (Ty.mu (.and T.weaken U)).translate ≤ T.translate := by
  rw [project, Ty.translate_mu, Ty.telSelf_and, ← Ty.tel_eq_telSelf_weaken]
  by_cases ho : T.isObj = true
  · rw [if_pos ho, Ty.translate_isObj ho]
    exact .obj (identityMorphism_typed_left _ _ (Ty.tel_closedBnds T))
  · rw [if_neg ho]
    exact .bound ((Ty.tel_bnd_at (by simpa using ho)).append_left' U.telSelf)

/-- Evidence for `mu z. (S(z) & U(z)) <= mu z. S(z)`.
The typedness theorem below requires `S` to be declaration-shaped; its
member types may still mention `z`. -/
def width (S U : Ty (s,x)) : FCdot.LeCo s :=
  let src := (Ty.and S U).telSelf
  .obj src (identityMorphism src 0 S.telSelf)

theorem width_typed {Γ : FCdot.Ctx s} (S U : Ty (s,x)) (hS : Ty.Decl S) :
    Γ ⊢ width S U : (Ty.mu (.and S U)).translate ≤ (Ty.mu S).translate := by
  rw [width, Ty.translate_mu, Ty.translate_mu, Ty.telSelf_and]
  exact .obj (identityMorphism_typed_left _ _ (Ty.telSelf_noBnd_of_decl hS).closedBnds)

/-- Recursive projection below a dependent function codomain. The result
`T` may mention the function parameter, but not the recursive self. -/
def projectCodomain (D : Ty s) (T : Ty (s,x)) (U : Ty (s,x,x)) : FCdot.LeCo s :=
  .pi (.refl D.translate) (project T U)

theorem projectCodomain_typed {Γ : FCdot.Ctx s}
    (D : Ty s) (T : Ty (s,x)) (U : Ty (s,x,x)) :
    Γ ⊢ projectCodomain D T U :
      (Ty.all D (.mu (.and T.weaken U))).translate ≤ (Ty.all D T).translate := by
  rw [projectCodomain, Ty.translate_all, Ty.translate_all]
  exact .pi .refl (project_typed T U)

namespace Chain

private def A : FCdot.Label := .typ 0
private def B : FCdot.Label := .typ 1
private def a : FCdot.Label := .trm 0

/-- `({A : bottom .. self.B} & {B : bottom .. top}) & {a : self.A}`. -/
def source : Ty ([],x) :=
  .and (.and (.typ A .bot (.sel (.var .here) B)) (.typ B .bot .top))
    (.fld a (.sel (.var .here) A))

/-- `{B : bottom .. top} & {a : self.B}`. -/
def target : Ty ([],x) :=
  .and (.typ B .bot .top) (.fld a (.sel (.var .here) B))

/-- A valid opened-self premise for a prospective BINDX rule. Its recursive
conclusion combines `self.a <= self.A` and `self.A <= self.B`. -/
def premise : WadlerFest.Sub (WadlerFest.Ctx.nil.extend source) source target :=
  .and (.trans .and1 .and2)
    (.trans .and2 (.fld (.selUpper (.sub (.sub .var .and1) .and1))))

/-- Every judgment in the premise respects the public source's label discipline. -/
theorem premise_labelSorted : premise.LabelSorted := by
  have hsource : source.LabelSorted :=
    .and (.and (.typ .bot .sel) (.typ .bot .top)) (.fld .sel)
  have hΓ := WadlerFest.Ctx.LabelSorted.nil.extend hsource
  simp only [premise, WadlerFest.Sub.LabelSorted, WadlerFest.HasTy.LabelSorted]
  repeat' first | exact hΓ | constructor

/-- Retain the bounds of `B` and the presence of `a`, then compose the
field upper bound (position 5) with the upper bound of `A` (position 1). -/
def morphism : Morphism [] :=
  .leTrans
    (.has (.le (.le .nil .none (.le 2) .none) .none (.le 3) .none) 4)
    (.le .nil .none (.le 5) .none)
    (.le .nil .none (.le 1) .none)

/-- Evidence for the recursive conclusion of `premise`. -/
def coercion : LeCo [] := .obj source.telSelf morphism

theorem coercion_typed :
    FCdot.Ctx.nil ⊢ coercion : (Ty.mu source).translate ≤ (Ty.mu target).translate := by
  apply FCdot.checkLe_sound
  simp only [coercion, source, target, Ty.translate, Ty.telSelf, Telescope.append]
  decide +kernel

/-- The new normal form contains both source holes; it introduces no
coercion in a context extended with a self assumption. -/
def templates : FCdot.Entries [] :=
  .nil ▹ .le .id (.le 2) .id ▹ .le .id (.le 3) .id ▹ .has 4 ▹
    .trans .id (.le .id (.le 5) .id) (.le .id (.le 1) .id) .id

theorem coercion_normalizes : FCdot.hnf .nil 10 coercion = some (.obj templates) := rfl

/-! ### A closed receiver

The object has `A = (top -> top)`, `B = top`, and an identity-function
field `a`. Its precise-to-source coercion also composes self facts, so
the final cast exercises substitution of composed templates as well as
their interpretation against an existing receiver view.
-/

private def functionType : FCdot.Ty s := .pi .top .top

private def witnesses : FCdot.Witnesses ([],x) :=
  .cons (.cons (.cons .nil A functionType) B .top) a functionType

private def fields : FCdot.Fields ([],x) :=
  .cons .nil a
    (.cast (.val (.lam .top (.atom (.var .here))))
      (.eqToLe (.symm (.def .here a))))

def literal : FCdot.Value [] := .obj witnesses fields

def literalType : FCdot.Ty [] := .obj (Telescope.ofLiteral witnesses fields.labels)

theorem literal_typed : FCdot.Value.HasType FCdot.Ctx.nil literal literalType :=
  FCdot.checkValue_sound (by decide +kernel)

/-- From the precise equalities for `A`, `B`, and `a` to the recursive
source telescope. Each use of `leTrans` combines finite source templates. -/
def literalToSource : LeCo [] :=
  .obj (Telescope.ofLiteral witnesses fields.labels)
    (.leTrans
      (.has
        (.le
          (.le
            (.leTrans
              (.le .nil (.some (.bot functionType)) (.eqSym 0) .none)
              (.le .nil .none (.eq 0) (.some (.top functionType)))
              (.le .nil .none (.eqSym 1) .none))
            (.some (.bot .top)) (.eqSym 1) .none)
          .none (.eq 1) .none)
        3)
      (.le .nil .none (.eq 2) .none)
      (.le .nil .none (.eqSym 0) .none))

theorem literalToSource_typed :
    FCdot.Ctx.nil ⊢ literalToSource : literalType ≤ (Ty.mu source).translate := by
  apply FCdot.checkLe_sound
  simp only [source, Ty.translate, Ty.telSelf, Telescope.append]
  decide +kernel

def store : FCdot.Store ([],x) := .cons .nil literal

def context : FCdot.Ctx ([],x) :=
  .cons .nil (.transparent literalType literal.witnesses literal.fieldLabels)

theorem store_typed : FCdot.Store.Typed store context :=
  .cons .nil trivial literal_typed

def receiver : Atom ([],x) :=
  .cast (.var .here) ((LeCo.trans literalToSource coercion).weaken)

theorem receiver_typed : context ⊢ₐ receiver : (Ty.mu target).translate.weaken := by
  apply FCdot.checkAtom_sound
  simp only [receiver, coercion, source, target, Ty.translate, Ty.telSelf, Telescope.append]
  decide +kernel

/-- The target view contains the retained bounds of `B`, field presence,
and the composed upper bound `self.a <= top`. -/
def targetView : FCdot.View ([],x) :=
  .nil ▹ .le .bot ▹ .le .id ▹ .has .here a ▹ .le .top

theorem receiver_view : FCdot.view store 30 receiver = some targetView := by
  simp [receiver, store, literal, witnesses, fields, coercion, literalToSource, morphism,
    targetView, FCdot.view, FCdot.viewThrough, FCdot.closedAtomForm,
    FCdot.hnf, FCdot.entries, FCdot.sideForm, FCdot.entriesAt, FCdot.Entry.at,
    FCdot.LocalEntry.at, FCdot.Form.combine, FCdot.Entries.through,
    FCdot.Entry.through, FCdot.LocalEntry.through.eq_def, FCdot.LocalEntry.surround,
    FCdot.Entry.toLocal?, FCdot.LocalEntry.toEntry, FCdot.Entries.get?Attach,
    FCdot.Entries.get?, FCdot.Entries.length, FCdot.View.get?, FCdot.View.length,
    FCdot.Hole.index,
    FCdot.LeCo.weaken, FCdot.LeCo.rename, FCdot.Morphism.rename, FCdot.Side.rename,
    FCdot.Store.lookup, FCdot.Value.weaken, FCdot.Value.rename, FCdot.Witnesses.rename,
    FCdot.Fields.rename, FCdot.Value.precView, FCdot.Witnesses.eqForms,
    FCdot.Fields.hasForms, FCdot.Fields.labels]

end Chain
end DotMNF.RecursiveSubtyping
