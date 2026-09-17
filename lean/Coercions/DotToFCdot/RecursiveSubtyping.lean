import Coercions.DotToFCdot.EvidenceTyped
import Coercions.DotMNF.WadlerFest.LabelSorted

/-!
# Experimental coercions for recursive subtyping

Two bounded recursive-subtyping principles already have evidence in FCdot:

* project a self-independent component out of a recursive intersection;
* retain a declaration-shaped component under its recursive binder.

These are explicit target coercions, not new constructors of source `Sub`.
The proofs use the existing target typing rules and require no changes to
normalization, preservation, or source typing. A final example records a
valid opened-self premise of a more general BINDX rule; it does not assert
that the corresponding recursive subtyping judgment has been translated.
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

/-- A valid opened-self premise for a prospective BINDX rule.
Translating its recursive conclusion would require a construction combining
two source facts, `self.a <= self.A` and `self.A <= self.B`. The current
one-hole object-template interface does not directly provide that construction. -/
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

end Chain
end DotMNF.RecursiveSubtyping
