import Coercions.FCdotR.Prefix
import Coercions.Oopsla16.SubstLemmas

/-!
# Prefix-respecting substitutions

The target's observation evidence is scoped at its subject's prefix, so a
substitution can act on it only if it carries, for each variable, a
substitution of that variable's prefix into the prefix of its image.  That is
`Mono`.

The condition those restrictions must satisfy is stated once, as an equation
between substitutions:

```text
ofRename (renameUpTo x) ; θ  =  θ↾x ; ofRename (renameAt (θ.abs x))
```

Read left to right: weakening out of the prefix and then substituting is the
same as substituting inside the prefix and then weakening out of the image's
prefix.  By fusion (`Oopsla16.SubstLemmas`) this one equation gives the
corresponding law for types, terms and definition lists at once, which is why
it is stated on substitutions rather than quantified over syntax.

Note what is *not* required: that `(Γ.upTo x)[θ↾x]` be `Γ'.upTo (θ.abs x)`.
Substitution moves a hypothesis's type, so that equality fails, and the
substitution theorem does not need it.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Subst scopeUpTo renameUpTo)

/-- The prefix of a weakened variable is the prefix of the variable: `scopeAt`
looks only at the `.there` spine, which weakening extends. -/
@[simp] theorem scopeAt_weaken {σ s : Sig} (v : Vr σ s) :
    scopeAt v.weaken = scopeAt v := by cases v <;> rfl

/-- A substitution together with its action on prefixes. -/
structure Mono {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) : Type where
  /-- The restriction of `θ` to the prefix at `x`. -/
  res : (x : BVar s1 .var) → Subst σ1 (scopeUpTo x) σ2 (scopeAt (θ.abs x))
  /-- Weakening out of the prefix commutes with substituting. -/
  star : ∀ x : BVar s1 .var,
      (Subst.ofRename (renameUpTo x)).comp θ
        = (res x).comp (Subst.ofRename (renameAt (θ.abs x)))

namespace Mono

/-- The law at types, by fusion. -/
theorem star_ty {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} (m : Mono θ)
    (x : BVar s1 .var) (T : Ty σ1 (scopeUpTo x)) :
    (T.rename (renameUpTo x)).subst θ
      = (T.subst (m.res x)).rename (renameAt (θ.abs x)) := by
  simp only [Ty.rename, Ty.subst_comp, m.star x]

/-- The identity respects prefixes. -/
def id {σ s : Sig} : Mono (Subst.id (σ := σ) (s := s)) where
  res := fun _ => Subst.id
  star := fun x => by
    apply Subst.ext <;> intro y <;> rfl

/-! ## What closure under `lift` needs

`Mono.lift` is the next step and is not yet proved.  The obstruction is
concrete and worth stating, because it is the "dependent-index ergonomics" risk
of the design in its sharpest form.

Pushing `θ` under a binder must supply, at `.there y`, a substitution of type
`Subst σ1 (scopeUpTo y) σ2 (scopeAt (θ.lift.abs (.there y)))`, i.e. at
`scopeAt ((θ.abs y).weaken)`.  `scopeAt_weaken` says that scope *is*
`scopeAt (θ.abs y)`, so `m.res y` is the witness — but only after a transport,
and `star` for the lifted substitution then has to be proved underneath it.

Per constructor the equation is definitional: `(.abs x).weaken` is
`.abs (.there x)` and `tailBelow (.there x)` reduces to `tailBelow x`;
`(.conc l).weaken` is `.conc l`.  It is opaque only because `θ.abs y` is a
neutral term.  So the fix is to case on `θ.abs y` where the restriction is
*built*, not to transport after the fact — which means `res` should be indexed
by a `Vr` rather than a `BVar`, and `Mono` should be stated so that the two
zones are separate fields.  That reshaping is the next tick's work; it also
matches what Lemma 1 will need, since the substitution theorem's subject is a
`Vr` and at `conc l` both prefixes are `[]`.
-/

end Mono

end FCdotR
