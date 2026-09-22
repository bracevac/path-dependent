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

The restriction is carried by an *inductive* `MonoAt`, one constructor per zone
of the image, each naming the image subject and the equation that identifies
it.  That is not bureaucracy: writing the restriction's codomain as
`scopeAt (θ.abs x)` makes it depend on a neutral term, and every closure
operation then needs a transport along `scopeAt_weaken` with its equation
proved underneath.  Naming the image makes each branch's scopes match
definitionally — `(.abs z).weaken` is `.abs (.there z)` and `tailBelow`
discards the `.there` — so `lift` is a case analysis and no transport occurs.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Subst scopeUpTo renameUpTo)

/-- The prefix of a weakened variable is the prefix of the variable: `scopeAt`
looks only at the `.there` spine, which weakening extends. -/
@[simp] theorem scopeAt_weaken {σ s : Sig} (v : Vr σ s) :
    scopeAt v.weaken = scopeAt v := by cases v <;> rfl

/-- Weakening after a renaming is a renaming. -/
@[simp] theorem Vr.weaken_subst_ofRename {σ s1 s2 : Sig} (v : Vr σ s1)
    (ρ : Rename s1 s2) :
    (v.subst (Subst.ofRename ρ)).weaken
      = v.subst (Subst.ofRename (ρ.comp (Rename.succ (k := .var)))) := by
  cases v <;> rfl

/-- The restriction of `θ` at one variable, with the image subject named.  The
two constructors are the two zones the image can be in. -/
inductive MonoAt {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) (x : BVar s1 .var) :
    Type where
  /-- The image is an abstract variable `z`, and the prefix at `x` substitutes
  into the prefix at `z`. -/
  | toAbs (z : BVar s2 .var) (r : Subst σ1 (scopeUpTo x) σ2 (scopeUpTo z)) :
      θ.abs x = .abs z →
      (Subst.ofRename (renameUpTo x)).comp θ
        = r.comp (Subst.ofRename (renameUpTo z)) →
      MonoAt θ x
  /-- The image is a location, whose prefix is the empty local scope. -/
  | toConc (l : BVar σ2 .var) (r : Subst σ1 (scopeUpTo x) σ2 []) :
      θ.abs x = .conc l →
      (Subst.ofRename (renameUpTo x)).comp θ
        = r.comp (Subst.ofRename Oopsla16.renameNil) →
      MonoAt θ x

/-- A substitution that respects prefixes at every variable. -/
abbrev Mono {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) : Type :=
  (x : BVar s1 .var) → MonoAt θ x

namespace MonoAt

/-- The image subject, read off the constructor.  Speaking through `image`
rather than through `θ.abs x` is what keeps the scopes definitional: the
restriction's codomain is `scopeAt image`, and `scopeAt` computes on a
constructor. -/
def image {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {x : BVar s1 .var} :
    MonoAt θ x → Vr σ2 s2
  | .toAbs z _ _ _ => .abs z
  | .toConc l _ _ _ => .conc l

/-- The restriction itself. -/
def restrict {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {x : BVar s1 .var} :
    (a : MonoAt θ x) → Subst σ1 (scopeUpTo x) σ2 (scopeAt a.image)
  | .toAbs _ r _ _ => r
  | .toConc _ r _ _ => r

/-- The image is the substitution's action, as it must be. -/
theorem image_eq {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {x : BVar s1 .var} :
    (a : MonoAt θ x) → a.image = θ.abs x
  | .toAbs _ _ h _ => h.symm
  | .toConc _ _ h _ => h.symm

/-- The defining equation, in terms of `image` and `restrict`. -/
theorem star {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} {x : BVar s1 .var} :
    (a : MonoAt θ x) →
    (Subst.ofRename (renameUpTo x)).comp θ
      = a.restrict.comp (Subst.ofRename (renameAt a.image))
  | .toAbs _ _ _ hs => hs
  | .toConc _ _ _ hs => hs

end MonoAt

namespace Mono

/-- The image of a subject of either zone. -/
def image {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} (m : Mono θ) :
    Vr σ1 s1 → Vr σ2 s2
  | .abs x => (m x).image
  | .conc l => .conc (θ.conc l)

/-- The restriction at a subject of either zone.  At a location this is the
substitution's store part alone, because a location's prefix is the empty local
scope. -/
def at' {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} (m : Mono θ) :
    (p : Vr σ1 s1) → Subst σ1 (scopeAt p) σ2 (scopeAt (m.image p))
  | .abs x => (m x).restrict
  | .conc _ => Subst.atNil θ

@[simp] theorem image_eq {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2}
    (m : Mono θ) (p : Vr σ1 s1) : m.image p = p.subst θ := by
  cases p with
  | abs x => exact (m x).image_eq
  | conc l => rfl

end Mono

namespace Mono

/-- The identity respects prefixes. -/
def id {σ s : Sig} : Mono (Subst.id (σ := σ) (s := s)) := fun x =>
  .toAbs x Subst.id rfl (by apply Subst.ext <;> intro y <;> rfl)

/-- A prefix-respecting substitution can be pushed under a binder.  Each
branch's scopes agree definitionally, so there is no transport. -/
def lift {σ1 σ2 s1 s2 : Sig} {θ : Subst σ1 s1 σ2 s2} (m : Mono θ) :
    Mono θ.lift
  | .here =>
      .toAbs .here θ.lift rfl (by
        apply Subst.ext <;> intro w
        · rfl
        · show θ.lift.abs w = (θ.lift.abs w).subst Subst.id
          exact (Vr.subst_id _).symm)
  | .there y =>
      match m y with
      | .toAbs z r h hs =>
          .toAbs (.there z) r
            (by simp only [Subst.lift, h]; rfl)
            (by
              apply Subst.ext <;> intro w
              · have hc : θ.conc w = r.conc w :=
                  congrArg (fun t => Subst.conc t w) hs
                exact hc
              · have hw : θ.abs ((renameUpTo y).var w)
                    = (r.abs w).subst (Subst.ofRename (renameUpTo z)) :=
                  congrArg (fun t => Subst.abs t w) hs
                show (θ.abs ((renameUpTo y).var w)).weaken
                    = (r.abs w).subst
                        (Subst.ofRename ((renameUpTo z).comp Rename.succ))
                rw [hw, Vr.weaken_subst_ofRename])
      | .toConc l r h hs =>
          .toConc l r
            (by simp only [Subst.lift, h]; rfl)
            (by
              apply Subst.ext <;> intro w
              · have hc : θ.conc w = r.conc w :=
                  congrArg (fun t => Subst.conc t w) hs
                exact hc
              · have hw : θ.abs ((renameUpTo y).var w)
                    = (r.abs w).subst (Subst.ofRename Oopsla16.renameNil) :=
                  congrArg (fun t => Subst.abs t w) hs
                show (θ.abs ((renameUpTo y).var w)).weaken
                    = (r.abs w).subst (Subst.ofRename Oopsla16.renameNil)
                rw [hw]
                cases hv : r.abs w with
                | conc c => rfl
                | abs u => exact nomatch u)

/-- Prefix-respecting substitutions compose.  At each variable the image's
zone is read off the two restrictions, and associativity does the rest. -/
def comp {σ1 σ2 σ3 s1 s2 s3 : Sig} {θ : Subst σ1 s1 σ2 s2}
    {φ : Subst σ2 s2 σ3 s3} (m : Mono θ) (n : Mono φ) : Mono (θ.comp φ) :=
  fun x =>
    match m x with
    | .toAbs z r h hs =>
        match n z with
        | .toAbs z' r' h' hs' =>
            .toAbs z' (r.comp r')
              (by simp only [Subst.comp_abs, h, Vr.subst, h'])
              (by rw [← Subst.comp_assoc, hs, Subst.comp_assoc, hs',
                    ← Subst.comp_assoc])
        | .toConc l' r' h' hs' =>
            .toConc l' (r.comp r')
              (by simp only [Subst.comp_abs, h, Vr.subst, h'])
              (by rw [← Subst.comp_assoc, hs, Subst.comp_assoc, hs',
                    ← Subst.comp_assoc])
    | .toConc l r h hs =>
        .toConc (φ.conc l) (r.comp (Subst.atNil φ))
          (by simp only [Subst.comp_abs, h, Vr.subst])
          (by rw [← Subst.comp_assoc, hs, Subst.comp_assoc, Subst.nil_comp,
                ← Subst.comp_assoc])

/-- Substituting the single binder of `([],x)` by a location respects
prefixes.  This is the case the machine produces: `ST_Obj` and `ST_AppAbs`
substitute a `Vr.conc`, and a running term has an empty local scope.

There is no general `Mono` for `Subst.one`.  At an abstract image the
restriction would have to map the *whole* scope `s,x` into the prefix at that
image, and a variable older than the image has nowhere to go. -/
def oneConc {σ : Sig} (l : BVar σ .var) :
    Mono (Subst.one (σ := σ) (s := []) (.conc l)) := by
  intro x
  cases x with
  | here =>
      exact .toConc l (Subst.one (.conc l)) rfl (by
        apply Subst.ext <;> intro w
        · rfl
        · cases w with
          | here => rfl
          | there y => cases y)
  | there y => cases y

/-! ## What the substitution action still needs

`Le.subst` must send `selL p a v` to `selL (m.image p) a (v.subst _)`, where the
inner substitution is `m.at' p`.  But `v` may contain `vcSub T₁ e w`, whose `e`
is itself inclusion evidence, so substituting `v` needs a `Mono (m.at' p)` and
not merely the substitution `m.at' p`.  **`Mono` therefore has to be closed
under restriction**, which the design round listed as the coherence condition

```text
(θ↾x)↾y = θ↾((renameUpTo x).var y)
```

but did not connect to this consequence.

That closure cannot be had by making the requirement recursive in the type —
`structure Mono θ where res : … ; resMono : ∀ x, Mono (res x)` is not an
inductive definition, and there is no descent to recurse on either, since
`scopeUpTo .here` is the whole scope and the restriction there is `θ` itself.

The fix is the coherence condition as *data*: carry, alongside `res` and
`star`, the equation identifying a restriction's own restrictions with `res` at
the corresponding variables.  Closure under restriction is then a
**definition** rather than a recursive type — `Mono (m.res x)` is built from
`m` by taking its restriction at `y` to be `m`'s at `(renameUpTo x).var y` —
and the scope mismatches are exactly `scopeUpTo_renameUpTo`, which `Prefix`
already proves.

Until that field is added, `Mono` supports the closure operations above but not
the substitution action, and the theorem stated against it is not yet provable.
-/

end Mono

end FCdotR
