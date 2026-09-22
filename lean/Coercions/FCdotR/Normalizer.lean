import Coercions.FCdotR.Forms

/-!
# The normalizer for closed observation evidence

Two normalizations, in increasing difficulty, and an honest statement of where
the second one stops.

* **Spine normalization** (`VcTy.toNf`).  Merge every stack of `vcSub` nodes
  into one, by composing the inclusions with `trans`.  This is structural, needs
  no fuel and no hypotheses, and it is *typed*: the observation it returns is
  typed at the same subject and the same type as the one it was given
  (`VcNf.typed`), is in normal form (`VcNf.normal`), and has the same pack
  count on its spine (`VcNf.packs`).  That is the `FormTyped` soundness this
  module owes.

* **Redex elimination** (`VcTy.canon`).  A redex is an unfolding that consumes
  a packing, either directly or through one widening.  Contracting it is the
  step that `PLAN.md` §I worries about, because the widening in the middle has
  to be inverted to a `bindx` and that `bindx`'s premise has to be instantiated
  at the location — evidence that is *not* a subderivation.  That contraction is
  this module's one hypothesis, the structure `Contract`.  **Nothing in this
  module inhabits `Contract`**, and everything that depends on it says so.

  Given `Contract`, the rest is proved here, and it settles `PLAN.md` §I's open
  question in the affirmative: the measure is `Vc.spinePacks`, the number of
  `vcPack` nodes on the spine over one subject, ordered lexicographically
  against the size of the evidence, and `VcTy.canon` terminates on it.  The
  reason it works, and the reason the *total* count `Vc.packs` would not, is
  that a contraction substitutes a location into a `bindx` premise: that copies
  whatever observations the premise carries, but every one of them observes a
  *different* subject, so it lands inside an inclusion and never on the spine
  the measure counts.  `Contract.step` is therefore asked only for
  `u.spinePacks ≤ w.spinePacks`, which is what a structure-preserving
  substitution gives along the `bindx` route, where the contracted observation
  is the packed one widened by the instantiated premise.  Whether every other
  route through which `μT ≤ μT'` could have been derived — a chain through a
  concrete selection, say — also respects the bound is part of what inhabiting
  `Contract` has to establish; it is not proved here and is not assumed
  anywhere else.

This module contains no inversion of inclusion evidence.  Eliminating `trans`
from a closed `LeTy` is the other half of canonical forms and is not here; see
`CanonicalForms`.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store renameNil)

/-! ## Merging widenings -/

/-- Merging a widening into a normal observation keeps it normal. -/
theorem Vc.InNf.pushSub {σ s : Sig} {T1 : Ty σ s} {e : Le σ s} :
    {w : Vc σ s} → Vc.InNf w → Vc.InNf (Vc.pushSub T1 e w)
  | .vcVar, h => .vcSub h rfl
  | .vcLoc _, h => .vcSub h rfl
  | .vcPack _ _, h => .vcSub h rfl
  | .vcUnfold _ _, h => .vcSub h rfl
  | .vcSub _ _ _, .vcSub hz hs => .vcSub hz hs

/-- Merging a widening into a redex-free observation keeps it redex-free. -/
theorem Vc.RedexFree.pushSub {σ s : Sig} {T1 : Ty σ s} {e : Le σ s} :
    {w : Vc σ s} → Vc.RedexFree w → Vc.RedexFree (Vc.pushSub T1 e w)
  | .vcVar, h => .vcSub h
  | .vcLoc _, h => .vcSub h
  | .vcPack _ _, h => .vcSub h
  | .vcUnfold _ _, h => .vcSub h
  | .vcSub _ _ _, .vcSub hz => .vcSub hz

/-- Merging a widening into an observation of an **abstract** subject.  Three
cases: a location and a packing have no rule at an abstract subject. -/
def VcTy.pushSubAbs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {x : BVar s .var} : {w : Vc σ (Oopsla16.scopeUpTo x)} →
    {T1 T2 : Ty σ (Oopsla16.scopeUpTo x)} → {e : Le σ (Oopsla16.scopeUpTo x)} →
    VcTy G W Γ (.abs x) w T1 → LeTy G W (Γ.upTo x) e T1 T2 →
    VcTy G W Γ (.abs x) (Vc.pushSub T1 e w) T2
  | _, _, _, _, .vcVar, he => .vcSub _ .vcVar he
  | _, _, _, _, .vcUnfold h, he => .vcSub _ (.vcUnfold h) he
  | _, _, _, _, .vcSub T0 h hd, he => .vcSub T0 h (.trans _ hd he)

/-- Merging a widening into an observation of a **location**. -/
def VcTy.pushSubConc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} : {w : Vc σ []} → {T1 T2 : Ty σ []} → {e : Le σ []} →
    VcTy G W Γ (.conc l) w T1 → LeTy G W .nil e T1 T2 →
    VcTy G W Γ (.conc l) (Vc.pushSub T1 e w) T2
  | _, _, _, _, .vcLoc, he => .vcSub _ .vcLoc he
  | _, _, _, _, .vcPack h, he => .vcSub _ (.vcPack h) he
  | _, _, _, _, .vcUnfold h, he => .vcSub _ (.vcUnfold h) he
  | _, _, _, _, .vcSub T0 h hd, he => .vcSub T0 h (.trans _ hd he)

/-- Merging a widening is typed: the composite inclusion widens to the same
type the two widenings did.  Stated at a subject of either zone, by dispatch;
the two halves differ only in which rules can have produced the observation. -/
def VcTy.pushSub {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    (p : Vr σ s) → {w : Vc σ (scopeAt p)} → {T1 T2 : Ty σ (scopeAt p)} →
    {e : Le σ (scopeAt p)} →
    VcTy G W Γ p w T1 → LeTy G W (ctxAt Γ p) e T1 T2 →
    VcTy G W Γ p (Vc.pushSub T1 e w) T2
  | .abs _, _, _, _, _, h, he => VcTy.pushSubAbs h he
  | .conc _, _, _, _, _, h, he => VcTy.pushSubConc h he

/-! ## Spine normalization -/

/-- The result of normalizing an observation's spine: an observation of the
same subject and the same type, in normal form, with the same number of packs
on its spine. -/
structure VcNf {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (p : Vr σ s) (v : Vc σ (scopeAt p)) (T : Ty σ (scopeAt p)) : Type where
  /-- The normalized evidence. -/
  ev : Vc σ (scopeAt p)
  /-- It is typed at the same endpoints. -/
  typed : VcTy G W Γ p ev T
  /-- It is in normal form. -/
  normal : ev.InNf
  /-- Normalization moves no packing. -/
  packs : ev.spinePacks = v.spinePacks

/-- Spine normalization at an **abstract** subject. -/
def VcTy.toNfAbs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {x : BVar s .var} : {v : Vc σ (Oopsla16.scopeUpTo x)} →
    {T : Ty σ (Oopsla16.scopeUpTo x)} →
    (d : VcTy G W Γ (.abs x) v T) → VcNf G W Γ (.abs x) v T
  | _, _, .vcVar => ⟨.vcVar, .vcVar, .vcVar, rfl⟩
  | _, _, .vcUnfold h =>
      let r := VcTy.toNfAbs h
      ⟨.vcUnfold _ r.ev, .vcUnfold r.typed, .vcUnfold r.normal, by
        simp only [Vc.spinePacks_vcUnfold, r.packs]⟩
  | _, _, .vcSub T1 h he =>
      let r := VcTy.toNfAbs h
      ⟨Vc.pushSub T1 _ r.ev, VcTy.pushSubAbs r.typed he, r.normal.pushSub, by
        simp only [Vc.spinePacks_pushSub, Vc.spinePacks_vcSub, r.packs]⟩

/-- Spine normalization at a **location**. -/
def VcTy.toNfConc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} : {v : Vc σ []} → {T : Ty σ []} →
    (d : VcTy G W Γ (.conc l) v T) → VcNf G W Γ (.conc l) v T
  | _, _, .vcLoc => ⟨.vcLoc _, .vcLoc, .vcLoc, rfl⟩
  | _, _, .vcPack h =>
      let r := VcTy.toNfConc h
      ⟨.vcPack _ r.ev, .vcPack r.typed, .vcPack r.normal, by
        simp only [Vc.spinePacks_vcPack, r.packs]⟩
  | _, _, .vcUnfold h =>
      let r := VcTy.toNfConc h
      ⟨.vcUnfold _ r.ev, .vcUnfold r.typed, .vcUnfold r.normal, by
        simp only [Vc.spinePacks_vcUnfold, r.packs]⟩
  | _, _, .vcSub T1 h he =>
      let r := VcTy.toNfConc h
      ⟨Vc.pushSub T1 _ r.ev, VcTy.pushSubConc r.typed he, r.normal.pushSub, by
        simp only [Vc.spinePacks_pushSub, Vc.spinePacks_vcSub, r.packs]⟩

/-- **Spine normalization.**  Every typed observation has a normal form at the
same subject and type: no `vcSub` stands on a `vcSub`, the two inclusions having
been composed with `trans`.  This is structural, needs no fuel and assumes
nothing about the store. -/
def VcTy.toNf {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
    (p : Vr σ s) → {v : Vc σ (scopeAt p)} → {T : Ty σ (scopeAt p)} →
    VcTy G W Γ p v T → VcNf G W Γ p v T
  | .abs _, _, _, d => VcTy.toNfAbs d
  | .conc _, _, _, d => VcTy.toNfConc d

/-! ## Redexes and the contraction hypothesis -/

/-- **The one thing this module assumes.**  A contraction of an
unfolding-over-packing redex at a location: given a closed observation of the
opened body `T` at `ℓ`, and a closed inclusion `μT ≤ μT'`, an observation of the
opened body `T'` at `ℓ`, with no more packs on its spine.

Two ingredients inhabit it.  The inclusion has to be inverted to a `bindx` —
that is transitivity elimination for closed inclusion evidence, the other half
of canonical forms, and it does **not** exist yet — and that `bindx`'s premise,
which lives under the self hypothesis, has to be instantiated at `ℓ` — that is
the substitution theorem, `SubstTyping.LeTy.substEv`, which **is** available
unconditionally (its former hypothesis `LemmaR` is discharged by
`SubstTyping.lemmaR`).  So only the inversion is missing.  The bound `u.spinePacks ≤ w.spinePacks` is what a
structure-preserving substitution gives along the `bindx` route: it copies
observations, but every copy observes a different subject and so does not land
on this spine.  Establishing it for every route by which `μT ≤ μT'` can be
derived is part of inhabiting this structure. -/
structure Contract {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type where
  /-- Contract one redex. -/
  step : ∀ {l : BVar σ .var} {T T' : Ty σ ([],x)} {w : Vc σ []} {e : Le σ []},
      VcTy G W .nil (.conc l) w (T.substVr (.conc l)) →
      LeTy G W .nil e (.TBind T) (.TBind T') →
      (u : Vc σ []) × VcTy G W .nil (.conc l) u (T'.substVr (.conc l)) ×
        PLift (u.spinePacks ≤ w.spinePacks)

/-- What one unfolding step over an already redex-free observation produces. -/
inductive UnfoldOut {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var)
    (w : Vc σ []) (T0 : Ty σ ([],x)) : Type where
  /-- No packing is exposed, so unfolding `w` is itself redex-free. -/
  | keep : w.exposesPack = false → UnfoldOut G W l w T0
  /-- A packing was consumed: an observation of the opened body with strictly
  fewer packs on its spine than the unfolding had. -/
  | contracted (u : Vc σ []) :
      VcTy G W .nil (.conc l) u (T0.substVr (.conc l)) →
      u.spinePacks + 1 ≤ w.spinePacks → UnfoldOut G W l w T0

/-- **One unfolding step.**  Either the observation exposes no packing, or a
redex is contracted and the pack measure drops by at least one.  The direct
redex `vcUnfold (vcPack …)` needs no hypothesis at all: the packed type *is*
the unfolded one.  Only the redex through a widening calls `Contract`. -/
def VcTy.unfoldStep {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {l : BVar σ .var}
    (c : Contract G W) {T0 : Ty σ ([],x)} :
    {w : Vc σ []} → VcTy G W .nil (.conc l) w (.TBind T0) → UnfoldOut G W l w T0
  | .vcLoc _, _ => .keep rfl
  | .vcUnfold _ _, _ => .keep rfl
  | .vcPack _ _, .vcPack h => .contracted _ h (Nat.le_refl _)
  | .vcSub _ _ (.vcLoc _), _ => .keep rfl
  | .vcSub _ _ (.vcUnfold _ _), _ => .keep rfl
  | .vcSub _ _ (.vcSub _ _ _), _ => .keep rfl
  | .vcSub _ _ (.vcPack _ _), .vcSub _ (.vcPack hz) hd =>
      let r := c.step hz hd
      .contracted r.1 r.2.1 (by
        have h := r.2.2.down
        simp only [Vc.spinePacks_vcSub, Vc.spinePacks_vcPack]
        omega)

/-! ## Redex elimination -/

/-- The result of eliminating every redex from a closed observation at a
location: an observation of the same type, redex-free, with no more packs on its
spine. -/
structure VcRf {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var)
    (v : Vc σ []) (T : Ty σ []) : Type where
  /-- The redex-free evidence. -/
  ev : Vc σ []
  /-- It is typed at the same location and type. -/
  typed : VcTy G W .nil (.conc l) ev T
  /-- No unfolding in it consumes a packing. -/
  redexFree : ev.RedexFree
  /-- Contraction never grows the pack measure. -/
  packs : ev.spinePacks ≤ v.spinePacks

/-- **Redex elimination, on the pack measure.**  Every closed observation at a
location reduces to a redex-free one of the same type.  The recursion is
lexicographic on the pair (remaining pack budget, size of the evidence): the
structural steps shrink the second component, and the one step that restarts
the traversal — contracting a redex — shrinks the first, by `unfoldStep`.

This is the theorem `PLAN.md` §I asks for, and it answers the question there:
the pack count on the spine *is* a well-founded measure for `vc_canon`, and no
count of derivation size is needed alongside it beyond the structural one.

**It is stated with an unproved hypothesis.**  `c : Contract G W` is the
contraction of a redex through a widening, and nothing inhabits it; see
`Contract`. -/
def VcTy.canon {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {l : BVar σ .var}
    (c : Contract G W) : (n : Nat) → (v : Vc σ []) → {T : Ty σ []} →
    VcTy G W .nil (.conc l) v T → v.spinePacks ≤ n → VcRf G W l v T
  | _, _, _, .vcLoc, _ => ⟨.vcLoc _, .vcLoc, .vcLoc, Nat.le_refl _⟩
  | n, _, _, .vcSub T1 h he, hn =>
      let r := VcTy.canon c n _ h (by simpa using hn)
      ⟨Vc.pushSub T1 _ r.ev, VcTy.pushSubConc r.typed he, r.redexFree.pushSub, by
        have h1 := r.packs
        simp only [Vc.spinePacks_pushSub, Vc.spinePacks_vcSub]
        omega⟩
  | n, _, _, .vcPack (T := T0) h, hn =>
      let r := VcTy.canon c n _ h (by
        simp only [Vc.spinePacks_vcPack] at hn; omega)
      ⟨.vcPack T0 r.ev, .vcPack r.typed, .vcPack r.redexFree, by
        have h1 := r.packs
        simp only [Vc.spinePacks_vcPack]
        omega⟩
  | n, _, _, .vcUnfold (T := T0) h, hn =>
      let r := VcTy.canon c n _ h (by simpa using hn)
      match VcTy.unfoldStep c r.typed with
      | .keep hk =>
          ⟨.vcUnfold T0 r.ev, .vcUnfold r.typed, .vcUnfold r.redexFree hk, by
            have h1 := r.packs
            simp only [Vc.spinePacks_vcUnfold]
            omega⟩
      | .contracted u hu hlt =>
          let r2 := VcTy.canon c u.spinePacks u hu (Nat.le_refl _)
          ⟨r2.ev, r2.typed, r2.redexFree, by
            have h1 := r.packs
            have h2 := r2.packs
            simp only [Vc.spinePacks_vcUnfold] at hn ⊢
            omega⟩
  termination_by n v => (n, v.size)
  decreasing_by
    · simp only [Vc.size]; omega
    · simp only [Vc.size]; omega
    · simp only [Vc.size]; omega
    · have h1 := r.packs
      simp only [Vc.spinePacks_vcUnfold] at hn
      omega

end FCdotR
