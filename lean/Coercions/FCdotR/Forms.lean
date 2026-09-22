import Coercions.FCdotR.StoreTyping

/-!
# Forms: the shape of closed evidence, and the measures that reach it

This module is the vocabulary the canonical-forms argument needs, and nothing
more.  It contains no inversion and no normalization: `Normalizer` does the
first, `CanonicalForms` the second.

Three things live here.

* **Measures.**  `Le.size`/`Vc.size` count nodes across the two mutually
  inductive evidence sorts.  `Le.packs`/`Vc.packs` count `vcPack` nodes
  *anywhere*, including inside the observations that `selL`/`selR` carry.
  `Vc.spinePacks` counts them on the **observation spine only** — the chain of
  `vcSub`/`vcPack`/`vcUnfold` nodes above one subject, not descending into the
  inclusion evidence a `vcSub` carries.  `PLAN.md` §I asks for this measure and
  asks whether it is the one the normalizer decreases.  `Normalizer.VcTy.canon`
  proves that it is: redex elimination terminates on the lexicographic pair
  (`spinePacks`, size of the evidence).  The reason the spine count and not the
  total count is the right one is a fact about the calculus: a `selL`/`selR`
  inside an inclusion observes a **different subject**, so substituting a
  location into a `bindx` premise — which is what contracting a redex does —
  copies observations, but every copy lands inside an inclusion and never on the
  spine being counted.  `Vc.packs` would have to absorb those copies and is
  therefore not usable.

* **Head shapes.**  `TyHead` and `headOf` name the outermost former of a type,
  and `HeadPair` names the pairs of head formers that a single non-`trans`
  inclusion rule can relate.  That is the whole content of "transitivity is the
  only rule that changes the head in an uncontrolled way", and it is what
  `CanonicalForms.typ_le_bind_is_trans` is read off from.

* **Normal and redex-free observations.**  `Vc.InNf` says no `vcSub` sits
  directly on top of another — the widenings have been merged by `trans` —
  and `Vc.pushSub` is the merging operation.  `Vc.RedexFree` says no `vcUnfold`
  consumes a `vcPack` through at most one widening; those are the redexes the
  pack measure counts down.

What this module does **not** contain: any claim that a form exists for a given
derivation.  Every definition here is on raw evidence, so nothing in it
presumes the store is honest or the evidence well typed.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Dm Dms renameNil)

/-! ## Measures on evidence -/

mutual

/-- The number of nodes of a piece of inclusion evidence, counting the
observations its selections carry. -/
def Le.size {σ s : Sig} : Le σ s → Nat
  | .refl _ => 1
  | .trans _ e f => e.size + f.size + 1
  | .top _ => 1
  | .bot _ => 1
  | .dtyp _ e f => e.size + f.size + 1
  | .dfun _ e f => e.size + f.size + 1
  | .andI _ _ e f => e.size + f.size + 1
  | .andE1 _ e => e.size + 1
  | .andE2 _ e => e.size + 1
  | .orI1 _ e => e.size + 1
  | .orI2 _ e => e.size + 1
  | .orE _ _ e f => e.size + f.size + 1
  | .defL _ _ e => e.size + 1
  | .defR _ _ e => e.size + 1
  | .selL _ _ v => v.size + 1
  | .selR _ _ v => v.size + 1
  | .bindx _ _ e => e.size + 1
  | .muDrop _ => 1

/-- The number of nodes of a piece of observation evidence, counting the
inclusions its widenings carry. -/
def Vc.size {σ s : Sig} : Vc σ s → Nat
  | .vcVar => 1
  | .vcLoc _ => 1
  | .vcPack _ v => v.size + 1
  | .vcUnfold _ v => v.size + 1
  | .vcSub _ e v => e.size + v.size + 1

end

mutual

/-- The number of `vcPack` nodes anywhere inside an inclusion, including the
observations its selections carry.  Recorded for contrast: this is the count a
naive termination argument would use, and it is *not* stable under the
substitution a redex contraction performs. -/
def Le.packs {σ s : Sig} : Le σ s → Nat
  | .refl _ => 0
  | .trans _ e f => e.packs + f.packs
  | .top _ => 0
  | .bot _ => 0
  | .dtyp _ e f => e.packs + f.packs
  | .dfun _ e f => e.packs + f.packs
  | .andI _ _ e f => e.packs + f.packs
  | .andE1 _ e => e.packs
  | .andE2 _ e => e.packs
  | .orI1 _ e => e.packs
  | .orI2 _ e => e.packs
  | .orE _ _ e f => e.packs + f.packs
  | .defL _ _ e => e.packs
  | .defR _ _ e => e.packs
  | .selL _ _ v => v.packs
  | .selR _ _ v => v.packs
  | .bindx _ _ e => e.packs
  | .muDrop _ => 0

/-- The number of `vcPack` nodes anywhere inside an observation, including the
inclusions its widenings carry. -/
def Vc.packs {σ s : Sig} : Vc σ s → Nat
  | .vcVar => 0
  | .vcLoc _ => 0
  | .vcPack _ v => v.packs + 1
  | .vcUnfold _ v => v.packs
  | .vcSub _ e v => e.packs + v.packs

end

/-- **The measure.**  The number of `vcPack` nodes on the observation *spine*:
the chain of `vcSub`, `vcPack` and `vcUnfold` nodes standing over one and the
same subject.  A `selL`/`selR` inside the inclusion that a `vcSub` carries
observes a *different* subject, so its packs do not belong to this spine and
are not counted. -/
def Vc.spinePacks {σ s : Sig} : Vc σ s → Nat
  | .vcVar => 0
  | .vcLoc _ => 0
  | .vcPack _ v => v.spinePacks + 1
  | .vcUnfold _ v => v.spinePacks
  | .vcSub _ _ v => v.spinePacks

/-- The foot of the observation spine: the hypothesis or the location the
chain of widenings, packings and unfoldings stands on. -/
def Vc.base {σ s : Sig} : Vc σ s → Vc σ s
  | .vcVar => .vcVar
  | .vcLoc l => .vcLoc l
  | .vcPack _ v => v.base
  | .vcUnfold _ v => v.base
  | .vcSub _ _ v => v.base

/-- The length of the observation spine, used only to order the structural
steps of the normalizer against the pack measure. -/
def Vc.spineLen {σ s : Sig} : Vc σ s → Nat
  | .vcVar => 0
  | .vcLoc _ => 0
  | .vcPack _ v => v.spineLen + 1
  | .vcUnfold _ v => v.spineLen + 1
  | .vcSub _ _ v => v.spineLen + 1

/-- A hypothesis carries no packing. -/
@[simp] theorem Vc.spinePacks_vcVar {σ s : Sig} :
    (Vc.vcVar (σ := σ) (s := s)).spinePacks = 0 := rfl

/-- A location carries no packing. -/
@[simp] theorem Vc.spinePacks_vcLoc {σ s : Sig} (l : BVar σ .var) :
    (Vc.vcLoc (s := s) l).spinePacks = 0 := rfl

/-- Packing adds one to the spine count. -/
@[simp] theorem Vc.spinePacks_vcPack {σ s : Sig} (T : Ty σ (s,x)) (v : Vc σ s) :
    (Vc.vcPack T v).spinePacks = v.spinePacks + 1 := rfl

/-- Unfolding leaves the spine count alone; only contracting a redex — an
unfolding that consumes a packing — lowers it. -/
@[simp] theorem Vc.spinePacks_vcUnfold {σ s : Sig} (T : Ty σ (s,x)) (v : Vc σ s) :
    (Vc.vcUnfold T v).spinePacks = v.spinePacks := rfl

/-- Widening leaves the spine count alone: the packings inside the inclusion it
carries observe other subjects. -/
@[simp] theorem Vc.spinePacks_vcSub {σ s : Sig} (T1 : Ty σ s) (e : Le σ s)
    (v : Vc σ s) : (Vc.vcSub T1 e v).spinePacks = v.spinePacks := rfl

/-- The spine measure never exceeds the total count: the spine is part of the
term.  Stated so that a bound on `packs` is also a bound on `spinePacks`. -/
theorem Vc.spinePacks_le_packs {σ s : Sig} : (v : Vc σ s) → v.spinePacks ≤ v.packs
  | .vcVar => Nat.le_refl 0
  | .vcLoc _ => Nat.le_refl 0
  | .vcPack _ v => Nat.succ_le_succ (Vc.spinePacks_le_packs v)
  | .vcUnfold _ v => Vc.spinePacks_le_packs v
  | .vcSub _ e v => Nat.le_trans (Vc.spinePacks_le_packs v) (Nat.le_add_left _ e.packs)

/-! ## Head shapes

A single inclusion rule other than `trans` relates types whose outermost
formers stand in one of a small number of relations.  Naming that relation is
all the "form" a consistency argument at the endpoints needs. -/

/-- The outermost former of a type. -/
inductive TyHead : Type where
  /-- `TBot`. -/
  | bot : TyHead
  /-- `TTop`. -/
  | top : TyHead
  /-- `TFun`. -/
  | fn : TyHead
  /-- `TTyp`. -/
  | typ : TyHead
  /-- `TSel`. -/
  | sel : TyHead
  /-- `TBind`. -/
  | bind : TyHead
  /-- `TAnd`. -/
  | and : TyHead
  /-- `TOr`. -/
  | or : TyHead
deriving DecidableEq, Repr

/-- The outermost former of a type. -/
def headOf {σ s : Sig} : Ty σ s → TyHead
  | .TBot => .bot
  | .TTop => .top
  | .TFun _ _ _ => .fn
  | .TTyp _ _ _ => .typ
  | .TSel _ _ => .sel
  | .TBind _ => .bind
  | .TAnd _ _ => .and
  | .TOr _ _ => .or

/-- The head pairs a single inclusion rule other than `trans` can relate.  Read
off the eighteen rules of `LeTy`: `bot` may start anywhere, `top` may end
anywhere, a selection may stand on either side (`defL`/`defR`/`selL`/`selR`), an
intersection on either side (`andE`/`andI`), a union on either side
(`orE`/`orI`), a `TBind` on the left may end anywhere (`muDrop`), and every
remaining rule is a congruence, which leaves the heads equal. -/
def HeadPair (h1 h2 : TyHead) : Prop :=
  h1 = .bot ∨ h2 = .top ∨ h1 = .sel ∨ h2 = .sel ∨ h1 = .and ∨ h2 = .and ∨
    h1 = .or ∨ h2 = .or ∨ h1 = .bind ∨ h1 = h2

/-- `HeadPair` is a disjunction of equations between constructors, so it is
decidable; the shape inversions are discharged by deciding it. -/
instance HeadPair.instDecidable (h1 h2 : TyHead) : Decidable (HeadPair h1 h2) := by
  unfold HeadPair; infer_instance

/-- Is the outermost rule of a piece of inclusion evidence `trans`? -/
def Le.isTrans {σ s : Sig} : Le σ s → Bool
  | .trans _ _ _ => true
  | _ => false

/-- Evidence whose outermost rule is `trans` names its middle type and its two
halves. -/
theorem Le.exists_trans {σ s : Sig} :
    (e : Le σ s) → e.isTrans = true → ∃ M e1 e2, e = .trans M e1 e2
  | .trans M e1 e2, _ => ⟨M, e1, e2, rfl⟩
  | .refl _, h | .top _, h | .bot _, h | .dtyp _ _ _, h | .dfun _ _ _, h
  | .andI _ _ _ _, h | .andE1 _ _, h | .andE2 _ _, h | .orI1 _ _, h
  | .orI2 _ _, h | .orE _ _ _ _, h | .defL _ _ _, h | .defR _ _ _, h
  | .selL _ _ _, h | .selR _ _ _, h | .bindx _ _ _, h | .muDrop _, h =>
      absurd h (by simp [Le.isTrans])

/-! ## Normal and redex-free observations -/

/-- Is the outermost rule of an observation `vcSub`? -/
def Vc.isSub {σ s : Sig} : Vc σ s → Bool
  | .vcSub _ _ _ => true
  | _ => false

/-- An observation is in **normal form** when no `vcSub` stands directly on
another: the widenings along the spine have been merged into single `trans`
chains.  Every closed observation has one (`Normalizer.VcTy.toNf`). -/
inductive Vc.InNf {σ : Sig} : {s : Sig} → Vc σ s → Prop where
  /-- A hypothesis is normal. -/
  | vcVar {s : Sig} : Vc.InNf (.vcVar (σ := σ) (s := s))
  /-- A location is normal. -/
  | vcLoc {s : Sig} {l : BVar σ .var} : Vc.InNf (.vcLoc (σ := σ) (s := s) l)
  /-- Packing preserves normality. -/
  | vcPack {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.InNf v → Vc.InNf (.vcPack T v)
  /-- Unfolding preserves normality. -/
  | vcUnfold {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.InNf v → Vc.InNf (.vcUnfold T v)
  /-- A widening is normal when what it widens is normal and is not itself a
  widening. -/
  | vcSub {s : Sig} {T1 : Ty σ s} {e : Le σ s} {v : Vc σ s} :
      Vc.InNf v → v.isSub = false → Vc.InNf (.vcSub T1 e v)

/-- Merge a widening into an observation: if the observation already ends in a
widening, compose the two inclusions with `trans` instead of stacking them.
This is the only operation the spine normalizer performs. -/
def Vc.pushSub {σ s : Sig} (T1 : Ty σ s) (e : Le σ s) : Vc σ s → Vc σ s
  | .vcSub T0 d w => .vcSub T0 (.trans T1 d e) w
  | w => .vcSub T1 e w

@[simp] theorem Vc.spinePacks_pushSub {σ s : Sig} (T1 : Ty σ s) (e : Le σ s)
    (w : Vc σ s) : (Vc.pushSub T1 e w).spinePacks = w.spinePacks := by
  cases w <;> rfl

/-- Does this observation present a `vcPack` to an unfolding standing over it,
either directly or through a single widening? -/
def Vc.exposesPack {σ s : Sig} : Vc σ s → Bool
  | .vcPack _ _ => true
  | .vcSub _ _ (.vcPack _ _) => true
  | _ => false

/-- An observation is **redex-free** when no `vcUnfold` consumes a `vcPack`,
either directly or through a single widening.  Those two shapes are the redexes
whose contraction the pack measure counts down. -/
inductive Vc.RedexFree {σ : Sig} : {s : Sig} → Vc σ s → Prop where
  /-- A hypothesis is redex-free. -/
  | vcVar {s : Sig} : Vc.RedexFree (.vcVar (σ := σ) (s := s))
  /-- A location is redex-free. -/
  | vcLoc {s : Sig} {l : BVar σ .var} : Vc.RedexFree (.vcLoc (σ := σ) (s := s) l)
  /-- Packing preserves redex-freedom. -/
  | vcPack {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.RedexFree v → Vc.RedexFree (.vcPack T v)
  /-- Unfolding preserves redex-freedom when it does not consume a pack. -/
  | vcUnfold {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.RedexFree v → v.exposesPack = false → Vc.RedexFree (.vcUnfold T v)
  /-- Widening preserves redex-freedom. -/
  | vcSub {s : Sig} {T1 : Ty σ s} {e : Le σ s} {v : Vc σ s} :
      Vc.RedexFree v → Vc.RedexFree (.vcSub T1 e v)

end FCdotR
