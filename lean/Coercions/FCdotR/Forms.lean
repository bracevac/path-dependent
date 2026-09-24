import Coercions.FCdotR.StoreTyping

/-!
# Forms: the shape of closed evidence, and the measures that reach it

This module is the vocabulary the canonical-forms argument needs, and nothing
more.  It contains no inversion and no normalization: `Normalizer` normalizes
observations, `CanonicalForms` reads off what the head shapes force, and
`Inversion` eliminates transitivity from closed inclusions.

Five things live here.

* **Measures.**  `Le.size`/`Vc.size` count nodes across the two mutually
  inductive evidence sorts.  `Le.packs`/`Vc.packs` count `vcPack` nodes
  *anywhere*, including inside the observations that `selL`/`selR` carry.
  `Vc.spinePacks` counts them on the **observation spine only** — the chain of
  `vcSub`/`vcPack`/`vcUnfold` nodes above one subject, not descending into the
  inclusion evidence a `vcSub` carries.  `Normalizer.VcTy.canon` proves that the
  normalizer decreases it: redex elimination terminates on the lexicographic
  pair (`spinePacks`, size of the evidence).  The reason the spine count and not
  the total count is the right one is a fact about the calculus: a `selL`/`selR`
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

* **Pack bounds.**  `Le.PackBound k` says every selection on a location, at any
  depth, observes it through fewer than `k` packings; `Le.Strong` is
  `PackBound 0`, evidence whose concrete selections are all `defL`/`defR`.

* **Normal forms of closed inclusions.**  `LeNf`/`LeNfHead`, the target's
  precise subtyping `stpp`, with strong premises `SLe`.

What this module does **not** contain: any claim that a form exists for a given
derivation.  Every definition here is on raw evidence or is a datatype, so
nothing in it presumes the store is honest or the evidence well typed.
`Inversion.SLe.nf` and `Inversion.Store.Honest.nf` are the existence results.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Dm renameNil)

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
  | .vcLocAny _ _ => 1
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
  | .vcLocAny _ _ => 0
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
  | .vcLocAny _ _ => 0
  | .vcPack _ v => v.spinePacks + 1
  | .vcUnfold _ v => v.spinePacks
  | .vcSub _ _ v => v.spinePacks

/-- The foot of the observation spine: the hypothesis or the location the
chain of widenings, packings and unfoldings stands on. -/
def Vc.base {σ s : Sig} : Vc σ s → Vc σ s
  | .vcVar => .vcVar
  | .vcLoc l => .vcLoc l
  | .vcLocAny l T => .vcLocAny l T
  | .vcPack _ v => v.base
  | .vcUnfold _ v => v.base
  | .vcSub _ _ v => v.base

/-- The length of the observation spine, used only to order the structural
steps of the normalizer against the pack measure. -/
def Vc.spineLen {σ s : Sig} : Vc σ s → Nat
  | .vcVar => 0
  | .vcLoc _ => 0
  | .vcLocAny _ _ => 0
  | .vcPack _ v => v.spineLen + 1
  | .vcUnfold _ v => v.spineLen + 1
  | .vcSub _ _ v => v.spineLen + 1

/-- A hypothesis carries no packing. -/
@[simp] theorem Vc.spinePacks_vcVar {σ s : Sig} :
    (Vc.vcVar (σ := σ) (s := s)).spinePacks = 0 := rfl

/-- A location carries no packing. -/
@[simp] theorem Vc.spinePacks_vcLoc {σ s : Sig} (l : BVar σ .var) :
    (Vc.vcLoc (s := s) l).spinePacks = 0 := rfl

/-- A location observed at a carried self type carries no packing either. -/
@[simp] theorem Vc.spinePacks_vcLocAny {σ s : Sig} (l : BVar σ .var)
    (T : Ty σ ([],x)) : (Vc.vcLocAny (s := s) l T).spinePacks = 0 := rfl

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
  | .vcLocAny _ _ => Nat.le_refl 0
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
  /-- A location observed at a carried self type is normal. -/
  | vcLocAny {s : Sig} {l : BVar σ .var} {T : Ty σ ([],x)} :
      Vc.InNf (.vcLocAny (σ := σ) (s := s) l T)
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

/-- Merging a widening moves no packing: `pushSub` only rebuilds a `vcSub`. -/
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
  /-- A location observed at a carried self type is redex-free. -/
  | vcLocAny {s : Sig} {l : BVar σ .var} {T : Ty σ ([],x)} :
      Vc.RedexFree (.vcLocAny (σ := σ) (s := s) l T)
  /-- Packing preserves redex-freedom. -/
  | vcPack {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.RedexFree v → Vc.RedexFree (.vcPack T v)
  /-- Unfolding preserves redex-freedom when it does not consume a pack. -/
  | vcUnfold {s : Sig} {T : Ty σ (s,x)} {v : Vc σ s} :
      Vc.RedexFree v → v.exposesPack = false → Vc.RedexFree (.vcUnfold T v)
  /-- Widening preserves redex-freedom. -/
  | vcSub {s : Sig} {T1 : Ty σ s} {e : Le σ s} {v : Vc σ s} :
      Vc.RedexFree v → Vc.RedexFree (.vcSub T1 e v)


/-! ## How far a concrete selection may observe

`LeTy.selL`/`LeTy.selR` read a location through an *observation*, which may
itself have been widened, packed and unfolded; `LeTy.defL`/`LeTy.defR` read the
stored definition exactly.  The source has only the second pair for a location
(`stp_strong_sel1/2`, `dot.v:305-314`).  `PackBound k` grades evidence by how
much of the first pair it uses: every selection **on a location**, at any
depth, observes that location with fewer than `k` packings on its spine.
Selections on an abstract variable are unconstrained, apart from the
constraint on the inclusions their observations carry.

`PackBound 0` forbids concrete `selL`/`selR` altogether; that is `Le.Strong`,
named after the source rules it leaves.  Strong closed evidence is what
transitivity elimination (`Inversion.LeTy.pushback`) runs on, and turning
arbitrary evidence into strong evidence (`Inversion.LeTy.strengthenAt`, and
`Inversion.Store.Honest.strengthen` over an honest store) is where the pack
count is spent: a concrete selection is replaced by `defL`/`defR` after its
observation has been inverted, which needs the substitution theorem at fewer
packs. -/

mutual

/-- Every selection on a location inside the inclusion evidence — including
inside the observations its selections carry — observes that location through
fewer than `k` packings on its spine. -/
def Le.PackBound {σ s : Sig} (k : Nat) : Le σ s → Prop
  | .refl _ => True
  | .trans _ e f => e.PackBound k ∧ f.PackBound k
  | .top _ => True
  | .bot _ => True
  | .dtyp _ e f => e.PackBound k ∧ f.PackBound k
  | .dfun _ e f => e.PackBound k ∧ f.PackBound k
  | .andI _ _ e f => e.PackBound k ∧ f.PackBound k
  | .andE1 _ e => e.PackBound k
  | .andE2 _ e => e.PackBound k
  | .orI1 _ e => e.PackBound k
  | .orI2 _ e => e.PackBound k
  | .orE _ _ e f => e.PackBound k ∧ f.PackBound k
  | .defL _ _ e => e.PackBound k
  | .defR _ _ e => e.PackBound k
  | .selL p _ v => v.PackBound k ∧ (zone p = .concrete → v.spinePacks < k)
  | .selR p _ v => v.PackBound k ∧ (zone p = .concrete → v.spinePacks < k)
  | .bindx _ _ e => e.PackBound k
  | .muDrop _ => True

/-- The observation counterpart: every inclusion a widening on the spine carries
satisfies `Le.PackBound k`.  The spine's *own* packings are not constrained
here; the enclosing selection constrains them when its subject is a location. -/
def Vc.PackBound {σ s : Sig} (k : Nat) : Vc σ s → Prop
  | .vcVar => True
  | .vcLoc _ => True
  | .vcLocAny _ _ => True
  | .vcPack _ v => v.PackBound k
  | .vcUnfold _ v => v.PackBound k
  | .vcSub _ e v => e.PackBound k ∧ v.PackBound k

end

/-- **Strong** inclusion evidence: no selection on a location goes through an
observation.  Every concrete selection is a `defL`/`defR`, as in the source. -/
abbrev Le.Strong {σ s : Sig} (e : Le σ s) : Prop := e.PackBound 0

/-- An observation whose widenings carry strong inclusions only. -/
abbrev Vc.Strong {σ s : Sig} (v : Vc σ s) : Prop := v.PackBound 0

mutual

/-- A larger bound is a weaker requirement. -/
theorem Le.PackBound.mono {σ s : Sig} {j k : Nat} (hjk : j ≤ k) :
    (e : Le σ s) → e.PackBound j → e.PackBound k
  | .refl _, _ => trivial
  | .trans _ e f, h | .dtyp _ e f, h | .dfun _ e f, h | .andI _ _ e f, h
  | .orE _ _ e f, h => by
      simp only [Le.PackBound] at h ⊢
      exact ⟨Le.PackBound.mono hjk e h.1, Le.PackBound.mono hjk f h.2⟩
  | .top _, _ => trivial
  | .bot _, _ => trivial
  | .andE1 _ e, h | .andE2 _ e, h | .orI1 _ e, h | .orI2 _ e, h
  | .defL _ _ e, h | .defR _ _ e, h | .bindx _ _ e, h => by
      simp only [Le.PackBound] at h ⊢
      exact Le.PackBound.mono hjk e h
  | .selL _ _ v, h | .selR _ _ v, h => by
      simp only [Le.PackBound] at h ⊢
      exact ⟨Vc.PackBound.mono hjk v h.1, fun hz => Nat.lt_of_lt_of_le (h.2 hz) hjk⟩
  | .muDrop _, _ => trivial

/-- A larger bound is a weaker requirement, for observations. -/
theorem Vc.PackBound.mono {σ s : Sig} {j k : Nat} (hjk : j ≤ k) :
    (v : Vc σ s) → v.PackBound j → v.PackBound k
  | .vcVar, _ => trivial
  | .vcLoc _, _ => trivial
  | .vcLocAny _ _, _ => trivial
  | .vcPack _ v, h | .vcUnfold _ v, h => by
      simp only [Vc.PackBound] at h ⊢
      exact Vc.PackBound.mono hjk v h
  | .vcSub _ e v, h => by
      simp only [Vc.PackBound] at h ⊢
      exact ⟨Le.PackBound.mono hjk e h.1, Vc.PackBound.mono hjk v h.2⟩

end

mutual

/-- **Every piece of evidence has a pack bound**: one more than the number of
packings it contains anywhere.  Every observation a selection carries is part
of the term, so its spine is counted by `Le.packs`. -/
theorem Le.packBound_of_packs {σ s : Sig} {k : Nat} :
    (e : Le σ s) → e.packs < k → e.PackBound k
  | .refl _, _ => trivial
  | .trans _ e f, h | .dtyp _ e f, h | .dfun _ e f, h | .andI _ _ e f, h
  | .orE _ _ e f, h => by
      simp only [Le.packs] at h
      simp only [Le.PackBound]
      exact ⟨Le.packBound_of_packs e (by omega), Le.packBound_of_packs f (by omega)⟩
  | .top _, _ => trivial
  | .bot _, _ => trivial
  | .andE1 _ e, h | .andE2 _ e, h | .orI1 _ e, h | .orI2 _ e, h
  | .defL _ _ e, h | .defR _ _ e, h | .bindx _ _ e, h => by
      simp only [Le.packs] at h
      simp only [Le.PackBound]
      exact Le.packBound_of_packs e h
  | .selL _ _ v, h | .selR _ _ v, h => by
      simp only [Le.packs] at h
      simp only [Le.PackBound]
      exact ⟨Vc.packBound_of_packs v h,
        fun _ => Nat.lt_of_le_of_lt (Vc.spinePacks_le_packs v) h⟩
  | .muDrop _, _ => trivial

/-- The observation counterpart of `Le.packBound_of_packs`. -/
theorem Vc.packBound_of_packs {σ s : Sig} {k : Nat} :
    (v : Vc σ s) → v.packs < k → v.PackBound k
  | .vcVar, _ => trivial
  | .vcLoc _, _ => trivial
  | .vcLocAny _ _, _ => trivial
  | .vcPack _ v, h => by
      simp only [Vc.packs] at h
      simp only [Vc.PackBound]
      exact Vc.packBound_of_packs v (by omega)
  | .vcUnfold _ v, h => by
      simp only [Vc.packs] at h
      simp only [Vc.PackBound]
      exact Vc.packBound_of_packs v h
  | .vcSub _ e v, h => by
      simp only [Vc.packs] at h
      simp only [Vc.PackBound]
      exact ⟨Le.packBound_of_packs e (by omega), Vc.packBound_of_packs v (by omega)⟩

end

/-! ## Normal forms of closed inclusion evidence

`LeNf G W S T` is a closed inclusion `S ≤ T` whose **outermost rule is not
`trans`** and is determined by the head of `S` or of `T`.  It is the target's
counterpart of the reference's precise subtyping `stpp`
(`dot_soundness.v:10-86`), in two layers.

* `LeNf` holds the forms decided by the **right** head: `⊤`, an intersection
  (`and2`), a union (`or21`/`or22`) and a selection on a location (`sel2`,
  read against the stored definition).  Each of them can absorb any inclusion
  on its left by one `trans` into its premises, which is why transitivity
  elimination handles them before looking at the left.
* `LeNfHead` holds the forms decided by the **left** head: `⊥`, the two member
  congruences, a selection on a location (`sel1`), reflexivity at a selection
  (`selx`), the two recursive forms `bind1`/`bindx`, and the three
  intersection-and-union eliminations.

The premises of `sel1`, `and11`, `and12` and `or1` are themselves forms, as in
`stpp` ("not stp! for leverage in pushback", `dot_soundness.v:32`); every other
premise is a **strong** inclusion `SLe`, which may contain `trans` but no
selection that observes a location.  That the premises are strong is what lets
a premise of `bind1`/`bindx` be instantiated at a location and strengthened
again at a smaller pack count (`Inversion.LeTy.substB`, used by
`Inversion.ObsInv.bindStep`).

No `selL`/`selR` form exists: a closed selection is on a location, and in a
normal form it is read against the store.  This is the precise sense in which
`obs_conc_admissible` says the concrete `selL`/`selR` add no power. -/

/-- A **strong** inclusion: evidence, its typing, and the fact that it makes no
selection on a location through an observation. -/
structure SLe {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (S T : Ty σ s) : Type where
  /-- The evidence. -/
  ev : Le σ s
  /-- Its typing. -/
  typed : LeTy G W Γ ev S T
  /-- It is strong. -/
  strong : ev.Strong

mutual

/-- A closed inclusion in normal form, the forms decided by the right head
first.  See the section header. -/
inductive LeNf {σ : Sig} (G : Store σ σ) (W : StoreTy σ) :
    Ty σ [] → Ty σ [] → Type where
  /-- Everything is below `⊤`. -/
  | top (T : Ty σ []) : LeNf G W T .TTop
  /-- `stp_and2`. -/
  | and2 {T T1 T2 : Ty σ []} :
      SLe G W .nil T T1 → SLe G W .nil T T2 → LeNf G W T (.TAnd T1 T2)
  /-- `stp_or21`. -/
  | or21 {T T1 T2 : Ty σ []} : SLe G W .nil T T1 → LeNf G W T (.TOr T1 T2)
  /-- `stp_or22`. -/
  | or22 {T T1 T2 : Ty σ []} : SLe G W .nil T T2 → LeNf G W T (.TOr T1 T2)
  /-- `stp_strong_sel2`: below a selection on a location is below its stored
  definition. -/
  | sel2 {l : BVar σ .var} {a : Lb} {TX T : Ty σ []} :
      (G.lookup l).get? a = some (.dty TX) → SLe G W .nil T TX →
      LeNf G W T (.TSel (.conc l) a)
  /-- A form decided by the left head. -/
  | head {S T : Ty σ []} : LeNfHead G W S T → LeNf G W S T

/-- A closed inclusion in normal form whose rule is decided by the left head. -/
inductive LeNfHead {σ : Sig} (G : Store σ σ) (W : StoreTy σ) :
    Ty σ [] → Ty σ [] → Type where
  /-- `⊥` is below everything. -/
  | bot (T : Ty σ []) : LeNfHead G W .TBot T
  /-- `stp_fun`. -/
  | fn {a : Lb} {S1 S2 : Ty σ []} {U1 U2 : Ty σ ([],x)} :
      SLe G W .nil S2 S1 → SLe G W (Ctx.nil.cons S2.weaken) U1 U2 →
      LeNfHead G W (.TFun a S1 U1) (.TFun a S2 U2)
  /-- `stp_typ`. -/
  | typ {a : Lb} {S1 U1 S2 U2 : Ty σ []} :
      SLe G W .nil S2 S1 → SLe G W .nil U1 U2 →
      LeNfHead G W (.TTyp a S1 U1) (.TTyp a S2 U2)
  /-- `stp_strong_sel1`, its premise a form. -/
  | sel1 {l : BVar σ .var} {a : Lb} {TX T : Ty σ []} :
      (G.lookup l).get? a = some (.dty TX) → LeNf G W TX T →
      LeNfHead G W (.TSel (.conc l) a) T
  /-- `stp_selx`: reflexivity at a selection. -/
  | selx (p : Vr σ []) (a : Lb) : LeNfHead G W (.TSel p a) (.TSel p a)
  /-- `stp_bind1`: a recursive type on the left only, the self assumed at the
  opened left body. -/
  | bind1 {T1 : Ty σ ([],x)} {T2 : Ty σ []} :
      SLe G W (Ctx.nil.cons T1) T1 T2.weaken → LeNfHead G W (.TBind T1) T2
  /-- `stp_bindx`. -/
  | bindx {T1 T2 : Ty σ ([],x)} :
      SLe G W (Ctx.nil.cons T1) T1 T2 → LeNfHead G W (.TBind T1) (.TBind T2)
  /-- `stp_and11`, its premise a form. -/
  | and11 {T1 T2 T : Ty σ []} : LeNf G W T1 T → LeNfHead G W (.TAnd T1 T2) T
  /-- `stp_and12`, its premise a form. -/
  | and12 {T1 T2 T : Ty σ []} : LeNf G W T2 T → LeNfHead G W (.TAnd T1 T2) T
  /-- `stp_or1`, both premises forms. -/
  | or1 {T1 T2 T : Ty σ []} :
      LeNf G W T1 T → LeNf G W T2 T → LeNfHead G W (.TOr T1 T2) T

end

end FCdotR
