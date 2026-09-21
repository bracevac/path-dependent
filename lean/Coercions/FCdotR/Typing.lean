import Coercions.FCdotR.Syntax

/-!
# Typing of FCdotR evidence

Two mutually inductive judgments, the images of `Oopsla16.Stp` and
`Oopsla16.Htp`:

```text
Γ ⊢ e : S ≤ T          Γ ⊢ v :: p : T      with T : Ty σ (scopeAt p)
```

Three things are worth reading against the source.

* **The truncation is the index.**  `VcTy`'s type lives at `scopeAt p`, and
  `vcSub` widens in `ctxAt Γ p`.  At an abstract subject that is the
  reference's `stp GL G1 T1 T2` with `length GL = S x` and `GH = GU ++ GL`
  (`dot.v:390-392`); at a location it is `stp [] G1 T1 T2`
  (`dot.v:308`), because `scopeAt (conc ℓ) = []`.  One rule covers both, which
  is what makes the substitution theorem structure-preserving: substitution
  sends an abstract subject to either zone, and the reference's own proof
  splits into `htp` and `htpy` at exactly that point.
* **`vcPack`'s subject index is `Vr.conc`.**  Packing an abstract variable is
  therefore not merely absent from the judgment, it is unwritable.  That is the
  target's form of the restriction whose necessity
  `Oopsla16/PackingCounterexample` and `coq/oopsla16-packing/` establish.
  Packing is still available on *atoms*, where the source allows it
  (`T_VarPack`, `dot.v:231-235`).
* **`bindx`'s hypothesis is the opened body**, `Γ.cons S`, never the folded
  `μ S`.  The folded assumption is what `FCdot/RecursiveEvidence.lean`'s
  composition prototype takes, and it hands back the packing power the source
  forbids.  The only inclusion that mentions `μ` on the right with a non-`μ`
  left would be a `stp_bind2`, which the source does not have and this
  calculus does not add; `muDrop`'s target is a weakening for the same reason.

The store's literal types are carried as a *function* `StoreTy`, not as a
derivation, so that `tyOf` is data and its stability under allocation is that
function's extension.

Terms, atoms and definitions are not typed here yet; the milestone this module
closes is that an `Oopsla16` recursive-subtyping derivation elaborates to
closed evidence.

One ergonomic consequence of indexing by a prefix: `scopeAt` is not injective —
`scopeAt (conc ℓ)` is `[]` for every `ℓ` — so a subject cannot be recovered
from the scope of its observation evidence.  Where elaboration has to guess it,
pass it: `VcTy.vcSub (p := …)`.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store renameNil)

/-- The type of each stored literal, before its self is instantiated. -/
abbrev StoreTy (σ : Sig) : Type := (l : BVar σ .var) → Ty σ ([],x)

/-- The type of the object at a location, its self instantiated by the
location itself.  The counterpart of `T_Vary`'s `substt x T'`
(`dot.v:220-226`). -/
def tyOf {σ : Sig} (W : StoreTy σ) (l : BVar σ .var) : Ty σ [] :=
  (W l).substVr (.conc l)

mutual

/-- `Γ ⊢ e : S ≤ T`, the image of `Oopsla16.Stp`. -/
inductive LeTy : {σ s : Sig} → Store σ σ → StoreTy σ → Ctx σ s → Le σ s →
    Ty σ s → Ty σ s → Type where
  | refl {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} (T : Ty σ s) :
      LeTy G W Γ (.refl T) T T
  | trans {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {S T : Ty σ s} (M : Ty σ s) {e f : Le σ s} :
      LeTy G W Γ e S M → LeTy G W Γ f M T → LeTy G W Γ (.trans M e f) S T
  | top {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} (T : Ty σ s) :
      LeTy G W Γ (.top T) T .TTop
  | bot {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} (T : Ty σ s) :
      LeTy G W Γ (.bot T) .TBot T
  | dtyp {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} {l : Lb}
      {S1 U1 S2 U2 : Ty σ s} {e f : Le σ s} :
      LeTy G W Γ e S2 S1 → LeTy G W Γ f U1 U2 →
      LeTy G W Γ (.dtyp l e f) (.TTyp l S1 U1) (.TTyp l S2 U2)
  | dfun {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} {l : Lb}
      {S1 S2 : Ty σ s} {U1 U2 : Ty σ (s,x)} {e : Le σ s} {f : Le σ (s,x)} :
      LeTy G W Γ e S2 S1 → LeTy G W (Γ.cons S2.weaken) f U1 U2 →
      LeTy G W Γ (.dfun l e f) (.TFun l S1 U1) (.TFun l S2 U2)
  | andI {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} {T : Ty σ s}
      (T1 T2 : Ty σ s) {e f : Le σ s} :
      LeTy G W Γ e T T1 → LeTy G W Γ f T T2 →
      LeTy G W Γ (.andI T1 T2 e f) T (.TAnd T1 T2)
  | andE1 {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {T1 T : Ty σ s} (T2 : Ty σ s) {e : Le σ s} :
      LeTy G W Γ e T1 T → LeTy G W Γ (.andE1 T2 e) (.TAnd T1 T2) T
  | andE2 {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {T2 T : Ty σ s} (T1 : Ty σ s) {e : Le σ s} :
      LeTy G W Γ e T2 T → LeTy G W Γ (.andE2 T1 e) (.TAnd T1 T2) T
  | orI1 {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {T T1 : Ty σ s} (T2 : Ty σ s) {e : Le σ s} :
      LeTy G W Γ e T T1 → LeTy G W Γ (.orI1 T2 e) T (.TOr T1 T2)
  | orI2 {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {T T2 : Ty σ s} (T1 : Ty σ s) {e : Le σ s} :
      LeTy G W Γ e T T2 → LeTy G W Γ (.orI2 T1 e) T (.TOr T1 T2)
  | orE {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} {T : Ty σ s}
      (S1 S2 : Ty σ s) {e f : Le σ s} :
      LeTy G W Γ e S1 T → LeTy G W Γ f S2 T →
      LeTy G W Γ (.orE S1 S2 e f) (.TOr S1 S2) T
  /-- `stp_strong_sel1`: the stored definition read exactly, its premise in the
  empty local scope. -/
  | defL {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} {a : Lb} {TX T2 : Ty σ []} {e : Le σ []} :
      (G.lookup l).get? a = some (.dty TX) →
      LeTy G W .nil e TX T2 →
      LeTy G W Γ (.defL l a e) (.TSel (.conc l) a) (T2.rename renameNil)
  /-- `stp_strong_sel2`. -/
  | defR {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} {a : Lb} {T1 TX : Ty σ []} {e : Le σ []} :
      (G.lookup l).get? a = some (.dty TX) →
      LeTy G W .nil e T1 TX →
      LeTy G W Γ (.defR l a e) (T1.rename renameNil) (.TSel (.conc l) a)
  /-- `stp_sel1`, at a subject of either zone. -/
  | selL {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {p : Vr σ s} {a : Lb} {U : Ty σ (scopeAt p)} {v : Vc σ (scopeAt p)} :
      VcTy G W Γ p v (.TTyp a .TBot U) →
      LeTy G W Γ (.selL p a v) (.TSel p a) (U.rename (renameAt p))
  /-- `stp_sel2`. -/
  | selR {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {p : Vr σ s} {a : Lb} {S : Ty σ (scopeAt p)} {v : Vc σ (scopeAt p)} :
      VcTy G W Γ p v (.TTyp a S .TTop) →
      LeTy G W Γ (.selR p a v) (S.rename (renameAt p)) (.TSel p a)
  /-- `stp_bindx`.  The hypothesis is the opened body. -/
  | bindx {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      (S T : Ty σ (s,x)) {e : Le σ (s,x)} :
      LeTy G W (Γ.cons S) e S T → LeTy G W Γ (.bindx S T e) (.TBind S) (.TBind T)
  /-- `μ(T↑) ≤ T`.  The target is a weakening, which is the source's
  `z ∉ FV(T2)` in `stp_bind1` (`dot.v:328-333`). -/
  | muDrop {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} (T : Ty σ s) :
      LeTy G W Γ (.muDrop T) (.TBind T.weaken) T

/-- `Γ ⊢ v :: p : T`, the image of `Oopsla16.Htp`.  The type lives in the
subject's prefix scope. -/
inductive VcTy : {σ s : Sig} → Store σ σ → StoreTy σ → Ctx σ s →
    (p : Vr σ s) → Vc σ (scopeAt p) → Ty σ (scopeAt p) → Type where
  /-- `htp_var`. -/
  | vcVar {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {x : BVar s .var} :
      VcTy G W Γ (.abs x) .vcVar (Γ.lookupAt x)
  /-- The stored literal's type, the observation counterpart of `T_Vary`. -/
  | vcLoc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} :
      VcTy G W Γ (.conc l) (.vcLoc l) (tyOf W l)
  /-- **Packing, at a location only.**  The subject index is `Vr.conc`, so
  there is no instance of this rule at an abstract variable. -/
  | vcPack {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} {T : Ty σ ([],x)} {v : Vc σ []} :
      VcTy G W Γ (.conc l) v (T.substVr (.conc l)) →
      VcTy G W Γ (.conc l) (.vcPack T v) (.TBind T)
  /-- `htp_unpack`. -/
  | vcUnfold {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {p : Vr σ s} {T : Ty σ (scopeAt p,x)} {v : Vc σ (scopeAt p)} :
      VcTy G W Γ p v (.TBind T) →
      VcTy G W Γ p (.vcUnfold T v) (T.substVr (selfAt p))
  /-- `htp_sub`.  The inclusion is checked in the subject's prefix. -/
  | vcSub {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {p : Vr σ s} (T1 : Ty σ (scopeAt p)) {T2 : Ty σ (scopeAt p)}
      {e : Le σ (scopeAt p)} {v : Vc σ (scopeAt p)} :
      VcTy G W Γ p v T1 → LeTy G W (ctxAt Γ p) e T1 T2 →
      VcTy G W Γ p (.vcSub T1 e v) T2

end

end FCdotR
