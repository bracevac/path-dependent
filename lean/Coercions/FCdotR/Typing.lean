import Coercions.FCdotR.Syntax
import Coercions.Oopsla16.Typing

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
* **`vcPack`'s subject index is `Vr.conc`.**  The syntax node exists at every
  scope, but at an abstract variable there is no rule that types it.  That is the
  target's form of the restriction whose necessity
  `Oopsla16/PackingCounterexample` and `coq/oopsla16/packing/` establish.
  Packing is still available on *atoms*, where the source allows it
  (`T_VarPack`, `dot.v:231-235`).
* **`bindx`'s hypothesis is the opened body**, `Γ.cons S`, never the folded
  `μ S`.  The only inclusion that mentions `μ` on the right with a non-`μ`
  left would be a `stp_bind2`, which the source does not have and this
  calculus does not add; `muDrop`'s target is a weakening for the same reason.

The store's literal types are carried as a *function* `StoreTy`, not as a
derivation, so that `tyOf` is data and its stability under allocation is that
function's extension.

**A location is observed by two rules.**  `vcLoc` reads the type off that
function.  `vcLocAny` observes the location at a self type `T` its node
carries, instantiated at the location, whenever that instance **matches** the
stored literal (`LitMatch`): it is `⊤` or a right-nested intersection of
members, where a type member is exactly what the literal defines at its label,
and a method member `{b : S → U}` finds at `b` a method stored with both
annotations, `S` and `U` exactly.  A stored method that lacks an annotation
matches no method member (`StoreTyping.LitMatch.no_unannotated_method`).

* **It is not `T_Vary`.**  `T_Vary` (`dot.v:220-226`) re-types the stored
  literal under its own self, every method body included, and reports the
  literal's whole intersection type.  The match re-types no method body and
  may leave members out.  So the rule gives a location `⊤` whatever it stores,
  and gives a location with unannotated stored methods the matching types that
  leave those methods out; neither needs the method bodies to be typable.
* **Over an honest store it derives nothing the source cannot.**  If `W` is
  honest (`StoreTyping.Store.Honest`), every conjunct of a matched type is a
  conjunct of the recorded type `tyOf W ℓ`: type members because `D_Typ` makes
  them exact, method members because the match fixes the stored annotations
  and `D_Fun`'s `EqSome` then fixes the recorded method type.  So `Oopsla16`
  proves the recorded type below the matched one
  (`Admissibility.Store.Honest.litMatch_stp`), and `T_Vary` at the honesty
  witness followed by `T_Sub` types the location at the matched type
  (`Admissibility.Store.Honest.litMatch_hasType`).
* **`T_Vary` gives the match exactly when the stored methods are annotated.**
  `StoreTyping.varyLitMatch` takes `T_Vary`'s two premises *and* that the
  literal stored at `ℓ` carries both annotations on every method
  (`StoreTyping.Dms.Annotated`); `StoreTyping.varyLitMatch_annotated` is the
  converse.  Without the annotations, `vcLocAny` and `AtomTy.varConcAny`
  type `ℓ` at no type `T_Vary` gives it (`Admissibility.vcLocAny_not_vary`,
  `Admissibility.varConcAny_not_vary`): that type lists every member, the
  unannotated method included.  `vcLoc` (and `AtomTy.varConc` for terms)
  still types `ℓ` at `tyOf W ℓ`, which over an honest store is a type
  `T_Vary` gives, but at no other type, while the elaboration of `T_Vary` has
  to work at every store typing and for every `T_Vary` typing.  That is why it
  takes `StoreTyping.Store.Annotated G`; that no elaboration could do without
  the hypothesis is argued here, not proved.  The empty store satisfies it
  trivially, and so does every store of the honest-store theorems, whose
  witnesses are in `Elaboration.DmsFrag`.
* **It takes the stored annotations on trust**, as `vcLoc` takes the store
  typing.  A method member is accepted at the stored method's two annotations
  whether or not the stored body has that type, and `W` plays no part.  Over a
  store whose annotated methods do not have their annotated types there is no
  honest store typing, and the rule types terms the source does not type at
  all: over `{def 0(y : ⊤) : ⊥ = y}` the target types `ℓ.0(ℓ)` at `⊥` at every
  store typing, and `Oopsla16` types it at no type
  (`Coverage.UncheckedBody.appBot_typed`, `app_untypable`, `not_honest`).  So
  the admissibility of the second point needs an honest store, and where there
  is none no store typing helps (`Coverage.noVary_not_admissible`).
* **It is sound.**  Every result downstream is proved for the rule as stated.
  Nothing reads a method body off the premise: at run time the body the
  machine invokes is typed by the machine store's honesty invariant
  (`Preservation.MachineStore.Honest`), and the erasure of a machine store
  annotates every method, so there a matched method member is the stored
  method's own type.  That invariant is what justifies, in the safety
  theorems, the trust of the previous point.
* **It is decidable**: one pass over the type, comparing each member with what
  the literal stores by the equality of types `Oopsla16.Ty` derives
  (`Checker.litMatchB`).  That is what a checker needs.  `T_Vary`'s premises
  are a source re-typing of the stored literal, method bodies included, and
  checking them would mean deciding `Oopsla16` typing.

The first rule is kept because every result downstream is stated at it.  Over
an honest store whose literal at `ℓ` is annotated it is the instance of the
second at the recorded type (`StoreTyping.Store.Honest.vcLoc_of_vcLocAny`);
at a location whose literal has an unannotated method it is not an instance
of the second at all (`StoreTyping.Store.Honest.not_vcLocAny_tyOf`).

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
open Oopsla16 (Vr Ty Lb Ctx Store Dm renameNil)

/-- The type of each stored literal, before its self is instantiated. -/
abbrev StoreTy (σ : Sig) : Type := (l : BVar σ .var) → Ty σ ([],x)

/-- The type of the object at a location, its self instantiated by the
location itself.  The counterpart of `T_Vary`'s `substt x T'`
(`dot.v:220-226`). -/
def tyOf {σ : Sig} (W : StoreTy σ) (l : BVar σ .var) : Ty σ [] :=
  (W l).substVr (.conc l)

/-- **A type matches a stored literal**, relative to the literal's member
lookup `g` (its `Dms.get?`): it is `⊤`, or a right-nested intersection of a
member with a matching rest.  A type member is exact and is what `g` finds at
its label.  A method member `{b : S → U}` finds at `b` a method stored with
**both** annotations, `some S` and `some U`: the stored annotations are the
member's types, so a method stored without an annotation matches no method
member (`StoreTyping.LitMatch.no_unannotated_method`).  Nothing is asked of a
method's body, and a member of the literal may be left out.

This is the premise of the two location rules, `VcTy.vcLocAny` and
`TermTyping.AtomTy.varConcAny`.  It is not `T_Vary`'s premise; `Typing`'s
module header says how the two relate.  Whether it holds is decided by one
pass over the type (`Checker.litMatchB`). -/
inductive LitMatch {σ : Sig} (g : Lb → Option (Dm σ [])) : Ty σ [] → Type where
  /-- `⊤` matches every literal. -/
  | top : LitMatch g .TTop
  /-- A type member, exact, as `g` defines it at its label. -/
  | typ {b : Lb} {TX B : Ty σ []} :
      g b = some (.dty TX) → LitMatch g B → LitMatch g (.TAnd (.TTyp b TX TX) B)
  /-- A method member, at exactly the two annotations the stored method
  carries. -/
  | fn {b : Lb} {S : Ty σ []} {U : Ty σ ([],x)} {B : Ty σ []}
      {t : Oopsla16.Tm σ ([],x)} :
      g b = some (.dfun (some S) (some U) t) →
      LitMatch g B → LitMatch g (.TAnd (.TFun b S U) B)

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
  /-- The stored literal's type **as the store typing records it**, the
  observation counterpart of `T_Vary` at that one type.  Over an honest store
  whose literal at `l` is annotated it is the instance of `vcLocAny` at `W l`
  (`StoreTyping.Store.Honest.vcLoc_of_vcLocAny`). -/
  | vcLoc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} :
      VcTy G W Γ (.conc l) (.vcLoc l) (tyOf W l)
  /-- The stored literal's type **at a self type the node carries**: `T`,
  instantiated at the location, whenever that instance matches the stored
  literal (`LitMatch`).  This is not `T_Vary` (`dot.v:220-226`).  A source
  `T_Vary` gives the match when the literal stored at `l` carries both
  annotations on every method (`StoreTyping.varyLitMatch`), and only then
  (`StoreTyping.varyLitMatch_annotated`); in that case any type the literal
  has under its own self may be observed here, not merely the one `StoreTy`
  records.  Conversely the premise re-types no method body, so the
  rule also observes a location at types `T_Vary` does not give it, such as
  `⊤`; over an honest store each of them is still a source typing of the
  location (`Admissibility.Store.Honest.litMatch_hasType`). -/
  | vcLocAny {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} {T : Ty σ ([],x)} :
      LitMatch (G.lookup l).get? (T.substVr (.conc l)) →
      VcTy G W Γ (.conc l) (.vcLocAny l T) (T.substVr (.conc l))
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
