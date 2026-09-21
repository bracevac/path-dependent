import Coercions.FCdotR.Prefix

/-!
# Syntax of FCdotR

Evidence, atoms, terms and definitions.  Types, contexts and stores are
`Oopsla16`'s verbatim: the type translation is the identity, which is what
makes `DotToFCdot/RecursiveTranslationCounterexample`'s collapse of recursive
layers have no counterpart here — `Ty.TBind` is a constructor of the source's
own grammar and nothing identifies it with an object type.

Four sorts, in two groups.

* **Inclusion evidence** `Le`, the image of `Oopsla16.Stp`, and **observation
  evidence** `Vc`, the image of `Oopsla16.Htp`.  Neither contains an atom, so
  the dependency runs atom → evidence and never back.  That is what lets the
  substitution theorem be layered.
* **Atoms** `Atom` and **terms** `Tm`, the images of variable typing and term
  typing.  Atoms have `pack`, the image of `T_VarPack`; observation evidence
  has `vcPack`, whose subject is a *location* only.

`Vc` is indexed by its subject's **prefix** scope, so `selL p _` takes a
`Vc σ (scopeAt p)`.  The reference's `length GL = S x` and `GH = GU ++ GL`
(`dot.v:391-392`) are therefore the index, here as in `Oopsla16`.

This module is syntax only; every well-formedness condition is in `Typing`.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb)

mutual

/-- Inclusion evidence, the image of `Oopsla16.Stp`.  Erases to nothing. -/
inductive Le : Sig → Sig → Type where
  /-- Reflexivity.  The source derives it (`dot.v:908`); here it is primitive
  because evidence must name the type it is reflexive at. -/
  | refl {σ s : Sig} (T : Ty σ s) : Le σ s
  /-- Transitivity, naming its middle type.  `stp_trans`. -/
  | trans {σ s : Sig} (M : Ty σ s) (e f : Le σ s) : Le σ s
  /-- `stp_top`. -/
  | top {σ s : Sig} (T : Ty σ s) : Le σ s
  /-- `stp_bot`. -/
  | bot {σ s : Sig} (T : Ty σ s) : Le σ s
  /-- `stp_typ`: contravariant in the lower bound. -/
  | dtyp {σ s : Sig} (l : Lb) (e f : Le σ s) : Le σ s
  /-- `stp_fun`: the codomains are compared under the new domain. -/
  | dfun {σ s : Sig} (l : Lb) (e : Le σ s) (f : Le σ (s,x)) : Le σ s
  /-- `stp_and2`. -/
  | andI {σ s : Sig} (T1 T2 : Ty σ s) (e f : Le σ s) : Le σ s
  /-- `stp_and11`. -/
  | andE1 {σ s : Sig} (T2 : Ty σ s) (e : Le σ s) : Le σ s
  /-- `stp_and12`. -/
  | andE2 {σ s : Sig} (T1 : Ty σ s) (e : Le σ s) : Le σ s
  /-- `stp_or21`. -/
  | orI1 {σ s : Sig} (T2 : Ty σ s) (e : Le σ s) : Le σ s
  /-- `stp_or22`. -/
  | orI2 {σ s : Sig} (T1 : Ty σ s) (e : Le σ s) : Le σ s
  /-- `stp_or1`. -/
  | orE {σ s : Sig} (S1 S2 : Ty σ s) (e f : Le σ s) : Le σ s
  /-- `stp_strong_sel1`: read the stored definition exactly.  Its premise is
  checked in the empty local scope, so the sub-evidence is `Le σ []`. -/
  | defL {σ s : Sig} (l : BVar σ .var) (a : Lb) (e : Le σ []) : Le σ s
  /-- `stp_strong_sel2`. -/
  | defR {σ s : Sig} (l : BVar σ .var) (a : Lb) (e : Le σ []) : Le σ s
  /-- `stp_sel1`, generalised to a subject of either zone.  The observation
  lives in the subject's prefix. -/
  | selL {σ s : Sig} (p : Vr σ s) (a : Lb) (v : Vc σ (scopeAt p)) : Le σ s
  /-- `stp_sel2`. -/
  | selR {σ s : Sig} (p : Vr σ s) (a : Lb) (v : Vc σ (scopeAt p)) : Le σ s
  /-- `stp_bindx`.  The hypothesis is the **opened body**, never the folded
  type; that is the single correction to `FCdot/RecursiveEvidence.lean`. -/
  | bindx {σ s : Sig} (S T : Ty σ (s,x)) (e : Le σ (s,x)) : Le σ s
  /-- `μ(T↑) ≤ T`, the target of which is a **weakening**.  `μ T ≤ T{x}` would
  be an unsoundness, not an optimisation: it is the fold-exposing inclusion
  that `FCdot/ReceiverCounterexample` turns into bottom. -/
  | muDrop {σ s : Sig} (T : Ty σ s) : Le σ s

/-- Observation evidence, the image of `Oopsla16.Htp`.  Its scope index is its
subject's prefix; the subject itself is fixed by the enclosing `selL`/`selR`
or by the typing judgment. -/
inductive Vc : Sig → Sig → Type where
  /-- `htp_var`: the subject's own hypothesis. -/
  | vcVar {σ s : Sig} : Vc σ s
  /-- The type of a stored object, the observation counterpart of `T_Vary`. -/
  | vcLoc {σ s : Sig} (l : BVar σ .var) : Vc σ s
  /-- **Packing, at a location only.**  The typing rule's subject index is
  `Vr.conc`, so packing an abstract variable is not merely absent but
  unwritable — which is what `Oopsla16/PackingCounterexample` shows it must
  be. -/
  | vcPack {σ s : Sig} (T : Ty σ (s,x)) (v : Vc σ s) : Vc σ s
  /-- `htp_unpack`. -/
  | vcUnfold {σ s : Sig} (T : Ty σ (s,x)) (v : Vc σ s) : Vc σ s
  /-- `htp_sub`.  The inclusion is scoped at the prefix, which is the
  reference's truncated `GL`. -/
  | vcSub {σ s : Sig} (T1 : Ty σ s) (e : Le σ s) (v : Vc σ s) : Vc σ s

end

mutual

/-- Atoms: variable typing with explicit casts and explicit fold and unfold.
`pack` is the image of `T_VarPack`, which the source allows on terms and
forbids inside subtyping. -/
inductive Atom : Sig → Sig → Type where
  /-- A variable of either zone. -/
  | var {σ s : Sig} (p : Vr σ s) : Atom σ s
  /-- `T_Sub` at a variable. -/
  | cast {σ s : Sig} (a : Atom σ s) (e : Le σ s) : Atom σ s
  /-- `T_VarPack`. -/
  | pack {σ s : Sig} (T : Ty σ (s,x)) (a : Atom σ s) : Atom σ s
  /-- `T_VarUnpack`. -/
  | unpack {σ s : Sig} (T : Ty σ (s,x)) (a : Atom σ s) : Atom σ s

/-- Terms.  Application takes atoms, so the calculus is in normal form; the
source's general `tapp` is A-normalised by the elaboration. -/
inductive Tm : Sig → Sig → Type where
  | atom {σ s : Sig} (a : Atom σ s) : Tm σ s
  /-- An object literal, with its self type. -/
  | new {σ s : Sig} (T : Ty σ (s,x)) (ds : Defs σ (s,x)) : Tm σ s
  /-- Method invocation. -/
  | app {σ s : Sig} (a : Atom σ s) (l : Lb) (b : Atom σ s) : Tm σ s
  | «let» {σ s : Sig} (t : Tm σ s) (u : Tm σ (s,x)) : Tm σ s
  | cast {σ s : Sig} (t : Tm σ s) (e : Le σ s) : Tm σ s

/-- Definition lists.  Labels stay positional, as in the source. -/
inductive Defs : Sig → Sig → Type where
  | dnil {σ s : Sig} : Defs σ s
  /-- A type member, exact. -/
  | dty {σ s : Sig} (T : Ty σ s) (ds : Defs σ s) : Defs σ s
  /-- A method member; the codomain and the body bind the parameter. -/
  | dfun {σ s : Sig} (S : Ty σ s) (U : Ty σ (s,x)) (t : Tm σ (s,x))
      (ds : Defs σ s) : Defs σ s

end

/-- The variable an atom is rooted at.  Casts, packs and unpacks do not move
it, which is what makes an atom's runtime meaning its root's. -/
def Atom.root {σ s : Sig} : Atom σ s → Vr σ s
  | .var p => p
  | .cast a _ => a.root
  | .pack _ a => a.root
  | .unpack _ a => a.root

/-- The number of members, hence the label of the next one. -/
def Defs.length {σ s : Sig} : Defs σ s → Nat
  | .dnil => 0
  | .dty _ ds => ds.length + 1
  | .dfun _ _ _ ds => ds.length + 1

end FCdotR
