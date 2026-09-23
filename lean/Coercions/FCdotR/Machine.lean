import Coercions.FCdotR.Syntax
import Coercions.FCdotR.Structural
import Coercions.FCdotR.Subst
import Coercions.Oopsla16.Semantics

/-!
# The FCdotR machine

A store-and-continuation machine for the terms of `Syntax`, in the shape of
`Coercions.FCdot.Machine` and `Coercions.DotMNF.Machine`: a state is a store
of definition lists, a continuation of `let` and `cast` frames, and a running
term of the **empty local scope**, all indexed by one store scope.  Allocation
extends that scope, and the step relation carries the reference's own
`Oopsla16.Grows` index so that a step of this machine and a step of
`Oopsla16.Semantics` can be compared at the same index.

Evidence is a no-op at runtime.  `cast` pushes a frame, a frame over an atom
is absorbed into the atom, and nothing ever inspects a coercion: `Le` and `Vc`
occur in the state only because they occur in the syntax.

## What the store holds, and why it is not the source's

The brief for this module asked for a machine over an `Oopsla16.Store σ σ`,
i.e. over *erased* definition lists, so that the source machine and the target
machine share one store.  That cannot be closed, and the reason is worth
recording: a stored `dfun`'s body is what the machine runs after an
invocation, so if the store held erased definitions, `app` would produce an
`Oopsla16.Tm` and the target machine would leave its own language after one
method call.  The store therefore holds **target** definitions, `Defs σ []`,
and the sharing is by erasure instead: `FCdotR.MachineStore.erase` (in `Erasure`) is
an `Oopsla16.Store σ σ`, it commutes with every operation the machine performs
on the store, and — because the type translation is the identity — a type
member is carried across *unchanged*, so `LeTy.defL`/`defR`, which read the
source store, read exactly the members this store holds.

It is called `MachineStore`, not `Store`.  The rest of the library writes
`open Oopsla16 (… Store …)` inside `namespace FCdotR`, and in a module that
imports this one as well the enclosing namespace would win over the `open`
*silently*, with no ambiguity error: bare `Store` would become the machine's.
A preservation module needs both stores at once, so the machine's is given a
name of its own and bare `Store` always means `Oopsla16.Store`.

## What the machine substitutes, and what it drops

`rename` and `app` substitute the **root location** of an atom, not the atom.
Dropping the atom's casts is sound at runtime, since erasure drops them too
(`Erasure.Atom.erase`), but it is not type-preserving: `FCdot.Machine` keeps
them with `Tm.adjust`, and a preservation theorem for this machine would have
to do the same.  This module proves no typing property, so the simpler rule is
taken and the limitation recorded here.

## The substitution

`Inst` below is the only substitution the machine performs: a store location
for the **oldest** binder of the local scope, i.e. `Subst.one (.conc y)` and
its lifts.  It is given its own inductive so that the traversals recurse on the
instantiation *structurally* and their equations hold definitionally, which is
what makes a machine run compute.  `Inst.at` is its closure under restriction.

**`Inst` is a `MonoSyn`.**  `MonoSyn.ofInst` below sends `.base` to
`MonoSyn.oneConc` and `.lift` to `MonoSyn.lift`, so every substitution this
machine performs is one of `Subst`'s generated substitutions and is therefore
covered by `SubstTyping`'s and `TermSubst`'s substitution theorems: the
`rename`, `alloc` and `app` rules all substitute at `MonoSyn.oneConc y`.

What is **not** established here is that the *syntactic* actions agree, i.e.
that `Le.inst e ι y` is `e.subst (MonoSyn.ofInst ι y)`.  They do not agree, and
deliberately: `Vc.inst` sends `vcVar` at the instantiated binder to `vcLoc y`,
because the image is a location and `htp_var` cannot justify it, whereas
`Vc.subst` keeps `vcVar` — `Vc.subst` is the erasure-preserving action on
syntax and `VcTy.substEv` is the semantic one.  `Le.inst` likewise leaves a
`defL`/`defR`'s sub-evidence alone where `Le.subst` re-traverses it through
`atNil`.  What *is* established, in `Erasure`, is that the two agree after
erasure (`Tm.erase_inst_subst`), which is all a runtime statement needs.

This module contains no typing judgment, no preservation or progress result,
and no erasure; erasure and the simulation are `FCdotR.Erasure`.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Subst Grows)

/-! ## Instantiating the oldest binder -/

/-- `Inst s1 s2`: `s1` is `s2` with one further binder at the bottom, the one
the machine instantiates by a store location.  `base` is that binder alone and
`lift` pushes under a binder the substitution does not touch. -/
inductive Inst : Sig → Sig → Type where
  /-- The binder being instantiated is the only one. -/
  | base : Inst ([],x) []
  /-- One more binder, kept. -/
  | lift {s1 s2 : Sig} : Inst s1 s2 → Inst (s1,x) (s2,x)

/-- The `Oopsla16` substitution an `Inst` denotes: `Subst.one (.conc y)` under
`n` lifts.  Types are the source's, so this is how the machine substitutes in
them. -/
def Inst.toSubst {σ : Sig} : {s1 s2 : Sig} → Inst s1 s2 → BVar σ .var →
    Subst σ s1 σ s2
  | _, _, .base, y => Subst.one (.conc y)
  | _, _, .lift ι, y => (ι.toSubst y).lift

/-- **The machine's substitution is a generated substitution.**  `base` is
`MonoSyn.oneConc`, which is the generator `Subst` introduced for exactly this
family, and `lift` is `MonoSyn.lift`.  So `SubstTyping.LeTy.substEv`,
`SubstTyping.VcTy.substEv` and `TermSubst.TmTy.substEv` all apply to what the
machine does, with no second substitution machinery. -/
def MonoSyn.ofInst {σ : Sig} : {s1 s2 : Sig} → (ι : Inst s1 s2) →
    (y : BVar σ .var) → MonoSyn (ι.toSubst y)
  | _, _, .base, y => .oneConc y
  | _, _, .lift ι, y => .lift (MonoSyn.ofInst ι y)

/-- At the binder the machine actually instantiates, the generated
substitution is `MonoSyn.oneConc` on the nose. -/
@[simp] theorem MonoSyn.ofInst_base {σ : Sig} (y : BVar σ .var) :
    MonoSyn.ofInst .base y = MonoSyn.oneConc y := rfl

/-- And pushing under a binder is `MonoSyn.lift`. -/
@[simp] theorem MonoSyn.ofInst_lift {σ s1 s2 : Sig} (ι : Inst s1 s2)
    (y : BVar σ .var) : MonoSyn.ofInst ι.lift y = (MonoSyn.ofInst ι y).lift := rfl

/-- Instantiate a type.  A type of FCdotR *is* a type of `Oopsla16`, so this
is the source's own traversal. -/
abbrev Ty.inst {σ s1 s2 : Sig} (T : Ty σ s1) (ι : Inst s1 s2)
    (y : BVar σ .var) : Ty σ s2 :=
  T.subst (ι.toSubst y)

/-- Instantiate an abstract variable.  It is a separate recursion from
`Vr.inst` so that it recurses on the instantiation *structurally*: `.abs x'` is
not a subterm of `.abs (.there x')`, so a single traversal over `Vr` would be
compiled by well-founded recursion, whose equations do not hold definitionally
— and `Inst.at`'s type needs them to. -/
def Vr.instAbs {σ : Sig} : {s1 s2 : Sig} → Inst s1 s2 → BVar s1 .var →
    BVar σ .var → Vr σ s2
  | _, _, .base, .here, y => .conc y
  | _, _, .lift _, .here, _ => .abs .here
  | _, _, .lift ι, .there x', y => (Vr.instAbs ι x' y).weaken

/-- Instantiate a variable.  A location is untouched, which is what makes the
`selL`/`selR` cases of `Le.inst` typecheck without a transport. -/
def Vr.inst {σ s1 s2 : Sig} : Vr σ s1 → Inst s1 s2 → BVar σ .var → Vr σ s2
  | .conc c, _, _ => .conc c
  | .abs x, ι, y => Vr.instAbs ι x y

/-- The restriction of an instantiation at a subject: the substitution that
carries the subject's prefix into the image's prefix.  The family is closed
under this operation, which is exactly what `Structural.Mono` still lacks.

At the binder being instantiated the restriction is `base` and the image is a
location, whose prefix is the empty local scope; at any other binder it is a
shorter member of the same family. -/
def Inst.at {σ : Sig} : {s1 s2 : Sig} → (ι : Inst s1 s2) → (x : BVar s1 .var) →
    (y : BVar σ .var) → Inst (Oopsla16.scopeUpTo x) (scopeAt (Vr.instAbs ι x y))
  | _, _, .base, .here, _ => .base
  | _, _, .lift ι, .here, _ => .lift ι
  | _, _, .lift ι, .there x', y => by
      show Inst _ (scopeAt (Vr.instAbs ι x' y).weaken)
      rw [scopeAt_weaken]
      exact Inst.at ι x' y

/-! ## The substitution action on evidence

Neither sort contains an atom, so this block is independent of the term
block below, exactly as the syntax is. -/

mutual

/-- Instantiate inclusion evidence. -/
def Le.inst {σ : Sig} : {s1 s2 : Sig} → Le σ s1 → Inst s1 s2 → BVar σ .var →
    Le σ s2
  | _, _, .refl T, ι, y => .refl (Ty.inst T ι y)
  | _, _, .trans M e f, ι, y =>
      .trans (Ty.inst M ι y) (e.inst ι y) (f.inst ι y)
  | _, _, .top T, ι, y => .top (Ty.inst T ι y)
  | _, _, .bot T, ι, y => .bot (Ty.inst T ι y)
  | _, _, .dtyp a e f, ι, y => .dtyp a (e.inst ι y) (f.inst ι y)
  | _, _, .dfun a e f, ι, y => .dfun a (e.inst ι y) (f.inst ι.lift y)
  | _, _, .andI T1 T2 e f, ι, y =>
      .andI (Ty.inst T1 ι y) (Ty.inst T2 ι y) (e.inst ι y) (f.inst ι y)
  | _, _, .andE1 T2 e, ι, y => .andE1 (Ty.inst T2 ι y) (e.inst ι y)
  | _, _, .andE2 T1 e, ι, y => .andE2 (Ty.inst T1 ι y) (e.inst ι y)
  | _, _, .orI1 T2 e, ι, y => .orI1 (Ty.inst T2 ι y) (e.inst ι y)
  | _, _, .orI2 T1 e, ι, y => .orI2 (Ty.inst T1 ι y) (e.inst ι y)
  | _, _, .orE S1 S2 e f, ι, y =>
      .orE (Ty.inst S1 ι y) (Ty.inst S2 ι y) (e.inst ι y) (f.inst ι y)
  | _, _, .defL c a e, _, _ => .defL c a e
  | _, _, .defR c a e, _, _ => .defR c a e
  | _, _, .selL (.conc c) a v, _, _ => .selL (.conc c) a v
  | _, _, .selL (.abs x) a v, ι, y =>
      .selL (Vr.instAbs ι x y) a (v.inst (Inst.at ι x y) y)
  | _, _, .selR (.conc c) a v, _, _ => .selR (.conc c) a v
  | _, _, .selR (.abs x) a v, ι, y =>
      .selR (Vr.instAbs ι x y) a (v.inst (Inst.at ι x y) y)
  | _, _, .bindx S T e, ι, y =>
      .bindx (Ty.inst S ι.lift y) (Ty.inst T ι.lift y) (e.inst ι.lift y)
  | _, _, .muDrop T, ι, y => .muDrop (Ty.inst T ι y)

/-- Instantiate observation evidence.  At `base` the subject *is* the binder
being instantiated, so its own hypothesis `vcVar` becomes the stored literal's
type `vcLoc`: the observation counterpart of the source's `T_Vary` at the
recorded type.  It is `vcLoc` and not `vcLocAny` because the instantiation has
no literal or self type to put in a witness; a `vcLocAny` node already carries
both, lives at the empty local scope, and is left alone. -/
def Vc.inst {σ : Sig} : {s1 s2 : Sig} → Vc σ s1 → Inst s1 s2 → BVar σ .var →
    Vc σ s2
  | _, _, .vcVar, .base, y => .vcLoc y
  | _, _, .vcVar, .lift _, _ => .vcVar
  | _, _, .vcLoc c, _, _ => .vcLoc c
  | _, _, .vcLocAny c T ds, _, _ => .vcLocAny c T ds
  | _, _, .vcPack T v, ι, y => .vcPack (Ty.inst T ι.lift y) (v.inst ι y)
  | _, _, .vcUnfold T v, ι, y => .vcUnfold (Ty.inst T ι.lift y) (v.inst ι y)
  | _, _, .vcSub T1 e v, ι, y =>
      .vcSub (Ty.inst T1 ι y) (e.inst ι y) (v.inst ι y)

end

/-! ## The substitution action on atoms, terms and definitions -/

mutual

/-- Instantiate an atom. -/
def Atom.inst {σ : Sig} : {s1 s2 : Sig} → Atom σ s1 → Inst s1 s2 →
    BVar σ .var → Atom σ s2
  | _, _, .var p, ι, y => .var (Vr.inst p ι y)
  | _, _, .cast a e, ι, y => .cast (a.inst ι y) (e.inst ι y)
  | _, _, .pack T a, ι, y => .pack (Ty.inst T ι.lift y) (a.inst ι y)
  | _, _, .unpack T a, ι, y => .unpack (Ty.inst T ι.lift y) (a.inst ι y)

/-- Instantiate a term. -/
def Tm.inst {σ : Sig} : {s1 s2 : Sig} → Tm σ s1 → Inst s1 s2 → BVar σ .var →
    Tm σ s2
  | _, _, .atom a, ι, y => .atom (a.inst ι y)
  | _, _, .new T ds, ι, y => .new (Ty.inst T ι.lift y) (ds.inst ι.lift y)
  | _, _, .app a l b, ι, y => .app (a.inst ι y) l (b.inst ι y)
  | _, _, .let t u, ι, y => .let (t.inst ι y) (u.inst ι.lift y)
  | _, _, .cast t e, ι, y => .cast (t.inst ι y) (e.inst ι y)

/-- Instantiate a definition list. -/
def Defs.inst {σ : Sig} : {s1 s2 : Sig} → Defs σ s1 → Inst s1 s2 →
    BVar σ .var → Defs σ s2
  | _, _, .dnil, _, _ => .dnil
  | _, _, .dty T ds, ι, y => .dty (Ty.inst T ι y) (ds.inst ι y)
  | _, _, .dfun S U t ds, ι, y =>
      .dfun (Ty.inst S ι y) (Ty.inst U ι.lift y) (t.inst ι.lift y) (ds.inst ι y)

end

/-! ## Renaming the store scope

Allocation extends the store scope, so everything the state holds has to be
weakened.  A store renaming leaves the local scope alone, hence leaves
`scopeAt` alone, and no transport occurs.

The renaming is a *parameter* of each traversal, before the varying local
scope: that is what makes the block compile by structural recursion, whose
equations hold definitionally.  With the renaming last the same definitions
are accepted by well-founded recursion instead, and then a machine run does
not compute. -/

mutual

/-- Rename the store scope of inclusion evidence. -/
def Le.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : {s : Sig} → Le σ1 s → Le σ2 s
  | _, .refl T => .refl (T.renameStore ρ)
  | _, .trans M e f =>
      .trans (M.renameStore ρ) (e.renameStore ρ) (f.renameStore ρ)
  | _, .top T => .top (T.renameStore ρ)
  | _, .bot T => .bot (T.renameStore ρ)
  | _, .dtyp a e f => .dtyp a (e.renameStore ρ) (f.renameStore ρ)
  | _, .dfun a e f => .dfun a (e.renameStore ρ) (f.renameStore ρ)
  | _, .andI T1 T2 e f =>
      .andI (T1.renameStore ρ) (T2.renameStore ρ) (e.renameStore ρ)
        (f.renameStore ρ)
  | _, .andE1 T2 e => .andE1 (T2.renameStore ρ) (e.renameStore ρ)
  | _, .andE2 T1 e => .andE2 (T1.renameStore ρ) (e.renameStore ρ)
  | _, .orI1 T2 e => .orI1 (T2.renameStore ρ) (e.renameStore ρ)
  | _, .orI2 T1 e => .orI2 (T1.renameStore ρ) (e.renameStore ρ)
  | _, .orE S1 S2 e f =>
      .orE (S1.renameStore ρ) (S2.renameStore ρ) (e.renameStore ρ)
        (f.renameStore ρ)
  | _, .defL c a e => .defL (ρ.var c) a (e.renameStore ρ)
  | _, .defR c a e => .defR (ρ.var c) a (e.renameStore ρ)
  | _, .selL (.conc c) a v => .selL (.conc (ρ.var c)) a (v.renameStore ρ)
  | _, .selL (.abs z) a v => .selL (.abs z) a (v.renameStore ρ)
  | _, .selR (.conc c) a v => .selR (.conc (ρ.var c)) a (v.renameStore ρ)
  | _, .selR (.abs z) a v => .selR (.abs z) a (v.renameStore ρ)
  | _, .bindx S T e =>
      .bindx (S.renameStore ρ) (T.renameStore ρ) (e.renameStore ρ)
  | _, .muDrop T => .muDrop (T.renameStore ρ)

/-- Rename the store scope of observation evidence. -/
def Vc.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : {s : Sig} → Vc σ1 s → Vc σ2 s
  | _, .vcVar => .vcVar
  | _, .vcLoc c => .vcLoc (ρ.var c)
  | _, .vcLocAny c T ds =>
      .vcLocAny (ρ.var c) (T.renameStore ρ) (ds.renameStore ρ)
  | _, .vcPack T v => .vcPack (T.renameStore ρ) (v.renameStore ρ)
  | _, .vcUnfold T v => .vcUnfold (T.renameStore ρ) (v.renameStore ρ)
  | _, .vcSub T1 e v =>
      .vcSub (T1.renameStore ρ) (e.renameStore ρ) (v.renameStore ρ)

end

mutual

/-- Rename the store scope of an atom. -/
def Atom.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → Atom σ1 s → Atom σ2 s
  | _, .var p => .var (p.subst (Subst.ofStore ρ))
  | _, .cast a e => .cast (a.renameStore ρ) (e.renameStore ρ)
  | _, .pack T a => .pack (T.renameStore ρ) (a.renameStore ρ)
  | _, .unpack T a => .unpack (T.renameStore ρ) (a.renameStore ρ)

/-- Rename the store scope of a term. -/
def Tm.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → Tm σ1 s → Tm σ2 s
  | _, .atom a => .atom (a.renameStore ρ)
  | _, .new T ds => .new (T.renameStore ρ) (ds.renameStore ρ)
  | _, .app a l b => .app (a.renameStore ρ) l (b.renameStore ρ)
  | _, .let t u => .let (t.renameStore ρ) (u.renameStore ρ)
  | _, .cast t e => .cast (t.renameStore ρ) (e.renameStore ρ)

/-- Rename the store scope of a definition list. -/
def Defs.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → Defs σ1 s → Defs σ2 s
  | _, .dnil => .dnil
  | _, .dty T ds => .dty (T.renameStore ρ) (ds.renameStore ρ)
  | _, .dfun S U t ds =>
      .dfun (S.renameStore ρ) (U.renameStore ρ) (t.renameStore ρ)
        (ds.renameStore ρ)

end

/-- Weaken an atom under one newly allocated location. -/
abbrev Atom.weakenStore {σ s : Sig} (a : Atom σ s) : Atom (σ,x) s :=
  a.renameStore Rename.succ
/-- Weaken a term under one newly allocated location. -/
abbrev Tm.weakenStore {σ s : Sig} (t : Tm σ s) : Tm (σ,x) s :=
  t.renameStore Rename.succ
/-- Weaken a definition list under one newly allocated location. -/
abbrev Defs.weakenStore {σ s : Sig} (ds : Defs σ s) : Defs (σ,x) s :=
  ds.renameStore Rename.succ


/-! ## Stores -/

/-- A store fragment: one definition list per binder of `σ'`, each living in
the full store scope `σ`, exactly as `Oopsla16.Store`.  Entries may mention
locations allocated after them, because the reference's store does. -/
inductive MachineStore : Sig → Sig → Type where
  /-- The empty fragment. -/
  | nil {σ : Sig} : MachineStore σ []
  /-- One more location. -/
  | cons {σ σ' : Sig} : MachineStore σ σ' → Defs σ [] → MachineStore σ (σ',x)

/-- The definitions stored at a location. -/
def MachineStore.lookup {σ : Sig} : {σ' : Sig} → MachineStore σ σ' → BVar σ' .var → Defs σ []
  | _, .cons _ ds, .here => ds
  | _, .cons G _, .there z => G.lookup z

/-- Rename every entry's store scope, which is what allocation needs. -/
def MachineStore.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {σ3 : Sig} → MachineStore σ1 σ3 → MachineStore σ2 σ3
  | _, .nil => .nil
  | _, .cons G ds => .cons (G.renameStore ρ) (ds.renameStore ρ)

/-- Weaken a store under one newly allocated location. -/
abbrev MachineStore.weakenStore {σ σ' : Sig} (G : MachineStore σ σ') : MachineStore (σ,x) σ' :=
  G.renameStore Rename.succ

/-- The method at a label: its domain, its codomain and its body.  Labels
count from the end, as `Oopsla16.Dms.get?` counts them. -/
def Defs.fun? {σ s : Sig} : Defs σ s → Lb →
    Option (Ty σ s × Ty σ (s,x) × Tm σ (s,x))
  | .dnil, _ => none
  | .dty _ ds, a => if a = ds.length then none else ds.fun? a
  | .dfun S U t ds, a => if a = ds.length then some (S, U, t) else ds.fun? a

/-- The type member at a label, if the member there is a type.  The machine
never reads it; it is what `LeTy.defL`/`LeTy.defR` read in the source store,
and `Erasure.Defs.erase_ty?` is the statement that the two agree. -/
def Defs.ty? {σ s : Sig} : Defs σ s → Lb → Option (Ty σ s)
  | .dnil, _ => none
  | .dty T ds, a => if a = ds.length then some T else ds.ty? a
  | .dfun _ _ _ ds, a => if a = ds.length then none else ds.ty? a

/-- The location a running variable denotes.  `Vr σ []` has no abstract
inhabitant, so this is total: the empty local scope is where the machine
works. -/
def Vr.loc {σ : Sig} : Vr σ [] → BVar σ .var
  | .conc c => c
  | .abs z => nomatch z

/-- Reading a running variable as a location loses nothing. -/
@[simp] theorem Vr.conc_loc {σ : Sig} (p : Vr σ []) : Vr.conc (Vr.loc p) = p := by
  cases p with
  | conc c => rfl
  | abs z => exact nomatch z

/-! ## Continuations -/

/-- A frame: a pending `let` body, or a pending coercion. -/
inductive Frame : Sig → Type where
  /-- `let x = □ in u`. -/
  | «let» {σ : Sig} : Tm σ ([],x) → Frame σ
  /-- `□ ▸ e`. -/
  | cast {σ : Sig} : Le σ [] → Frame σ

/-- Rename a frame's store scope. -/
def Frame.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : Frame σ1 → Frame σ2
  | .let u => .let (u.renameStore ρ)
  | .cast e => .cast (e.renameStore ρ)

/-- A continuation: frames, innermost last. -/
inductive Cont : Sig → Type where
  /-- The empty continuation. -/
  | nil {σ : Sig} : Cont σ
  /-- One more frame, innermost. -/
  | cons {σ : Sig} : Cont σ → Frame σ → Cont σ

@[inherit_doc] scoped infixl:65 " ▹ " => Cont.cons

/-- Rename a continuation's store scope. -/
def Cont.renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) : Cont σ1 → Cont σ2
  | .nil => .nil
  | .cons K f => .cons (K.renameStore ρ) (f.renameStore ρ)

/-- Weaken a continuation under one newly allocated location. -/
abbrev Cont.weakenStore {σ : Sig} (K : Cont σ) : Cont (σ,x) :=
  K.renameStore Rename.succ

/-! ## States and steps -/

/-- A machine state: a store, a continuation, and a running term of the empty
local scope. -/
structure State (σ : Sig) where
  /-- The store. -/
  G : MachineStore σ σ
  /-- The continuation. -/
  K : Cont σ
  /-- The running term. -/
  t : Tm σ []

/-- The reduction relation, indexed by the allocation it performs, as
`Oopsla16.Step` is.  `alloc` is the only rule that changes the store scope,
and `let`, `castPush`, `castAtom` and `rename` are the only rules that change
the continuation. -/
inductive Step : {σ1 σ2 : Sig} → Grows σ1 σ2 → State σ1 → State σ2 → Prop where
  /-- Push a `let` frame. -/
  | «let» {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {t : Tm σ []} {u : Tm σ ([],x)} :
      Step .refl ⟨G, K, .let t u⟩ ⟨G, K ▹ .let u, t⟩
  /-- Push a coercion frame. -/
  | castPush {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {t : Tm σ []} {e : Le σ []} :
      Step .refl ⟨G, K, .cast t e⟩ ⟨G, K ▹ .cast e, t⟩
  /-- A coercion frame over an atom is absorbed into the atom: evidence never
  blocks and never fires. -/
  | castAtom {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {a : Atom σ []} {e : Le σ []} :
      Step .refl ⟨G, K ▹ .cast e, .atom a⟩ ⟨G, K, .atom (.cast a e)⟩
  /-- A `let` frame over an atom substitutes the atom's root location. -/
  | rename {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {u : Tm σ ([],x)} {a : Atom σ []} :
      Step .refl ⟨G, K ▹ .let u, .atom a⟩ ⟨G, K, u.inst .base (Vr.loc a.root)⟩
  /-- Allocate, substituting the object's own new location for its self.  This
  is `Oopsla16.Step.ST_Obj`, with the self type discarded: the machine does not
  read it. -/
  | alloc {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {T : Ty σ ([],x)}
      {ds : Defs σ ([],x)} :
      Step (.snoc .refl) ⟨G, K, .new T ds⟩
        ⟨G.weakenStore.cons (ds.weakenStore.inst .base .here), K.weakenStore,
          .atom (.var (.conc .here))⟩
  /-- Invoke a method of a stored object.  The self was substituted at
  allocation, so only the argument's root is substituted.  This is
  `Oopsla16.Step.ST_AppAbs`. -/
  | app {σ : Sig} {G : MachineStore σ σ} {K : Cont σ} {a b : Atom σ []} {l : Lb}
      {S : Ty σ []} {U : Ty σ ([],x)} {t : Tm σ ([],x)} :
      (G.lookup (Vr.loc a.root)).fun? l = some (S, U, t) →
      Step .refl ⟨G, K, .app a l b⟩ ⟨G, K, t.inst .base (Vr.loc b.root)⟩

/-- Reflexive transitive closure, across store scopes. -/
inductive Steps : {σ1 σ2 : Sig} → Grows σ1 σ2 → State σ1 → State σ2 → Prop where
  /-- No steps. -/
  | refl {σ : Sig} {st : State σ} : Steps .refl st st
  /-- One more step. -/
  | tail {σ1 σ2 σ3 : Sig} {g : Grows σ1 σ2} {h : Grows σ2 σ3} {st : State σ1}
      {st' : State σ2} {st'' : State σ3} :
      Steps g st st' → Step h st' st'' → Steps (g.comp h) st st''

/-- The answers: an atom under the empty continuation.  The source's answers
are its concrete variables (`Tm.IsAnswer`), and an atom erases to one. -/
def State.Final {σ : Sig} (st : State σ) : Prop :=
  st.K = .nil ∧ ∃ a : Atom σ [], st.t = .atom a

/-- A state that is neither an answer nor able to step. -/
def State.Stuck {σ : Sig} (st : State σ) : Prop :=
  ¬ st.Final ∧ ¬ ∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Step g st st'

end FCdotR
