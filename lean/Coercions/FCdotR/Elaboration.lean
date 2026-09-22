import Coercions.FCdotR.TermTyping
import Coercions.FCdotR.Examples

/-!
# Elaboration: `Oopsla16` derivations become FCdotR evidence and terms

The translation R1 of `PLAN.md` §E, as functions on derivations.  Every
function here is a structural recursion over the source's `Type`-valued
derivations, so the source's proof *is* the target's evidence, computed.

```text
Oopsla16.Stp     G Γ S T          ↦  (e : Le σ s)     × LeTy G W Γ e S T
Oopsla16.Htp     G Γ x T          ↦  (v : Vc σ _)     × VcTy G W Γ (.abs x) v T
Oopsla16.HasType G Γ (.tvar p) T  ↦  an atom rooted at `p`, with its typing
Oopsla16.HasType G Γ t T          ↦  (t' : Tm σ s)    × TmTy G W Γ t' T
Oopsla16.DmsHasType G Γ ds T      ↦  (ds' : Defs σ s) × DefsTy G W Γ ds' T
```

## What needs no hypothesis at all

All 18 `Stp` rules and all 3 `Htp` rules elaborate for an **arbitrary** store
typing `W`: `Store.Honest` is not needed anywhere in `elabStp`/`elabHtp`.  The
reason is that the two rules which read the store, `stp_strong_sel1` and
`stp_strong_sel2`, have target counterparts `LeTy.defL`/`LeTy.defR` with
*literally the same* premises — they read `G`, not `W` — and no other rule
mentions a location.  Two rules are derived rather than primitive, exactly as
`PLAN.md` §E says: `stp_selx` is `refl` at the selection, and `stp_bind1` is
`bindx` into the weakened right body followed by `muDrop`.

## Where a hypothesis *is* needed: `T_Vary`

The source's `T_Vary` (`dot.v:220-226`) re-types the stored literal at a type
`T` of its own choosing; the target's `AtomTy.varConc` reads the type off the
store typing `W`.  Nothing forces the two to agree, and nothing can: a
literal's type is not determined by the literal, because `D_Fun` types the
method body with `HasType` and `HasType` has `T_Sub`.  So the elaboration of a
term takes a `VaryEv G W` — the statement that at every location the store
typing's own entry is *included* in whatever type the source derived there —
and `T_Vary` becomes `AtomTy.varConc` followed by that inclusion.

`StoreTyping.Store.Honest.vary` is the **converse** implication: it turns the
target's rule back into a source derivation, so it shows that reading `W` is
not a new power.  It does not discharge `VaryEv`, and this module does not
pretend that it does.  `VaryEv.empty` inhabits the hypothesis over the empty
store, which is where the `FunctionField` instantiation at the end lives.

## The fragment: applications with variable operands

`TmTy.app` takes two **atoms**; the source's `tapp` takes two arbitrary terms.
Elaborating a general `tapp` means A-normalising it — binding each operand with
`Tm.let` and proving the operational correspondence — and that is not done
here, nor anywhere else in this library.  So term elaboration is restricted to
the fragment `TmFrag`, in which every application has variable operands.  On
that fragment the elaborated term contains no `let` at all, which is also the
fragment on which `Erasure.Steps.simulate` holds.

`TmFrag` carries a second restriction, for erasure rather than for typing: a
source `dfun` may leave either annotation absent (`EqSome`, `dot.v:216`), while
`Defs.dfun` carries both, so an unannotated source method would elaborate to an
annotated target method and `ElaborationErasure`'s equality would fail on the
nose.  `TmFrag` therefore asks for Church-style definitions.

## The acceptance test

The last section runs the elaboration on `Oopsla16.Examples.FunctionField`, the
recursive-subtyping derivation the present FCdot target provably cannot express
(`DotToFCdot.RecursiveSubtyping.FunctionField.no_coercion`), and checks that it
computes the evidence `FCdotR/Examples.lean` writes out by hand — not up to
anything, but on the nose, by `rfl`.

## What this module does not contain

No erasure statement (that is `ElaborationErasure`), no A-normalisation of
general application, and no claim that elaboration is injective, surjective or
unique.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store HasType DmsHasType Stp Htp EqSome
  renameNil renameUpTo varUpTo scopeUpTo)

/-! ## Subtyping and variable observation

The two evidence judgments, elaborated together because the source's `stp_sel1`
and `stp_sel2` consume an `Htp` and the source's `htp_sub` consumes a `Stp`.
Neither uses the store typing, so `W` is an arbitrary parameter. -/

mutual

/-- **Every `Stp` derivation is inclusion evidence.**  One clause per rule, for
all 18 rules of `dot.v:285-374`, at an arbitrary store typing `W`: no honesty
hypothesis, because `defL`/`defR` read the same store the source rules read.

Two rules have no primitive counterpart and are derived: `stp_selx` is `refl`
at the selection itself, and `stp_bind1` is `bindx` into the weakened right
body composed with `muDrop`, which is `PLAN.md` §E's entry for it. -/
def elabStp {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} :
    {S T : Ty σ s} → Stp G Γ S T → (e : Le σ s) × LeTy G W Γ e S T
  | _, T, .stp_bot => ⟨.bot T, .bot T⟩
  | T, _, .stp_top => ⟨.top T, .top T⟩
  | _, _, .stp_fun (l := l) h1 h2 =>
      let ⟨e, he⟩ := elabStp W h1
      let ⟨f, hf⟩ := elabStp W h2
      ⟨.dfun l e f, .dfun he hf⟩
  | _, _, .stp_typ (l := l) h1 h2 =>
      let ⟨e, he⟩ := elabStp W h1
      let ⟨f, hf⟩ := elabStp W h2
      ⟨.dtyp l e f, .dtyp he hf⟩
  | _, _, .stp_strong_sel1 (x := x) (l := l) hg h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.defL x l e, .defL hg he⟩
  | _, _, .stp_strong_sel2 (x := x) (l := l) hg h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.defR x l e, .defR hg he⟩
  | _, _, .stp_sel1 (x := x) (l := l) h =>
      let ⟨v, hv⟩ := elabHtp W h
      ⟨.selL (.abs x) l v, .selL hv⟩
  | _, _, .stp_sel2 (x := x) (l := l) h =>
      let ⟨v, hv⟩ := elabHtp W h
      ⟨.selR (.abs x) l v, .selR hv⟩
  | _, _, .stp_selx (p := p) (l := l) => ⟨.refl (.TSel p l), .refl (.TSel p l)⟩
  | _, T2, .stp_bind1 (T1 := T1) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.trans (.TBind T2.weaken) (.bindx T1 T2.weaken e) (.muDrop T2),
        .trans (.TBind T2.weaken) (.bindx T1 T2.weaken he) (.muDrop T2)⟩
  | _, _, .stp_bindx (T1 := T1) (T2 := T2) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.bindx T1 T2 e, .bindx T1 T2 he⟩
  | _, _, .stp_and11 (T2 := T2) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.andE1 T2 e, .andE1 T2 he⟩
  | _, _, .stp_and12 (T1 := T1) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.andE2 T1 e, .andE2 T1 he⟩
  | _, _, .stp_and2 (T1 := T1) (T2 := T2) h1 h2 =>
      let ⟨e, he⟩ := elabStp W h1
      let ⟨f, hf⟩ := elabStp W h2
      ⟨.andI T1 T2 e f, .andI T1 T2 he hf⟩
  | _, _, .stp_or21 (T2 := T2) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.orI1 T2 e, .orI1 T2 he⟩
  | _, _, .stp_or22 (T1 := T1) h =>
      let ⟨e, he⟩ := elabStp W h
      ⟨.orI2 T1 e, .orI2 T1 he⟩
  | _, _, .stp_or1 (T1 := T1) (T2 := T2) h1 h2 =>
      let ⟨e, he⟩ := elabStp W h1
      let ⟨f, hf⟩ := elabStp W h2
      ⟨.orE T1 T2 e f, .orE T1 T2 he hf⟩
  | _, _, .stp_trans (T2 := M) h1 h2 =>
      let ⟨e, he⟩ := elabStp W h1
      let ⟨f, hf⟩ := elabStp W h2
      ⟨.trans M e f, .trans M he hf⟩

/-- **Every `Htp` derivation is observation evidence at an abstract subject.**
All 3 rules of `dot.v:375-393`, again at an arbitrary `W`.

The reference's truncation `length GL = S x`, `GH = GU ++ GL` is the index on
both sides — `Ty σ (scopeUpTo x)` in the source, `Ty σ (scopeAt (.abs x))` in
the target — and these are the same scope definitionally, so no transport
appears.  Likewise `htp_unpack`'s `.abs (varUpTo x)` is `selfAt (.abs x)` and
`htp_sub`'s `Γ.upTo x` is `ctxAt Γ (.abs x)`, both definitionally. -/
def elabHtp {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s}
    {x : BVar s .var} : {T : Ty σ (scopeUpTo x)} → Htp G Γ x T →
    (v : Vc σ (scopeUpTo x)) × VcTy G W Γ (.abs x) v T
  | _, .htp_var => ⟨.vcVar, .vcVar⟩
  | _, .htp_unpack (TX := TX) h =>
      let ⟨v, hv⟩ := elabHtp W h
      ⟨.vcUnfold TX v, .vcUnfold hv⟩
  | _, .htp_sub (T1 := T1) h hs =>
      let ⟨v, hv⟩ := elabHtp W h
      let ⟨e, he⟩ := elabStp W hs
      ⟨.vcSub T1 e v, .vcSub (Γ := Γ) (p := .abs x) T1 hv he⟩

end

/-! ## The `T_Vary` bridge

The one thing the elaboration of terms needs that `Typing` does not already
give. -/

/-- **What elaboration asks of a store typing.**  Whenever the source types a
location by re-typing the literal stored there — the two premises of `T_Vary`,
`dot.v:220-226` — the type the store typing records for that location is
*included* in the type the source derived, and the inclusion is available as
target evidence in whatever local scope the use sits in.

This is a **hypothesis**: this module proves nothing that inhabits it in
general, and `Store.Honest` does not imply it.  Honesty says the store typing
tells *a* truth about each stored literal; `VaryEv` says it tells a truth at
least as precise as any the source can derive about it, and that is a strictly
stronger demand, because `D_Fun` types a method body with `HasType` and
`HasType` has `T_Sub`, so a literal has no principal type.

The field is stated at an arbitrary local scope `s` rather than at `[]`, where
both of its types actually live before their `renameNil`.  That is not
generality for its own sake: `LeTy` has no weakening lemma stated, so evidence
derived at `[]` cannot be moved to `s`.  That is now a gap of convenience
rather than of substance — `SubstTyping.LeTy.substEv` is unconditional and
`TermSubst.MonoSyn.Ev.weaken` is its weakening instance, so the lemma is
derivable; this module simply sits below `TermSubst` in the import order and
does not see it.  Once `LeTy` weakening is stated, the `s = []` instance of
this field will suffice. -/
structure VaryEv {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type where
  /-- The inclusion, from the recorded type to the derived one. -/
  le : {s : Sig} → {Γ : Ctx σ s} → {l : BVar σ .var} → {T : Ty σ ([],x)} →
    {ds : Dms σ ([],x)} → DmsHasType G (Ctx.nil.cons T) ds T →
    ds.substVr (.conc l) = G.lookup l →
    (e : Le σ s) × LeTy G W Γ e ((tyOf W l).rename renameNil)
      ((T.substVr (.conc l)).rename renameNil)

/-- Over the empty store the hypothesis is free: there is no location to make a
demand about.  This is what the `FunctionField` instantiation uses. -/
def VaryEv.empty {G : Store [] []} {W : StoreTy []} : VaryEv G W where
  le := fun {_ _ l} _ _ => nomatch l

/-! ## The elaborable fragment

`TmFrag t` says two things about the source term `t`, and says them
structurally, so that a derivation over `t` can be elaborated by recursion:

* every application has **variable operands**, so that `TmTy.app`, whose
  operands are atoms, applies without A-normalisation;
* every method definition carries **both annotations**, so that its elaboration
  erases back to it on the nose.

Neither is a restriction on the *calculus*; both are restrictions on this
translation, and `PLAN.md` §E records the first as the MNF lemma that is still
owed. -/

mutual

/-- The source terms this module elaborates. -/
inductive TmFrag : {σ s : Sig} → Oopsla16.Tm σ s → Type where
  /-- A variable. -/
  | tvar {σ s : Sig} {p : Vr σ s} : TmFrag (.tvar p)
  /-- An object literal whose definitions are in the fragment. -/
  | tobj {σ s : Sig} {ds : Dms σ (s,x)} : DmsFrag ds → TmFrag (.tobj ds)
  /-- An application of a variable to a variable. -/
  | tapp {σ s : Sig} {p q : Vr σ s} {l : Lb} :
      TmFrag (.tapp (.tvar p) l (.tvar q))

/-- The source member definitions this module elaborates. -/
inductive DmFrag : {σ s : Sig} → Dm σ s → Type where
  /-- A type member. -/
  | dty {σ s : Sig} {T : Ty σ s} : DmFrag (.dty T)
  /-- A method member, with **both** annotations present. -/
  | dfun {σ s : Sig} {S : Ty σ s} {U : Ty σ (s,x)} {t : Oopsla16.Tm σ (s,x)} :
      TmFrag t → DmFrag (.dfun (some S) (some U) t)

/-- The source definition lists this module elaborates. -/
inductive DmsFrag : {σ s : Sig} → Dms σ s → Type where
  /-- The empty list. -/
  | dnil {σ s : Sig} : DmsFrag (.dnil (σ := σ) (s := s))
  /-- One more member. -/
  | dcons {σ s : Sig} {d : Dm σ s} {ds : Dms σ s} :
      DmFrag d → DmsFrag ds → DmsFrag (.dcons d ds)

end

/-! ## Atoms

A source typing of a *variable* elaborates to an atom, and the atom is rooted
at that same variable.  The root has to be part of the result, because
`AtomTy.pack`, `AtomTy.unpack` and `TmTy.app` all instantiate a type by the
root of the atom they are handed, where the source instantiates by the variable
it was handed. -/

/-- An atom of type `T` rooted at `p`, with its typing. -/
structure AtomElab {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (p : Vr σ s) (T : Ty σ s) : Type where
  /-- The atom. -/
  atom : Atom σ s
  /-- It is rooted at the source's variable. -/
  root : atom.root = p
  /-- And it has the source's type. -/
  typed : AtomTy G W Γ atom T

/-- **A source typing of a variable elaborates to an atom rooted at it.**
`T_Varz` and `T_Vary` become the two variable rules, `T_Sub` becomes a `cast`,
`T_VarPack` and `T_VarUnpack` become `pack` and `unpack`; the three rules whose
subject is not a variable cannot conclude at `.tvar p`, and the match discards
them.

`T_Vary` is where `VaryEv` is consumed, and the only place in this module where
anything beyond the source derivation is used.  **`VaryEv` is an unproved
hypothesis**: nothing in this library inhabits it except over the empty store,
so this function is a translation *relative to* an agreement between the source
and the store typing that no one has established in general. -/
def elabAtom {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} (V : VaryEv G W)
    {Γ : Ctx σ s} : {p : Vr σ s} → {T : Ty σ s} → HasType G Γ (.tvar p) T →
    AtomElab G W Γ p T
  | _, _, .T_Vary (x := l) hds heq =>
      let ⟨e, he⟩ := V.le (Γ := Γ) (l := l) hds heq
      ⟨.cast (.var (.conc l)) e, rfl, .cast .varConc he⟩
  | _, _, .T_Varz (x := y) => ⟨.var (.abs y), rfl, .varAbs⟩
  | p, _, .T_VarPack (T := T) h =>
      let r := elabAtom V h
      ⟨.pack T r.atom, r.root, .pack (by rw [r.root]; exact r.typed)⟩
  | p, _, .T_VarUnpack (T := T) h =>
      let r := elabAtom V h
      ⟨.unpack T r.atom, r.root, by
        have hu := AtomTy.unpack (T := T) r.typed
        rw [r.root] at hu
        exact hu⟩
  | _, _, .T_Sub h hs =>
      let r := elabAtom V h
      let ⟨e, he⟩ := elabStp W hs
      ⟨.cast r.atom e, r.root, .cast r.typed he⟩

/-! ## Terms and definition lists

The elaboration of a definition list has to know that it did not change the
number of members, because `DefsTy.dty` and `DefsTy.dfun` label a member by the
length of its tail and that label appears in the member's *type*.  The equation
is therefore carried alongside the list. -/

/-- An elaborated definition list: the list, the fact that it has as many
members as the source's, and its typing. -/
structure DefsElab {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (ds : Dms σ s) (T : Ty σ s) : Type where
  /-- The list. -/
  defs : Defs σ s
  /-- It has as many members as the source's, so the positional labels agree. -/
  length : defs.length = ds.length
  /-- And it has the source's type. -/
  typed : DefsTy G W Γ defs T

mutual

/-- **A source term typing elaborates to a target term of the same type**, on
the fragment `TmFrag`.

`T_App` and `T_AppVar` both become `TmTy.app` — the non-dependent one through
`TmTy.appWeaken` — because on this fragment both operands are already
variables, hence atoms.  Off the fragment the function is not defined: a
general `tapp t1 l t2` needs its operands bound by `Tm.let` first, and the
operational correspondence for that binding is proved nowhere in this library.

Like `elabAtom`, this takes the **unproved hypothesis** `VaryEv`; see there. -/
def elabHasType {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} (V : VaryEv G W)
    {Γ : Ctx σ s} : {t : Oopsla16.Tm σ s} → {T : Ty σ s} → HasType G Γ t T →
    TmFrag t → (t' : Tm σ s) × TmTy G W Γ t' T
  | _, _, .T_Vary hds heq, _ =>
      let r := elabAtom V (.T_Vary hds heq)
      ⟨.atom r.atom, .atom r.typed⟩
  | _, _, .T_Varz (x := y), _ => ⟨.atom (.var (.abs y)), .atom .varAbs⟩
  | _, _, .T_VarPack h, _ =>
      let r := elabAtom V (.T_VarPack h)
      ⟨.atom r.atom, .atom r.typed⟩
  | _, _, .T_VarUnpack h, _ =>
      let r := elabAtom V (.T_VarUnpack h)
      ⟨.atom r.atom, .atom r.typed⟩
  | _, _, .T_Obj (T := T) hds, .tobj f =>
      let r := elabDms V hds f
      ⟨.new T r.defs, .new T r.typed⟩
  | _, _, .T_App (l := l) h1 h2, .tapp =>
      let r1 := elabAtom V h1
      let r2 := elabAtom V h2
      ⟨.app r1.atom l r2.atom, .appWeaken r1.typed r2.typed⟩
  | _, _, .T_AppVar (l := l) h1 h2, .tapp =>
      let r1 := elabAtom V h1
      let r2 := elabAtom V h2
      ⟨.app r1.atom l r2.atom, by
        have ha := TmTy.app (l := l) r1.typed r2.typed
        rw [r2.root] at ha
        exact ha⟩
  | _, _, .T_Sub h hs, f =>
      let ⟨t', ht'⟩ := elabHasType V h f
      let ⟨e, he⟩ := elabStp W hs
      ⟨.cast t' e, .cast ht' he⟩

/-- **A source definition-list typing elaborates to a target one.**  `D_Nil`,
`D_Typ` and `D_Fun` are the three rules; the positional label is transported by
the length equation, and `D_Fun`'s target annotations are the types the source
rule checked, which the fragment's `some` annotations agree with.

Like `elabAtom`, this takes the **unproved hypothesis** `VaryEv`; see there. -/
def elabDms {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} (V : VaryEv G W)
    {Γ : Ctx σ s} : {ds : Dms σ s} → {T : Ty σ s} → DmsHasType G Γ ds T →
    DmsFrag ds → DefsElab G W Γ ds T
  | _, _, .D_Nil, _ => ⟨.dnil, rfl, .dnil⟩
  | _, _, .D_Typ (T11 := T11) hds, .dcons _ f =>
      let r := elabDms V hds f
      ⟨.dty T11 r.defs, by simp [Defs.length, r.length],
        by rw [← r.length]; exact .dty r.typed⟩
  | _, _, .D_Fun (T11 := T11) (T12 := T12) hds hb _ _, .dcons (.dfun fb) f =>
      let r := elabDms V hds f
      let ⟨t', ht'⟩ := elabHasType V hb fb
      ⟨.dfun T11 T12 t' r.defs, by simp [Defs.length, r.length],
        by rw [← r.length]; exact .dfun r.typed ht'⟩

end

/-! ## The acceptance test: `FunctionField`, elaborated

`Oopsla16.Examples.FunctionField.recursive` derives `μz. S(z) <: μz. T(z)` for

```text
S(z) = {A : ⊥ .. z.B} ∧ ({B : ⊥ .. ⊤} ∧ {f : ∀(_ : ⊤) z.A})
T(z) =                                   {f : ∀(_ : ⊤) z.B}
```

and `FCdotR/Examples.lean` writes the corresponding evidence by hand.  Running
`elabStp` on the source derivation produces that same evidence term — not an
equivalent one, the same one — so the hand-written example is exactly what the
translation computes.  `DotToFCdot.RecursiveSubtyping.FunctionField.no_coercion`
proves the previous target has no closed inclusion with these endpoints at all.

The store is empty here, so no `VaryEv` is involved; `elabStp` never needs one. -/

/-- The observation of the self's `A` member that the source's `htp_sub` builds
is `Examples.aMember`. -/
theorem elab_selMember :
    (elabHtp Examples.W0 Oopsla16.Examples.FunctionField.selMember).1
      = Examples.aMember := rfl

/-- The `stp_bindx` premise elaborates to `Examples.premise`. -/
theorem elab_premise :
    (elabStp Examples.W0 Oopsla16.Examples.FunctionField.premise).1
      = Examples.premise := rfl

/-- **And the whole derivation elaborates to `Examples.recursive`.** -/
theorem elab_recursive :
    (elabStp Examples.W0 Oopsla16.Examples.FunctionField.recursive).1
      = Examples.recursive := rfl

/-- So the elaboration reproves `Examples.recursive_typed`, by computation from
the source derivation rather than by hand. -/
def elabRecursiveTyped :
    LeTy (σ := []) (s := []) .nil Examples.W0 .nil Examples.recursive
      (.TBind Oopsla16.Examples.FunctionField.Sbody)
      (.TBind Oopsla16.Examples.FunctionField.Tbody) :=
  elab_recursive ▸ (elabStp Examples.W0 Oopsla16.Examples.FunctionField.recursive).2

/-- `stp_bind1` is the one derived rule with a compound image, so it gets its
own instance: `Oopsla16.Examples.forgetSelf` elaborates to a `bindx` into the
weakened body composed with `muDrop`. -/
def elabForgetSelf :
    (e : Le [] []) × LeTy (σ := []) (s := []) .nil Examples.W0 .nil e
      (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop)))
      (.TAnd .TTop (.TTyp 1 .TBot .TTop)) :=
  elabStp Examples.W0 Oopsla16.Examples.forgetSelf

end FCdotR
