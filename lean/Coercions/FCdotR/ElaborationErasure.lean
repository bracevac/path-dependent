import Coercions.FCdotR.Elaboration
import Coercions.FCdotR.Erasure

/-!
# The elaboration erases back to the source term

`Elaboration` turns a source typing derivation into a target term; `Erasure`
turns a target term back into a source term.  This module proves that the round
trip is the identity on the fragment `TmFrag`:

```text
(elabHasType V h f).1.erase = t        (elabDms V h f).defs.erase = ds
```

That is the `⌊h.translate⌋ = ⌊t⌋` of the finished line (`DotToFCdot`'s erasure
theorem), specialised to a target whose erasure lands in the source itself, so
there is no third language and the statement is a plain equation between source
terms.

Three observations make it hold, and they are exactly the three places where
the fragment or the elaboration was designed for it.

* **An atom erases to its root** (`Atom.erase a = .tvar a.root`), and
  `AtomElab` carries the root equation as a field.  So `elabAtom_erase` is that
  field, transported along `Oopsla16.Tm.tvar`, and every coercion, `pack` and
  `unpack` the elaboration inserts is invisible.
* **`TmFrag`'s applications have variable operands**, so the elaborated `app`
  erases to `tapp` of two variables, which is the source term on the nose.
  Without the restriction the elaboration would introduce `Tm.let`, whose
  erasure is `letEncode` — an object allocation — and the equation would be
  false, not merely unproved.
* **`DmFrag` demands both annotations.**  `Defs.dfun` carries a domain and a
  codomain outright and erases them to `some`, while the source's `dfun` may
  carry `none` (`EqSome`, `dot.v:216`).  On the fragment the source's
  annotations are `some`, and `D_Fun`'s `EqSome` premises then say they are the
  very types the rule checked.

For `Stp` and `Htp` there is nothing to state: inclusion and observation
evidence have no erasure, because they are not terms.  That is the point of the
target — the coercions of a derivation are the part that vanishes.

The closing section runs the theorem on three source derivations: the empty
object of `Oopsla16.Examples.ex0`, an object with an annotated method, and a
method invocation with variable operands.

This module proves no typing property; `Elaboration` already carries the
typings, as the second components of its results.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx HasType DmsHasType EqSome)

/-- **An elaborated atom erases to its source variable.**  `Atom.erase` is the
root, and `AtomElab.root` says the root is the variable the source typed. -/
theorem elabAtom_erase {σ s : Sig} {G : Oopsla16.Store σ σ} {W : StoreTy σ}
    (V : VaryEv G W) {Γ : Ctx σ s} {p : Vr σ s} {T : Ty σ s}
    (h : HasType G Γ (.tvar p) T) :
    (elabAtom V h).atom.erase = .tvar p :=
  congrArg Oopsla16.Tm.tvar (elabAtom V h).root

mutual

/-- **An elaborated term erases to the source term it came from.**  By
structural recursion on the derivation, one clause per rule of `HasType`, on
the fragment `TmFrag`.  It inherits `elabHasType`'s unproved hypothesis
`VaryEv`, but uses nothing of it: the clause for `T_Vary` needs only that the
elaborated atom is rooted where the source's variable is. -/
theorem elabHasType_erase {σ s : Sig} {G : Oopsla16.Store σ σ} {W : StoreTy σ}
    (V : VaryEv G W) {Γ : Ctx σ s} :
    {t : Oopsla16.Tm σ s} → {T : Ty σ s} → (h : HasType G Γ t T) →
    (f : TmFrag t) → (elabHasType V h f).1.erase = t
  | _, _, .T_Vary hds heq, _ => by
      simp only [elabHasType, Tm.erase]
      exact elabAtom_erase V (.T_Vary hds heq)
  | _, _, .T_Varz, _ => by simp only [elabHasType, Tm.erase, Atom.erase, Atom.root]
  | _, _, .T_VarPack h, _ => by
      simp only [elabHasType, Tm.erase]
      exact elabAtom_erase V (.T_VarPack h)
  | _, _, .T_VarUnpack h, _ => by
      simp only [elabHasType, Tm.erase]
      exact elabAtom_erase V (.T_VarUnpack h)
  | _, _, .T_Obj hds, .tobj f => by
      simp only [elabHasType, Tm.erase]
      exact congrArg Oopsla16.Tm.tobj (elabDms_erase V hds f)
  | _, _, .T_App h1 h2, .tapp => by
      simp only [elabHasType, Tm.erase]
      rw [elabAtom_erase V h1, elabAtom_erase V h2]
  | _, _, .T_AppVar h1 h2, .tapp => by
      simp only [elabHasType, Tm.erase]
      rw [elabAtom_erase V h1, elabAtom_erase V h2]
  | _, _, .T_Sub h hs, f => by
      simp only [elabHasType, Tm.erase]
      exact elabHasType_erase V h f

/-- **An elaborated definition list erases to the source list it came from.**
The `dfun` clause is where the fragment's Church-style annotations and
`D_Fun`'s `EqSome` premises meet. -/
theorem elabDms_erase {σ s : Sig} {G : Oopsla16.Store σ σ} {W : StoreTy σ}
    (V : VaryEv G W) {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → (h : DmsHasType G Γ ds T) →
    (f : DmsFrag ds) → (elabDms V h f).defs.erase = ds
  | _, _, .D_Nil, _ => by simp only [elabDms, Defs.erase]
  | _, _, .D_Typ hds, .dcons _ f => by
      simp only [elabDms, Defs.erase]
      exact congrArg _ (elabDms_erase V hds f)
  | _, _, .D_Fun hds hb hS hU, .dcons (.dfun fb) f => by
      have eS := Or.resolve_left hS (by simp)
      have eU := Or.resolve_left hU (by simp)
      simp only [elabDms, Defs.erase, eS, eU, elabHasType_erase V hb fb,
        elabDms_erase V hds f]

end

/-! ## Instances

Three source derivations run through the theorem.  All three live over the
empty store, where `VaryEv` is free. -/

namespace ErasureInstances

/-- The empty store. -/
abbrev G0 : Oopsla16.Store ([] : Sig) [] := .nil

/-- Its literal typing: there are no locations to type. -/
def W0 : StoreTy [] := fun l => nomatch l

/-- And so the `T_Vary` bridge is free. -/
def V0 : VaryEv G0 W0 := VaryEv.empty

/-- `Oopsla16.Examples.ex0`, the empty object at `⊤`, erases back to
`{ z => }`.  Its derivation ends in `T_Sub`, so the elaborated term is a
`Tm.cast`, and the cast is what vanishes. -/
theorem ex0 : (elabHasType V0 (Γ := Ctx.nil) Oopsla16.Examples.ex0
    (.tobj .dnil)).1.erase = .tobj .dnil :=
  elabHasType_erase V0 _ _

/-- The self type of a one-method object: `{f : ∀(_ : ⊤) ⊤} ∧ ⊤`, the trailing
`⊤` being `D_Nil`'s. -/
abbrev methodTy : Ty [] ([],x) := .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- Its definitions, Church-style as `DmFrag` demands: the method returns its
own parameter. -/
abbrev methodDefs : Dms [] ([],x) :=
  .dcons (.dfun (some .TTop) (some .TTop) (.tvar (.abs .here))) .dnil

/-- They have that type, by `D_Fun` over `D_Nil` with both annotations
matching. -/
def methodDms : DmsHasType G0 (Ctx.nil.cons methodTy) methodDefs methodTy :=
  .D_Fun .D_Nil .T_Varz (.inr rfl) (.inr rfl)

/-- The literal. -/
def methodObj :
    HasType G0 (Ctx.nil : Ctx [] []) (Oopsla16.Tm.tobj methodDefs)
      (Ty.TBind methodTy) :=
  .T_Obj methodDms

/-- It is in the fragment. -/
def methodFrag : TmFrag (Oopsla16.Tm.tobj methodDefs) :=
  .tobj (.dcons (.dfun .tvar) .dnil)

/-- **`D_Fun` erases back**: the elaborated `Defs.dfun`, whose annotations are
the types the source rule checked, erases to the source's `some`
annotations. -/
theorem methodObj_erase :
    (elabHasType V0 methodObj methodFrag).1.erase = .tobj methodDefs :=
  elabHasType_erase V0 _ _

/-- A context holding a method object and an argument. -/
abbrev Gamma : Ctx [] ([],x,x) :=
  (Ctx.nil.cons (.TFun 0 .TTop .TTop)).cons .TTop

/-- The invocation `y.0(z)`, both operands variables, by `T_AppVar`. -/
def invocation : HasType G0 Gamma
    (Oopsla16.Tm.tapp (.tvar (.abs (.there .here))) 0 (.tvar (.abs .here)))
    Ty.TTop :=
  .T_AppVar (T2 := .TTop) .T_Varz .T_Varz

/-- **`T_AppVar` erases back**: the elaborated `Tm.app` takes two atoms, each
erasing to its root, so the application is the source's on the nose.  This is
the clause that a general `tapp` would break, because its operands would have
to be `let`-bound first. -/
theorem invocation_erase :
    (elabHasType V0 invocation .tapp).1.erase
      = .tapp (.tvar (.abs (.there .here))) 0 (.tvar (.abs .here)) :=
  elabHasType_erase V0 _ _

end ErasureInstances

end FCdotR
