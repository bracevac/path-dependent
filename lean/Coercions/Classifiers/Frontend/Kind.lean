import Coercions.Classifiers.Frontend.Alg

/-!
# Kinding at the examples

Capture kinding `Γ ⊢ C :ᶜ φ` says that every capability in the set `C` has a
classifier that the kind `φ` admits.  The Classifiers development states it as
the `Type`-valued family `CapKind` (`lean/Coercions/Classifiers/DotMNF/Typing.lean`).

Kinding is a goal kind of the algorithm of `Sub.lean`, beside subtyping,
subcapturing, answers and variables.  It runs on the same tank and the same
pending list.  `kind?` asks it from a full tank.  A member bounded by a kind,
which `ksel` reads, and the upper bound of a capture member, which `kle`
reads along `Subcap.selUpper`, are found by the member lookup of `Look.lean`
on demand.  So kinding needs no fuel of its own and no table of member
typings.  A kinding that ends with the tank unmarked has the same verdict at
every larger fuel (`kind?_stable`), and a rejection with the tank unmarked
has no algorithmic derivation (`kind?_reject`).

This module checks the kinding goal at judgments of the Classifiers examples
(`lean/Coercions/Classifiers/DotMNF/Examples.lean`).  Each check states the
rules of the derivation found, outermost first, and the tank it used, as a
`decide +kernel` fact.  A success is also checked by the FCdot checker on its
translation, and compared with the written derivation of the same judgment.
Where the derivation reads a member, its translation is slow to unfold in the
kernel, so those two comparisons run as `#eval expect` tests.
-/

namespace ClassifiersFrontend

open Frontend.Fuel ClassifiersFrontend.Core
open Classifiers.FCdot (Kind Sig BVar Label)
open Classifiers.DotMNF (CapAtom CaptureSet Shape Ctx Subcap CapKind HasTy)
open Classifiers
open scoped Classifiers.DotMNF

section Tests

open Classifiers.DotMNF.Examples (E1PlatCtx E1Filt E1_kind E2IoCtx E2_io_arg_kind E2PlatIOCtx
  E2Filt E2TlDescent E3PlatCtx E3Uses E3_kind E3ClientCtx E3ClosureSet E3_client_kind_plat
  C2CtxG E3k1 E3k2 lC up)

/-- The FCdot checker's verdict on the translation of a kinding found. -/
private def kindVerdict {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (r : Option (CapKind Γ C φ)) : Bool :=
  match r with
  | some g => FCdot.checkKindCo Γ.translate g.translate C.translate φ
  | none => false

/-- A kinding found and a written one have the same translation. -/
private def agreesWith {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (r : Option (CapKind Γ C φ)) (g : CapKind Γ C φ) : Bool :=
  match r with
  | some g' => decide (g'.translate = g.translate)
  | none => false

/-- The rules of a kinding derivation, outermost first. -/
private def ruleNames {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (g : CapKind Γ C φ) : List String :=
  match g with
  | .nil => ["nil"]
  | .cons g h => "cons" :: (ruleNames g ++ ruleNames h)
  | .kproj _ => ["kproj"]
  | .kcls _ _ => ["kcls"]
  | .kvar _ g => "kvar" :: ruleNames g
  | .kcvar _ _ g => "kcvar" :: ruleNames g
  | .ksel _ => ["ksel"]
  | .kprojS g => "kprojS" :: ruleNames g
  | .ksub g _ => "ksub" :: ruleNames g
  | .kle _ g => "kle" :: ruleNames g
termination_by structural g

/-- The rules of the kinding found from a full tank, and the tank used. -/
private def kindRules {s : Sig} (Γ : Ctx s) (C : CaptureSet s) (φ : Cls.Kind) :
    Option (List String) × Nat × Bool :=
  ((kind? Γ C φ).1.map ruleNames, defaultFuel - (kind? Γ C φ).2.left, (kind? Γ C φ).2.out)

/-- `only[Control]`. -/
private def kindCtl : Cls.Kind := Cls.only Cls.Control

/-- `except[ThreadLocal]`. -/
private def kindNoTl : Cls.Kind := Cls.except Cls.ThreadLocal

/-! ### E1, the filtered platform set

A restricted atom carries its own kind, so `kproj` kinds both atoms.  The
written `E1_kind` takes `kcls` there, so the two derivations differ. -/

example : kindRules E1PlatCtx E1Filt kindCtl = (some ["cons", "kproj", "kproj"], 5, false) := by
  decide +kernel
example : agreesWith (kind? E1PlatCtx E1Filt kindCtl).1 E1_kind = false := by decide +kernel
example : kindVerdict (kind? E1PlatCtx E1Filt kindCtl).1 = true := by decide +kernel

/-! ### E2, an argument charged to the IO capability, and the thread-local one

At a bare variable `kproj` fails, since `⊤` is not a subkind of
`except[ThreadLocal]`, and `kcls` fails, since the binder is a term variable.
`kvar` descends to the declared set, where `kcls` finishes.  These are the
rules of `E2_io_arg_kind`.  The set a thread-local argument descends to is
not kinded at the filter (`E2_tl_descent_not_capKind`), and the rejection
ends with the tank unmarked. -/

example : kindRules E2IoCtx [CapAtom.var .here] kindNoTl = (some ["kvar", "kcls"], 3, false) := by
  decide +kernel
example : kindRules E2PlatIOCtx E2Filt kindNoTl =
    (some ["cons", "kproj", "cons", "kproj", "kproj"], 11, false) := by
  decide +kernel
example : kindVerdict (kind? E2PlatIOCtx E2Filt kindNoTl).1 = true := by decide +kernel
example : kindRules E2PlatIOCtx E2TlDescent kindNoTl = (none, 3, false) := by decide +kernel

/-- No algorithmic derivation kinds the thread-local descent at the filter. -/
theorem E2_tl_descent_no_alg : ¬ Alg ⟨_, E2PlatIOCtx, .kind E2TlDescent kindNoTl⟩ := by
  have h1 : (kind? E2PlatIOCtx E2TlDescent kindNoTl).1 = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have h2 : (kind? E2PlatIOCtx E2TlDescent kindNoTl).2 = ⟨defaultFuel - 3, false⟩ := by
    decide +kernel
  exact kind?_reject (Prod.ext h1 h2)

/-! ### E3, the use set, by `kcls` twice -/

example : kindRules E3PlatCtx E3Uses kindCtl = (some ["cons", "kcls", "kcls"], 5, false) := by
  decide +kernel

/-! ### E3, the client's closure set, through `ksel`

The member of `x` bounded by `only[Control]` is found by the lookup, so `ksel`
takes it with no typing given in advance.  The derivation is the written
`E3_client_kind_plat`.  At a kind the member's kind is a subkind of, `ksub`
follows `ksel`. -/

example : kindRules E3ClientCtx E3ClosureSet kindCtl = (some ["ksel"], 10, false) := by
  decide +kernel
#eval expect (agreesWith (kind? E3ClientCtx E3ClosureSet kindCtl).1 E3_client_kind_plat)
  "E3: the kinding found is not E3_client_kind_plat"
#eval expect (kindVerdict (kind? E3ClientCtx E3ClosureSet kindCtl).1)
  "E3: the target checker rejects the kinding found"
example : kindRules E3ClientCtx E3ClosureSet (kindCtl ∪ Cls.only Cls.IO) =
    (some ["ksub", "ksel"], 10, false) := by
  decide +kernel

/-! ### The closure `g` at `{x.C}`, under a filtered domain

`g` is declared at `{x.C}`.  Handing it to a domain `{any.only[Control]}` asks
for a kinding of `{g}` at `only[Control]`.  `kvar` descends to `{x.C ↾ ⊤}`,
which `kprojS` takes to `{x.C}`, where `ksel` finishes. -/

example : kindRules E3ClientCtx [CapAtom.var .here] kindCtl =
    (some ["kvar", "kprojS", "ksel"], 15, false) := by
  decide +kernel
#eval expect (kindVerdict (kind? E3ClientCtx [CapAtom.var .here] kindCtl).1)
  "g: the target checker rejects the kinding found"

/-! ### A selection off a member bounded by sets

C2's client read over E3's platform, where both capabilities are `Control`.
`x` has the member `{C : {}..{κ₁,κ₂}}`, and `g` is declared at `{x.C}`.
`{x.C}` is kinded at `only[Control]` by `kle` along `Subcap.selUpper` over two
`kcls`, and `{g}` by `kvar` and `kprojS` over that. -/

/-- C2's client context over E3's platform. -/
private abbrev C2OnE3Ctx : Ctx (Sig.body (Sig.body ([],c,c)),x) := C2CtxG E3PlatCtx E3k1 E3k2

example : kindRules C2OnE3Ctx [CapAtom.sel (.there (up .here)) lC] kindCtl =
    (some ["kle", "cons", "kcls", "kcls"], 27, false) := by
  decide +kernel
#eval expect (kindVerdict (kind? C2OnE3Ctx [CapAtom.sel (.there (up .here)) lC] kindCtl).1)
  "x.C: the target checker rejects the kinding found"
example : kindRules C2OnE3Ctx [CapAtom.var .here] kindCtl =
    (some ["kvar", "kprojS", "kle", "cons", "kcls", "kcls"], 38, false) := by
  decide +kernel
#eval expect (kindVerdict (kind? C2OnE3Ctx [CapAtom.var .here] kindCtl).1)
  "g: the target checker rejects the kinding found"

end Tests

end ClassifiersFrontend
