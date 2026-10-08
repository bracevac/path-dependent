import Coercions.Classifiers.Frontend.Decide
import Coercions.Classifiers.Frontend.Surface

/-!
# The kinding search

Capture kinding `Γ ⊢ C :ᶜ φ` says that every capability in the set `C` has a
classifier that the kind `φ` admits.  The Classifiers development states it as
the `Type`-valued family `CapKind` (`lean/Coercions/Classifiers/DotMNF/Typing.lean`).
This module searches for a `CapKind` derivation and returns it, so there is no
soundness theorem.  The result type is the statement.

`capKind?` takes a set apart.  The empty set is `nil`, and `a :: C` is `cons`
of a kinding of `[a]` and one of `C`.  `atomKind?` kinds one atom `a` at `φ`
and tries these rules in order.

1. `kproj`, when the kind `a` carries is a subkind of `φ`.  A bare atom has
   kind `⊤`.
2. `kcls`, when the binder under `a` declares a classifier and the kind of
   `a` admits it only if `φ` does.
3. `kvar`, when the binder under `a` is a term variable.  The variable's
   declared set, projected at the kind of `a`, is kinded at `φ`.
4. `kcvar`, the same through the set an instance binder stands for.
5. `ksel`, when `a` is a selection `x.A` and `x` has a member `{A : ψ}`
   bounded by a kind.  `ksub` follows it when `ψ` is not `φ`.
6. `kprojS`, when `[a]` is a projected set `C₀ ↾ ψ`.  Then `C₀` is kinded
   at `φ`.
7. `kle`, along `Subcap.var` at a variable to its declared set, and along
   `Subcap.selUpper` at a selection off a member bounded by a set to that
   upper bound.

The last alternative is not a rule.  It retries the search with one unit
less fuel.  It changes no answer and makes monotonicity in the fuel an
induction on the fuel alone.

`kind?` is the entry point.  A one-atom goal goes to `atomKind?` and any
other set to `capKind?`.

Every leaf premise is a `Bool` or `Option` equation, so evaluation decides
it.  `Subkind` is not known to be reflexive, so `ksel` at the kind it is
declared at is bare, and `ksub` is tried only when the kinds differ.

`ksel` and `kle` along `Subcap.selUpper` need a typing of `x` at a member.
Those typings come from the typer, which calls the subcapturing search, which
calls this one.  `KindOracle` cuts the cycle.  It lists the member typings
known at each variable and label.  The typer reads it off its declaration
table, and `KindOracle.empty` knows none.

The search does not find:

- a subkinding that `subkindB` does not confirm,
- `ksub` anywhere but behind `ksel`, since `Subkind` is not known to be
  transitive,
- `kle` through a middle set other than a declared set or an upper bound,
- `kprojS` at a nested projection, which `unprojSetW?` does not recognise,
- a member typing the oracle does not list,
- anything past the fuel.  A set needs its length plus the depth of its
  chain of `kvar`, `kcvar`, `kprojS` and `kle` steps.

Every function is structural, on the fuel or on a list, so the kernel
reduces the search.  The tests at the end are `decide +kernel` checks.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Label)
open Classifiers.DotMNF (CapAtom CaptureSet Shape Ctx Subcap CapKind HasTy)
open Classifiers
open scoped Classifiers.DotMNF

/-! ## The oracle -/

/-- A typing of the variable `x` at a member `{A : kind}` bounded by a kind,
the premise of `CapKind.ksel`. -/
structure CapkView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (A : Label) where
  /-- The use set of the derivation. -/
  uses : CaptureSet s
  /-- The kind the member is bounded by. -/
  kind : Cls.Kind
  /-- The capture set of the type the derivation concludes at. -/
  set : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.capk A kind) ^ set))

/-- A typing of the variable `x` at a member `{A : lo..hi}` bounded by two
sets, the premise of `Subcap.selUpper`. -/
structure CapBoundView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (A : Label) where
  /-- The lower bound. -/
  lo : CaptureSet s
  /-- The upper bound. -/
  hi : CaptureSet s
  /-- The use set of the derivation. -/
  uses : CaptureSet s
  /-- The capture set of the type the derivation concludes at. -/
  set : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.cap A lo hi) ^ set))

/-- The member typings the kinding search may use, at each variable and
label. -/
structure KindOracle {s : Sig} (Γ : Ctx s) where
  /-- The typings at members bounded by a kind, for `ksel`. -/
  capk : (x : BVar s .var) → (A : Label) → List (CapkView Γ x A)
  /-- The typings at members bounded by sets, for `kle` along
  `Subcap.selUpper`. -/
  bound : (x : BVar s .var) → (A : Label) → List (CapBoundView Γ x A)

/-- The oracle that knows no member typing. -/
def KindOracle.empty {s : Sig} {Γ : Ctx s} : KindOracle Γ := ⟨fun _ _ => [], fun _ _ => []⟩

/-- The entries of a list that sit at the variable `x` and the label `A`.  It
reads an oracle off a table that keeps variable and label beside each entry. -/
def viewsAt {s : Sig} {V : BVar s .var → Label → Type}
    (es : List ((y : BVar s .var) × (B : Label) × V y B)) (x : BVar s .var) (A : Label) :
    List (V x A) :=
  match es with
  | [] => []
  | ⟨y, B, v⟩ :: es =>
      if h : y = x ∧ B = A then (h.1 ▸ h.2 ▸ v) :: viewsAt es x A else viewsAt es x A
termination_by structural es

/-- An oracle read off two tables of entries. -/
def KindOracle.ofLists {s : Sig} {Γ : Ctx s}
    (ks : List ((y : BVar s .var) × (B : Label) × CapkView Γ y B))
    (bs : List ((y : BVar s .var) × (B : Label) × CapBoundView Γ y B)) : KindOracle Γ :=
  ⟨viewsAt ks, viewsAt bs⟩

/-! ## The search -/

/-- `ksel` through one view, with `ksub` when the kinds differ.  Equality is
tried first because `Kind.Subkind` is not known to be reflexive. -/
def kselOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} {A : Label} (φ : Cls.Kind)
    (v : CapkView Γ x A) : Option (CapKind Γ [.sel x A] φ) :=
  if h : v.kind = φ then some (h ▸ CapKind.ksel v.deriv)
  else if hs : v.kind.subkindB φ = true then some (.ksub (.ksel v.deriv) hs)
  else none

mutual

/-- The kinding search on a set.  `capKind? Γ V 0 C φ` is `none`.  At `n + 1`
the empty set is `nil`, and `a :: C` is `cons` of the atom search at `a` and
the set search at `C`, both at fuel `n`.  The last alternative retries at
fuel `n`. -/
def capKind? {s : Sig} (Γ : Ctx s) (V : KindOracle Γ) (n : Nat) (C : CaptureSet s)
    (φ : Cls.Kind) : Option (CapKind Γ C φ) :=
  match n with
  | 0 => none
  | n + 1 =>
      ((match C with
        | [] => some .nil
        | a :: C' =>
            match atomKind? Γ V n a φ, capKind? Γ V n C' φ with
            | some g, some h => some (.cons g h)
            | _, _ => none : Option (CapKind Γ C φ))).orElse fun _ =>
      -- the retry
      capKind? Γ V n C φ
termination_by structural n

/-- The kinding search at one atom.  `atomKind? Γ V 0 a φ` is `none`.  At
`n + 1` it tries the seven rules of the module's header in order, every
searched premise at fuel `n`, and then retries at fuel `n`. -/
def atomKind? {s : Sig} (Γ : Ctx s) (V : KindOracle Γ) (n : Nat) (a : CapAtom s)
    (φ : Cls.Kind) : Option (CapKind Γ [a] φ) :=
  match n with
  | 0 => none
  | n + 1 =>
      -- 1. kproj
      ((if h : a.kindOf.subkindB φ = true then some (CapKind.kproj h) else none :
          Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- 2. kcls
      ((match hc : Γ.clsOf? a.base with
        | some c =>
            if h2 : (a.kindOf.containsB c = true → φ.containsB c = true) then
              some (CapKind.kcls hc h2)
            else none
        | none => none : Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- 3, 4. kvar and kcvar
      ((match hb : a.base with
        | .var x =>
            (capKind? Γ V n (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ).map
              (CapKind.kvar hb)
        | .cvar κ =>
            match hi : Γ.instSet? κ with
            | some C => (capKind? Γ V n (CaptureSet.proj C a.kindOf) φ).map
                (CapKind.kcvar hb hi)
            | none => none
        | _ => none : Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- 5. ksel
      ((match a with
        | .sel x A => (V.capk x A).findSome? (kselOf φ)
        | _ => none : Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- 6. kprojS
      ((match unprojSetW? [a] with
        | some ⟨p, h⟩ => (capKind? Γ V n p.1 φ).map fun g => h ▸ CapKind.kprojS g
        | none => none : Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- 7. kle, along `Subcap.var` and along `Subcap.selUpper`
      ((match a with
        | .var x => (capKind? Γ V n (Γ.lookup x).captureSet φ).map (CapKind.kle Subcap.var)
        | .sel x A =>
            (V.bound x A).findSome? fun v =>
              (capKind? Γ V n v.hi φ).map (CapKind.kle (Subcap.selUpper v.deriv))
        | _ => none : Option (CapKind Γ [a] φ))).orElse fun _ =>
      -- the retry
      atomKind? Γ V n a φ
termination_by structural n

end

/-- The entry point.  A goal of one atom is kinded by the atom's own rule,
and any other set as a `cons` list. -/
def kind? {s : Sig} (Γ : Ctx s) (V : KindOracle Γ) (n : Nat) (C : CaptureSet s)
    (φ : Cls.Kind) : Option (CapKind Γ C φ) :=
  match C with
  | [a] => atomKind? Γ V n a φ
  | C => capKind? Γ V n C φ

/-! ## Fuel monotonicity

The statements are about successes, not derivations.  More fuel may find
another derivation of the same judgment, and `CapKind` is `Type` valued.  A
failure is not monotone. -/

/-- An alternative that succeeds makes the `orElse` succeed. -/
theorem isSome_orElse_right {α : Type} {a : Option α} {b : Unit → Option α}
    (h : (b ()).isSome = true) : (a.orElse b).isSome = true := by
  cases a with
  | none => simpa [Option.orElse] using h
  | some x => rfl

/-- A search that never loses an answer to one more unit of fuel never
loses it to any larger fuel. -/
theorem isSome_of_le {α : Type} (f : Nat → Option α)
    (hs : ∀ n, (f n).isSome = true → (f (n + 1)).isSome = true) {n n' : Nat} (h : n ≤ n') :
    (f n).isSome = true → (f n').isSome = true := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun x => hs _ (ih x)

/-- One more unit of fuel never loses a kinding of an atom. -/
theorem atomKind?_succ {s : Sig} {Γ : Ctx s} {V : KindOracle Γ} {n : Nat} {a : CapAtom s}
    {φ : Cls.Kind} (h : (atomKind? Γ V n a φ).isSome) : (atomKind? Γ V (n + 1) a φ).isSome := by
  rw [atomKind?.eq_def]
  iterate 6 refine isSome_orElse_right ?_
  exact h

/-- One more unit of fuel never loses a kinding of a set. -/
theorem capKind?_succ {s : Sig} {Γ : Ctx s} {V : KindOracle Γ} {n : Nat} {C : CaptureSet s}
    {φ : Cls.Kind} (h : (capKind? Γ V n C φ).isSome) : (capKind? Γ V (n + 1) C φ).isSome := by
  rw [capKind?.eq_def]
  refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a kinding of an atom. -/
theorem atomKind?_le {s : Sig} {Γ : Ctx s} {V : KindOracle Γ} {n n' : Nat} {a : CapAtom s}
    {φ : Cls.Kind} (h : n ≤ n') :
    (atomKind? Γ V n a φ).isSome → (atomKind? Γ V n' a φ).isSome :=
  isSome_of_le (fun n => atomKind? Γ V n a φ) (fun _ => atomKind?_succ) h

/-- More fuel never loses a kinding of a set. -/
theorem capKind?_le {s : Sig} {Γ : Ctx s} {V : KindOracle Γ} {n n' : Nat} {C : CaptureSet s}
    {φ : Cls.Kind} (h : n ≤ n') :
    (capKind? Γ V n C φ).isSome → (capKind? Γ V n' C φ).isSome :=
  isSome_of_le (fun n => capKind? Γ V n C φ) (fun _ => capKind?_succ) h

/-- More fuel never loses a kinding at the entry point. -/
theorem kind?_le {s : Sig} {Γ : Ctx s} {V : KindOracle Γ} {n n' : Nat} {C : CaptureSet s}
    {φ : Cls.Kind} (h : n ≤ n') :
    (kind? Γ V n C φ).isSome → (kind? Γ V n' C φ).isSome := by
  match C with
  | [] => exact capKind?_le h
  | [a] => exact atomKind?_le h
  | a :: b :: C => exact capKind?_le h

/-! ## Checks

Each kinding is searched at a judgment of the Classifiers examples
(`lean/Coercions/Classifiers/DotMNF/Examples.lean`).  A success is checked
against the written derivation of the same judgment, by equality of the two
translations, and by the FCdot checker on the translation.  Both are `Bool`
tests.  Where the oracle holds no typing they are kernel checks.  Where it
holds one, the translation is slow to unfold, so the comparison runs as
`#eval expect` and the success itself stays a kernel check. -/

section Tests

open Classifiers.DotMNF.Examples (E1PlatCtx E1Filt E1_kind E2IoCtx E2_io_arg_kind E2PlatIOCtx
  E2Filt E2TlDescent E3PlatCtx E3Uses E3_kind E3ClientCtx E3ClosureSet E3_client_kind_plat
  E3xCapPlat C2CtxG C2xCap E3k1 E3k2 lC up)

/-- The FCdot checker's verdict on the translation of a searched kinding. -/
private def kindVerdict {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (r : Option (CapKind Γ C φ)) : Bool :=
  match r with
  | some g => FCdot.checkKindCo Γ.translate g.translate C.translate φ
  | none => false

/-- A searched kinding and a written one have the same translation. -/
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

/-- `only[Control]`. -/
private def kindCtl : Cls.Kind := Cls.only Cls.Control

/-- `except[ThreadLocal]`. -/
private def kindNoTl : Cls.Kind := Cls.except Cls.ThreadLocal

/-! ### E1, the filtered platform set

A projected atom carries its own kind, so `kproj` succeeds at both atoms.
The written `E1_kind` takes `kcls` there, so the two derivations differ. -/

/-- The derivation the search takes for E1's use set. -/
private def E1_kind_kproj : CapKind E1PlatCtx E1Filt kindCtl :=
  .cons (.kproj (by decide)) (.cons (.kproj (by decide)) .nil)

example : agreesWith (kind? E1PlatCtx .empty 4 E1Filt kindCtl) E1_kind_kproj = true := by
  decide +kernel
example : agreesWith (kind? E1PlatCtx .empty 4 E1Filt kindCtl) E1_kind = false := by
  decide +kernel
example : kindVerdict (kind? E1PlatCtx .empty 4 E1Filt kindCtl) = true := by
  decide +kernel

/-! ### E2, an argument charged to the IO capability, and the thread-local one

At a bare variable `kproj` fails, since `⊤` is not a subkind of
`except[ThreadLocal]`, and `kcls` fails, since the binder is a term variable.
`kvar` descends to the declared set, where `kcls` finishes.  This is
`E2_io_arg_kind`. -/

example : agreesWith (kind? E2IoCtx .empty 4 [CapAtom.var .here] kindNoTl) E2_io_arg_kind
    = true := by
  decide +kernel
example : kindVerdict (kind? E2PlatIOCtx .empty 5 E2Filt kindNoTl) = true := by
  decide +kernel

/-- The set a thread-local argument descends to is not kinded at the filter
(`E2_tl_descent_not_capKind`).  The search finds none up to fuel 10. -/
example : (List.range 11).all
    (fun n => (kind? E2PlatIOCtx .empty n E2TlDescent kindNoTl).isNone) = true := by
  decide +kernel

/-! ### E3, the use set, by `kcls` twice as written -/

example : agreesWith (kind? E3PlatCtx .empty 4 E3Uses kindCtl) E3_kind = true := by
  decide +kernel

/-! ### E3, the client's closure set, through `ksel`

The oracle holds the typing `E3xCapPlat` of `x` at the member bounded by
`only[Control]`. -/

/-- The oracle at the client's context. -/
private def e3Oracle : KindOracle E3ClientCtx :=
  .ofLists [⟨_, _, ⟨_, _, _, E3xCapPlat⟩⟩] []

example : (kind? E3ClientCtx e3Oracle 1 E3ClosureSet kindCtl).isSome = true := by
  decide +kernel

#eval expect (agreesWith (kind? E3ClientCtx e3Oracle 1 E3ClosureSet kindCtl)
    E3_client_kind_plat)
  "E3: the search does not reproduce E3_client_kind"

/-- At a kind the member's kind is a subkind of, `ksub` follows `ksel`. -/
example : (kind? E3ClientCtx e3Oracle 1 E3ClosureSet (kindCtl ∪ Cls.only Cls.IO)).map ruleNames
    = some ["ksub", "ksel"] := by
  decide +kernel

/-- The member bounded by a kind is read only through `ksel`, and the empty
oracle holds no typing for it.  The written derivation `E3_client_kind` needs
that typing. -/
example : (kind? E3ClientCtx .empty 10 E3ClosureSet kindCtl).isNone = true := by
  decide +kernel

/-! ### The closure `g` at `{x.C}`, under a filtered domain

`g` is declared at `{x.C}`.  Handing it to a domain `{any.only[Control]}` asks
for a kinding of `{g}` at `only[Control]`.  `kvar` descends to `{x.C ↾ ⊤}`,
which `kprojS` takes to `{x.C}`, where `ksel` finishes. -/

example : (kind? E3ClientCtx e3Oracle 5 [CapAtom.var .here] kindCtl).isSome = true := by
  decide +kernel

/-- More fuel keeps the kinding. -/
example : (kind? E3ClientCtx e3Oracle 9 [CapAtom.var .here] kindCtl).isSome = true :=
  kind?_le (n := 5) (by decide) (by decide +kernel)

#eval expect (kindVerdict (kind? E3ClientCtx e3Oracle 5 [CapAtom.var .here] kindCtl))
  "g: the target checker rejects the searched kinding"

example : (kind? E3ClientCtx e3Oracle 5 [CapAtom.var .here] kindCtl).map ruleNames
    = some ["kvar", "cons", "kprojS", "cons", "ksel", "nil", "nil"] := by
  decide +kernel

/-! ### A selection off a member bounded by sets

C2's client read over E3's platform, where both capabilities are `Control`.
`x` has the member `{C : {}..{κ₁,κ₂}}`, and `g` is declared at `{x.C}`.
`{x.C}` is kinded at `only[Control]` by `kle` along `Subcap.selUpper` over two
`kcls`, and `{g}` by `kle` along `Subcap.var` over that. -/

/-- C2's client context over E3's platform. -/
private abbrev C2OnE3Ctx : Ctx (Sig.body (Sig.body ([],c,c)),x) := C2CtxG E3PlatCtx E3k1 E3k2

/-- The oracle holds the typing of `x` at its member bounded by sets. -/
private def c2Oracle : KindOracle C2OnE3Ctx := .ofLists [] [⟨_, _, ⟨_, _, _, _, C2xCap⟩⟩]

example : (kind? C2OnE3Ctx c2Oracle 4 [CapAtom.sel (.there (up .here)) lC] kindCtl).isSome
    = true := by
  decide +kernel
example : (kind? C2OnE3Ctx c2Oracle 6 [CapAtom.var .here] kindCtl).isSome = true := by
  decide +kernel

#eval expect (kindVerdict (kind? C2OnE3Ctx c2Oracle 4 [CapAtom.sel (.there (up .here)) lC]
    kindCtl))
  "x.C: the target checker rejects the searched kinding"

#eval expect (kindVerdict (kind? C2OnE3Ctx c2Oracle 6 [CapAtom.var .here] kindCtl))
  "g: the target checker rejects the searched kinding"

example : (kind? C2OnE3Ctx c2Oracle 4 [CapAtom.sel (.there (up .here)) lC] kindCtl).map ruleNames
    = some ["kle", "cons", "kcls", "cons", "kcls", "nil"] := by
  decide +kernel

/-- The upper bound is read only off a typing the oracle holds. -/
example : (kind? C2OnE3Ctx .empty 10 [CapAtom.sel (.there (up .here)) lC] kindCtl).isNone
    = true := by
  decide +kernel

end Tests

end ClassifiersFrontend
