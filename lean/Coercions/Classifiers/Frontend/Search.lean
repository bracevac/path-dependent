import Coercions.Classifiers.Frontend.Kind
import Coercions.Classifiers.Frontend.Surface

/-!
# Views, the declaration table, and the subtyping and subcapturing search

The typer needs two things this module provides.  A *view* of a context
variable is a type the variable has, carried with its use set and its
derivation, so the typer may read a field or a member off a variable whose
declared type does not display it.  A *declaration* is a type member or a
capture member a context variable has, again with its derivation.  The
*declaration table* of a context is the family of middles the search may
try for `SubShape.trans` and `Subcap.trans`, whose middles are otherwise
undetermined (`lean/Coercions/Classifiers/DotMNF/Typing.lean:830,948`).

Everything here returns the derivation, so there is no soundness theorem.
The result type is the statement.  Nothing here is complete, and no
completeness theorem is claimed.

## The three layers

A type of the version is a shape with a capture set, `S ^ C`, and `Sub` has
the one rule `capt`, a `SubShape` on the shapes beside a `Subcap` on the
sets (`Typing.lean:994-996`).  An answer is a type or an existential over a
capture binder, and `ESub` relates answers by three rules.  So the search is
three functions.  `subcap?` searches sets.  `subShape?` searches shapes and
calls `subcap?` for every set it meets.  `esub?` searches answers by the
three rules of `ESub` over the other two.

The arrow rule opens scopes.  It compares the domains under `Γ.scope` and
the codomains, which are answers, under `Γ.body T₂`
(`Typing.lean:979-982`).  An existential packs under `Γ.scopeInst C`, where
an instance binder stands for the witness `C`, and two existentials compare
under `Γ.scope` (`Typing.lean:1008-1017`).  So the answer rules are written
once, in `esubWith`, against searches at those three contexts, and the arrow
rule of `subShape?` hands them its own recursive calls.

## The rules of subcapturing

Beside the inclusion, the union, `sc-var` and the two capture-member rules,
the version has two rules about capture binders.  The level rule puts `{e}`
below a scope root `κ` when `e` is at or outside the level of `κ`
(`Typing.lean:856-858`).  Both premises are `Bool` equations of the frozen
`Ctx.isRootB` and `Ctx.lvlLeB`, so the search decides them.  The instance
rule puts the set an instance binder stands for below that binder
(`Typing.lean:843-844`), read off the frozen `Ctx.instSet?`.

## Projections and kinds

A capture set may be projected at a classifier kind, `C ↾ φ`.  Three rules
relate a projected set to its base: `unproj` puts `C ↾ φ` below `C`, `proj`
puts `C` below `C ↾ φ` when `C` is kinded at `φ`, and `projMono` projects both
sides of a subcapturing (`Typing.lean:871-882`).  The search tries them on
the whole goal, and atom by atom: a left side that mixes projected and plain
atoms is split by the union rule, and an atom may go into one projected atom
of the right side and from there into the whole right side by inclusion.

`proj` premises a kinding `CapKind`, and so does the shape rule `capkI`,
which takes a capture member bounded by sets to one bounded by a kind.  The
kinding search of `Kind.lean` finds them.  It reads the member typings it
needs off the declaration table, which records the members bounded by
kinds beside the others, and it runs at the table's own fuel, `kindFuel`,
which `decls` sets to `Budget.kind`.

## What is fuel bounded, and why

Seven counters live in `Budget`.  `decls` counts rounds of the table, `views`
counts rounds of the view closure, `cap` is the fuel of the subcapturing
search, `sub` is the fuel of the shape search, `typer` is the fuel of the
typer, `obj` bounds the passes of the object rule, and `kind` is the fuel of
the kinding search.  An unbounded closure
grows too fast to compute, so duplicates are dropped after every round, the
table is computed once per context and passed as a parameter, and the
closure and the table have small round counters of their own, separate
from the fuel of the search.

## The order of definition

The view closure calls the search in its detour step, and the arrow rule of
the search builds a table under a scope.  Taken literally that is a cycle.
It is cut by making the table a parameter of the search and by writing the
view steps once, in `viewStepOf`, against an abstract search.  The tables
the scope rules build are computed with `noSub`, the search that finds
nothing, so the search mentions no search but its own.

## The kernel

Every function here is structural, on a fuel or on a list, so the kernel
reduces the search, and the probes at the end are `decide +kernel`.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy CapKind)
open Classifiers
open scoped Classifiers.DotMNF

/-! ## Views and declarations -/

/-- A type a context variable has, at a use set, with the derivation. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ty)

/-- A pure binder at its declared type, at the empty use set.  `Var`
concludes at `{x}` for both sets, and `sc-var` takes both down to the
declared set, which is empty (`Typing.lean:838-839,1022-1023`). -/
def pureVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (h : (Γ.lookup x).captureSet = []) :
    HasTy [] Γ (.path (.var x)) (.ty (Γ.lookup x)) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  have e : HasTy [] Γ (.path (.var x)) (.ty ((Γ.lookup x).shape ^ [])) :=
    HasTy.sub HasTy.var (.ty (.capt .refl hv)) hv
  have hT : (Γ.lookup x).shape ^ [] = Γ.lookup x := by
    rw [← h]
    exact (Ty.eta _).symm
  rw [hT] at e
  exact e

/-- The first view of a variable, at the least use set and the least
capture set the rules give it.  A binder declared at the empty set is used
at the empty set and keeps its declared type.  Any other binder is used at
`{x}` and has its declared shape at `{x}`, by `Var`. -/
def varView {s : Sig} (Γ : Ctx s) (x : BVar s .var) : View Γ x :=
  if h : (Γ.lookup x).captureSet = [] then ⟨[], Γ.lookup x, pureVar Γ x h⟩
  else ⟨[.var x], (Γ.lookup x).shape ^ [.var x], .var⟩

/-- A type member a context variable has, with the derivation.  The four
fields `vr`, `lbl`, `lo`, `hi` are the key by which the table is
deduplicated. -/
structure Decl {s : Sig} (Γ : Ctx s) where
  /-- The variable the member is read off. -/
  vr : BVar s .var
  /-- The label of the member. -/
  lbl : Label
  /-- The lower bound. -/
  lo : Shape s
  /-- The upper bound. -/
  hi : Shape s
  /-- The use set of the derivation. -/
  uses : CaptureSet s
  /-- The capture set of the type the derivation concludes at. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var vr)) (.ty ((Shape.typ lbl lo hi) ^ cs))

/-- A capture member a context variable has, with the derivation.  The four
fields `vr`, `lbl`, `lo`, `hi` are the key by which the table is
deduplicated. -/
structure CapDecl {s : Sig} (Γ : Ctx s) where
  /-- The variable the member is read off. -/
  vr : BVar s .var
  /-- The label of the member. -/
  lbl : Label
  /-- The lower bound. -/
  lo : CaptureSet s
  /-- The upper bound. -/
  hi : CaptureSet s
  /-- The use set of the derivation. -/
  uses : CaptureSet s
  /-- The capture set of the type the derivation concludes at. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var vr)) (.ty ((Shape.cap lbl lo hi) ^ cs))

/-- A capture member bounded by a kind, `{C : φ}`, that a context variable
has, with the derivation.  The three fields `vr`, `lbl`, `kind` are the key by
which the table is deduplicated. -/
structure CapkDecl {s : Sig} (Γ : Ctx s) where
  /-- The variable the member is read off. -/
  vr : BVar s .var
  /-- The label of the member. -/
  lbl : Label
  /-- The kind that bounds the member. -/
  kind : Cls.Kind
  /-- The use set of the derivation. -/
  uses : CaptureSet s
  /-- The capture set of the type the derivation concludes at. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var vr)) (.ty ((Shape.capk lbl kind) ^ cs))

/-- The declaration table of a context: its type members, its capture
members bounded by sets and its capture members bounded by kinds.  It also
holds the fuel at which a search over the table calls the kinding search,
since the rules `Subcap.proj` and `SubShape.capkI` premise a kinding, and the
kinding search reads its member typings off this table. -/
structure DeclTable {s : Sig} (Γ : Ctx s) where
  /-- The type members. -/
  typs : List (Decl Γ)
  /-- The capture members bounded by sets. -/
  caps : List (CapDecl Γ)
  /-- The capture members bounded by kinds. -/
  capks : List (CapkDecl Γ)
  /-- The fuel of the kinding search. -/
  kindFuel : Nat

/-- The empty table, with the kinding search at fuel `k`. -/
def DeclTable.emptyAt {s : Sig} {Γ : Ctx s} (k : Nat) : DeclTable Γ := ⟨[], [], [], k⟩

/-- The empty table.  A search over it finds no kinding. -/
def DeclTable.empty {s : Sig} {Γ : Ctx s} : DeclTable Γ := .emptyAt 0

/-- Two tables side by side, at the kinding fuel of the first. -/
def DeclTable.append {s : Sig} {Γ : Ctx s} (D E : DeclTable Γ) : DeclTable Γ :=
  ⟨D.typs ++ E.typs, D.caps ++ E.caps, D.capks ++ E.capks, D.kindFuel⟩

/-- The member typings of a table as the kinding search reads them: the
members bounded by kinds for `CapKind.ksel`, and those bounded by sets for
`CapKind.kle` along `Subcap.selUpper`. -/
def DeclTable.oracle {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) : KindOracle Γ :=
  KindOracle.ofLists (D.capks.map fun d => ⟨d.vr, d.lbl, ⟨d.uses, d.kind, d.cs, d.deriv⟩⟩)
    (D.caps.map fun d => ⟨d.vr, d.lbl, ⟨d.lo, d.hi, d.uses, d.cs, d.deriv⟩⟩)

/-- The kinding search at the oracle and the fuel of a table. -/
def DeclTable.kind? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (C : CaptureSet s) (φ : Cls.Kind) :
    Option (CapKind Γ C φ) :=
  ClassifiersFrontend.kind? Γ D.oracle D.kindFuel C φ

/-- The selection a type member licenses, `y.A`. -/
def declSel {s : Sig} {Γ : Ctx s} (d : Decl Γ) : Shape s := .sel (.var d.vr) d.lbl

/-- `<:-Sel` at a type member of the table. -/
def declLower {s : Sig} {Γ : Ctx s} (d : Decl Γ) : SubShape Γ d.lo (declSel d) :=
  SubShape.selLower d.deriv

/-- `Sel-<:` at a type member of the table. -/
def declUpper {s : Sig} {Γ : Ctx s} (d : Decl Γ) : SubShape Γ (declSel d) d.hi :=
  SubShape.selUpper d.deriv

/-- The atom a capture member licenses, `y.C`. -/
def capSel {s : Sig} {Γ : Ctx s} (d : CapDecl Γ) : CapAtom s := .sel d.vr d.lbl

/-- `sc-sel-lower` at a capture member of the table. -/
def capLower {s : Sig} {Γ : Ctx s} (d : CapDecl Γ) : Subcap Γ d.lo [capSel d] :=
  Subcap.selLower d.deriv

/-- `sc-sel-upper` at a capture member of the table. -/
def capUpper {s : Sig} {Γ : Ctx s} (d : CapDecl Γ) : Subcap Γ [capSel d] d.hi :=
  Subcap.selUpper d.deriv

/-- The seven counters.  The defaults are a starting point, not a
measurement.  The probes below give the budget at which each was found. -/
structure Budget where
  /-- Rounds of the declaration table. -/
  decls : Nat := 3
  /-- Rounds of the view closure. -/
  views : Nat := 3
  /-- Fuel of the shape search. -/
  sub : Nat := 6
  /-- Fuel of the subcapturing search. -/
  cap : Nat := 6
  /-- Fuel of the typer. -/
  typer : Nat := 8
  /-- Passes of the object rule. -/
  obj : Nat := 3
  /-- Fuel of the kinding search. -/
  kind : Nat := 6
deriving Repr, Inhabited

/-! ## Deduplication

Both closures grow only by rounds, and both drop duplicates after each
round: views by their type, declarations by their four key fields.  The
first entry of each key is the one kept.  One procedure serves all three
lists, generic in the key.  It is structural on the list, with the keys seen
so far as an accumulator. -/

/-- Membership of a key in a list of keys, as a decision. -/
def keyMem? {κ : Type} [DecidableEq κ] (k : κ) (ks : List κ) : Bool :=
  match ks with
  | [] => false
  | k' :: ks => if k' = k then true else keyMem? k ks
termination_by structural ks

theorem keyMem?_cons {κ : Type} [DecidableEq κ] (k k' : κ) (ks : List κ) :
    keyMem? k (k' :: ks) = true ↔ (k' = k ∨ keyMem? k ks = true) := by
  by_cases h : k' = k
  · simp [keyMem?, h]
  · simp [keyMem?, h]

/-- Entries whose key is already in `seen` are dropped. -/
def dedupFrom {α κ : Type} [DecidableEq κ] (key : α → κ) (seen : List κ) (l : List α) :
    List α :=
  match l with
  | [] => []
  | a :: as =>
      if keyMem? (key a) seen then dedupFrom key seen as
      else a :: dedupFrom key (key a :: seen) as
termination_by structural l

/-- Keep the first entry of each key. -/
def dedupBy {α κ : Type} [DecidableEq κ] (key : α → κ) (l : List α) : List α :=
  dedupFrom key [] l

theorem dedupFrom_covers {α κ : Type} [DecidableEq κ] (key : α → κ) (l : List α) :
    ∀ (seen : List κ) (a : α), a ∈ l →
      keyMem? (key a) seen = true ∨ ∃ b ∈ dedupFrom key seen l, key b = key a := by
  induction l with
  | nil => intro seen a ha; cases ha
  | cons u l ih =>
      intro seen a ha
      by_cases hs : keyMem? (key u) seen = true
      · have heq : dedupFrom key seen (u :: l) = dedupFrom key seen l := by
          simp [dedupFrom, hs]
        cases List.mem_cons.mp ha with
        | inl he => exact Or.inl (he ▸ hs)
        | inr ha' => rw [heq]; exact ih seen a ha'
      · have heq : dedupFrom key seen (u :: l) = u :: dedupFrom key (key u :: seen) l := by
          simp [dedupFrom, hs]
        cases List.mem_cons.mp ha with
        | inl he => exact Or.inr ⟨u, by rw [heq]; simp, by rw [he]⟩
        | inr ha' =>
            cases ih (key u :: seen) a ha' with
            | inl h =>
                cases (keyMem?_cons (key a) (key u) seen).mp h with
                | inl h' => exact Or.inr ⟨u, by rw [heq]; simp, h'⟩
                | inr h' => exact Or.inl h'
            | inr h =>
                obtain ⟨b, hb, hbk⟩ := h
                exact Or.inr ⟨b, by rw [heq]; exact List.mem_cons_of_mem _ hb, hbk⟩

/-- Deduplication keeps one entry of each key. -/
theorem dedupBy_covers {α κ : Type} [DecidableEq κ] (key : α → κ) (l : List α) :
    ∀ a ∈ l, ∃ b ∈ dedupBy key l, key b = key a := by
  intro a ha
  cases dedupFrom_covers key l [] a ha with
  | inl h => exact absurd h (by simp [keyMem?])
  | inr h => exact h

/-- The key of a type member. -/
def declKey {s : Sig} {Γ : Ctx s} (d : Decl Γ) : BVar s .var × Label × Shape s × Shape s :=
  (d.vr, d.lbl, d.lo, d.hi)

/-- The key of a capture member. -/
def capDeclKey {s : Sig} {Γ : Ctx s} (d : CapDecl Γ) :
    BVar s .var × Label × CaptureSet s × CaptureSet s :=
  (d.vr, d.lbl, d.lo, d.hi)

/-- The key of a capture member bounded by a kind. -/
def capkDeclKey {s : Sig} {Γ : Ctx s} (d : CapkDecl Γ) : BVar s .var × Label × Cls.Kind :=
  (d.vr, d.lbl, d.kind)

/-! ## The view closure

A step of the closure takes one view of a variable to the views reachable
from it in one rule.  `open` and the two `and` steps read the rules off the
derivation alone.  The `upper` step and the `detour` step consult the
table, and the detour step consults a search as well, which is why the step
is written against an abstract search.  Every step keeps the use set and
the capture set of the view it starts from: they change only the shape. -/

/-- One step of the view closure, uniform in the variable. -/
def ViewStep {s : Sig} (Γ : Ctx s) : Type :=
  (x : BVar s .var) → View Γ x → List (View Γ x)

/-- A search on shapes over a fixed context, as the detour step consumes
it. -/
def SubSearch {s : Sig} (Γ : Ctx s) : Type := (S T : Shape s) → Option (SubShape Γ S T)

/-- The search that finds nothing.  It is what the scope rules pass when
they build a table under a scope, where calling the real search would be
circular. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-- A shape subtyping lifted to the type it starts from, the capture set
kept. -/
def subOfShape {s : Sig} {Γ : Ctx s} : (T : Ty s) → {S : Shape s} →
    SubShape Γ T.shape S → Sub Γ T (S ^ T.captureSet)
  | .capt _ _, _, e => .capt e .refl

/-- The five view steps, against an abstract search.

| step | condition on `v.ty` | new view | rule |
|---|---|---|---|
| open | `(μ S) ^ C` and `Shape.Decl S` | `S.substVar x ^ C` | `HasTy.recE` (`Typing.lean:1082-1085`) |
| left | `(S ∧ T) ^ C` | `S ^ C` | `HasTy.sub` with `SubShape.and1` |
| right | `(S ∧ T) ^ C` | `T ^ C` | `HasTy.sub` with `SubShape.and2` |
| upper | `y.A ^ C` at a type member `d` | `d.hi ^ C` | `HasTy.sub` with `SubShape.selUpper` |
| detour | the search takes the shape to `d.lo` | `d.hi ^ C` | `HasTy.sub` with `SubShape.trans` |

The detour step's derivation carries the evidence `e` of its own side
condition. -/
def viewStepOf {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) (D : DeclTable Γ) : ViewStep Γ :=
  fun x v =>
    (match hv : v.ty with
      | .capt C (.mu S) =>
          if hd : Shape.Decl S then
            [⟨v.uses, (S.substVar x) ^ C, .recE (hv ▸ v.deriv) hd⟩]
          else []
      | .capt C (.and S T) =>
          [⟨v.uses, S ^ C, .sub (hv ▸ v.deriv) (.ty (.capt .and1 .refl)) .refl⟩,
           ⟨v.uses, T ^ C, .sub (hv ▸ v.deriv) (.ty (.capt .and2 .refl)) .refl⟩]
      | _ => [])
    ++ D.typs.filterMap (fun d =>
        if h : v.ty.shape = declSel d then
          some ⟨v.uses, d.hi ^ v.ty.captureSet,
            .sub v.deriv (.ty (subOfShape v.ty (h ▸ declUpper d))) .refl⟩
        else none)
    ++ D.typs.filterMap (fun d =>
        (sub v.ty.shape d.lo).map (fun e =>
          ⟨v.uses, d.hi ^ v.ty.captureSet,
            .sub v.deriv
              (.ty (subOfShape v.ty
                (SubShape.trans e (SubShape.trans (declLower d) (declUpper d)))))
              .refl⟩))

/-- One round of the closure: every view of the list, plus one step from
each, with the duplicates by type dropped. -/
def viewsRoundOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : List (View Γ x) :=
  dedupBy View.ty (vs ++ vs.flatMap (st x))

/-- The closure of the first view of a variable under `m` rounds. -/
def viewsOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (m : Nat) (x : BVar s .var) :
    List (View Γ x) :=
  match m with
  | 0 => [varView Γ x]
  | m + 1 => viewsRoundOf st x (viewsOf st m x)
termination_by structural m

/-! ## The declaration table -/

/-- The members a list of views of one variable displays: its `typ` views
as type members, its `cap` views as capture members bounded by sets, its
`capk` views as capture members bounded by kinds.  The kinding fuel of the
result is not read. -/
def tableOfViews {s : Sig} {Γ : Ctx s} {y : BVar s .var} (vs : List (View Γ y)) :
    DeclTable Γ :=
  match vs with
  | [] => .empty
  | v :: vs =>
      DeclTable.append
        (match hv : v.ty with
          | .capt C (.typ A L U) => ⟨[⟨y, A, L, U, v.uses, C, hv ▸ v.deriv⟩], [], [], 0⟩
          | .capt C (.cap A c1 c2) => ⟨[], [⟨y, A, c1, c2, v.uses, C, hv ▸ v.deriv⟩], [], 0⟩
          | .capt C (.capk A φ) => ⟨[], [], [⟨y, A, φ, v.uses, C, hv ▸ v.deriv⟩], 0⟩
          | _ => .empty)
        (tableOfViews vs)
termination_by structural vs

/-- The members the views of the listed variables display, each variable's
closure computed once. -/
def tableOfVars {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (m : Nat) (ys : List (BVar s .var)) :
    DeclTable Γ :=
  match ys with
  | [] => .empty
  | y :: ys => DeclTable.append (tableOfViews (viewsOf st m y)) (tableOfVars st m ys)
termination_by structural ys

/-- One round of the table: every member already in it, plus the members
the views of every context variable display, computed against it and
deduplicated by key.  The kinding fuel is kept. -/
def declsRoundOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    (D : DeclTable Γ) : DeclTable Γ :=
  let N := tableOfVars (stf D) m (ctxVars Γ)
  ⟨dedupBy declKey (D.typs ++ N.typs), dedupBy capDeclKey (D.caps ++ N.caps),
    dedupBy capkDeclKey (D.capks ++ N.capks), D.kindFuel⟩

/-- The table after `k` rounds, each round running `m` rounds of the
closure, with the kinding search at fuel `kf`. -/
def declsOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (kf m : Nat) (k : Nat) :
    DeclTable Γ :=
  match k with
  | 0 => .emptyAt kf
  | k + 1 => declsRoundOf stf m (declsOf stf kf m k)
termination_by structural k

/-- The detour free table, the one the scope rules of the search build under
the scopes they open.  Building the full table there would make the search
mutual with the view closure. -/
def baseDecls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStepOf noSub D) b.kind b.views b.decls

/-! ## Helpers of the search

The shape rules are written either as a decidable equality on a constructed
shape or as a `match` whose fall-through branch is `none`, never as a
`match` whose fall-through branch returns a derivation: a `match` on `S` or
on `T` inside a function whose result type mentions them generalizes them
in the motive, and a fall-through that is not `none` then does not
typecheck.

The helpers below move a derivation across a decided equality.  They are
written with `cases` rather than with `▸` because the label of a member
occurs twice in the conclusion and a rewrite would hit both occurrences. -/

/-- The first success of a function along a list. -/
def firstSome {α β : Type} (f : α → Option β) (l : List α) : Option β :=
  match l with
  | [] => none
  | a :: as => (f a).orElse fun _ => firstSome f as
termination_by structural l

/-- `Sub.capt` of a shape search and a set search, at two given types. -/
def subCapt {s : Sig} {Γ : Ctx s} (sh : (S S' : Shape s) → Option (SubShape Γ S S'))
    (sc : (C C' : CaptureSet s) → Option (Subcap Γ C C')) :
    (T U : Ty s) → Option (Sub Γ T U)
  | .capt C S, .capt C' S' => do
      let e1 ← sh S S'
      let e2 ← sc C C'
      some (Sub.capt e1 e2)

/-- `SubShape.fld` with the two labels equal by a decision. -/
def subFldOf {s : Sig} {Γ : Ctx s} {a b : Label} {T U : Ty s} (h : a = b)
    (e : Sub Γ T U) : SubShape Γ (.fld a T) (.fld b U) := by
  cases h; exact SubShape.fld e

/-- `SubShape.typ` with the two labels equal by a decision. -/
def subTypOf {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Shape s} (h : A = B)
    (e1 : SubShape Γ S2 S1) (e2 : SubShape Γ T1 T2) :
    SubShape Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h; exact SubShape.typ e1 e2

/-- `SubShape.cap` with the two labels equal by a decision. -/
def subCapOf {s : Sig} {Γ : Ctx s} {A B : Label} {c1 c2 c1' c2' : CaptureSet s} (h : A = B)
    (e1 : Subcap Γ c1' c1) (e2 : Subcap Γ c2 c2') :
    SubShape Γ (.cap A c1 c2) (.cap B c1' c2') := by
  cases h; exact SubShape.cap e1 e2

/-- `S <: d.lo <: y.A`, where `T` is that selection. -/
def subToSel {s : Sig} {Γ : Ctx s} {d : Decl Γ} {S T : Shape s} (h : T = declSel d)
    (e : SubShape Γ S d.lo) : SubShape Γ S T := by
  cases h; exact SubShape.trans e (declLower d)

/-- `y.A <: d.hi <: T`, where `S` is that selection. -/
def subFromSel {s : Sig} {Γ : Ctx s} {d : Decl Γ} {S T : Shape s} (h : S = declSel d)
    (e : SubShape Γ d.hi T) : SubShape Γ S T := by
  cases h; exact SubShape.trans (declUpper d) e

/-- `S <: d1.lo <: y.A <: d2.hi <: T`, the one family of transitivity
middles the search tries on shapes.  The two members may differ, which is
what E3 needs (`lean/Coercions/Classifiers/DotMNF/Examples.lean:232`). -/
def subThroughPair {s : Sig} {Γ : Ctx s} {d1 d2 : Decl Γ} {S T : Shape s}
    (h : declSel d2 = declSel d1) (e1 : SubShape Γ S d1.lo) (e2 : SubShape Γ d2.hi T) :
    SubShape Γ S T :=
  SubShape.trans e1 (SubShape.trans (declLower d1) (SubShape.trans (h ▸ declUpper d2) e2))

/-- `{y.C} <: d.hi <: C₂`, where `C₁` is `{y.C}`. -/
def subcapFromSel {s : Sig} {Γ : Ctx s} {d : CapDecl Γ} {C1 C2 : CaptureSet s}
    (h : C1 = [capSel d]) (e : Subcap Γ d.hi C2) : Subcap Γ C1 C2 := by
  cases h; exact Subcap.trans (capUpper d) e

/-- `C₁ <: d.lo <: {y.C} ⊆ C₂`. -/
def subcapToSel {s : Sig} {Γ : Ctx s} {d : CapDecl Γ} {C1 C2 : CaptureSet s}
    (h : CaptureSet.Subset [capSel d] C2) (e : Subcap Γ C1 d.lo) : Subcap Γ C1 C2 :=
  Subcap.trans e (Subcap.trans (capLower d) (.elem h))

/-- The pairs of type members the transitivity rule walks. -/
def declPairs {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) : List (Decl Γ × Decl Γ) :=
  D.typs.flatMap (fun d1 => D.typs.map (fun d2 => (d1, d2)))

/-- The rounds the scope rules give the detour free table they build under
a scope.  Small on purpose: the table is rebuilt at every application of
a scope rule. -/
def allBudget : Budget := { decls := 1, views := 2, sub := 0, cap := 0, typer := 0, obj := 0 }

/-- The budget of a table under a scope, at the kinding fuel `k` of the table
outside it. -/
def scopeBudget (k : Nat) : Budget := { allBudget with kind := k }

/-! ## The subcapturing search -/

/-- The level rule into one atom of the target set: `{e} <: {κ} ⊆ C₂` when
the atom is a capture binder `κ` that is a scope root and `e` is at or
outside its level.  Every premise is decided. -/
def levelInto? {s : Sig} {Γ : Ctx s} (e : CapAtom s) (C2 : CaptureSet s) (b : CapAtom s) :
    Option (Subcap Γ [e] C2) :=
  match b with
  | .cvar κ =>
      if h1 : Γ.IsRoot (.cvar κ) then
        if h2 : Γ.LvlLe e (.cvar κ) then
          if hm : CaptureSet.Subset [CapAtom.cvar κ] C2 then
            some (Subcap.trans (Subcap.level h1 h2) (Subcap.elem hm))
          else none
        else none
      else none
  | _ => none

/-! ### The three projection rules

`Subcap.unproj` puts a projected set below the set it projects,
`Subcap.proj` puts a kinded set below its projection, and `Subcap.projMono`
projects both sides of a subcapturing at one kind.  A side is read as a
projection `C₀ ↾ φ` by `unprojSetW?`, which returns the decided equation
with it, so a wrong reading costs a `none`.  The helpers move a derivation
across that equation. -/

/-- `L = C₀ ↾ φ <: C₀ <: R`. -/
def unprojTo {s : Sig} {Γ : Ctx s} {C₀ L R : CaptureSet s} {φ : Cls.Kind}
    (h : CaptureSet.proj C₀ φ = L) (e : Subcap Γ C₀ R) : Subcap Γ L R := by
  cases h; exact Subcap.trans Subcap.unproj e

/-- `L = C₀ ↾ φ <: C₀ = R`, a bare `unproj`. -/
def unprojBare {s : Sig} {Γ : Ctx s} {C₀ L R : CaptureSet s} {φ : Cls.Kind}
    (h : CaptureSet.proj C₀ φ = L) (hR : C₀ = R) : Subcap Γ L R := by
  cases h; cases hR; exact Subcap.unproj

/-- `L <: C₀ <: C₀ ↾ φ = R`, with `C₀` kinded at `φ`. -/
def projTo {s : Sig} {Γ : Ctx s} {C₀ L R : CaptureSet s} {φ : Cls.Kind}
    (h : CaptureSet.proj C₀ φ = R) (g : CapKind Γ C₀ φ) (e : Subcap Γ L C₀) : Subcap Γ L R := by
  cases h; exact Subcap.trans e (Subcap.proj g)

/-- `L = C₀ <: C₀ ↾ φ = R`, a bare `proj`. -/
def projBare {s : Sig} {Γ : Ctx s} {C₀ L R : CaptureSet s} {φ : Cls.Kind}
    (h : CaptureSet.proj C₀ φ = R) (g : CapKind Γ C₀ φ) (hL : L = C₀) : Subcap Γ L R := by
  cases h; cases hL; exact Subcap.proj g

/-- `L = C ↾ φ <: D ↾ ψ = R` from `C <: D`, with `φ = ψ`. -/
def projMonoTo {s : Sig} {Γ : Ctx s} {C D L R : CaptureSet s} {φ ψ : Cls.Kind}
    (h1 : CaptureSet.proj C φ = L) (h2 : CaptureSet.proj D ψ = R) (hk : φ = ψ)
    (e : Subcap Γ C D) : Subcap Γ L R := by
  cases h1; cases h2; cases hk; exact Subcap.projMono e

/-- The three projection rules against a base search, in order.

1. `L = C₀ ↾ φ`, `unproj`: bare when `C₀` is `R`, otherwise the base search
   of `C₀ <: R`.
2. `R = C₀ ↾ φ`, `proj`: `C₀` kinded at `φ` by the kinding search of the
   table, then bare when `L` is `C₀`, otherwise the base search of
   `L <: C₀`.
3. `L = C ↾ φ` and `R = D ↾ φ`, `projMono` over the base search of `C <: D`.

The bare forms are the ones the version writes at a call
(`E1call`, `E2call`, `lean/Coercions/Classifiers/DotMNF/Examples.lean`). -/
def projStep? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ)
    (base : (C C' : CaptureSet s) → Option (Subcap Γ C C')) (L R : CaptureSet s) :
    Option (Subcap Γ L R) :=
  ((match unprojSetW? L with
    | some ⟨p, h⟩ =>
        if hR : p.1 = R then some (unprojBare h hR)
        else (base p.1 R).map (unprojTo h)
    | none => none : Option (Subcap Γ L R))).orElse fun _ =>
  ((match unprojSetW? R with
    | some ⟨p, h⟩ =>
        (D.kind? p.1 p.2).bind fun g =>
          if hL : L = p.1 then some (projBare h g hL)
          else (base L p.1).map (projTo h g)
    | none => none : Option (Subcap Γ L R))).orElse fun _ =>
  (match unprojSetW? L, unprojSetW? R with
    | some ⟨p, h1⟩, some ⟨q, h2⟩ =>
        if hk : p.2 = q.2 then (base p.1 q.1).map (projMonoTo h1 h2 hk) else none
    | _, _ => none)

/-- The subcapturing search.  `subcap? D 0 C₁ C₂` is `none`.
`subcap? D (n+1) C₁ C₂` tries nine rules in order and returns the first
success.  Every premise that is searched is searched at fuel `n`.

1. `C₁ ⊆ C₂`, `Subcap.elem`, decided.
2. The three projection rules of `projStep?` on the whole goal.
3. `C₁ = a :: C` with `C` not empty, `Subcap.union` of `[a]` and `C`.
   `[a] ∪ C` is `a :: C` by reduction.
4. `C₁ = {e}` and `κ ∈ C₂` a scope root at or inside the level of `e`,
   `Subcap.level`, both premises decided, then the inclusion of `{κ}` in
   `C₂`.
5. `κ ∈ C₂` an instance binder standing for `C`, a search of `C₁ <: C`, then
   `Subcap.inst`, then the inclusion of `{κ}` in `C₂`.
6. `C₁ = {x}`, `sc-var`, then a search from the set `x` is declared at.
7. `C₁ = {y.C}` at a capture member of the table, `sc-sel-upper`, then a
   search from its upper bound.
8. `C₁ = {a}` and `y.C ∈ C₂` at a capture member of the table, a search
   into its lower bound, then `sc-sel-lower`, then the inclusion of
   `{y.C}` in `C₂`.
9. `C₁ = {a}` and a projected atom `r ∈ C₂`, the projection rules of
   `projStep?` from `{a}` to `{r}`, then the inclusion of `{r}` in `C₂`.

Rules 2 and 9 read a set atom by atom where the other rules do: a set that
mixes projected and plain atoms is split by rule 3, and a right side that
mixes them is entered at one projected atom by rule 9.

The tenth alternative is not a rule of the calculus: it retries the whole
search at the previous fuel.  It changes no answer the nine rules give at
this fuel, and it is what makes `subcap?_le` an induction on the fuel
alone. -/
def subcap? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (C1 C2 : CaptureSet s) :
    Option (Subcap Γ C1 C2) :=
  match n with
  | 0 => none
  | n + 1 =>
      -- 1
      ((if h : CaptureSet.Subset C1 C2 then some (Subcap.elem h) else none :
          Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 2
      (projStep? D (fun L R => subcap? D n L R) C1 C2).orElse fun _ =>
      -- 3
      ((match C1 with
        | a :: b :: C => do
            let e1 ← subcap? D n [a] C2
            let e2 ← subcap? D n (b :: C) C2
            some (Subcap.union (C1 := [a]) (C2 := b :: C) e1 e2)
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 4
      ((match C1 with
        | [e] => firstSome (levelInto? e C2) C2
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 5
      (firstSome (fun b =>
        match b with
        | .cvar κ =>
            match h : Γ.instSet? κ with
            | some C =>
                if hm : CaptureSet.Subset [CapAtom.cvar κ] C2 then
                  (subcap? D n C1 C).map (fun e =>
                    Subcap.trans e (Subcap.trans (Subcap.inst h) (Subcap.elem hm)))
                else none
            | none => none
        | _ => none) C2).orElse fun _ =>
      -- 6
      ((match C1 with
        | [.var x] =>
            (subcap? D n (Γ.lookup x).captureSet C2).map (fun e => Subcap.trans Subcap.var e)
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 7
      (firstSome (fun d =>
        if h : C1 = [capSel d] then (subcap? D n d.hi C2).map (fun e => subcapFromSel h e)
        else none) D.caps).orElse fun _ =>
      -- 8
      ((match C1 with
        | [a] =>
            firstSome (fun d =>
              if h : CaptureSet.Subset [capSel d] C2 then
                (subcap? D n [a] d.lo).map (fun e => subcapToSel h e)
              else none) D.caps
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 9
      ((match C1 with
        | [a] =>
            firstSome (fun r =>
              match unprojSetW? [r] with
              | some _ =>
                  if h : CaptureSet.Subset [r] C2 then
                    (projStep? D (fun L R => subcap? D n L R) [a] [r]).map
                      (fun e => Subcap.trans e (Subcap.elem h))
                  else none
              | none => none) C2
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- the retry
      subcap? D n C1 C2
termination_by structural n

/-! ## Answers

`ESub` has three rules.  `ty` compares two plain answers by `Sub`.  `pack`
widens a plain answer `T'` to an existential `∃ᶜ[C₀] T`: the witness `C` is
below the bound `C₀`, and `T'` is below `T` under a scope whose instance
binder stands for `C`.  `exist` compares two existentials, the bounds
covariantly and the bodies under a scope.

The rules are written once, against four searches: plain answers at the
context, sets at the context, types under `Γ.scope`, and types under
`Γ.scopeInst C` for a witness `C`.  The arrow rule of the shape search and
the top level `esub?` both instantiate them. -/

/-- `ESub.pack` at one witness `C`. -/
def packAt {s : Sig} {Γ : Ctx s}
    (sc : (C C' : CaptureSet s) → Option (Subcap Γ C C'))
    (sbInst : (C : CaptureSet s) → (T U : Ty ((s,c),c)) → Option (Sub (Γ.scopeInst C) T U))
    (T' : Ty s) (C₀ : CaptureSet s) (T : Ty (s,c)) (C : CaptureSet s) :
    Option (ESub Γ (.ty T') (∃ᶜ[C₀] T)) := do
  let e1 ← sc C C₀
  let e2 ← sbInst C ((T'.weaken (k := .cap)).weaken (k := .cap)) (Dom.underRoot (s := s) T)
  some (ESub.pack e1 e2)

/-- The answer rules against four searches.

1. Two plain answers, `ESub.ty`.
2. A plain answer below an existential, `ESub.pack`, the witness tried
   first as the plain answer's own capture set and then as the bound.  The
   first candidate serves every answer `Ty.expandFresh` makes, whose witness
   binder sits in the top set only.  The second serves a written `∃` whose
   binder sits deeper, below a field or a box.
3. Two existentials, `ESub.exist`.

An existential is below no plain answer. -/
def esubWith {s : Sig} {Γ : Ctx s}
    (sb : (T U : Ty s) → Option (Sub Γ T U))
    (sc : (C C' : CaptureSet s) → Option (Subcap Γ C C'))
    (sbScope : (T U : Ty ((s,c),c)) → Option (Sub Γ.scope T U))
    (sbInst : (C : CaptureSet s) → (T U : Ty ((s,c),c)) → Option (Sub (Γ.scopeInst C) T U)) :
    (E E' : ETy s) → Option (ESub Γ E E')
  | .ty T, .ty T' => (sb T T').map ESub.ty
  | .ty T', .ex C₀ T =>
      (packAt sc sbInst T' C₀ T T'.captureSet).orElse fun _ => packAt sc sbInst T' C₀ T C₀
  | .ex C₀ T, .ex C₀' T' => do
      let e1 ← sc C₀ C₀'
      let e2 ← sbScope (Dom.underRoot (s := s) T) (Dom.underRoot (s := s) T')
      some (ESub.exist e1 e2)
  | .ex _ _, .ty _ => none

/-! ## The shape search -/

/-- The two rules of a member bounded by a kind.  `SubShape.capkI` takes a
member bounded by sets to one bounded by a kind, when the kinding search of
the table kinds the upper bound.  `SubShape.capk` widens a kind bound, when
`subkindB` confirms the subkinding.  Equal kinds are `SubShape.refl`, which
the shape search tries first, since `Kind.Subkind` is not known to be
reflexive. -/
def subShapeKind? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (S T : Shape s) :
    Option (SubShape Γ S T) :=
  match S, T with
  | .cap A c1 c2, .capk B φ =>
      if h : A = B then (D.kind? c2 φ).map fun g => (h ▸ SubShape.capkI (c1 := c1) g)
      else none
  | .capk A φ₁, .capk B φ₂ =>
      if h : A = B then
        if hs : φ₁.subkindB φ₂ = true then some (h ▸ SubShape.capk hs) else none
      else none
  | _, _ => none

/-- The shape search.  `subShape? D c 0 S T` is `none`.
`subShape? D c (n+1) S T` tries thirteen rules in order and returns the
first success.  Every shape premise is searched at fuel `n`, every set
premise by `subcap?` at fuel `c`, and every kinding premise by the kinding
search of the table.

1. `S = T`, `SubShape.refl`.
2. `T = ⊤`, `SubShape.top`.
3. `S = ⊥`, `SubShape.bot`.
4. `T = T1 ∧ T2`, `SubShape.and`.
5. `S = S1 ∧ S2`, `SubShape.trans` with `SubShape.and1` or `SubShape.and2`.
6. Two fields at one label, `SubShape.fld`, the types compared by `Sub.capt`.
7. Two type members at one label, `SubShape.typ`.
8. Two capture members at one label, `SubShape.cap`, by `subcap?`
   contravariant on the lower bounds and covariant on the upper.  Then
   the two rules of a member bounded by a kind, `subShapeKind?`.
9. Two boxes, `SubShape.box`.
10. Two functions, `SubShape.all`: the domains under `Γ.scope`, the
    codomains by the answer rules under `Γ.body T2`, each against a table
    rebuilt there.
11. `T = y.A` at a type member of the table, `SubShape.selLower`.
12. `S = y.A` at a type member of the table, `SubShape.selUpper`.
13. The one transitivity family, at a pair of type members of one variable
    at one label.

The fourteenth alternative is the retry at the previous fuel, as in
`subcap?`. -/
def subShape? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c : Nat) (n : Nat) (S T : Shape s) :
    Option (SubShape Γ S T) :=
  match n with
  | 0 => none
  | n + 1 =>
      -- 1
      ((if h : S = T then some (h ▸ SubShape.refl) else none : Option (SubShape Γ S T))).orElse
        fun _ =>
      -- 2
      ((if h : T = .top then some (h ▸ SubShape.top) else none : Option (SubShape Γ S T))).orElse
        fun _ =>
      -- 3
      ((if h : S = .bot then some (h ▸ SubShape.bot) else none : Option (SubShape Γ S T))).orElse
        fun _ =>
      -- 4
      ((match T with
        | .and T1 T2 => do
            let e1 ← subShape? D c n S T1
            let e2 ← subShape? D c n S T2
            some (SubShape.and e1 e2)
        | _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 5
      ((match S with
        | .and S1 S2 =>
            ((subShape? D c n S1 T).map (fun e => SubShape.trans SubShape.and1 e)).orElse fun _ =>
            ((subShape? D c n S2 T).map (fun e => SubShape.trans SubShape.and2 e))
        | _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 6
      ((match S, T with
        | .fld a T1, .fld b T2 =>
            if h : a = b then
              (subCapt (fun S S' => subShape? D c n S S') (fun C C' => subcap? D c C C') T1 T2).map
                (fun e => subFldOf h e)
            else none
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 7
      ((match S, T with
        | .typ A S1 T1, .typ B S2 T2 =>
            if h : A = B then do
              let e1 ← subShape? D c n S2 S1
              let e2 ← subShape? D c n T1 T2
              some (subTypOf h e1 e2)
            else none
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 8
      ((match S, T with
        | .cap A c1 c2, .cap B c1' c2' =>
            if h : A = B then do
              let e1 ← subcap? D c c1' c1
              let e2 ← subcap? D c c2 c2'
              some (subCapOf h e1 e2)
            else none
        | _, _ => none : Option (SubShape Γ S T)).orElse fun _ => subShapeKind? D S T).orElse fun _ =>
      -- 9
      ((match S, T with
        | .box T1, .box T2 =>
            (subCapt (fun S S' => subShape? D c n S S') (fun C C' => subcap? D c C C') T1 T2).map
              (fun e => SubShape.box e)
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 10
      ((match S, T with
        | .all T1 U1, .all T2 U2 => do
            let e1 ← subCapt (fun S S' => subShape? (baseDecls (scopeBudget D.kindFuel) Γ.scope) c n S S')
              (fun C C' => subcap? (baseDecls (scopeBudget D.kindFuel) Γ.scope) c C C')
              (Dom.underRoot (s := s) T2) (Dom.underRoot (s := s) T1)
            let e2 ← esubWith (Γ := Γ.body T2)
              (subCapt (fun S S' => subShape? (baseDecls (scopeBudget D.kindFuel) (Γ.body T2)) c n S S')
                (fun C C' => subcap? (baseDecls (scopeBudget D.kindFuel) (Γ.body T2)) c C C'))
              (fun C C' => subcap? (baseDecls (scopeBudget D.kindFuel) (Γ.body T2)) c C C')
              (subCapt (fun S S' => subShape? (baseDecls (scopeBudget D.kindFuel) (Γ.body T2).scope) c n S S')
                (fun C C' => subcap? (baseDecls (scopeBudget D.kindFuel) (Γ.body T2).scope) c C C'))
              (fun W => subCapt
                (fun S S' => subShape? (baseDecls (scopeBudget D.kindFuel) ((Γ.body T2).scopeInst W)) c n S S')
                (fun C C' => subcap? (baseDecls (scopeBudget D.kindFuel) ((Γ.body T2).scopeInst W)) c C C'))
              (Cod.underRoot (s := s) U1) (Cod.underRoot (s := s) U2)
            some (SubShape.all e1 e2)
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 11
      (firstSome (fun d =>
        if h : T = declSel d then (subShape? D c n S d.lo).map (fun e => subToSel h e)
        else none) D.typs).orElse fun _ =>
      -- 12
      (firstSome (fun d =>
        if h : S = declSel d then (subShape? D c n d.hi T).map (fun e => subFromSel h e)
        else none) D.typs).orElse fun _ =>
      -- 13
      (firstSome (fun (p : Decl Γ × Decl Γ) =>
        if h : declSel p.2 = declSel p.1 then do
          let e1 ← subShape? D c n S p.1.lo
          let e2 ← subShape? D c n p.2.hi T
          some (subThroughPair h e1 e2)
        else none) (declPairs D)).orElse fun _ =>
      -- the retry
      subShape? D c n S T
termination_by structural n

/-- The search on types: `Sub.capt` of the shape search at fuel `n` and the
set search at fuel `c`.  `Sub` has no other rule. -/
def sub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) (T U : Ty s) :
    Option (Sub Γ T U) :=
  subCapt (fun S S' => subShape? D c n S S') (fun C C' => subcap? D c C C') T U

/-- The search on answers: the answer rules over `sub?` at the context and
at the two kinds of scope, each scope against a detour free table rebuilt
there. -/
def esub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) (E E' : ETy s) :
    Option (ESub Γ E E') :=
  esubWith (sub? D c n) (subcap? D c)
    (sub? (baseDecls (scopeBudget D.kindFuel) Γ.scope) c n)
    (fun W => sub? (baseDecls (scopeBudget D.kindFuel) (Γ.scopeInst W)) c n) E E'

/-! ## The closure at the real search

Each name is the generic body above at `viewStep D c n`, the five view
steps with the detour step consulting `subShape? D c n`. -/

/-- The five view steps at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) : ViewStep Γ :=
  viewStepOf (fun S T => subShape? D c n S T) D

/-- One round of the view closure, the round `views` iterates `b.views`
times. -/
def viewsRound {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) {x : BVar s .var}
    (vs : List (View Γ x)) : List (View Γ x) :=
  viewsRoundOf (viewStep D c n) x vs

/-- The views of a variable at a budget.  `Γ` is implicit: it is determined
by the table, which is a table of `Γ`. -/
def views {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.cap b.sub) b.views x

/-- One round of the declaration table, the round `decls` iterates
`b.decls` times. -/
def declsRound {s : Sig} (b : Budget) (Γ : Ctx s) (D : DeclTable Γ) : DeclTable Γ :=
  declsRoundOf (fun D => viewStep D b.cap b.sub) b.views D

/-- The declaration table of a context at a budget. -/
def decls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStep D b.cap b.sub) b.kind b.views b.decls

/-! ## Round monotonicity

More rounds never lose a type, and never lose a member.  Both statements
are about keys, not about derivations: deduplication drops later
derivations of the same key, and a larger budget may find a different
derivation of the same judgment. -/

/-- Every key of `l` is a key of `l'`. -/
def KeyLe {α κ : Type} (key : α → κ) (l l' : List α) : Prop :=
  ∀ a ∈ l, ∃ b ∈ l', key b = key a

theorem keyLe_refl {α κ : Type} (key : α → κ) (l : List α) : KeyLe key l l :=
  fun a ha => ⟨a, ha, rfl⟩

theorem keyLe_trans {α κ : Type} {key : α → κ} {l l' l'' : List α}
    (h1 : KeyLe key l l') (h2 : KeyLe key l' l'') : KeyLe key l l'' := by
  intro a ha
  obtain ⟨b, hb, hbk⟩ := h1 a ha
  obtain ⟨c, hc, hck⟩ := h2 b hb
  exact ⟨c, hc, hck.trans hbk⟩

/-- A family that only grows from one count to the next grows from any
count to any larger one. -/
theorem keyLe_of_succ {α κ : Type} {key : α → κ} (f : Nat → List α)
    (hs : ∀ m, KeyLe key (f m) (f (m + 1))) {m m' : Nat} (h : m ≤ m') :
    KeyLe key (f m) (f m') := by
  induction h with
  | refl => exact keyLe_refl key _
  | step _ ih => exact keyLe_trans ih (hs _)

/-- A round of the closure only adds. -/
theorem viewsRoundOf_covers {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : KeyLe View.ty vs (viewsRoundOf st x vs) := by
  intro v hv
  exact dedupBy_covers View.ty _ v (List.mem_append_left _ hv)

theorem viewsOf_mono {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) {m m' : Nat}
    (h : m ≤ m') (x : BVar s .var) : KeyLe View.ty (viewsOf st m x) (viewsOf st m' x) :=
  keyLe_of_succ (fun m => viewsOf st m x) (fun _ => viewsRoundOf_covers st x _) h

/-- More rounds of the view closure never lose a type.  The two fuels of
the search are held fixed, since the detour step consults it. -/
theorem views_mono {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b b' : Budget}
    (h : b.views ≤ b'.views) (hs : b.sub = b'.sub) (hc : b.cap = b'.cap) (x : BVar s .var) :
    ∀ v ∈ views D b x, ∃ w ∈ views D b' x, w.ty = v.ty := by
  unfold views
  rw [hs, hc]
  exact viewsOf_mono (viewStep D b'.cap b'.sub) h x

/-- Every member of `D` has an entry of the same key in `D'`, for all three
kinds of member. -/
def TableLe {s : Sig} {Γ : Ctx s} (D D' : DeclTable Γ) : Prop :=
  KeyLe declKey D.typs D'.typs ∧ KeyLe capDeclKey D.caps D'.caps ∧
    KeyLe capkDeclKey D.capks D'.capks

/-- A round of the table only adds. -/
theorem declsRoundOf_covers {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ)
    (m : Nat) (D : DeclTable Γ) : TableLe D (declsRoundOf stf m D) :=
  ⟨fun d hd => dedupBy_covers declKey _ d (List.mem_append_left _ hd),
   fun d hd => dedupBy_covers capDeclKey _ d (List.mem_append_left _ hd),
   fun d hd => dedupBy_covers capkDeclKey _ d (List.mem_append_left _ hd)⟩

theorem declsOf_mono {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (kf m : Nat)
    {k k' : Nat} (h : k ≤ k') : TableLe (declsOf stf kf m k) (declsOf stf kf m k') :=
  ⟨keyLe_of_succ (fun k => (declsOf stf kf m k).typs)
      (fun k => (declsRoundOf_covers stf m (declsOf stf kf m k)).1) h,
   keyLe_of_succ (fun k => (declsOf stf kf m k).caps)
      (fun k => (declsRoundOf_covers stf m (declsOf stf kf m k)).2.1) h,
   keyLe_of_succ (fun k => (declsOf stf kf m k).capks)
      (fun k => (declsRoundOf_covers stf m (declsOf stf kf m k)).2.2) h⟩

/-- More rounds of the table never lose a member, of any of the three kinds.
The rounds of the closure and the three fuels of the search are held
fixed. -/
theorem decls_mono {s : Sig} {Γ : Ctx s} {b b' : Budget} (h : b.decls ≤ b'.decls)
    (hv : b.views = b'.views) (hs : b.sub = b'.sub) (hc : b.cap = b'.cap)
    (hk : b.kind = b'.kind) :
    (∀ d ∈ (decls b Γ).typs, ∃ d' ∈ (decls b' Γ).typs,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) ∧
    (∀ d ∈ (decls b Γ).caps, ∃ d' ∈ (decls b' Γ).caps,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) ∧
    (∀ d ∈ (decls b Γ).capks, ∃ d' ∈ (decls b' Γ).capks,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.kind = d.kind) := by
  unfold decls
  rw [hv, hs, hc, hk]
  obtain ⟨ht, hcs, hks⟩ := declsOf_mono (fun D => viewStep D b'.cap b'.sub) b'.kind b'.views h
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨d', hd', hk⟩ := ht d hd
    simp only [declKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩
  · obtain ⟨d', hd', hk⟩ := hcs d hd
    simp only [capDeclKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩
  · obtain ⟨d', hd', hk⟩ := hks d hd
    simp only [capkDeclKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩

/-! ## Fuel monotonicity

The last alternative of `subShape?` and of `subcap?` is the retry at the
previous fuel, so the statements are an induction on the fuel and not a
walk through the rules.  They are about `isSome` and not about derivations:
more fuel may find another derivation of the same judgment, and the
judgments are `Type` valued with no decidable equality.  `sub?` and `esub?`
are monotone in the shape fuel at a fixed set fuel, since their only
recursion is that of `subShape?`. -/

/-- One more unit of fuel never loses a subcapturing. -/
theorem subcap?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n : Nat} {C C' : CaptureSet s}
    (h : (subcap? D n C C').isSome) : (subcap? D (n + 1) C C').isSome := by
  rw [subcap?.eq_def]
  iterate 9 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a subcapturing. -/
theorem subcap?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n n' : Nat} (h : n ≤ n')
    {C C' : CaptureSet s} : (subcap? D n C C').isSome → (subcap? D n' C C').isSome :=
  isSome_of_le (fun n => subcap? D n C C') (fun _ => subcap?_succ) h

/-- One more unit of fuel never loses a shape subtyping. -/
theorem subShape?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {c n : Nat} {S T : Shape s}
    (h : (subShape? D c n S T).isSome) : (subShape? D c (n + 1) S T).isSome := by
  rw [subShape?.eq_def]
  iterate 13 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a shape subtyping. -/
theorem subShape?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {c n n' : Nat} (h : n ≤ n')
    {S T : Shape s} : (subShape? D c n S T).isSome → (subShape? D c n' S T).isSome :=
  isSome_of_le (fun n => subShape? D c n S T) (fun _ => subShape?_succ) h

/-- `Sub.capt` keeps every answer when its shape search does. -/
theorem subCapt_mono {s : Sig} {Γ : Ctx s}
    {sh sh' : (S S' : Shape s) → Option (SubShape Γ S S')}
    {sc : (C C' : CaptureSet s) → Option (Subcap Γ C C')}
    (hsh : ∀ S S', (sh S S').isSome = true → (sh' S S').isSome = true) (T U : Ty s) :
    (subCapt sh sc T U).isSome = true → (subCapt sh' sc T U).isSome = true := by
  cases T with
  | capt C S =>
  cases U with
  | capt C' S' =>
  intro hs
  cases h1 : sh S S' with
  | none => simp [subCapt, h1] at hs
  | some e1 =>
  cases h2 : sc C C' with
  | none => simp [subCapt, h1, h2] at hs
  | some e2 =>
  obtain ⟨f1, hf1⟩ := Option.isSome_iff_exists.mp (hsh S S' (by rw [h1]; rfl))
  simp [subCapt, hf1, h2]

/-- More fuel never loses a subtyping. -/
theorem sub?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {c n n' : Nat} (h : n ≤ n')
    {S T : Ty s} : (sub? D c n S T).isSome → (sub? D c n' S T).isSome :=
  subCapt_mono (fun _ _ => subShape?_le h) S T

/-- An `orElse` keeps an answer when both of its alternatives do. -/
theorem isSome_orElse_mono {α : Type} {a a' : Option α} {b b' : Unit → Option α}
    (ha : a.isSome = true → a'.isSome = true) (hb : (b ()).isSome = true → (b' ()).isSome = true) :
    (a.orElse b).isSome = true → (a'.orElse b').isSome = true := by
  cases a with
  | some x =>
      intro _
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (ha rfl)
      rw [hy]; rfl
  | none =>
      intro h
      have hb' : (b' ()).isSome = true := hb (by simpa [Option.orElse] using h)
      exact isSome_orElse_right hb'

/-- One pack keeps an answer when its residual search does. -/
theorem packAt_mono {s : Sig} {Γ : Ctx s}
    {sc : (C C' : CaptureSet s) → Option (Subcap Γ C C')}
    {si si' : (C : CaptureSet s) → (T U : Ty ((s,c),c)) → Option (Sub (Γ.scopeInst C) T U)}
    (hi : ∀ W T U, (si W T U).isSome = true → (si' W T U).isSome = true)
    (T' : Ty s) (C₀ : CaptureSet s) (T : Ty (s,c)) (W : CaptureSet s) :
    (packAt sc si T' C₀ T W).isSome = true → (packAt sc si' T' C₀ T W).isSome = true := by
  intro hs
  cases h1 : sc W C₀ with
  | none => simp [packAt, h1] at hs
  | some e1 =>
  cases h2 : si W ((T'.weaken (k := .cap)).weaken (k := .cap)) (Dom.underRoot (s := s) T) with
  | none => simp [packAt, h1, h2] at hs
  | some e2 =>
  obtain ⟨f2, hf2⟩ := Option.isSome_iff_exists.mp (hi _ _ _ (by rw [h2]; rfl))
  simp [packAt, h1, hf2]

/-- The answer rules keep every answer when their three type searches do.
The set search is shared. -/
theorem esubWith_mono {s : Sig} {Γ : Ctx s}
    {sb sb' : (T U : Ty s) → Option (Sub Γ T U)}
    {sc : (C C' : CaptureSet s) → Option (Subcap Γ C C')}
    {ss ss' : (T U : Ty ((s,c),c)) → Option (Sub Γ.scope T U)}
    {si si' : (C : CaptureSet s) → (T U : Ty ((s,c),c)) → Option (Sub (Γ.scopeInst C) T U)}
    (hb : ∀ T U, (sb T U).isSome = true → (sb' T U).isSome = true)
    (hs : ∀ T U, (ss T U).isSome = true → (ss' T U).isSome = true)
    (hi : ∀ W T U, (si W T U).isSome = true → (si' W T U).isSome = true) (E E' : ETy s) :
    (esubWith sb sc ss si E E').isSome = true → (esubWith sb' sc ss' si' E E').isSome = true := by
  cases E with
  | ty T =>
      cases E' with
      | ty T' =>
          intro h
          simp only [esubWith, Option.isSome_map] at h ⊢
          exact hb T T' h
      | ex C₀ T0 =>
          simp only [esubWith]
          exact isSome_orElse_mono (packAt_mono hi T C₀ T0 _) (packAt_mono hi T C₀ T0 _)
  | ex C₀ T =>
      cases E' with
      | ty T' => intro h; simp [esubWith] at h
      | ex C₀' T' =>
          intro h
          cases h1 : sc C₀ C₀' with
          | none => simp [esubWith, h1] at h
          | some e1 =>
          cases h2 : ss (Dom.underRoot (s := s) T) (Dom.underRoot (s := s) T') with
          | none => simp [esubWith, h1, h2] at h
          | some e2 =>
          obtain ⟨f2, hf2⟩ := Option.isSome_iff_exists.mp (hs _ _ (by rw [h2]; rfl))
          simp [esubWith, h1, hf2]

/-- More fuel never loses an answer inclusion. -/
theorem esub?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {c n n' : Nat} (h : n ≤ n')
    {E E' : ETy s} : (esub? D c n E E').isSome → (esub? D c n' E E').isSome :=
  esubWith_mono (fun T U => sub?_le h (S := T) (T := U))
    (fun T U => sub?_le h (S := T) (T := U))
    (fun _ T U => sub?_le h (S := T) (T := U)) E E'

/-! ## A rejection certificate

When the search does not put `C` below `D`, that is no proof that no
derivation exists.  The level rule is the one rule that relates a binder to
a root, and its failure has a semantic witness: the version's
`source_lvl_safety` (`lean/Coercions/Classifiers/DotToFCdot/EvidenceTyped.lean:1862`)
says that a member-free subcapturing keeps every resolved atom of `C`
confined to whatever atom `r` confines every resolved atom of `D`.  So one
depth `n` at which the resolution of `C` is not confined to `r`, while that
of `D` is at every depth, rules out every member-free derivation of
`C <: D`.  The statement is at any target set and any atom of the target,
so the escape at the top of a program, where `r` is the target's universal
root and no source root exists, is decided too. -/

/-- No member-free subcapturing puts `C` below `D` when `D` is confined to
`r` at every depth and `C` is not at one depth `n`. -/
theorem escape_rejected_at {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf)
    (r : Classifiers.FCdot.CapAtom s)
    (hD : ∀ m, Γ.translate.Confined (Γ.translate.caps m D.translate) r)
    (n : Nat) (hn : ¬ Γ.translate.Confined (Γ.translate.caps n C.translate) r) :
    ¬ ∃ d : Subcap Γ C D, d.MemberFree :=
  fun ⟨_, hd⟩ => hn (Classifiers.DotMNF.source_lvl_safety hwf hd hD n)

/-! ## Probes

Probes of `subcap?`, `sub?` and `esub?` at the version's examples
(`lean/Coercions/Classifiers/DotMNF/Examples.lean`).  Each names the
derivation it reproduces.  Every probe is a `decide +kernel`: the search is
structural, so the kernel runs it.

The budget of each probe is one at which the search finds the chain.  A
search may also find it at a smaller one, and the retry clauses make every
larger fuel of the same counter find it too (`subcap?_le`, `sub?_le`,
`esub?_le`). -/

section Probes

open Classifiers.DotMNF.Examples

/-! ### The level rule and the instance rule -/

/-- `W5_level_own` (`Examples.lean:2257`): inside the callback's body the
parameter is below the body root, by the level rule. -/
example : (subcap? DeclTable.empty 1 [CapAtom.var W5f] [CapAtom.cvar W5kb] (Γ := W5Ctx)).isSome
    = true := by
  decide +kernel

/-- And it is not below the root of the scope outside the call, at the
default budget.  The failure of the search is not the rejection.  The
rejection is `escape_rejected_at` at a reached goal. -/
example : (subcap? (decls {} W5Ctx) (({} : Budget).cap) [CapAtom.var W5f]
    [CapAtom.cvar W5kout]).isSome = false := by
  decide +kernel

/-- `W2_level` (`Examples.lean:2121`): the arrow binder below the body
root. -/
example : (subcap? DeclTable.empty 1 [CapAtom.cvar (.there .here)]
    [CapAtom.cvar (.there (.there .here))] (Γ := W2BodyCtx)).isSome = true := by
  decide +kernel

/-- `W2_level_param` (`Examples.lean:2126`): the parameter below the body
root. -/
example : (subcap? DeclTable.empty 1 [CapAtom.var .here]
    [CapAtom.cvar (.there (.there .here))] (Γ := W2BodyCtx)).isSome = true := by
  decide +kernel

/-- The level rule is directional: the body root is not below the arrow
binder, which is no root. -/
example : (subcap? (decls {} W2BodyCtx) (({} : Budget).cap)
    [CapAtom.cvar (.there (.there .here))] [CapAtom.cvar (.there .here)]).isSome = false := by
  decide +kernel

/-- At the top of a program there is no root, so the witness of an
unpacked `fresh` result is below nothing smaller: `{c} <: {}` is not found
at the default budget. -/
example : (subcap? (decls {} ((Z1Ctx.consC).cons (fileS ^ [CapAtom.cvar .here])))
    (({} : Budget).cap) [CapAtom.var .here] []).isSome = false := by
  decide +kernel

/-- The instance rule, the residual of `Z1Pack` (`Examples.lean:1858-1867`):
under a pack's scope the witness `{u}` is below the instance binder.  The
rule searches the witness below the set the binder stands for, so it takes
two units of fuel. -/
example : (subcap? DeclTable.empty 2
    (CaptureSet.weaken (CaptureSet.weaken [CapAtom.var .here]))
    [CapAtom.cvar .here] (Γ := (platCtx.body unitTy).scopeInst [CapAtom.var .here])).isSome
    = true := by
  decide +kernel

/-- An instance binder stands for its set and nothing larger. -/
example : (subcap? (decls {} ((platCtx.body unitTy).scopeInst [CapAtom.var .here]))
    (({} : Budget).cap) [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]
    [CapAtom.cvar .here]).isSome = false := by
  decide +kernel

/-! ### `sc-var` and the capture members -/

/-- The function of `Z1call` (`Examples.lean:1886`) is below the platform
binder it is declared at, by `sc-var`. -/
example : (subcap? DeclTable.empty 2 [CapAtom.var (.there .here)] [CapAtom.cvar fs2]
    (Γ := Z1Ctx)).isSome = true := by
  decide +kernel

/-- C2, `{g} <: {κ₁,κ₂}` in the client: `sc-var` takes `{g}` to `{x.C}`, and
`sc-sel-upper` at the abstract member of `x` takes it to `{κ₁,κ₂}`
(`C2call`, `Examples.lean:1031-1037`). -/
def probeC2 : Budget := { decls := 1, views := 2, sub := 0, cap := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) probeC2.cap [CapAtom.var .here]
    [CapAtom.cvar (.there (up (up k1))), CapAtom.cvar (.there (up (up k2)))]).isSome
    = true := by
  decide +kernel

/-- The same at one unit less fuel finds nothing. -/
example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) 2 [CapAtom.var .here]
    [CapAtom.cvar (.there (up (up k1))), CapAtom.cvar (.there (up (up k2)))]).isSome
    = false := by
  decide +kernel

/-- S1, `{fs} <: {cp.C}` at the caller: the lower bound of the precise
member of `cp` is `{fs}`, so `sc-sel-lower` puts `{fs}` below `{cp.C}`
(`S1op`, `Examples.lean:1405-1409`). -/
def probeS1 : Budget := { decls := 1, views := 1, sub := 0, cap := 2, typer := 0, obj := 0 }

example : (subcap? (decls probeS1 S1Ctx2) probeS1.cap [CapAtom.cvar fs2]
    [CapAtom.sel .here lC]).isSome = true := by
  decide +kernel

/-- C5, `{n} <: {fs}` at the caller of `mk`: `sc-var` takes `{n}` to
`{it.C}`, and `sc-sel-upper` at the abstract member of `it` takes it to
`{fs}` (`S2nVar`, `Examples.lean:1731-1737`). -/
def probeC5 : Budget := { decls := 1, views := 2, sub := 0, cap := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC5 S2Ctx4) probeC5.cap [CapAtom.var .here]
    [CapAtom.cvar fs4]).isSome = true := by
  decide +kernel

/-! ### Shapes -/

/-- E1, the transitivity family at one member: `{A : ⊤..⊥} <: {B : …}`
through `⊤ <: x.A <: ⊥`, the chain of `badBounds` (`Examples.lean:119-122`). -/
def probeE1 : Budget := { decls := 1, views := 0, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE1 E1Ctx) probeE1.cap probeE1.sub
    (E1Dom : Ty (Sig.body ([] : Sig))) E1Res).isSome = true := by
  decide +kernel

/-- The same at one unit less shape fuel finds nothing. -/
example : (sub? (decls probeE1 E1Ctx) probeE1.cap 1
    (E1Dom : Ty (Sig.body ([] : Sig))) E1Res).isSome = false := by
  decide +kernel

/-- E3, the transitivity family at two members of one variable at one label:
`{b : ⊤} <: x.A <: {a : ⊤}`, the chain of `E3sub` (`Examples.lean:232`). -/
def probeE3 : Budget := { decls := 1, views := 1, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE3 E3Ctx2) probeE3.cap probeE3.sub
    (E3T2 : Ty (Sig.body (Sig.body ([] : Sig)))) E3T1).isSome = true := by
  decide +kernel

/-- E4, the detour view step followed by `<:-Sel`: `w` reaches
`{A : Int..⊤}` through `S <: x.B <: T`, and then `Int <: w.A`, the chain of
`E4nA` (`Examples.lean:301-303`). -/
def probeE4 : Budget := { decls := 2, views := 1, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE4 E4Ctx4) probeE4.cap probeE4.sub
    (E4Int : Ty (Sig.body (Sig.body (Sig.body ([] : Sig))),x))
    ((Shape.sel (.var (.there (up .here))) lA) ^ [])).isSome = true := by
  decide +kernel

/-- E6, `<:-Sel` through the self binder's own member: `Int <: z.T` where `z`
is the literal's self binder, the chain of `E6nT` (`Examples.lean:435-437`). -/
def probeE6 : Budget := { decls := 1, views := 2, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE6 E6Ctxz) probeE6.cap probeE6.sub
    (E6Int : Ty (([],x,c),x)) ((Shape.sel (.var .here) lT) ^ [])).isSome = true := by
  decide +kernel

/-- E8, the right view step: `y : x.A ∧ {a : ⊤}` has a view at `{a : ⊤}`,
which is `E8yFld2` (`Examples.lean:511-512`). -/
def probeE8views : Budget := { decls := 0, views := 1, sub := 0, cap := 0, typer := 0, obj := 0 }

example : ((views (decls probeE8views E8Ctx2) probeE8views
    (.here : BVar (Sig.body (Sig.body ([] : Sig))) .var)).any
    (fun v => decide (v.ty = ((Shape.fld la (.top ^ [])) ^ [] :
      Ty (Sig.body (Sig.body ([] : Sig))))))) = true := by
  decide +kernel

/-- E8, `Sel-<:`: `x.A <: {a : ⊤}` by the upper bound of `x`'s member `A`,
which is `E8Upper` (`Examples.lean:519-520`). -/
def probeE8sub : Budget := { decls := 1, views := 0, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE8sub E8Ctx2) probeE8sub.cap probeE8sub.sub
    ((Shape.sel (.var (up .here)) lA) ^ [] : Ty (Sig.body (Sig.body ([] : Sig))))
    ((Shape.fld la (.top ^ [])) ^ [])).isSome = true := by
  decide +kernel

/-! ### The arrow rule and answers -/

/-- `Z1_widen` (`Examples.lean:2385-2386`): the arrow rule opens its two
scopes, and the codomains compare by `ESub.exist`, the bodies under a scope
of their own. -/
example : (sub? DeclTable.empty 1 2 (Z1Ty k1) (Z1TyTop k1) (Γ := platCtx)).isSome = true := by
  decide +kernel

/-- `Z1Pack` (`Examples.lean:1858-1867`): the body's plain answer packs into
the existential the result `fresh` reads as, the witness the answer's own
capture set and the residual by the instance rule. -/
example : (esub? DeclTable.empty 2 1 (Γ := platCtx.body unitTy)
    (.ty (fileS ^ [CapAtom.var .here]))
    (∃ᶜ[[CapAtom.cvar (up k1), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))).isSome
    = true := by
  decide +kernel

/-- A written `∃` whose binder sits below a field: the answer's own capture
set, here empty, is no witness, and the bound is.  The context is the body
of `process`, whose parameter `f` is declared at the arrow binder. -/
example : (esub? DeclTable.empty 2 2 (Γ := W2BodyCtx)
    (.ty ((Shape.fld la (.top ^ [CapAtom.var .here])) ^ []))
    (∃ᶜ[[CapAtom.var .here]] ((Shape.fld la (.top ^ [CapAtom.cvar .here])) ^ []))).isSome
    = true := by
  decide +kernel

/-- The same with the empty witness alone: no pack at that witness. -/
example : (packAt (Γ := W2BodyCtx) (subcap? DeclTable.empty 2)
    (fun W => sub? DeclTable.empty 2 2 (Γ := W2BodyCtx.scopeInst W))
    ((Shape.fld la (.top ^ [CapAtom.var .here])) ^ []) [CapAtom.var .here]
    ((Shape.fld la (.top ^ [CapAtom.cvar .here])) ^ []) []).isSome = false := by
  decide +kernel

/-- An existential is below no plain answer. -/
example : (esub? DeclTable.empty 3 3 (Γ := platCtx)
    (∃ᶜ[[CapAtom.cvar k1]] (Shape.top ^ [CapAtom.cvar .here])) (.ty (Shape.top ^ []))).isSome
    = false := by
  decide +kernel

/-! ### Projections and kinds

The probes below are at the classifier examples of the version.  A searched
subcapturing is a derivation, so beside its success it is checked by the
target checker on its translation, `capVerdict`, and its outermost rule is
read by `capRule`.  Where the table holds a member typing of the version,
the checker's verdict runs as `#eval expect`: the kernel does not unfold the
translation of that typing quickly.  The success itself stays a kernel
check. -/

/-- The target checker's verdict on a searched subcapturing. -/
def capVerdict {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (r : Option (Subcap Γ C D)) : Bool :=
  match r with
  | some f => Classifiers.FCdot.checkCap Γ.translate f.translate C.translate D.translate
  | none => false

/-- The outermost rule of a subcapturing. -/
def capRule {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (f : Subcap Γ C D) : String :=
  match f with
  | .refl => "refl"
  | .trans _ _ => "trans"
  | .elem _ => "elem"
  | .union _ _ => "union"
  | .var => "var"
  | .inst _ => "inst"
  | .level _ _ => "level"
  | .selLower _ => "selLower"
  | .selUpper _ => "selUpper"
  | .unproj => "unproj"
  | .proj _ => "proj"
  | .projMono _ => "projMono"

/-- `only[Control]`. -/
abbrev kCtl : Cls.Kind := Cls.only Cls.Control

/-- `except[ThreadLocal]`. -/
abbrev kNoTl : Cls.Kind := Cls.except Cls.ThreadLocal

/-- E1's filtered platform set under `b` and `f`, and its base. -/
abbrev E1FiltW : CaptureSet ([],c,c,x,x) := CaptureSet.weaken (CaptureSet.weaken E1Filt)

abbrev E1PlatW : CaptureSet ([],c,c,x,x) :=
  [CapAtom.cvar (.there (.there E1ctl)), CapAtom.cvar (.there (.there E1io))]

/-- `E1call` (`lean/Coercions/Classifiers/DotMNF/Examples.lean`): the
argument `b` is declared at the filtered set, and the call reads it at the
declared domain `{κ_ctl, κ_io}`.  The search takes the filtered set there by
a bare `unproj`, the version's own derivation. -/
example : (subcap? DeclTable.empty 1 E1FiltW E1PlatW (Γ := E1Ctx2)).map
    (fun f => decide (f.translate =
      (Subcap.unproj (Γ := E1Ctx2) (C := E1PlatW) (φ := kCtl)).translate)) = some true := by
  decide +kernel

/-- From `{b}` itself: `sc-var`, then the bare `unproj`. -/
example : capVerdict (subcap? DeclTable.empty 2 [CapAtom.var (.there .here)] E1PlatW
    (Γ := E1Ctx2)) = true := by
  decide +kernel

/-- `E2call`: the argument `{b}` is below `{b ↾ except[ThreadLocal]}` by a bare
`proj`, whose kinding the kinding search finds at fuel 5. -/
example : (subcap? (DeclTable.emptyAt 5) 1 [CapAtom.var (.there .here)]
    (CaptureSet.proj [CapAtom.var (.there .here)] kNoTl) (Γ := E2CtxF)).map capRule
    = some "proj" := by
  decide +kernel

example : capVerdict (subcap? (DeclTable.emptyAt 5) 1 [CapAtom.var (.there .here)]
    (CaptureSet.proj [CapAtom.var (.there .here)] kNoTl) (Γ := E2CtxF)) = true := by
  decide +kernel

/-- The kinding fuel is what the rule needs: at fuel 4 no kinding is found,
and the goal is not reached at any subcapturing fuel up to 10. -/
example : (List.range 11).all (fun n => (subcap? (DeclTable.emptyAt 4) n
    [CapAtom.var (.there .here)] (CaptureSet.proj [CapAtom.var (.there .here)] kNoTl)
    (Γ := E2CtxF)).isNone) = true := by
  decide +kernel

/-- An argument charged to the thread-local capability is not put below the
filtered domain at any fuel up to 10: its set is not kinded at
`except[ThreadLocal]`, which the version proves of every derivation. -/
example : (List.range 11).all (fun n => (subcap? (DeclTable.emptyAt 10) n
    [CapAtom.var .here] (CaptureSet.proj [CapAtom.var .here] kNoTl)
    (Γ := E2PlatIOCtx.cons (arrowS ^ [CapAtom.cvar E2tl]))).isNone) = true := by
  decide +kernel

/-- A mixed set on the left: `{b ↾ only[Control], f}` is below the
filtered platform set.  The union splits it, the projected atom goes by
`unproj` then `sc-var`, and `f` by `sc-var` to its empty set. -/
abbrev mixedLeft : CaptureSet ([],c,c,x,x) :=
  [CapAtom.proj (CapAtom.var (.there .here)) kCtl, CapAtom.var .here]

example : capVerdict (subcap? DeclTable.empty 4 mixedLeft E1FiltW (Γ := E1Ctx2)) = true := by
  decide +kernel

/-- One unit of fuel short. -/
example : (subcap? DeclTable.empty 3 mixedLeft E1FiltW (Γ := E1Ctx2)).isNone = true := by
  decide +kernel

/-- A mixed set on the right: `{y} <: {κ_ctl, y ↾ except[ThreadLocal]}`,
the domain a call reads after the argument is substituted.  The search
enters the projected atom by a bare `proj`, then `elem`. -/
abbrev mixedRight : CaptureSet ([],c,c,c,x) :=
  [CapAtom.cvar (.there E2ctl), CapAtom.proj (CapAtom.var .here) kNoTl]

example : capVerdict (subcap? (DeclTable.emptyAt 3) 1 [CapAtom.var .here] mixedRight
    (Γ := E2IoCtx)) = true := by
  decide +kernel

/-- The filtered route from a least use set: `{κ_ctl}` is below
`{κ_ctl, κ_io} ↾ only[Control]`.  The whole base is not kinded at
`only[Control]`, so the search enters the projected atom `κ_ctl ↾ only[Control]`
by a bare `proj` over `kcls`, then `elem`. -/
example : capVerdict (subcap? (DeclTable.emptyAt 1) 1 [CapAtom.cvar E1ctl] E1Filt
    (Γ := E1PlatCtx)) = true := by
  decide +kernel

/-- The same at a larger kinding fuel and the default subcapturing fuel. -/
example : capVerdict (subcap? (DeclTable.emptyAt 6) 6 [CapAtom.cvar E1ctl] E1Filt
    (Γ := E1PlatCtx)) = true := by
  decide +kernel

/-- `projMono`: a subcapturing of the bases, projected at one kind. -/
example : (subcap? DeclTable.empty 2 (CaptureSet.proj [CapAtom.cvar E1ctl] kCtl) E1Filt
    (Γ := E1PlatCtx)).map capRule = some "elem" := by
  decide +kernel

example : (subcap? DeclTable.empty 3 (CaptureSet.proj [CapAtom.var .here] kNoTl)
    (CaptureSet.proj [CapAtom.cvar (.there E2io)] kNoTl) (Γ := E2IoCtx)).map capRule
    = some "projMono" := by
  decide +kernel

/-! ### Kinds read off the table

The table records the members bounded by kinds that the views display, and
the kinding search reads its typings there. -/

/-- The budget of the client probes: two rounds of views open `x` and split
its intersection. -/
def probeClient : Budget := { decls := 1, views := 2, sub := 0, cap := 1, typer := 0, obj := 0, kind := 5 }

/-- The table of E3's client holds the member of `x` bounded by
`only[Control]`. -/
example : ((decls probeClient E3ClientCtx).capks.map (fun d => (d.lbl, d.kind))) = [(lC, kCtl)] := by
  decide +kernel

/-- The closure `g`, declared at `{x.C}`, is below
`{g ↾ only[Control]}`, the set a domain written `{any.only[Control]}`
reads at a call.  A bare `proj`, the kinding by `kvar` over `kprojS` over
`ksel` at the table's typing of `x`. -/
example : (subcap? (decls probeClient E3ClientCtx) 1 [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] kCtl)).map capRule = some "proj" := by
  decide +kernel

#eval expect (capVerdict (subcap? (decls probeClient E3ClientCtx) 1 [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] kCtl)))
  "g: the target checker rejects the searched subcapturing"

/-- Over E3's platform, C2's client has `x` with a member bounded by the
sets `{}..{κ₁,κ₂}`.  `{x.C}` is below its projection at `only[Control]`, the
kinding by `kle` along `Subcap.selUpper` at the table's typing of `x`. -/
abbrev C2OnE3Ctx : Ctx (Sig.body (Sig.body ([],c,c)),x) := C2CtxG E3PlatCtx E3k1 E3k2

def probeR2 : Budget := { decls := 1, views := 2, sub := 0, cap := 1, typer := 0, obj := 0, kind := 4 }

example : (subcap? (decls probeR2 C2OnE3Ctx) 1 [CapAtom.sel (.there (up .here)) lC]
    (CaptureSet.proj [CapAtom.sel (.there (up .here)) lC] kCtl)).map capRule = some "proj" := by
  decide +kernel

#eval expect (capVerdict (subcap? (decls probeR2 C2OnE3Ctx) 1 [CapAtom.sel (.there (up .here)) lC]
    (CaptureSet.proj [CapAtom.sel (.there (up .here)) lC] kCtl)))
  "x.C: the target checker rejects the searched subcapturing"

/-- A test of the table, not a refusal of the version: with no table the
member typing is not known and no kinding is found. -/
example : (subcap? (DeclTable.emptyAt 10) 10 [CapAtom.sel (.there (up .here)) lC]
    (CaptureSet.proj [CapAtom.sel (.there (up .here)) lC] kCtl) (Γ := C2OnE3Ctx)).isNone = true := by
  decide +kernel

/-! ### The two kind rules of subtyping -/

/-- E3's literal reaches the kind bound: `{C : {κ₁}..{κ₁}} <: {C : only[Control]}`
by `capkI` over `kcls`, the step the version writes in `E3abstract`. -/
example : (subShape? (DeclTable.emptyAt 1) 0 1
    (Shape.cap lC [CapAtom.cvar E3k1] [CapAtom.cvar E3k1]) (Shape.capk lC kCtl)
    (Γ := E3PlatCtx)).isSome = true := by
  decide +kernel

/-- A kind bound widens to a kind `subkindB` confirms. -/
example : (subShape? DeclTable.empty 0 1 (Shape.capk lC kCtl)
    (Shape.capk lC (kCtl ∪ Cls.only Cls.IO)) (Γ := E3PlatCtx)).isSome = true := by
  decide +kernel

/-- And not the other way. -/
example : (subShape? DeclTable.empty 0 1 (Shape.capk lC (kCtl ∪ Cls.only Cls.IO))
    (Shape.capk lC kCtl) (Γ := E3PlatCtx)).isNone = true := by
  decide +kernel

/-- A member bounded by a set that holds an `IO` capability does not reach
`only[Control]`. -/
example : (subShape? (DeclTable.emptyAt 10) 0 10
    (Shape.cap lC [] [CapAtom.cvar E1io]) (Shape.capk lC kCtl) (Γ := E1PlatCtx)).isNone = true := by
  decide +kernel

end Probes

end ClassifiersFrontend
