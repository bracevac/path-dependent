import Coercions.Captures.Frontend.Decide
import Coercions.Captures.Frontend.Surface
import Coercions.Captures.DotMNF.Examples

/-!
# Views, the declaration table, and the subtyping and subcapturing search

The typer needs two things this module provides.  A *view* of a context
variable is a type the variable has, carried with its use set and its
derivation, so the typer may read a field or a member off a variable whose
declared type does not display it.  A *declaration* is a type member or a
capture member a context variable has, again with its derivation.  The
*declaration table* of a context is the family of middles the search may
try for `SubShape.trans` and `Subcap.trans`, whose middles are otherwise
undetermined (`lean/Coercions/Captures/DotMNF/Typing.lean:96,125`).

Everything here returns the derivation, so there is no soundness theorem.
The result type is the statement.  Nothing here is complete, and no
completeness theorem is claimed.

## The two layers

A type of the version is a shape with a capture set, `S ^ C`, and `Sub` has
the one rule `capt`, a `SubShape` on the shapes beside a `Subcap` on the
sets (`Typing.lean:156-158`).  So the search is two functions, `subShape?`
and `subcap?`, in one block, and `sub?` pairs them.  A shape rule that
compares types (a field, a box, the domain and codomain of a function)
pairs the two at the same fuel inline, so a type layer costs no fuel of its
own.

## What is fuel bounded, and why

Five counters live in `Budget`.  `decls` counts rounds of the table,
`views` counts rounds of the view closure, `sub` is the fuel of the search,
`typer` is the fuel of the typer, and `obj` bounds the passes of the object
rule.  An unbounded closure grows too fast to compute, so duplicates are
dropped after every round, the table is computed once per context and
passed as a parameter, and the closure and the table have small round
counters of their own, separate from the fuel of the search.

## The order of definition

The view closure calls the search in its detour step, and the `∀` rule of
the search builds a table under an extended context.  Taken literally that
is a cycle.  It is cut by making the table a parameter of the search and by
writing the view steps once, in `viewStepOf`, against an abstract search.
The table the `∀` rule builds is computed with `noSub`, the search that
finds nothing, so the block of the search mentions no search but its own.

## The kernel

Every function here is structural, on a fuel or on a list, so the kernel
reduces the search, and the probes at the end are `decide +kernel`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open scoped Captures.DotMNF

/-! ## Views and declarations -/

/-- A type a context variable has, at a use set, with the derivation. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ty

/-- A pure binder at its declared type, at the empty use set.  `Var`
concludes at `{x}` for both sets, and `sc-var` takes both down to the
declared set, which is empty (`Typing.lean:104-105,163-164`). -/
def pureVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (h : (Γ.lookup x).captureSet = []) :
    HasTy [] Γ (.path (.var x)) (Γ.lookup x) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  have e : HasTy [] Γ (.path (.var x)) ((Γ.lookup x).shape ^ []) :=
    HasTy.sub HasTy.var (.capt .refl hv) hv
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
  deriv : HasTy uses Γ (.path (.var vr)) ((Shape.typ lbl lo hi) ^ cs)

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
  deriv : HasTy uses Γ (.path (.var vr)) ((Shape.cap lbl lo hi) ^ cs)

/-- The declaration table of a context: its type members and its capture
members. -/
structure DeclTable {s : Sig} (Γ : Ctx s) where
  /-- The type members. -/
  typs : List (Decl Γ)
  /-- The capture members. -/
  caps : List (CapDecl Γ)

/-- The empty table. -/
def DeclTable.empty {s : Sig} {Γ : Ctx s} : DeclTable Γ := ⟨[], []⟩

/-- Two tables side by side. -/
def DeclTable.append {s : Sig} {Γ : Ctx s} (D E : DeclTable Γ) : DeclTable Γ :=
  ⟨D.typs ++ E.typs, D.caps ++ E.caps⟩

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

/-- The five counters.  The defaults are a starting point, not a
measurement.  The probes below give the budget at which each was found. -/
structure Budget where
  /-- Rounds of the declaration table. -/
  decls : Nat := 3
  /-- Rounds of the view closure. -/
  views : Nat := 3
  /-- Fuel of the search. -/
  sub : Nat := 6
  /-- Fuel of the typer. -/
  typer : Nat := 8
  /-- Passes of the object rule. -/
  obj : Nat := 3
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

/-- The search that finds nothing.  It is what the `∀` rule passes when it
builds a table under an extended context, where calling the real search
would be circular. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-- A shape subtyping lifted to the type it starts from, the capture set
kept. -/
def subOfShape {s : Sig} {Γ : Ctx s} : (T : Ty s) → {S : Shape s} →
    SubShape Γ T.shape S → Sub Γ T (S ^ T.captureSet)
  | .capt _ _, _, e => .capt e .refl

/-- The five view steps, against an abstract search.

| step | condition on `v.ty` | new view | rule |
|---|---|---|---|
| open | `(μ S) ^ C` and `Shape.Decl S` | `S.substVar x ^ C` | `HasTy.recE` (`Typing.lean:210-213`) |
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
          [⟨v.uses, S ^ C, .sub (hv ▸ v.deriv) (.capt .and1 .refl) .refl⟩,
           ⟨v.uses, T ^ C, .sub (hv ▸ v.deriv) (.capt .and2 .refl) .refl⟩]
      | _ => [])
    ++ D.typs.filterMap (fun d =>
        if h : v.ty.shape = declSel d then
          some ⟨v.uses, d.hi ^ v.ty.captureSet,
            .sub v.deriv (subOfShape v.ty (h ▸ declUpper d)) .refl⟩
        else none)
    ++ D.typs.filterMap (fun d =>
        (sub v.ty.shape d.lo).map (fun e =>
          ⟨v.uses, d.hi ^ v.ty.captureSet,
            .sub v.deriv
              (subOfShape v.ty (SubShape.trans e (SubShape.trans (declLower d) (declUpper d))))
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
as type members, its `cap` views as capture members. -/
def tableOfViews {s : Sig} {Γ : Ctx s} {y : BVar s .var} (vs : List (View Γ y)) :
    DeclTable Γ :=
  match vs with
  | [] => .empty
  | v :: vs =>
      DeclTable.append
        (match hv : v.ty with
          | .capt C (.typ A L U) => ⟨[⟨y, A, L, U, v.uses, C, hv ▸ v.deriv⟩], []⟩
          | .capt C (.cap A c1 c2) => ⟨[], [⟨y, A, c1, c2, v.uses, C, hv ▸ v.deriv⟩]⟩
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
deduplicated by key. -/
def declsRoundOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    (D : DeclTable Γ) : DeclTable Γ :=
  let N := tableOfVars (stf D) m (ctxVars Γ)
  ⟨dedupBy declKey (D.typs ++ N.typs), dedupBy capDeclKey (D.caps ++ N.caps)⟩

/-- The table after `k` rounds, each round running `m` rounds of the
closure. -/
def declsOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat) (k : Nat) :
    DeclTable Γ :=
  match k with
  | 0 => .empty
  | k + 1 => declsRoundOf stf m (declsOf stf m k)
termination_by structural k

/-- The detour free table, the one the `∀` rule of the search builds under
the context it extends.  Building the full table there would make the
search mutual with the view closure. -/
def baseDecls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStepOf noSub D) b.views b.decls

/-! ## The search

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
what E3 needs (`lean/Coercions/Captures/DotMNF/Examples.lean:216`). -/
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

/-- The rounds the `∀` rule gives the detour free table it builds under the
context it extends.  Small on purpose: the table is rebuilt at every
application of the rule. -/
def allBudget : Budget := { decls := 1, views := 2, sub := 0, typer := 0, obj := 0 }

mutual

/-- The shape search.  `subShape? D 0 S T` is `none`.  `subShape? D (n+1) S T`
tries thirteen rules in order and returns the first success.  Every premise
is searched at fuel `n`.

1. `S = T`, `SubShape.refl`.
2. `T = ⊤`, `SubShape.top`.
3. `S = ⊥`, `SubShape.bot`.
4. `T = T1 ∧ T2`, `SubShape.and`.
5. `S = S1 ∧ S2`, `SubShape.trans` with `SubShape.and1` or `SubShape.and2`.
6. Two fields at one label, `SubShape.fld`, the types compared by `Sub.capt`.
7. Two type members at one label, `SubShape.typ`.
8. Two capture members at one label, `SubShape.cap`, by `subcap?`
   contravariant on the lower bounds and covariant on the upper.
9. Two boxes, `SubShape.box`.
10. Two functions, `SubShape.all`, with the codomains compared under
    `Γ.cons T2` against a table rebuilt there.
11. `T = y.A` at a type member of the table, `SubShape.selLower`.
12. `S = y.A` at a type member of the table, `SubShape.selUpper`.
13. The one transitivity family, at a pair of type members of one variable
    at one label.

The fourteenth alternative is not a rule of the calculus: it retries the
whole search at the previous fuel.  It changes no answer the thirteen rules
give at this fuel, and it is what makes `subShape?_le` an induction on the
fuel alone. -/
def subShape? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (S T : Shape s) :
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
            let e1 ← subShape? D n S T1
            let e2 ← subShape? D n S T2
            some (SubShape.and e1 e2)
        | _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 5
      ((match S with
        | .and S1 S2 =>
            ((subShape? D n S1 T).map (fun e => SubShape.trans SubShape.and1 e)).orElse fun _ =>
            ((subShape? D n S2 T).map (fun e => SubShape.trans SubShape.and2 e))
        | _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 6
      ((match S, T with
        | .fld a T1, .fld b T2 =>
            if h : a = b then
              (subCapt (fun S S' => subShape? D n S S') (fun C C' => subcap? D n C C') T1 T2).map
                (fun e => subFldOf h e)
            else none
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 7
      ((match S, T with
        | .typ A S1 T1, .typ B S2 T2 =>
            if h : A = B then do
              let e1 ← subShape? D n S2 S1
              let e2 ← subShape? D n T1 T2
              some (subTypOf h e1 e2)
            else none
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 8
      ((match S, T with
        | .cap A c1 c2, .cap B c1' c2' =>
            if h : A = B then do
              let e1 ← subcap? D n c1' c1
              let e2 ← subcap? D n c2 c2'
              some (subCapOf h e1 e2)
            else none
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 9
      ((match S, T with
        | .box T1, .box T2 =>
            (subCapt (fun S S' => subShape? D n S S') (fun C C' => subcap? D n C C') T1 T2).map
              (fun e => SubShape.box e)
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 10
      ((match S, T with
        | .all T1 U1, .all T2 U2 => do
            let e1 ← subCapt (fun S S' => subShape? D n S S') (fun C C' => subcap? D n C C') T2 T1
            let e2 ← subCapt (fun S S' => subShape? (baseDecls allBudget (Γ.cons T2)) n S S')
              (fun C C' => subcap? (baseDecls allBudget (Γ.cons T2)) n C C') U1 U2
            some (SubShape.all e1 e2)
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 11
      (firstSome (fun d =>
        if h : T = declSel d then (subShape? D n S d.lo).map (fun e => subToSel h e)
        else none) D.typs).orElse fun _ =>
      -- 12
      (firstSome (fun d =>
        if h : S = declSel d then (subShape? D n d.hi T).map (fun e => subFromSel h e)
        else none) D.typs).orElse fun _ =>
      -- 13
      (firstSome (fun (p : Decl Γ × Decl Γ) =>
        if h : declSel p.2 = declSel p.1 then do
          let e1 ← subShape? D n S p.1.lo
          let e2 ← subShape? D n p.2.hi T
          some (subThroughPair h e1 e2)
        else none) (declPairs D)).orElse fun _ =>
      -- the retry
      subShape? D n S T
termination_by structural n

/-- The subcapturing search.  `subcap? D 0 C₁ C₂` is `none`.
`subcap? D (n+1) C₁ C₂` tries five rules in order and returns the first
success.  Every premise is searched at fuel `n`.

1. `C₁ ⊆ C₂`, `Subcap.elem`, decided.
2. `C₁ = a :: C` with `C` not empty, `Subcap.union` of `[a]` and `C`.
   `[a] ∪ C` is `a :: C` by reduction.
3. `C₁ = {x}`, `sc-var`, then a search from the set `x` is declared at.
4. `C₁ = {y.C}` at a capture member of the table, `sc-sel-upper`, then a
   search from its upper bound.
5. `C₁ = {a}` and `y.C ∈ C₂` at a capture member of the table, a search
   into its lower bound, then `sc-sel-lower`, then the inclusion of
   `{y.C}` in `C₂`.

The sixth alternative is the retry at the previous fuel, as in
`subShape?`. -/
def subcap? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (C1 C2 : CaptureSet s) :
    Option (Subcap Γ C1 C2) :=
  match n with
  | 0 => none
  | n + 1 =>
      -- 1
      ((if h : CaptureSet.Subset C1 C2 then some (Subcap.elem h) else none :
          Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 2
      ((match C1 with
        | a :: b :: C => do
            let e1 ← subcap? D n [a] C2
            let e2 ← subcap? D n (b :: C) C2
            some (Subcap.union (C1 := [a]) (C2 := b :: C) e1 e2)
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 3
      ((match C1 with
        | [.var x] =>
            (subcap? D n (Γ.lookup x).captureSet C2).map (fun e => Subcap.trans Subcap.var e)
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 4
      (firstSome (fun d =>
        if h : C1 = [capSel d] then (subcap? D n d.hi C2).map (fun e => subcapFromSel h e)
        else none) D.caps).orElse fun _ =>
      -- 5
      ((match C1 with
        | [a] =>
            firstSome (fun d =>
              if h : CaptureSet.Subset [capSel d] C2 then
                (subcap? D n [a] d.lo).map (fun e => subcapToSel h e)
              else none) D.caps
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- the retry
      subcap? D n C1 C2
termination_by structural n

end

/-- The search on types: `Sub.capt` of the shape search and the set search
at the same fuel.  `Sub` has no other rule. -/
def sub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (T U : Ty s) : Option (Sub Γ T U) :=
  subCapt (fun S S' => subShape? D n S S') (fun C C' => subcap? D n C C') T U

/-! ## The closure at the real search

Each name is the generic body above at `viewStep D n`, the five view steps
with the detour step consulting `subShape? D n`. -/

/-- The five view steps at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) : ViewStep Γ :=
  viewStepOf (fun S T => subShape? D n S T) D

/-- One round of the view closure, the round `views` iterates `b.views`
times. -/
def viewsRound {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) {x : BVar s .var}
    (vs : List (View Γ x)) : List (View Γ x) :=
  viewsRoundOf (viewStep D n) x vs

/-- The views of a variable at a budget.  `Γ` is implicit: it is determined
by the table, which is a table of `Γ`. -/
def views {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.sub) b.views x

/-- One round of the declaration table, the round `decls` iterates
`b.decls` times. -/
def declsRound {s : Sig} (b : Budget) (Γ : Ctx s) (D : DeclTable Γ) : DeclTable Γ :=
  declsRoundOf (fun D => viewStep D b.sub) b.views D

/-- The declaration table of a context at a budget. -/
def decls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStep D b.sub) b.views b.decls

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

/-- More rounds of the view closure never lose a type. -/
theorem views_mono {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b b' : Budget}
    (h : b.views ≤ b'.views) (hs : b.sub = b'.sub) (x : BVar s .var) :
    ∀ v ∈ views D b x, ∃ w ∈ views D b' x, w.ty = v.ty := by
  unfold views
  rw [hs]
  exact viewsOf_mono (viewStep D b'.sub) h x

/-- Every member of `D` has an entry of the same key in `D'`, for both
kinds of member. -/
def TableLe {s : Sig} {Γ : Ctx s} (D D' : DeclTable Γ) : Prop :=
  KeyLe declKey D.typs D'.typs ∧ KeyLe capDeclKey D.caps D'.caps

/-- A round of the table only adds. -/
theorem declsRoundOf_covers {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ)
    (m : Nat) (D : DeclTable Γ) : TableLe D (declsRoundOf stf m D) :=
  ⟨fun d hd => dedupBy_covers declKey _ d (List.mem_append_left _ hd),
   fun d hd => dedupBy_covers capDeclKey _ d (List.mem_append_left _ hd)⟩

theorem declsOf_mono {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    {k k' : Nat} (h : k ≤ k') : TableLe (declsOf stf m k) (declsOf stf m k') :=
  ⟨keyLe_of_succ (fun k => (declsOf stf m k).typs)
      (fun k => (declsRoundOf_covers stf m (declsOf stf m k)).1) h,
   keyLe_of_succ (fun k => (declsOf stf m k).caps)
      (fun k => (declsRoundOf_covers stf m (declsOf stf m k)).2) h⟩

/-- More rounds of the table never lose a member, of either kind. -/
theorem decls_mono {s : Sig} {Γ : Ctx s} {b b' : Budget} (h : b.decls ≤ b'.decls)
    (hv : b.views = b'.views) (hs : b.sub = b'.sub) :
    (∀ d ∈ (decls b Γ).typs, ∃ d' ∈ (decls b' Γ).typs,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) ∧
    (∀ d ∈ (decls b Γ).caps, ∃ d' ∈ (decls b' Γ).caps,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) := by
  unfold decls
  rw [hv, hs]
  obtain ⟨ht, hc⟩ := declsOf_mono (fun D => viewStep D b'.sub) b'.views h
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨d', hd', hk⟩ := ht d hd
    simp only [declKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩
  · obtain ⟨d', hd', hk⟩ := hc d hd
    simp only [capDeclKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩

/-! ## Fuel monotonicity

The last alternative of `subShape?` and of `subcap?` is the retry at the
previous fuel, so the statements are an induction on the fuel and not a
walk through the rules.  They are about `isSome` and not about derivations:
more fuel may find another derivation of the same judgment, and the
judgments are `Type` valued with no decidable equality. -/

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

/-- One more unit of fuel never loses a shape subtyping. -/
theorem subShape?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n : Nat} {S T : Shape s}
    (h : (subShape? D n S T).isSome) : (subShape? D (n + 1) S T).isSome := by
  rw [subShape?.eq_def]
  iterate 13 refine isSome_orElse_right ?_
  exact h

/-- One more unit of fuel never loses a subcapturing. -/
theorem subcap?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n : Nat} {C C' : CaptureSet s}
    (h : (subcap? D n C C').isSome) : (subcap? D (n + 1) C C').isSome := by
  rw [subcap?.eq_def]
  iterate 5 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a shape subtyping. -/
theorem subShape?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n n' : Nat} (h : n ≤ n')
    {S T : Shape s} : (subShape? D n S T).isSome → (subShape? D n' S T).isSome :=
  isSome_of_le (fun n => subShape? D n S T) (fun _ => subShape?_succ) h

/-- More fuel never loses a subcapturing. -/
theorem subcap?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n n' : Nat} (h : n ≤ n')
    {C C' : CaptureSet s} : (subcap? D n C C').isSome → (subcap? D n' C C').isSome :=
  isSome_of_le (fun n => subcap? D n C C') (fun _ => subcap?_succ) h

/-- More fuel never loses a subtyping. -/
theorem sub?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n n' : Nat} (h : n ≤ n')
    {S T : Ty s} : (sub? D n S T).isSome → (sub? D n' S T).isSome := by
  cases S with
  | capt C S =>
  cases T with
  | capt C' S' =>
  intro hs
  cases h1 : subShape? D n S S' with
  | none => simp [sub?, subCapt, h1] at hs
  | some e1 =>
  cases h2 : subcap? D n C C' with
  | none => simp [sub?, subCapt, h1, h2] at hs
  | some e2 =>
  obtain ⟨f1, hf1⟩ := Option.isSome_iff_exists.mp
    (subShape?_le h (D := D) (S := S) (T := S') (by rw [h1]; rfl))
  obtain ⟨f2, hf2⟩ := Option.isSome_iff_exists.mp
    (subcap?_le h (D := D) (C := C) (C' := C') (by rw [h2]; rfl))
  simp [sub?, subCapt, hf1, hf2]

/-! ## Probes

Three probes of `subcap?` at the capture examples, and six probes at the
examples E1 to E8, whose capture sets are all empty.  Each names the chain of
`lean/Coercions/Captures/DotMNF/Examples.lean` it reproduces.  Every probe
is a `decide +kernel`: the search is structural, so the kernel runs it.

The budget of each probe is one at which the search finds the chain.  A
search may also find it at a smaller one, and the retry clauses make every
larger fuel find it too (`subcap?_le`, `sub?_le`).  The default `Budget`
finds all nine as well. -/

section Probes

open Captures.DotMNF.Examples

/-- C2, `{g} <: {κ₁,κ₂}` in the client: `sc-var` takes `{g}` to `{x.C}`, and
`sc-sel-upper` at the abstract member of `x` takes it to `{κ₁,κ₂}`
(`C2call`, `Examples.lean:1001-1008`).  The member is read off the second
round of `x`'s views: the first opens the `μ`, the second takes the left
operand of the intersection. -/
def probeC2 : Budget := { decls := 1, views := 2, sub := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) probeC2.sub [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1))), CapAtom.cvar (.there (.there (.there k2)))]).isSome
    = true := by
  decide +kernel

/-- The same at one unit less fuel finds nothing, so the probe measures the
search and not an accident of the table. -/
example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) 2 [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1))), CapAtom.cvar (.there (.there (.there k2)))]).isSome
    = false := by
  decide +kernel

/-- The member's upper bound is `{κ₁,κ₂}`, so the search does not put `{g}`
below `{κ₁}` alone, at the default budget either. -/
example : (subcap? (decls {} (C2CtxG platCtx k1 k2)) (({} : Budget).sub) [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1)))]).isSome = false := by
  decide +kernel

/-- S1, `{fs} <: {cp.C}` at the caller: the lower bound of the precise
member of `cp` is `{fs}`, so `sc-sel-lower` puts `{fs}` below `{cp.C}`
(`S1op`, `Examples.lean:1322-1327`). -/
def probeS1 : Budget := { decls := 1, views := 1, sub := 2, typer := 0, obj := 0 }

example : (subcap? (decls probeS1 S1Ctx2) probeS1.sub [CapAtom.cvar fs2]
    [CapAtom.sel .here lC]).isSome = true := by
  decide +kernel

/-- C5, `{n} <: {fs}` at the caller of `mk`: `sc-var` takes `{n}` to
`{it.C}`, and `sc-sel-upper` at the abstract member of `it` takes it to
`{fs}` (`S2nVar`, `Examples.lean:1633-1638`). -/
def probeC5 : Budget := { decls := 1, views := 2, sub := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC5 S2Ctx4) probeC5.sub [CapAtom.var .here]
    [CapAtom.cvar fs4]).isSome = true := by
  decide +kernel

/-- E1, the transitivity family at one member: `{A : ⊤..⊥} <: {B : …}`
through `⊤ <: x.A <: ⊥`, the chain of `badBounds` (`Examples.lean:106-110`). -/
def probeE1 : Budget := { decls := 1, views := 0, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE1 E1Ctx) probeE1.sub (E1Dom : Ty ([],x)) E1Res).isSome = true := by
  decide +kernel

/-- The same at one unit less fuel finds nothing. -/
example : (sub? (decls probeE1 E1Ctx) 1 (E1Dom : Ty ([],x)) E1Res).isSome = false := by
  decide +kernel

/-- E3, the transitivity family at two members of one variable at one label:
`{b : ⊤} <: x.A <: {a : ⊤}`, the chain of `E3sub` (`Examples.lean:216`). -/
def probeE3 : Budget := { decls := 1, views := 1, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE3 E3Ctx2) probeE3.sub (E3T2 : Ty ([],x,x)) E3T1).isSome = true := by
  decide +kernel

/-- E4, the detour view step followed by `<:-Sel`: `w` reaches
`{A : Int..⊤}` through `S <: x.B <: T`, and then `Int <: w.A`, the chain of
`E4nA` (`Examples.lean:288-291`).  Round one of the table reads `x`'s member
`B` and `w`'s member `A` at `⊥..⊤`.  Round two runs the detour step on `w`
and adds `w`'s member `A` at `Int..⊤`. -/
def probeE4 : Budget := { decls := 2, views := 1, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE4 E4Ctx4) probeE4.sub (E4Int : Ty ([],x,x,x,x))
    ((Shape.sel (.var (.there (.there .here))) lA) ^ [])).isSome = true := by
  decide +kernel

/-- E6, `<:-Sel` through the self binder's own member: `Int <: z.T` where `z`
is the literal's self binder, the chain of `E6nT` (`Examples.lean:419-422`).
Two rounds of the closure open the `μ` and then take the left operand of the
intersection. -/
def probeE6 : Budget := { decls := 1, views := 2, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE6 E6Ctxz) probeE6.sub (E6Int : Ty ([],x,x))
    ((Shape.sel (.var .here) lT) ^ [])).isSome = true := by
  decide +kernel

/-- E8, the right view step: `y : x.A ∧ {a : ⊤}` has a view at `{a : ⊤}`,
which is `E8yFld2` (`Examples.lean:494-495`). -/
def probeE8views : Budget := { decls := 0, views := 1, sub := 0, typer := 0, obj := 0 }

example : ((views (decls probeE8views E8Ctx2) probeE8views (.here : BVar ([],x,x) .var)).any
    (fun v => decide (v.ty = ((Shape.fld la (.top ^ [])) ^ [] : Ty ([],x,x))))) = true := by
  decide +kernel

/-- E8, `Sel-<:`: `x.A <: {a : ⊤}` by the upper bound of `x`'s member `A`,
which is `E8Upper` (`Examples.lean:502-503`). -/
def probeE8sub : Budget := { decls := 1, views := 0, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE8sub E8Ctx2) probeE8sub.sub
    ((Shape.sel (.var (.there .here)) lA) ^ [] : Ty ([],x,x))
    ((Shape.fld la (.top ^ [])) ^ [])).isSome = true := by
  decide +kernel

end Probes

end CapturesFrontend
