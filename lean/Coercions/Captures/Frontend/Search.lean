import Coercions.Captures.Frontend.Decide
import Coercions.Captures.Frontend.Surface
import Coercions.Captures.DotMNF.Examples

/-!
# Views, declarations and the search

The typer needs two things from this module.

A *view* of a context variable is a type the variable has, with its use set
and derivation.  It lets the typer read a field or a member off a variable
whose declared type does not display it.

A *declaration* is a type member or a capture member of a context variable,
with its derivation.  The *declaration table* of a context is the family of
middles the search tries for `SubShape.trans` and `Subcap.trans`, whose
middles the rules leave undetermined (`DotMNF/Typing.lean`).

Everything here returns the derivation, so the result type is the soundness
statement.  Nothing here is complete.

## Two layers

A type is a shape with a capture set, and `Sub` has the one rule `capt`: a
`SubShape` on the shapes and a `Subcap` on the sets.  So the search is two
functions in one block, `subShape?` and `subcap?`, and `sub?` pairs them.
Shape rules that compare types pair the two at the same fuel inline.

## Bounds

`Budget` has five counters: `decls` (rounds of the table), `views` (rounds of
the view closure), `sub` (fuel of the search), `typer` (fuel of the typer) and
`obj` (passes of the object rule).  Closures grow too fast to be unbounded, so
duplicates are dropped after every round and the table is computed once per
context and passed as a parameter.

## Order of definition

The view closure calls the search in its detour step, and the `∀` rule of the
search builds a table under an extended context.  That would be a cycle.  The
table is a parameter of the search, and the view steps are written once, in
`viewStepOf`, against an abstract search.  The `∀` rule builds its table with
`noSub`, the search that finds nothing.

Every function is structural, on a fuel or a list, so the kernel reduces the
search and the examples at the end are `decide +kernel`.
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
concludes at `{x}` for both sets, and `sc-var` takes both down to the declared
set, which is empty. -/
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

/-- The first view of a variable.  A binder declared at the empty set is used
at the empty set and keeps its declared type.  Any other binder is used at
`{x}` and has its declared shape at `{x}`, by `Var`. -/
def varView {s : Sig} (Γ : Ctx s) (x : BVar s .var) : View Γ x :=
  if h : (Γ.lookup x).captureSet = [] then ⟨[], Γ.lookup x, pureVar Γ x h⟩
  else ⟨[.var x], (Γ.lookup x).shape ^ [.var x], .var⟩

/-- A type member of a context variable, with the derivation.  The fields
`vr`, `lbl`, `lo`, `hi` are the key for deduplication. -/
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

/-- A capture member of a context variable, with the derivation.  The fields
`vr`, `lbl`, `lo`, `hi` are the key for deduplication. -/
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

/-- The type members and capture members of a context. -/
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

/-- The five counters. -/
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

Both closures drop duplicates after each round: views by their type,
declarations by their key fields.  The first entry of each key is kept. -/

/-- Membership of a key in a list of keys. -/
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

/-! ## View closure

A step takes one view of a variable to the views reachable from it by one
rule.  Every step keeps the use set and the capture set and changes only the
shape. -/

/-- One step of the view closure, uniform in the variable. -/
def ViewStep {s : Sig} (Γ : Ctx s) : Type :=
  (x : BVar s .var) → View Γ x → List (View Γ x)

/-- A search on shapes over a fixed context. -/
def SubSearch {s : Sig} (Γ : Ctx s) : Type := (S T : Shape s) → Option (SubShape Γ S T)

/-- The search that finds nothing, for tables built inside the search. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-- A shape subtyping lifted to types, keeping the capture set. -/
def subOfShape {s : Sig} {Γ : Ctx s} : (T : Ty s) → {S : Shape s} →
    SubShape Γ T.shape S → Sub Γ T (S ^ T.captureSet)
  | .capt _ _, _, e => .capt e .refl

/-- The five view steps, against an abstract search.

| step | condition on `v.ty` | new view | rule |
|---|---|---|---|
| open | `(μ S) ^ C` and `Shape.Decl S` | `S.substVar x ^ C` | `HasTy.recE` |
| left | `(S ∧ T) ^ C` | `S ^ C` | `HasTy.sub` with `SubShape.and1` |
| right | `(S ∧ T) ^ C` | `T ^ C` | `HasTy.sub` with `SubShape.and2` |
| upper | `y.A ^ C` at a type member `d` | `d.hi ^ C` | `HasTy.sub` with `SubShape.selUpper` |
| detour | the search takes the shape to `d.lo` | `d.hi ^ C` | `HasTy.sub` with `SubShape.trans` |
-/
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

/-- Every view of the list plus one step from each, deduplicated by type. -/
def viewsRoundOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : List (View Γ x) :=
  dedupBy View.ty (vs ++ vs.flatMap (st x))

/-- The closure of the first view of a variable after `m` rounds. -/
def viewsOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (m : Nat) (x : BVar s .var) :
    List (View Γ x) :=
  match m with
  | 0 => [varView Γ x]
  | m + 1 => viewsRoundOf st x (viewsOf st m x)
termination_by structural m

/-! ## Declaration table -/

/-- The members displayed by views of one variable. -/
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

/-- The members displayed by the views of the listed variables. -/
def tableOfVars {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (m : Nat) (ys : List (BVar s .var)) :
    DeclTable Γ :=
  match ys with
  | [] => .empty
  | y :: ys => DeclTable.append (tableOfViews (viewsOf st m y)) (tableOfVars st m ys)
termination_by structural ys

/-- Every member of the table plus the members the views of every context
variable display against it, deduplicated by key. -/
def declsRoundOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    (D : DeclTable Γ) : DeclTable Γ :=
  let N := tableOfVars (stf D) m (ctxVars Γ)
  ⟨dedupBy declKey (D.typs ++ N.typs), dedupBy capDeclKey (D.caps ++ N.caps)⟩

/-- The table after `k` rounds, each with `m` rounds of the view closure. -/
def declsOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat) (k : Nat) :
    DeclTable Γ :=
  match k with
  | 0 => .empty
  | k + 1 => declsRoundOf stf m (declsOf stf m k)
termination_by structural k

/-- The table without detour steps, which the `∀` rule builds under its
extended context. -/
def baseDecls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStepOf noSub D) b.views b.decls

/-! ## Search

A shape rule is either a decidable equality on a constructed shape or a
`match` whose fall-through branch is `none`.  A fall-through that returns a
derivation does not typecheck, because a `match` on `S` or `T` generalizes
them in the motive.

The helpers move a derivation across a decided equality.  They use `cases`
and not `▸`, because the label of a member occurs twice in the conclusion. -/

/-- The first success of a function along a list. -/
def firstSome {α β : Type} (f : α → Option β) (l : List α) : Option β :=
  match l with
  | [] => none
  | a :: as => (f a).orElse fun _ => firstSome f as
termination_by structural l

/-- `Sub.capt` from a shape search and a set search. -/
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

/-- `S <: d1.lo <: y.A <: d2.hi <: T`, the family of transitivity middles the
search tries on shapes.  The two members may differ, as E3 needs. -/
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

/-- The rounds of the table the `∀` rule builds.  Small, because the table is
rebuilt at every application. -/
def allBudget : Budget := { decls := 1, views := 2, sub := 0, typer := 0, obj := 0 }

mutual

/-- The shape search.  `subShape? D 0 S T` is `none`.  `subShape? D (n+1) S T`
tries thirteen rules in order and returns the first success.  Premises are
searched at fuel `n`.

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

A fourteenth alternative, not a rule of the calculus, retries the search at
the previous fuel.  It makes `subShape?_le` an induction on the fuel. -/
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
success.  Premises are searched at fuel `n`.

1. `C₁ ⊆ C₂`, `Subcap.elem`, decided.
2. `C₁ = a :: C` with `C` not empty, `Subcap.union` of `[a]` and `C`.
   `[a] ∪ C` is `a :: C` by reduction.
3. `C₁ = {x}`, `sc-var`, then a search from the set `x` is declared at.
4. `C₁ = {y.C}` at a capture member of the table, `sc-sel-upper`, then a
   search from its upper bound.
5. `C₁ = {a}` and `y.C ∈ C₂` at a capture member of the table, a search
   into its lower bound, then `sc-sel-lower`, then the inclusion of
   `{y.C}` in `C₂`.

A sixth alternative retries at the previous fuel, as in `subShape?`. -/
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

/-- The search on types: the shape search and the set search at one fuel. -/
def sub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (T U : Ty s) : Option (Sub Γ T U) :=
  subCapt (fun S S' => subShape? D n S S') (fun C C' => subcap? D n C C') T U

/-! ## The closure at the real search -/

/-- The five view steps at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) : ViewStep Γ :=
  viewStepOf (fun S T => subShape? D n S T) D

/-- One round of the view closure. -/
def viewsRound {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) {x : BVar s .var}
    (vs : List (View Γ x)) : List (View Γ x) :=
  viewsRoundOf (viewStep D n) x vs

/-- The views of a variable at a budget. -/
def views {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.sub) b.views x

/-- One round of the declaration table. -/
def declsRound {s : Sig} (b : Budget) (Γ : Ctx s) (D : DeclTable Γ) : DeclTable Γ :=
  declsRoundOf (fun D => viewStep D b.sub) b.views D

/-- The declaration table of a context at a budget. -/
def decls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStep D b.sub) b.views b.decls

/-! ## Round monotonicity

More rounds never lose a type or a member.  The statements are about keys,
not derivations, because deduplication drops later derivations of a key. -/

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

/-- Every member of `D` has an entry of the same key in `D'`. -/
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

The last alternative of `subShape?` and `subcap?` is the retry, so these are
inductions on the fuel.  They speak of `isSome`, because more fuel may find
another derivation of the same judgment. -/

theorem isSome_orElse_right {α : Type} {a : Option α} {b : Unit → Option α}
    (h : (b ()).isSome = true) : (a.orElse b).isSome = true := by
  cases a with
  | none => simpa [Option.orElse] using h
  | some x => rfl

/-- A search that keeps its answer at one more unit of fuel keeps it at any
larger fuel. -/
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

/-! ## Examples

Each reproduces a chain of `DotMNF/Examples.lean`.  C2, S1 and C5 are
subcapturing.  E1, E3, E4, E6 and E8 are subtyping or views, with empty
capture sets. -/

section Probes

open Captures.DotMNF.Examples

/-- C2, `{g} <: {κ₁,κ₂}` in the client (`C2call`).  `sc-var` takes `{g}` to
`{x.C}`, and `sc-sel-upper` at the abstract member of `x` takes it to
`{κ₁,κ₂}`.  The member comes from the second round of `x`'s views, which
opens the `μ` and then takes the left operand of the intersection. -/
def probeC2 : Budget := { decls := 1, views := 2, sub := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) probeC2.sub [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1))), CapAtom.cvar (.there (.there (.there k2)))]).isSome
    = true := by
  decide +kernel

/-- One unit less fuel finds nothing. -/
example : (subcap? (decls probeC2 (C2CtxG platCtx k1 k2)) 2 [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1))), CapAtom.cvar (.there (.there (.there k2)))]).isSome
    = false := by
  decide +kernel

/-- The member's upper bound is `{κ₁,κ₂}`, so `{g}` is not below `{κ₁}` alone. -/
example : (subcap? (decls {} (C2CtxG platCtx k1 k2)) (({} : Budget).sub) [CapAtom.var .here]
    [CapAtom.cvar (.there (.there (.there k1)))]).isSome = false := by
  decide +kernel

/-- S1, `{fs} <: {cp.C}` at the caller (`S1op`).  The lower bound of the
precise member of `cp` is `{fs}`, so `sc-sel-lower` applies. -/
def probeS1 : Budget := { decls := 1, views := 1, sub := 2, typer := 0, obj := 0 }

example : (subcap? (decls probeS1 S1Ctx2) probeS1.sub [CapAtom.cvar fs2]
    [CapAtom.sel .here lC]).isSome = true := by
  decide +kernel

/-- C5, `{n} <: {fs}` at the caller of `mk` (`S2nVar`).  `sc-var` takes `{n}`
to `{it.C}`, and `sc-sel-upper` at the abstract member of `it` takes it to
`{fs}`. -/
def probeC5 : Budget := { decls := 1, views := 2, sub := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC5 S2Ctx4) probeC5.sub [CapAtom.var .here]
    [CapAtom.cvar fs4]).isSome = true := by
  decide +kernel

/-- E1, transitivity at one member: `{A : ⊤..⊥} <: {B : …}` through
`⊤ <: x.A <: ⊥` (`badBounds`). -/
def probeE1 : Budget := { decls := 1, views := 0, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE1 E1Ctx) probeE1.sub (E1Dom : Ty ([],x)) E1Res).isSome = true := by
  decide +kernel

/-- One unit less fuel finds nothing. -/
example : (sub? (decls probeE1 E1Ctx) 1 (E1Dom : Ty ([],x)) E1Res).isSome = false := by
  decide +kernel

/-- E3, transitivity at two members of one variable at one label:
`{b : ⊤} <: x.A <: {a : ⊤}` (`E3sub`). -/
def probeE3 : Budget := { decls := 1, views := 1, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE3 E3Ctx2) probeE3.sub (E3T2 : Ty ([],x,x)) E3T1).isSome = true := by
  decide +kernel

/-- E4, the detour view step followed by `<:-Sel` (`E4nA`).  `w` reaches
`{A : Int..⊤}` through `S <: x.B <: T`, and then `Int <: w.A`.  Round one of
the table reads `x`'s member `B` and `w`'s member `A` at `⊥..⊤`.  Round two
runs the detour step on `w` and adds `w`'s member `A` at `Int..⊤`. -/
def probeE4 : Budget := { decls := 2, views := 1, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE4 E4Ctx4) probeE4.sub (E4Int : Ty ([],x,x,x,x))
    ((Shape.sel (.var (.there (.there .here))) lA) ^ [])).isSome = true := by
  decide +kernel

/-- E6, `<:-Sel` through the self binder's own member (`E6nT`): `Int <: z.T`
where `z` is the literal's self binder.  Two rounds of the closure open the
`μ` and take the left operand of the intersection. -/
def probeE6 : Budget := { decls := 1, views := 2, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE6 E6Ctxz) probeE6.sub (E6Int : Ty ([],x,x))
    ((Shape.sel (.var .here) lT) ^ [])).isSome = true := by
  decide +kernel

/-- E8, the right view step: `y : x.A ∧ {a : ⊤}` has a view at `{a : ⊤}`
(`E8yFld2`). -/
def probeE8views : Budget := { decls := 0, views := 1, sub := 0, typer := 0, obj := 0 }

example : ((views (decls probeE8views E8Ctx2) probeE8views (.here : BVar ([],x,x) .var)).any
    (fun v => decide (v.ty = ((Shape.fld la (.top ^ [])) ^ [] : Ty ([],x,x))))) = true := by
  decide +kernel

/-- E8, `Sel-<:`: `x.A <: {a : ⊤}` by the upper bound of `x`'s member `A`
(`E8Upper`). -/
def probeE8sub : Budget := { decls := 1, views := 0, sub := 2, typer := 0, obj := 0 }

example : (sub? (decls probeE8sub E8Ctx2) probeE8sub.sub
    ((Shape.sel (.var (.there .here)) lA) ^ [] : Ty ([],x,x))
    ((Shape.fld la (.top ^ [])) ^ [])).isSome = true := by
  decide +kernel

end Probes

end CapturesFrontend
