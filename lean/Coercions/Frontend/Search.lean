import Coercions.Frontend.Decide
import Coercions.Frontend.Surface
import Coercions.DotMNF.Examples

/-!
# Views, the declaration table, and the subtyping search

Stages F1.2 and F1.3 of `plan-5e-frontend-stages.md`.  The typer of F1.4 needs
two things this module provides.  A *view* of a context variable is a type the
variable has, carried with its derivation, so the typer may read a field or a
member off a variable whose declared type does not display it.  A *declaration*
is a type member a context variable has, again with its derivation, and the
*declaration table* of a context is the family of middles the subtyping search
is allowed to try for `Sub.trans`, whose middle is otherwise undetermined
(`lean/Coercions/DotMNF/Typing.lean:74`).

Everything here returns the derivation, so there is no soundness theorem: the
result type is the statement.  Nothing here is complete, and no completeness
theorem is claimed.

## What is fuel bounded, and why

Four counters live in `Budget`.  `decls` counts rounds of the table, `views`
counts rounds of the view closure, `sub` is the fuel of `sub?`, and `typer` is
the fuel of F1.4.  The refuter measured the unbounded closure of the design at
`V(n+1) ~ 1 + 3*V(n) + 2*k*V(n)^2` and found fuel four already past the machine
(`notes-frontend-design/refute-frontend.md`, F3).  The three repairs it named
are all taken here: duplicates are dropped after every round, the table is
computed once per context and passed as a parameter rather than recomputed
inside the search, and the closure and the table have small round counters of
their own, separate from the fuel of `sub?`.  The numbers of F1.2 are a
starting point.  The measured ones are in the stage report.

## The order of definition

`viewStep` calls `sub?` in its detour step, and rule 8 of `sub?` calls the table
builder under an extended context.  Taken literally that is a cycle.  It is cut
the way F1.2 says, by making the table a parameter, plus one further step: the
five view steps are written once, in `viewStepOf`, against an abstract
`SubSearch`, the search the detour step consults.  `sub?` is defined against
`viewStepOf noSub`, the detour free step, so its own definition mentions no
search but its own.  The public `viewStep` of F1.2 instantiates the same body at
the real `sub? D n`.  So there is one copy of every definition, the block of
well-founded definitions is `sub?` and its two list walkers and nothing else,
and the deviation is confined to one place, named in the stage report: the table
that rule 8 builds under `Γ.cons S2` is detour free.

## The kernel

`sub?` is well-founded, so it does not reduce in the kernel and no `decide` or
`rfl` may mention it (F1.7).  The probes of F1.6 at the end of this module run
through `expect` and `#eval`, which run compiled code.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Defs Ctx Sub HasTy)

/-! ## Views and declarations -/

/-- A type a context variable has, with the derivation that it has it. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ (.path (.var x)) ty

/-- A type member a context variable has, with the derivation.  The four data
fields are the key by which the table is deduplicated. -/
structure Decl {s : Sig} (Γ : Ctx s) where
  /-- The variable the member is read off. -/
  vr : BVar s .var
  /-- The label of the member. -/
  lbl : Label
  /-- The lower bound. -/
  lo : Ty s
  /-- The upper bound. -/
  hi : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ (.path (.var vr)) (.typ lbl lo hi)

/-- The declaration table of a context. -/
abbrev DeclTable {s : Sig} (Γ : Ctx s) := List (Decl Γ)

/-- The selection a declaration licenses, `y.A`. -/
def declSel {s : Sig} {Γ : Ctx s} (d : Decl Γ) : Ty s := .sel (.var d.vr) d.lbl

/-- `<:-Sel` at a declaration of the table. -/
def declLower {s : Sig} {Γ : Ctx s} (d : Decl Γ) : Sub Γ d.lo (declSel d) :=
  Sub.selLower d.deriv

/-- `Sel-<:` at a declaration of the table. -/
def declUpper {s : Sig} {Γ : Ctx s} (d : Decl Γ) : Sub Γ (declSel d) d.hi :=
  Sub.selUpper d.deriv

/-- The four counters of F1.2.  The defaults are the plan's starting point, not
a measurement.  The stage report gives the measured budget of every probe. -/
structure Budget where
  /-- Rounds of the declaration table. -/
  decls : Nat := 3
  /-- Rounds of the view closure. -/
  views : Nat := 3
  /-- Fuel of the subtyping search. -/
  sub : Nat := 6
  /-- Fuel of the typer of F1.4. -/
  typer : Nat := 8
deriving Repr, Inhabited

/-! ## Deduplication

Both closures grow only by rounds, and both drop duplicates after each round:
views by their type, declarations by their four data fields.  The first entry of
each key is the one kept.  Both procedures are structural, on the list, with the
keys seen so far as an accumulator, so neither needs well-founded recursion. -/

/-- Membership of a type in a list of types, as a decision. -/
def tyMem? {s : Sig} (T : Ty s) : List (Ty s) → Bool
  | [] => false
  | U :: Us => if U = T then true else tyMem? T Us

theorem tyMem?_nil {s : Sig} (T : Ty s) : tyMem? T [] = false := rfl

theorem tyMem?_cons {s : Sig} (T U : Ty s) (Us : List (Ty s)) :
    tyMem? T (U :: Us) = true ↔ (U = T ∨ tyMem? T Us = true) := by
  by_cases h : U = T
  · simp [tyMem?, h]
  · simp [tyMem?, h]

/-- Views whose type is already in `seen` are dropped. -/
def dedupViewsFrom {s : Sig} {Γ : Ctx s} {x : BVar s .var} (seen : List (Ty s)) :
    List (View Γ x) → List (View Γ x)
  | [] => []
  | v :: vs =>
      if tyMem? v.ty seen then dedupViewsFrom seen vs
      else v :: dedupViewsFrom (v.ty :: seen) vs

/-- Keep the first view of each type. -/
def dedupViews {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    List (View Γ x) :=
  dedupViewsFrom [] vs

/-- The four data fields of two declarations agree, as a decision. -/
def declSame {s : Sig} {Γ : Ctx s} (d e : Decl Γ) : Bool :=
  d.vr = e.vr && d.lbl = e.lbl && d.lo = e.lo && d.hi = e.hi

/-- Membership of a declaration in a table, by the four data fields. -/
def declMem? {s : Sig} {Γ : Ctx s} (d : Decl Γ) : DeclTable Γ → Bool
  | [] => false
  | e :: es => if declSame e d then true else declMem? d es

/-- Declarations whose key is already in `seen` are dropped. -/
def dedupDeclsFrom {s : Sig} {Γ : Ctx s} (seen : DeclTable Γ) :
    DeclTable Γ → DeclTable Γ
  | [] => []
  | d :: ds =>
      if declMem? d seen then dedupDeclsFrom seen ds
      else d :: dedupDeclsFrom (d :: seen) ds

/-- Keep the first declaration of each key. -/
def dedupDecls {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) : DeclTable Γ :=
  dedupDeclsFrom [] D

/-! ## The view closure

A step of the closure takes one view of a variable to the views reachable from
it in one rule.  The five steps are the table of F1.2.  `open` and the two
`and` steps read the rules off the derivation alone.  The `upper` step and the
`detour` step consult the table, and the detour step consults a subtyping
search as well, which is why the step is written against an abstract search:
`sub?` instantiates it at the detour free `noSub`, and the public `viewStep`
instantiates it at the real search. -/

/-- One step of the view closure, uniform in the variable. -/
def ViewStep {s : Sig} (Γ : Ctx s) : Type :=
  (x : BVar s .var) → View Γ x → List (View Γ x)

/-- A subtyping search over a fixed context, as the detour step consumes it. -/
def SubSearch {s : Sig} (Γ : Ctx s) : Type := (S T : Ty s) → Option (Sub Γ S T)

/-- The search that finds nothing.  It is what `sub?` passes when it rebuilds a
table under an extended context, where calling the real search would be
circular. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-- The five view steps of F1.2, against an abstract search.

| step | condition on `v.ty` | new view | rule |
|---|---|---|---|
| open | `.mu T` and `Ty.Decl T` | `T.substVar x` | `HasTy.recE` (`Typing.lean:113-115`) |
| left | `.and S T` | `S` | `HasTy.sub` with `Sub.and1` (`Typing.lean:75,121`) |
| right | `.and S T` | `T` | `HasTy.sub` with `Sub.and2` (`Typing.lean:76,121`) |
| upper | `v.ty = y.A` at a `d` of the table | `d.hi` | `HasTy.sub` with `Sub.selUpper` (`Typing.lean:81`) |
| detour | `sub v.ty d.lo` succeeds at a `d` | `d.hi` | `HasTy.sub` with `Sub.trans` (`Typing.lean:74,81,83`) |

The detour step's derivation carries the evidence `e` of its own side
condition.  Without it the term is ill typed, which is the refuter's C3. -/
def viewStepOf {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) (D : DeclTable Γ) : ViewStep Γ :=
  fun x v =>
    (match hv : v.ty with
      | .mu T =>
          if hd : Ty.Decl T then [⟨T.substVar x, .recE (hv ▸ v.deriv) hd⟩] else []
      | .and S T =>
          [⟨S, .sub (hv ▸ v.deriv) .and1⟩, ⟨T, .sub (hv ▸ v.deriv) .and2⟩]
      | _ => [])
    ++ D.filterMap (fun d =>
        if h : v.ty = declSel d then some ⟨d.hi, .sub (h ▸ v.deriv) (declUpper d)⟩
        else none)
    ++ D.filterMap (fun d =>
        (sub v.ty d.lo).map (fun e =>
          ⟨d.hi, .sub v.deriv (Sub.trans e (Sub.trans (declLower d) (declUpper d)))⟩))

/-- One round of the closure: every view of the list, plus one step from each,
with the duplicates by type dropped. -/
def viewsRoundOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : List (View Γ x) :=
  dedupViews (vs ++ vs.flatMap (st x))

/-- The closure of the declared type of a variable under `m` rounds. -/
def viewsOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) : Nat → (x : BVar s .var) → List (View Γ x)
  | 0, x => [⟨Ctx.lookup Γ x, .var⟩]
  | m + 1, x => viewsRoundOf st x (viewsOf st m x)

/-! ## The declaration table -/

/-- The `.typ` views of a variable, as declarations. -/
def declsOfViews {s : Sig} {Γ : Ctx s} {y : BVar s .var} :
    List (View Γ y) → DeclTable Γ
  | [] => []
  | v :: vs =>
      (match hv : v.ty with
        | .typ A L U => [⟨y, A, L, U, hv ▸ v.deriv⟩]
        | _ => []) ++ declsOfViews vs

/-- One round of the table: every declaration already in it, plus the `.typ`
views of every context variable computed against it, deduplicated by key. -/
def declsRoundOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    (D : DeclTable Γ) : DeclTable Γ :=
  dedupDecls (D ++ (ctxVars Γ).flatMap (fun y => declsOfViews (viewsOf (stf D) m y)))

/-- The table after `k` rounds, each round running `m` rounds of the closure. -/
def declsOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat) :
    Nat → DeclTable Γ
  | 0 => []
  | k + 1 => declsRoundOf stf m (declsOf stf m k)

/-- The detour free table, the one rule 8 of `sub?` builds under the context it
extends.  Building the full table there would make `sub?` mutual with the view
closure, which F1.2 cuts on purpose. -/
def baseDecls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStepOf noSub D) b.views b.decls

/-! ## The subtyping search

Eleven rules in a fixed order, plus one retry, described below.  Each rule is
written either as a decidable equality on a constructed shape or as a `match`
whose fall-through branch is `none`, never as a `match` whose fall-through
branch returns a derivation: a `match` on `S` or on `T` inside a function whose
result type mentions them generalizes them in the motive, and a fall-through
that is not `none` then does not typecheck.  The refuter recorded the exact
error on that shape.

The three helpers below move a derivation across a decided equality of labels or
of a selection.  They are written with `cases` rather than with `▸` because the
label of a `fld` or a `typ` occurs twice in the conclusion and a rewrite would
hit both occurrences. -/

/-- `Sub.fld` with the two labels equal by a decision. -/
def subFldOf {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b)
    (e : Sub Γ S T) : Sub Γ (.fld a S) (.fld b T) := by
  cases h; exact Sub.fld e

/-- `Sub.typ` with the two labels equal by a decision. -/
def subTypOf {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Ty s} (h : A = B)
    (e1 : Sub Γ S2 S1) (e2 : Sub Γ T1 T2) :
    Sub Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h; exact Sub.typ e1 e2

/-- Rule 9's conclusion: `S <: d.lo <: y.A`, where `T` is that selection. -/
def subToSel {s : Sig} {Γ : Ctx s} {d : Decl Γ} {S T : Ty s} (h : T = declSel d)
    (e : Sub Γ S d.lo) : Sub Γ S T := by
  cases h; exact Sub.trans e (declLower d)

/-- Rule 10's conclusion: `y.A <: d.hi <: T`, where `S` is that selection. -/
def subFromSel {s : Sig} {Γ : Ctx s} {d : Decl Γ} {S T : Ty s} (h : S = declSel d)
    (e : Sub Γ d.hi T) : Sub Γ S T := by
  cases h; exact Sub.trans (declUpper d) e

/-- Rule 11's conclusion: `S <: d1.lo <: y.A <: d2.hi <: T`, the one family of
transitivity middles the search tries.  The two declarations may differ, which
is what E3 needs (`lean/Coercions/DotMNF/Examples.lean:151`). -/
def subThroughPair {s : Sig} {Γ : Ctx s} {d1 d2 : Decl Γ} {S T : Ty s}
    (h : declSel d2 = declSel d1) (e1 : Sub Γ S d1.lo) (e2 : Sub Γ d2.hi T) :
    Sub Γ S T :=
  Sub.trans e1 (Sub.trans (declLower d1) (Sub.trans (h ▸ declUpper d2) e2))

/-- The pairs of declarations rule 11 walks. -/
def declPairs {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) : List (Decl Γ × Decl Γ) :=
  D.flatMap (fun d1 => D.map (fun d2 => (d1, d2)))

/-- The rounds rule 8 gives the detour free table it builds under the context it
extends.  Small on purpose: the table is rebuilt at every application of the
rule. -/
def allBudget : Budget := { decls := 1, views := 2, sub := 0, typer := 0 }

mutual

/-- The subtyping search.  `sub? D 0 S T` is `none`.  `sub? D (n+1) S T` tries
the eleven rules of F1.3 in order and returns the first success.

1. `S = T`, `Sub.refl` (`lean/Coercions/DotMNF/Typing.lean:73`).
2. `T = ⊤`, `Sub.top` (`Typing.lean:71`).
3. `S = ⊥`, `Sub.bot` (`Typing.lean:72`).
4. `T = T1 ∧ T2`, `Sub.and` (`Typing.lean:77`).
5. `S = S1 ∧ S2`, `Sub.trans` with `Sub.and1` or `Sub.and2`
   (`Typing.lean:74,75,76`).
6. `S = {a : S'}` and `T = {a : T'}`, `Sub.fld` (`Typing.lean:78`).
7. `S = {A : S1..T1}` and `T = {A : S2..T2}`, `Sub.typ` (`Typing.lean:79`).
8. `S = ∀(x : S1) T1` and `T = ∀(x : S2) T2`, `Sub.all` (`Typing.lean:84`), with
   the body compared under `Γ.cons S2` against a table rebuilt there.
9. `T = y.A` at a declaration of the table, `Sub.selLower` (`Typing.lean:83`).
10. `S = y.A` at a declaration of the table, `Sub.selUpper` (`Typing.lean:81`).
11. The one transitivity family, at a pair of declarations of one variable at
    one label (`Typing.lean:74,81,83`).

The twelfth alternative is not a rule of the calculus: it retries the whole
search at the previous fuel.  It changes no answer that the eleven rules give at
this fuel, since every rule of the list is tried here at strictly more fuel than
it was tried there, and it costs one call at fuel `n` beside the `2|D|^2` that
rule 11 already makes.  What it buys is `sub?_le`, which is otherwise an
induction through all eleven rules and both walkers. -/
def sub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) (S T : Ty s) :
    Option (Sub Γ S T) :=
  match n with
  | 0 => none
  | n + 1 =>
      -- 1
      ((if h : S = T then some (h ▸ Sub.refl) else none : Option (Sub Γ S T))).orElse fun _ =>
      -- 2
      ((if h : T = .top then some (h ▸ Sub.top) else none : Option (Sub Γ S T))).orElse fun _ =>
      -- 3
      ((if h : S = .bot then some (h ▸ Sub.bot) else none : Option (Sub Γ S T))).orElse fun _ =>
      -- 4
      ((match T with
        | .and T1 T2 => do
            let e1 ← sub? D n S T1
            let e2 ← sub? D n S T2
            some (Sub.and e1 e2)
        | _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 5
      ((match S with
        | .and S1 S2 =>
            ((sub? D n S1 T).map (fun e => Sub.trans Sub.and1 e)).orElse fun _ =>
            ((sub? D n S2 T).map (fun e => Sub.trans Sub.and2 e))
        | _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 6
      ((match S, T with
        | .fld a S', .fld b T' =>
            if h : a = b then (sub? D n S' T').map (fun e => subFldOf h e) else none
        | _, _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 7
      ((match S, T with
        | .typ A S1 T1, .typ B S2 T2 =>
            if h : A = B then do
              let e1 ← sub? D n S2 S1
              let e2 ← sub? D n T1 T2
              some (subTypOf h e1 e2)
            else none
        | _, _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 8
      ((match S, T with
        | .all S1 T1, .all S2 T2 => do
            let e1 ← sub? D n S2 S1
            let e2 ← sub? (baseDecls allBudget (Γ.cons S2)) n T1 T2
            some (Sub.all e1 e2)
        | _, _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 9 and 10
      (pickLower D (n + 1) D S T).orElse fun _ =>
      (pickUpper D (n + 1) D S T).orElse fun _ =>
      -- 11
      (pickPair D (n + 1) (declPairs D) S T).orElse fun _ =>
      -- the retry
      sub? D n S T
termination_by (n, 3, 0)

/-- Rule 9: walk the table for a declaration whose selection is `T`. -/
def pickLower {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat)
    (ds : DeclTable Γ) (S T : Ty s) : Option (Sub Γ S T) :=
  match n, ds with
  | 0, _ => none
  | _, [] => none
  | n + 1, d :: ds =>
      (if h : T = declSel d then (sub? D n S d.lo).map (fun e => subToSel h e)
       else none).orElse fun _ => pickLower D (n + 1) ds S T
termination_by (n, 2, ds.length)

/-- Rule 10: walk the table for a declaration whose selection is `S`. -/
def pickUpper {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat)
    (ds : DeclTable Γ) (S T : Ty s) : Option (Sub Γ S T) :=
  match n, ds with
  | 0, _ => none
  | _, [] => none
  | n + 1, d :: ds =>
      (if h : S = declSel d then (sub? D n d.hi T).map (fun e => subFromSel h e)
       else none).orElse fun _ => pickUpper D (n + 1) ds S T
termination_by (n, 2, ds.length)

/-- Rule 11: walk the pairs of the table for one variable at one label. -/
def pickPair {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat)
    (ps : List (Decl Γ × Decl Γ)) (S T : Ty s) : Option (Sub Γ S T) :=
  match n, ps with
  | 0, _ => none
  | _, [] => none
  | n + 1, (d1, d2) :: ps =>
      (if h : declSel d2 = declSel d1 then do
          let e1 ← sub? D n S d1.lo
          let e2 ← sub? D n d2.hi T
          some (subThroughPair h e1 e2)
       else none).orElse fun _ => pickPair D (n + 1) ps S T
termination_by (n, 1, ps.length)

end

/-! ## The closure at the real search

The names of F1.2.  Each is the generic body above at `viewStep D n`, the five
view steps with the detour step consulting `sub? D n`. -/

/-- The five view steps of F1.2 at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) : ViewStep Γ :=
  viewStepOf (sub? D n) D

/-- One round of the view closure, the round `views` iterates `b.views` times. -/
def viewsRound {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (n : Nat) {x : BVar s .var}
    (vs : List (View Γ x)) : List (View Γ x) :=
  viewsRoundOf (viewStep D n) x vs

/-- The views of a variable at a budget.  `Γ` is implicit: it is determined by
the table, which is a table of `Γ`. -/
def views {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.sub) b.views x

/-- One round of the declaration table, the round `decls` iterates `b.decls`
times. -/
def declsRound {s : Sig} (b : Budget) (Γ : Ctx s) (D : DeclTable Γ) : DeclTable Γ :=
  declsRoundOf (fun D => viewStep D b.sub) b.views D

/-- The declaration table of a context at a budget. -/
def decls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStep D b.sub) b.views b.decls

/-! ## Round monotonicity

More rounds never lose a type, and never lose a declaration.  Both statements
are about types and about the four data fields of a declaration, not about
derivations: deduplication drops later derivations of the same key, and a larger
budget may legitimately find a different derivation of the same judgment. -/

/-- Every type of `l` occurs in `l'`. -/
def ViewsLe {s : Sig} {Γ : Ctx s} {x : BVar s .var} (l l' : List (View Γ x)) : Prop :=
  ∀ v ∈ l, ∃ w ∈ l', w.ty = v.ty

theorem viewsLe_refl {s : Sig} {Γ : Ctx s} {x : BVar s .var} (l : List (View Γ x)) :
    ViewsLe l l := fun v hv => ⟨v, hv, rfl⟩

theorem viewsLe_trans {s : Sig} {Γ : Ctx s} {x : BVar s .var} {l l' l'' : List (View Γ x)}
    (h1 : ViewsLe l l') (h2 : ViewsLe l' l'') : ViewsLe l l'' := by
  intro v hv
  obtain ⟨w, hw, hwty⟩ := h1 v hv
  obtain ⟨u, hu, huty⟩ := h2 w hw
  exact ⟨u, hu, huty.trans hwty⟩

theorem dedupViewsFrom_covers {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    (l : List (View Γ x)) :
    ∀ (seen : List (Ty s)) (v : View Γ x), v ∈ l →
      tyMem? v.ty seen = true ∨ ∃ w ∈ dedupViewsFrom seen l, w.ty = v.ty := by
  induction l with
  | nil => intro seen v hv; cases hv
  | cons u l ih =>
      intro seen v hv
      by_cases hs : tyMem? u.ty seen = true
      · have heq : dedupViewsFrom seen (u :: l) = dedupViewsFrom seen l := by
          simp [dedupViewsFrom, hs]
        cases List.mem_cons.mp hv with
        | inl he => exact Or.inl (he ▸ hs)
        | inr hv' => rw [heq]; exact ih seen v hv'
      · have heq : dedupViewsFrom seen (u :: l) = u :: dedupViewsFrom (u.ty :: seen) l := by
          simp [dedupViewsFrom, hs]
        cases List.mem_cons.mp hv with
        | inl he => exact Or.inr ⟨u, by rw [heq]; simp, by rw [he]⟩
        | inr hv' =>
            cases ih (u.ty :: seen) v hv' with
            | inl h =>
                cases (tyMem?_cons v.ty u.ty seen).mp h with
                | inl h' => exact Or.inr ⟨u, by rw [heq]; simp, h'⟩
                | inr h' => exact Or.inl h'
            | inr h =>
                obtain ⟨w, hw, hwty⟩ := h
                exact Or.inr ⟨w, by rw [heq]; exact List.mem_cons_of_mem _ hw, hwty⟩

/-- Deduplication keeps one view of each type. -/
theorem dedupViews_covers {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    (l : List (View Γ x)) : ViewsLe l (dedupViews l) := by
  intro v hv
  cases dedupViewsFrom_covers l [] v hv with
  | inl h => exact absurd h (by simp [tyMem?])
  | inr h => exact h

/-- A round only adds. -/
theorem viewsRoundOf_covers {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : ViewsLe vs (viewsRoundOf st x vs) := by
  intro v hv
  exact dedupViews_covers _ v (List.mem_append_left _ hv)

theorem viewsOf_mono {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) {m m' : Nat}
    (h : m ≤ m') (x : BVar s .var) : ViewsLe (viewsOf st m x) (viewsOf st m' x) := by
  induction m' with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp h
      subst hm
      exact viewsLe_refl _
  | succ k ih =>
      cases Nat.lt_or_ge m (k + 1) with
      | inl hlt =>
          exact viewsLe_trans (ih (Nat.lt_succ_iff.mp hlt))
            (viewsRoundOf_covers st x (viewsOf st k x))
      | inr hge =>
          have hm : m = k + 1 := Nat.le_antisymm h hge
          subst hm
          exact viewsLe_refl _

/-- More rounds of the view closure never lose a type (F1.5). -/
theorem views_mono {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b b' : Budget}
    (h : b.views ≤ b'.views) (hs : b.sub = b'.sub) (x : BVar s .var) :
    ∀ v ∈ views D b x, ∃ w ∈ views D b' x, w.ty = v.ty := by
  unfold views
  rw [hs]
  exact viewsOf_mono (viewStep D b'.sub) h x

/-- The four data fields of two declarations agree. -/
def DeclAgree {s : Sig} {Γ : Ctx s} (d' d : Decl Γ) : Prop :=
  d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi

theorem declAgree_refl {s : Sig} {Γ : Ctx s} (d : Decl Γ) : DeclAgree d d :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem declAgree_trans {s : Sig} {Γ : Ctx s} {d'' d' d : Decl Γ}
    (h1 : DeclAgree d'' d') (h2 : DeclAgree d' d) : DeclAgree d'' d :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem declSame_agree {s : Sig} {Γ : Ctx s} {d e : Decl Γ} (h : declSame e d = true) :
    DeclAgree e d := by
  simp only [declSame, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem declMem?_agree {s : Sig} {Γ : Ctx s} {d : Decl Γ} :
    ∀ {D : DeclTable Γ}, declMem? d D = true → ∃ e ∈ D, DeclAgree e d := by
  intro D
  induction D with
  | nil => intro h; exact absurd h (by simp [declMem?])
  | cons u D ih =>
      intro h
      by_cases hu : declSame u d = true
      · exact ⟨u, by simp, declSame_agree hu⟩
      · have h' : declMem? d D = true := by
          simp only [declMem?, hu] at h
          exact h
        obtain ⟨e, he, hae⟩ := ih h'
        exact ⟨e, List.mem_cons_of_mem _ he, hae⟩

/-- Every declaration of `D` has an entry of the same key in `D'`. -/
def DeclsLe {s : Sig} {Γ : Ctx s} (D D' : DeclTable Γ) : Prop :=
  ∀ d ∈ D, ∃ d' ∈ D', DeclAgree d' d

theorem declsLe_refl {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) : DeclsLe D D :=
  fun d hd => ⟨d, hd, declAgree_refl d⟩

theorem declsLe_trans {s : Sig} {Γ : Ctx s} {D D' D'' : DeclTable Γ}
    (h1 : DeclsLe D D') (h2 : DeclsLe D' D'') : DeclsLe D D'' := by
  intro d hd
  obtain ⟨e, he, hae⟩ := h1 d hd
  obtain ⟨f, hf, haf⟩ := h2 e he
  exact ⟨f, hf, declAgree_trans haf hae⟩

theorem dedupDeclsFrom_covers {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) :
    ∀ (seen : DeclTable Γ) (d : Decl Γ), d ∈ D →
      (∃ e ∈ seen, DeclAgree e d) ∨ ∃ e ∈ dedupDeclsFrom seen D, DeclAgree e d := by
  induction D with
  | nil => intro seen d hd; cases hd
  | cons u D ih =>
      intro seen d hd
      by_cases hs : declMem? u seen = true
      · have heq : dedupDeclsFrom seen (u :: D) = dedupDeclsFrom seen D := by
          simp [dedupDeclsFrom, hs]
        cases List.mem_cons.mp hd with
        | inl he =>
            obtain ⟨e, hem, hae⟩ := declMem?_agree hs
            exact Or.inl ⟨e, hem, he ▸ hae⟩
        | inr hd' => rw [heq]; exact ih seen d hd'
      · have heq : dedupDeclsFrom seen (u :: D) = u :: dedupDeclsFrom (u :: seen) D := by
          simp [dedupDeclsFrom, hs]
        cases List.mem_cons.mp hd with
        | inl he => exact Or.inr ⟨u, by rw [heq]; simp, he ▸ declAgree_refl u⟩
        | inr hd' =>
            cases ih (u :: seen) d hd' with
            | inl h =>
                obtain ⟨e, hem, hae⟩ := h
                cases List.mem_cons.mp hem with
                | inl he' => exact Or.inr ⟨u, by rw [heq]; simp, he' ▸ hae⟩
                | inr he' => exact Or.inl ⟨e, he', hae⟩
            | inr h =>
                obtain ⟨e, hem, hae⟩ := h
                exact Or.inr ⟨e, by rw [heq]; exact List.mem_cons_of_mem _ hem, hae⟩

/-- Deduplication keeps one declaration of each key. -/
theorem dedupDecls_covers {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) :
    DeclsLe D (dedupDecls D) := by
  intro d hd
  cases dedupDeclsFrom_covers D [] d hd with
  | inl h => obtain ⟨e, he, _⟩ := h; cases he
  | inr h => exact h

/-- A round of the table only adds. -/
theorem declsRoundOf_covers {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ)
    (m : Nat) (D : DeclTable Γ) : DeclsLe D (declsRoundOf stf m D) := by
  intro d hd
  exact dedupDecls_covers _ d (List.mem_append_left _ hd)

theorem declsOf_mono {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    {k k' : Nat} (h : k ≤ k') : DeclsLe (declsOf stf m k) (declsOf stf m k') := by
  induction k' with
  | zero =>
      have hk : k = 0 := Nat.le_zero.mp h
      subst hk
      exact declsLe_refl _
  | succ j ih =>
      cases Nat.lt_or_ge k (j + 1) with
      | inl hlt =>
          exact declsLe_trans (ih (Nat.lt_succ_iff.mp hlt))
            (declsRoundOf_covers stf m (declsOf stf m j))
      | inr hge =>
          have hk : k = j + 1 := Nat.le_antisymm h hge
          subst hk
          exact declsLe_refl _

/-- More rounds of the table never lose a declaration (F1.5). -/
theorem decls_mono {s : Sig} {Γ : Ctx s} {b b' : Budget} (h : b.decls ≤ b'.decls)
    (hv : b.views = b'.views) (hs : b.sub = b'.sub) :
    ∀ d ∈ decls b Γ, ∃ d' ∈ decls b' Γ,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi := by
  unfold decls
  rw [hv, hs]
  exact declsOf_mono (fun D => viewStep D b'.sub) b'.views h

/-! ## Fuel monotonicity

The twelfth alternative of `sub?` is the retry at the previous fuel, so the
statement is an induction on the difference and not a walk through the eleven
rules.  The statement is about `isSome` and not about derivations, for the same
reason the two round statements are about types: more fuel may find another
derivation of the same judgment, and `Sub` is `Type` valued with no decidable
equality. -/

theorem isSome_orElse_right {α : Type u} {a : Option α} {b : Unit → Option α}
    (h : (b ()).isSome = true) : (a.orElse b).isSome = true := by
  cases a with
  | none => simpa [Option.orElse] using h
  | some x => rfl

/-- One more unit of fuel never loses an answer. -/
theorem sub?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n : Nat} {S T : Ty s}
    (h : (sub? D n S T).isSome) : (sub? D (n + 1) S T).isSome := by
  rw [sub?.eq_def]
  iterate 11 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses an answer (F1.5). -/
theorem sub?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} : ∀ {n n' : Nat}, n ≤ n' →
    ∀ {S T : Ty s}, (sub? D n S T).isSome → (sub? D n' S T).isSome := by
  intro n n'
  induction n' with
  | zero =>
      intro h S T hs
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn
      exact hs
  | succ k ih =>
      intro h S T hs
      cases Nat.lt_or_ge n (k + 1) with
      | inl hlt => exact sub?_succ (ih (Nat.lt_succ_iff.mp hlt) hs)
      | inr hge =>
          have hn : n = k + 1 := Nat.le_antisymm h hge
          subst hn
          exact hs

/-! ## The probes of F1.6

Four probes of `sub?` and two of `views`, each naming the chain of
`lean/Coercions/DotMNF/Examples.lean` it reproduces.  None of them is a
`decide` or a `rfl`: `sub?` is well-founded and does not reduce in the kernel
(F1.7), so every probe runs compiled code through `expect`, where a false
result throws and fails the build.

The budget of each probe is the smallest at which it passes, measured, not
guessed.  The stage report carries the table and the timings.  The measurement
also says what the nominal defaults of `Budget` cost: building `decls {} E4Ctx4`
at `sub := 6` takes about 3.7 seconds on this machine, against 0.44 milliseconds
at `sub := 2`, so a caller that does not need the deeper search should pass a
small budget rather than the default. -/

section Probes

open DotMNF.Examples

/-- E1, rule 11 at one declaration: `{A : ⊤..⊥} <: {B : {a : ⊤}..{a : ⊤}}`
through `⊤ <: x.A <: ⊥`, the chain of `badBounds`
(`lean/Coercions/DotMNF/Examples.lean:53-57`). -/
def probeE1 : Budget := { decls := 1, views := 0, sub := 2, typer := 0 }

#eval expect
  (sub? (decls probeE1 E1Ctx) probeE1.sub (E1Dom : Ty ([],x)) E1Res).isSome
  "E1: sub? does not find the bad bounds chain"

-- The same at one unit less fuel finds nothing, so the probe measures the
-- search and not an accident of the table.
#eval expect
  (! (sub? (decls probeE1 E1Ctx) 1 (E1Dom : Ty ([],x)) E1Res).isSome)
  "E1: sub? finds the chain at fuel 1, so the probe is not measuring the search"

/-- E3, rule 11 at two declarations of one variable at one label:
`{b : ⊤} <: x.A <: {a : ⊤}`, the chain of `E3sub`
(`lean/Coercions/DotMNF/Examples.lean:151`). -/
def probeE3 : Budget := { decls := 1, views := 1, sub := 2, typer := 0 }

#eval expect
  (sub? (decls probeE3 E3Ctx2) probeE3.sub (E3T2 : Ty ([],x,x)) E3T1).isSome
  "E3: sub? does not find the two declaration chain"

/-- E4, the detour view step followed by rule 9: `w` reaches `{A : Int..⊤}`
through `S <: x.B <: T`, and then `Int <: w.A`, the chain of `E4nA`
(`lean/Coercions/DotMNF/Examples.lean:213-216`).  Two rounds of the table are
the minimum: round one reads `x`'s member `B` and `w`'s member `A` at `⊥..⊤`,
round two runs the detour step on `w` and adds `w`'s member `A` at `Int..⊤`. -/
def probeE4 : Budget := { decls := 2, views := 1, sub := 2, typer := 0 }

#eval expect
  (sub? (decls probeE4 E4Ctx4) probeE4.sub (E4Int : Ty ([],x,x,x,x))
    (.sel (.var (.there (.there .here))) lA)).isSome
  "E4: sub? does not find the detour to w.A"

/-- E6, rule 9 through the self binder's own member: `Int <: x.T` where `x` is
the literal's self binder, the chain of `E6nT`
(`lean/Coercions/DotMNF/Examples.lean:335-337`).  Two rounds of the closure open
the `μ` and then take the left operand of the intersection. -/
def probeE6 : Budget := { decls := 1, views := 2, sub := 2, typer := 0 }

#eval expect
  (sub? (decls probeE6 E6Ctxz) probeE6.sub (E6Int : Ty ([],x,x))
    (.sel (.var .here) lT)).isSome
  "E6: sub? does not find the self member chain"

/-- E8, the right view step: `y : x.A ∧ {a : ⊤}` has a view at `{a : ⊤}`, which
is `E8yFld2` (`lean/Coercions/DotMNF/Examples.lean:405`). -/
def probeE8views : Budget := { decls := 0, views := 1, sub := 0, typer := 0 }

#eval expect
  ((views (decls probeE8views E8Ctx2) probeE8views (.here : BVar ([],x,x) .var)).any
    (fun v => decide (v.ty = (.fld la .top : Ty ([],x,x)))))
  "E8: the view closure of y does not reach {a : ⊤}"

/-- E8, rule 10: `x.A <: {a : ⊤}` by the upper bound of `x`'s member `A`, which
is `E8Upper` (`lean/Coercions/DotMNF/Examples.lean:412`). -/
def probeE8sub : Budget := { decls := 1, views := 0, sub := 2, typer := 0 }

#eval expect
  (sub? (decls probeE8sub E8Ctx2) probeE8sub.sub
    (.sel (.var (.there .here)) lA : Ty ([],x,x)) (.fld la .top)).isSome
  "E8: sub? does not find the upper bound step"

end Probes

end Frontend
