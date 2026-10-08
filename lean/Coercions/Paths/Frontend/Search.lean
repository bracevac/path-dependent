import Coercions.Paths.Frontend.Table
import Coercions.Paths.Frontend.Surface
import Coercions.Paths.DotMNF.Examples
import Coercions.Paths.Frontend.Look

/-!
# The subtyping search, the term views and path checking

Three things for the typer.

- The subtyping search `sub?` returns a `Sub` derivation for two types, or
  nothing.
- The term views of a context variable are the types it has as a term, each
  with its `HasTy` derivation.
- Path checking `checkPath?` returns a `PathTy` derivation of a path at a goal
  type, read off the path table of `Table.lean`.

Everything returns the derivation, so there is no soundness theorem: the result
type is the statement.  There is no completeness theorem, and subtyping in DOT
is undecidable.

## The search

`sub?` tries a fixed list of rules and returns the first success.  The middle
type of `Sub.trans` is not determined by the goal.  The search tries one family
of middles: the selections `p.A` of the declarations (`PDecl`) that the path
table found.  The declarations are a parameter.

Three rules go beyond DOT without paths: `Sub.vfld` (stable field against stable
field), `Sub.vfldToFld` (stable field against plain field) and `Sub.mu` (`μ`
against `μ`).  `Sub.mu` reads the members of the left body one by one and asks for
a self-free step between the bounds.  That step may need a subtyping at the
outer context.  The walker of this view is `Core.subDecl?` of `Look.lean`,
which takes that subtyping as an argument on the tank.  The search hands it
`sub?` as a computation that draws nothing, and runs it from an empty tank.

## Fuel

`sub?` is structural on its fuel.  Every rule that needs another subtyping calls
`sub?` at the fuel one below.  The walkers of the selection rules and of the
abstract view take that call as a function argument, so each is structural on
its own list or type.  The module reduces in the kernel, and the checks at the
end are `decide +kernel` facts.

The last alternative of `sub?` retries at the fuel one below.  It is not a rule
and changes no answer.  It makes `sub?_le`, that more fuel never loses an
answer, an induction on the difference.

## The function rule

`Sub.all` compares the codomains under `Γ.cons S2`, where the declarations are
not those of `Γ`.  The rule rebuilds a path table there, without the detour
step (`baseTable`) and at the small budget `allBudget`, because the detour step
would call the search being defined.  This table is the one approximation of
the module.

## The term views

`HasTy` has its own rules at a variable, and no rule leads from a path typing
back to a term typing except at a singleton.  So the typer keeps a closure of
term views per variable, apart from the path table.  It grows in rounds by five
steps: open a `μ`, the two sides of an intersection, the upper bound of a
declaration, and the detour through a declaration whose lower bound the search
reaches.

Nothing here belongs to the metatheory.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Ctx Sub PathTy HasTy SelfFree SubDecl)

/-! ## Casts across a decided equality

These derivations move across a decided equality of labels or of a selection.
They use `cases`, not `▸`, because the label occurs twice in the conclusion and
a rewrite would hit both. -/

/-- `Sub.fld` with the two labels equal by a decision. -/
def subFldOf {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b)
    (e : Sub Γ S T) : Sub Γ (.fld a S) (.fld b T) := by
  cases h; exact Sub.fld e

/-- `Sub.vfld` with the two labels equal by a decision. -/
def subVfldOf {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b)
    (e : Sub Γ S T) : Sub Γ (.vfld a S) (.vfld b T) := by
  cases h; exact Sub.vfld e

/-- A stable field below a plain field: `Sub.vfldToFld`, then `Sub.fld`. -/
def subVfldFldOf {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b)
    (e : Sub Γ S T) : Sub Γ (.vfld a S) (.fld b T) := by
  cases h; exact Sub.trans Sub.vfldToFld (Sub.fld e)

/-- `Sub.typ` with the two labels equal by a decision. -/
def subTypOf {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Ty s} (h : A = B)
    (e1 : Sub Γ S2 S1) (e2 : Sub Γ T1 T2) :
    Sub Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h; exact Sub.typ e1 e2

/-- The lower selection rule: `S <: d.lo <: p.A`, where `T` is that selection. -/
def subToSel {s : Sig} {Γ : Ctx s} {d : PDecl Γ} {S T : Ty s} (h : T = pdeclSel d)
    (e : Sub Γ S d.lo) : Sub Γ S T := by
  cases h; exact Sub.trans e (pdeclLower d)

/-- The upper selection rule: `p.A <: d.hi <: T`, where `S` is that selection. -/
def subFromSel {s : Sig} {Γ : Ctx s} {d : PDecl Γ} {S T : Ty s} (h : S = pdeclSel d)
    (e : Sub Γ d.hi T) : Sub Γ S T := by
  cases h; exact Sub.trans (pdeclUpper d) e

/-- The one family of transitivity middles: `S <: d1.lo <: p.A <: d2.hi <: T`.
The two declarations may differ, as long as they select the same `p.A`. -/
def subThroughPair {s : Sig} {Γ : Ctx s} {d1 d2 : PDecl Γ} {S T : Ty s}
    (h : pdeclSel d2 = pdeclSel d1) (e1 : Sub Γ S d1.lo) (e2 : Sub Γ d2.hi T) :
    Sub Γ S T :=
  Sub.trans e1 (Sub.trans (pdeclLower d1) (Sub.trans (h ▸ pdeclUpper d2) e2))

/-- The pairs of declarations the pair rule walks. -/
def declPairs {s : Sig} {Γ : Ctx s} (D : List (PDecl Γ)) : List (PDecl Γ × PDecl Γ) :=
  D.flatMap (fun d1 => D.map (fun d2 => (d1, d2)))

/-! ## The walkers of the selection rules

Each walks a list of declarations, or of pairs, and asks the search it is
handed for the remaining subtyping.  `sub?` passes itself at the lower fuel. -/

/-- The lower selection rule: a declaration whose selection is `T`. -/
def pickLower {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) :
    List (PDecl Γ) → (S T : Ty s) → Option (Sub Γ S T)
  | [], _, _ => none
  | d :: ds, S, T =>
      (if h : T = pdeclSel d then (sub S d.lo).map (fun e => subToSel h e)
       else none).orElse fun _ => pickLower sub ds S T
termination_by structural ds => ds

/-- The upper selection rule: a declaration whose selection is `S`. -/
def pickUpper {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) :
    List (PDecl Γ) → (S T : Ty s) → Option (Sub Γ S T)
  | [], _, _ => none
  | d :: ds, S, T =>
      (if h : S = pdeclSel d then (sub d.hi T).map (fun e => subFromSel h e)
       else none).orElse fun _ => pickUpper sub ds S T
termination_by structural ds => ds

/-- The pair rule: two declarations of one path at one label. -/
def pickPair {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) :
    List (PDecl Γ × PDecl Γ) → (S T : Ty s) → Option (Sub Γ S T)
  | [], _, _ => none
  | (d1, d2) :: ps, S, T =>
      (if h : pdeclSel d2 = pdeclSel d1 then do
          let e1 ← sub S d1.lo
          let e2 ← sub d2.hi T
          some (subThroughPair h e1 e2)
       else none).orElse fun _ => pickPair sub ps S T
termination_by structural ps => ps

/-! ## The subtyping search

Each rule is a decided equality or a `match` whose fall-through is `none`.  A
`match` on `S` or `T` generalizes them in the motive, so a fall-through cannot
return a derivation of the original goal. -/

/-- The budget of the table that the function rule rebuilds.  It is small
because the table is rebuilt at every application. -/
def allBudget : Budget := { table := 2, views := 0, sub := 0, typer := 0, rows := 4 }

/-- The subtyping search.  `sub? D 0 S T` is `none`.  `sub? D (n+1) S T` tries
the rules below in order and returns the first success.  Premises are searched
at fuel `n`.

1. `S = T`, `Sub.refl`.
2. `T = ⊤`, `Sub.top`.
3. `S = ⊥`, `Sub.bot`.
4. `T = T1 ∧ T2`, `Sub.and`.
5. `S = S1 ∧ S2`, `Sub.trans` with `Sub.and1` or `Sub.and2`.
6. `{a : S'}` against `{a : T'}` by `Sub.fld`, `{val a : S'}` against
   `{val a : T'}` by `Sub.vfld`, and `{val a : S'}` against `{a : T'}` by
   `Sub.vfldToFld` then `Sub.fld`.
7. `{A : S1..T1}` against `{A : S2..T2}`, `Sub.typ`.
8. `∀(x : S1) T1` against `∀(x : S2) T2`, `Sub.all`, with the codomains
   compared under `Γ.cons S2` against a table rebuilt there.
9. `μ(z. L)` against `μ(z. R)`, both declaration shaped, `Sub.mu` with the
   abstract view `Core.subDecl?`.
10. `T = p.A` at a declaration, `Sub.selLower`.
11. `S = p.A` at a declaration, `Sub.selUpper`.
12. A pair of declarations of one path at one label, `S <: d1.lo <: p.A <:
    d2.hi <: T`.

The last alternative retries at fuel `n`.  It changes no answer and makes
`sub?_le` an induction on the difference. -/
def sub? {s : Sig} {Γ : Ctx s} (D : List (PDecl Γ)) :
    (n : Nat) → (S T : Ty s) → Option (Sub Γ S T)
  | 0, _, _ => none
  | n + 1, S, T =>
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
        | .vfld a S', .vfld b T' =>
            if h : a = b then (sub? D n S' T').map (fun e => subVfldOf h e) else none
        | .vfld a S', .fld b T' =>
            if h : a = b then (sub? D n S' T').map (fun e => subVfldFldOf h e) else none
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
            let e2 ← sub? (declsOf (baseTable allBudget (Γ.cons S2))) n T1 T2
            some (Sub.all e1 e2)
        | _, _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 9
      ((match S, T with
        | .mu L, .mu R =>
            if hL : Ty.Decl L then
              if hR : Ty.Decl R then
                (Core.subDecl? (fun S' T' => Frontend.Fuel.Fu.ret (sub? D n S' T')) L R
                  ⟨0, false⟩).1.map (fun e => Sub.mu e hL hR)
              else none
            else none
        | _, _ => none : Option (Sub Γ S T))).orElse fun _ =>
      -- 10 and 11
      (pickLower (sub? D n) D S T).orElse fun _ =>
      (pickUpper (sub? D n) D S T).orElse fun _ =>
      -- 12
      (pickPair (sub? D n) (declPairs D) S T).orElse fun _ =>
      -- the retry
      sub? D n S T
termination_by structural n => n

/-! ## Fuel monotonicity

The statement is about `isSome`, not derivations: more fuel may find another
derivation of the same judgment. -/

/-- An `orElse` succeeds when its second alternative does. -/
theorem isSome_orElse_right {α : Type u} {a : Option α} {b : Unit → Option α}
    (h : (b ()).isSome = true) : (a.orElse b).isSome = true := by
  cases a with
  | none => simpa [Option.orElse] using h
  | some x => rfl

/-- One more unit of fuel never loses an answer. -/
theorem sub?_succ {s : Sig} {Γ : Ctx s} {D : List (PDecl Γ)} {n : Nat} {S T : Ty s}
    (h : (sub? D n S T).isSome) : (sub? D (n + 1) S T).isSome := by
  rw [sub?.eq_def]
  iterate 12 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses an answer. -/
theorem sub?_le {s : Sig} {Γ : Ctx s} {D : List (PDecl Γ)} : ∀ {n n' : Nat}, n ≤ n' →
    ∀ {S T : Ty s}, (sub? D n S T).isSome → (sub? D n' S T).isSome := by
  intro n n' h
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => sub?_succ (ih hs)

/-! ## The path table at the search

`Table.lean` defines the table against an abstract search.  Here it is
instantiated at `sub?`.  The detour step of a round consults `sub?` at the
declarations of the table at the start of the round. -/

/-- The path table of a context at a budget, the detour step consulting
`sub?` at fuel `b.sub`. -/
def table {s : Sig} (b : Budget) (Γ : Ctx s) : PTable Γ :=
  tableAt (fun n D => sub? D n) b

/-- More rounds never lose a type at a path, for fixed search fuel and row
cap. -/
theorem table_mono' {s : Sig} {Γ : Ctx s} {b b' : Budget} (h : b.table ≤ b'.table)
    (hs : b.sub = b'.sub) (hr : b.rows = b'.rows) :
    ∀ (p : Path s) (v : PView Γ p), v ∈ (table b Γ).viewsAt p →
      ∃ w ∈ (table b' Γ).viewsAt p, w.ty = v.ty :=
  table_mono _ h hs hr

/-! ## Path checking

`checkPath?` tries three clauses in order: the singleton of the path itself by
`PathTy.snglRefl`, a view of the table at exactly the goal, and a view the
search takes to the goal by `PathTy.sub`.  It never uses `PathTy.recI` or
`PathTy.andI`. -/

/-- A path typing of `p` at `T`, read off the views `tbl` holds for `p`. -/
def checkPath? {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (D : List (PDecl Γ)) (n : Nat)
    (p : Path s) (T : Ty s) : Option (PathTy Γ p T) :=
  let vs := tbl.viewsAt p
  ((if h : T = .sngl p then (vs.head?.map fun v => h ▸ PathTy.snglRefl v.deriv) else none :
      Option (PathTy Γ p T))).orElse fun _ =>
  (vs.findSome? fun v => if h : v.ty = T then some (h ▸ v.deriv) else none).orElse fun _ =>
  vs.findSome? fun v => (sub? D n v.ty T).map fun e => PathTy.sub v.deriv e

/-! ## The term views

A view of a context variable is a type it has as a term, with the derivation.
`viewStepOf` defines the five steps against an abstract search. -/

/-- A type a context variable has, with the derivation that it has it. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ (.path x) ty

/-- One step of the closure, uniform in the variable. -/
def ViewStep {s : Sig} (Γ : Ctx s) : Type :=
  (x : BVar s .var) → View Γ x → List (View Γ x)

/-- The five steps, against an abstract search.

| step | condition on `v.ty` | new view | rule |
|---|---|---|---|
| open | `μ(z. T)` and `Ty.Decl T` | `T[z := x]` | `HasTy.recE` |
| left | `S ∧ T` | `S` | `HasTy.sub` with `Sub.and1` |
| right | `S ∧ T` | `T` | `HasTy.sub` with `Sub.and2` |
| upper | `v.ty = p.A` at a declaration `d` | `d.hi` | `HasTy.sub` with `Sub.selUpper` |
| detour | `sub v.ty d.lo` succeeds at a `d` | `d.hi` | `HasTy.sub` with `Sub.trans` | -/
def viewStepOf {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) (D : List (PDecl Γ)) : ViewStep Γ :=
  fun x v =>
    (match hv : v.ty with
      | .mu T =>
          if hd : Ty.Decl T then [⟨T.substVar x, .recE (hv ▸ v.deriv) hd⟩] else []
      | .and S T =>
          [⟨S, .sub (hv ▸ v.deriv) .and1⟩, ⟨T, .sub (hv ▸ v.deriv) .and2⟩]
      | _ => [])
    ++ D.filterMap (fun d =>
        if h : v.ty = pdeclSel d then some ⟨d.hi, .sub (h ▸ v.deriv) (pdeclUpper d)⟩
        else none)
    ++ D.filterMap (fun d =>
        (sub v.ty d.lo).map (fun e =>
          ⟨d.hi, .sub v.deriv (Sub.trans e (Sub.trans (pdeclLower d) (pdeclUpper d)))⟩))

/-- Views whose type is already in `seen` are dropped. -/
def dedupViewsFrom {s : Sig} {Γ : Ctx s} {x : BVar s .var} (seen : List (Ty s)) :
    List (View Γ x) → List (View Γ x)
  | [] => []
  | v :: vs =>
      if tyMem? v.ty seen then dedupViewsFrom seen vs
      else v :: dedupViewsFrom (v.ty :: seen) vs
termination_by structural vs => vs

/-- Keep the first view of each type. -/
def dedupViews {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    List (View Γ x) :=
  dedupViewsFrom [] vs

/-- One round: every view of the list plus one step from each, duplicates by
type dropped. -/
def viewsRoundOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (x : BVar s .var)
    (vs : List (View Γ x)) : List (View Γ x) :=
  dedupViews (vs ++ vs.flatMap (st x))

/-- The closure of the declared type of a variable under `m` rounds. -/
def viewsOf {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) : Nat → (x : BVar s .var) → List (View Γ x)
  | 0, x => [⟨Γ.lookup x, .var⟩]
  | m + 1, x => viewsRoundOf st x (viewsOf st m x)
termination_by structural m => m

/-- The five steps at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : List (PDecl Γ)) (n : Nat) : ViewStep Γ :=
  viewStepOf (sub? D n) D

/-- The term views of a variable: `b.views` rounds, the detour step searching at
fuel `b.sub`.  `D` is the declarations of the context's path table. -/
def views {s : Sig} {Γ : Ctx s} (D : List (PDecl Γ)) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.sub) b.views x

/-! ## Round monotonicity of the term views

More rounds never lose a type.  The statement is about types, not derivations,
because deduplication keeps the first derivation of each type. -/

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
  induction h with
  | refl => exact viewsLe_refl _
  | step _ ih => exact viewsLe_trans ih (viewsRoundOf_covers st x _)

/-- More rounds of the term views never lose a type. -/
theorem views_mono {s : Sig} {Γ : Ctx s} {D : List (PDecl Γ)} {b b' : Budget}
    (h : b.views ≤ b'.views) (hs : b.sub = b'.sub) (x : BVar s .var) :
    ∀ v ∈ views D b x, ∃ w ∈ views D b' x, w.ty = v.ty := by
  unfold views
  rw [hs]
  exact viewsOf_mono (viewStep D b'.sub) h x

/-! ## Probes

Each probe names the chain of `lean/Coercions/Paths/DotMNF/Examples.lean` it
reproduces and a budget at which the search finds it.  A negative check one
unit of one counter below shows that the counter matters.  All are
`decide +kernel` facts. -/

section Probes

open Paths.DotMNF.Examples

/-- The search at a budget, against the declarations of the path table. -/
def subProbe {s : Sig} (b : Budget) (Γ : Ctx s) (S T : Ty s) : Bool :=
  (sub? (declsOf (table b Γ)) b.sub S T).isSome

/-- Path checking at a budget, against the context's path table. -/
def pathProbe {s : Sig} (b : Budget) (Γ : Ctx s) (p : Path s) (T : Ty s) : Bool :=
  let tbl := table b Γ
  (checkPath? tbl (declsOf tbl) b.sub p T).isSome

/-- E1, the pair rule at one declaration: `{A : ⊤..⊥} <: {B : {a : ⊤}..{a : ⊤}}`
through `⊤ <: x.A <: ⊥`, the chain of `badBounds`.  The seed of the table holds
the declaration. -/
def probeE1 : Budget := { table := 0, views := 0, sub := 2, typer := 0, rows := 0 }

example : subProbe probeE1 E1Ctx (E1Dom : Ty ([],x)) E1Res = true := by decide +kernel
example : subProbe { probeE1 with sub := 1 } E1Ctx (E1Dom : Ty ([],x)) E1Res = false := by
  decide +kernel

/-- E3, the pair rule at two declarations of one path at one label:
`{b : ⊤} <: x.A <: {a : ⊤}`, the chain of `E3sub`.  One round splits the
intersection that declares `A` twice. -/
def probeE3 : Budget := { table := 1, views := 0, sub := 2, typer := 0, rows := 0 }

example : subProbe probeE3 E3Ctx2 (E3T2 : Ty ([],x,x)) E3T1 = true := by decide +kernel
example : subProbe { probeE3 with table := 0 } E3Ctx2 (E3T2 : Ty ([],x,x)) E3T1 = false := by
  decide +kernel

/-- E4, the detour step of the table, then the lower selection rule: `w` reaches
`{A : Int..⊤}` through `S <: x.B <: T`, then `Int <: w.A`, the chain of
`E4nA`. -/
def probeE4 : Budget := { table := 1, views := 0, sub := 2, typer := 0, rows := 0 }

example : subProbe probeE4 E4Ctx4 (E4Int : Ty ([],x,x,x,x))
    (.sel (.var (.there (.there .here))) lA) = true := by decide +kernel
example : subProbe { probeE4 with table := 0 } E4Ctx4 (E4Int : Ty ([],x,x,x,x))
    (.sel (.var (.there (.there .here))) lA) = false := by decide +kernel
/-- Without the detour step the table never has the member. -/
example : (sub? (declsOf (baseTable probeE4 E4Ctx4)) probeE4.sub (E4Int : Ty ([],x,x,x,x))
    (.sel (.var (.there (.there .here))) lA)).isSome = false := by decide +kernel

/-- E6, the lower selection rule at the self binder's own member: `Int <: x.T`
where `x` is the literal's self binder, the chain of `E6nT`.  Two rounds open
the `μ` and take the left side of the intersection. -/
def probeE6 : Budget := { table := 2, views := 0, sub := 2, typer := 0, rows := 0 }

example : subProbe probeE6 E6Ctxz (E6Int : Ty ([],x,x)) (.sel (.var .here) lT) = true := by
  decide +kernel
example : subProbe { probeE6 with table := 1 } E6Ctxz (E6Int : Ty ([],x,x))
    (.sel (.var .here) lT) = false := by decide +kernel

/-- E8, the right step of the term views: `y : x.A ∧ {a : ⊤}` has the view
`{a : ⊤}`, which is `E8yFld2`. -/
def probeE8views : Budget := { table := 0, views := 1, sub := 0, typer := 0, rows := 0 }

example : ((views (declsOf (table probeE8views E8Ctx2)) probeE8views
    (.here : BVar ([],x,x) .var)).any (fun v => decide (v.ty = (.fld la .top : Ty ([],x,x)))))
    = true := by decide +kernel
example : ((views (declsOf (table probeE8views E8Ctx2)) { probeE8views with views := 0 }
    (.here : BVar ([],x,x) .var)).any (fun v => decide (v.ty = (.fld la .top : Ty ([],x,x)))))
    = false := by decide +kernel

/-- E8, the upper selection rule: `x.A <: {a : ⊤}` by the upper bound of `x`'s
member `A`, which is `E8Upper`. -/
def probeE8sub : Budget := { table := 0, views := 0, sub := 2, typer := 0, rows := 0 }

example : subProbe probeE8sub E8Ctx2 (.sel (.var (.there .here)) lA : Ty ([],x,x))
    (.fld la .top) = true := by decide +kernel
example : subProbe { probeE8sub with sub := 1 } E8Ctx2
    (.sel (.var (.there .here)) lA : Ty ([],x,x)) (.fld la .top) = false := by decide +kernel

/-- E1p, the pair rule at the path `w.f`: `{val f : {A : ⊤..⊥}} <: {B : …}`
through `⊤ <: w.f.A <: ⊥`, the chain of `E1p_badBounds`.  One round makes the
row `w.f`. -/
def probeE1p : Budget := { table := 1, views := 0, sub := 2, typer := 0, rows := 1 }

example : subProbe probeE1p E1p_Ctx1 (E1p_Dom : Ty ([],x)) E1p_Res = true := by decide +kernel
example : subProbe { probeE1p with table := 0 } E1p_Ctx1 (E1p_Dom : Ty ([],x)) E1p_Res
    = false := by decide +kernel
/-- With no new row allowed, the row `w.f` never appears. -/
example : subProbe { probeE1p with rows := 0 } E1p_Ctx1 (E1p_Dom : Ty ([],x)) E1p_Res
    = false := by decide +kernel

/-- X1, `x.c.A <: x.B` and back, a path of length two.  `x.B` has both bounds
`x.c.A`, so either selection rule closes the chain once the table has opened
`x` and split its body. -/
def probeX1 : Budget := { table := 2, views := 0, sub := 2, typer := 0, rows := 1 }

example : subProbe probeX1 X1_Ctx (.sel (.sel (.var .here) X1_lc) lA : Ty ([],x))
    (.sel (.var .here) lB) = true := by decide +kernel
example : subProbe probeX1 X1_Ctx (.sel (.var .here) lB : Ty ([],x))
    (.sel (.sel (.var .here) X1_lc) lA) = true := by decide +kernel
example : subProbe { probeX1 with table := 1 } X1_Ctx
    (.sel (.sel (.var .here) X1_lc) lA : Ty ([],x)) (.sel (.var .here) lB) = false := by
  decide +kernel

/-- E9, `y.B <: N` under `y : q.type`: the second round copies `q`'s member `B`
to `y`, after the first has opened `q`. -/
def probeE9 : Budget := { table := 2, views := 0, sub := 2, typer := 0, rows := 1 }

example : subProbe probeE9 E9_Γ4 (.sel (.var (.there .here)) lB) E9_N = true := by decide +kernel
example : subProbe { probeE9 with table := 1 } E9_Γ4 (.sel (.var (.there .here)) lB) E9_N
    = false := by decide +kernel

/-- E2p, the argument of `f f`: `f`'s type `∀(y : x.c.A) x.c.A` is below
`x.c.A` by the lower selection rule at the path `x.c`.  Four rounds: open `x`,
the child row `x.c`, open `x.c`, the left side of its body. -/
def probeE2p : Budget := { table := 4, views := 0, sub := 2, typer := 0, rows := 1 }

example : subProbe probeE2p E2p_Γ3 (E2p_Γ3.lookup .here) (E2p_xcA (.there (.there .here)))
    = true := by decide +kernel
example : subProbe { probeE2p with table := 3 } E2p_Γ3 (E2p_Γ3.lookup .here)
    (E2p_xcA (.there (.there .here))) = false := by decide +kernel

/-- `μ(z. {A : ⊥..⊤} ∧ {a : {b : ⊤} ∧ {v : ⊤}})`. -/
def probeMuL : Ty [] :=
  .mu (.and (.typ lA .bot .top) (.fld la (.and (.fld lb .top) (.fld lv .top))))
/-- `μ(z. {a : {b : ⊤}})`. -/
def probeMuR : Ty [] := .mu (.fld la (.fld lb .top))

/-- The abstract view.  The field bound takes the self-free step `closed`, whose
subtyping needs two more units of fuel. -/
example : subProbe { table := 0, views := 0, sub := 3, typer := 0, rows := 0 } .nil
    probeMuL probeMuR = true := by decide +kernel
example : subProbe { table := 0, views := 0, sub := 2, typer := 0, rows := 0 } .nil
    probeMuL probeMuR = false := by decide +kernel
/-- A stable field is read as a field inside the abstract view, and not back. -/
example : subProbe { table := 0, views := 0, sub := 1, typer := 0, rows := 0 } .nil
    (.mu (.vfld la .top)) (.mu (.fld la .top)) = true := by decide +kernel
example : subProbe { table := 0, views := 0, sub := 4, typer := 0, rows := 0 } .nil
    (.mu (.fld la .top)) (.mu (.vfld la .top)) = false := by decide +kernel

/-- `∀(y : {A : ⊥..{a : ⊤}}) y.A`. -/
def probeAllL : Ty [] := .all (.typ lA .bot (.fld la .top)) (.sel (.var .here) lA)
/-- `∀(y : {A : ⊥..{a : ⊤}}) {a : ⊤}`. -/
def probeAllR : Ty [] := .all (.typ lA .bot (.fld la .top)) (.fld la .top)

/-- The function rule.  The upper selection rule reads `y`'s member in the
rebuilt table. -/
example : subProbe { table := 0, views := 0, sub := 3, typer := 0, rows := 0 } .nil
    probeAllL probeAllR = true := by decide +kernel
example : subProbe { table := 0, views := 0, sub := 2, typer := 0, rows := 0 } .nil
    probeAllL probeAllR = false := by decide +kernel

/-! Path checking under X3's context `x : {val a : {val b : ⊤}}, y : (x.a).type`.
The checks cover the singleton of `y` by `snglRefl`, the declared singleton of
`y` as a view at the goal, `x.a : {b : ⊤}` by the search from the view
`{val b : ⊤}`, and `y : {val b : ⊤}` through the alias in the second round. -/

example : pathProbe { table := 0, views := 0, sub := 0, typer := 0, rows := 0 } X3_CtxY
    (.var .here) (.sngl (.var .here)) = true := by decide +kernel
example : pathProbe { table := 0, views := 0, sub := 0, typer := 0, rows := 0 } X3_CtxY
    (.var .here) (.sngl (.sel (.var (.there .here)) la)) = true := by decide +kernel
example : pathProbe { table := 1, views := 0, sub := 2, typer := 0, rows := 1 } X3_CtxY
    (.sel (.var (.there .here)) la) (.fld lb .top) = true := by decide +kernel
example : pathProbe { table := 1, views := 0, sub := 1, typer := 0, rows := 1 } X3_CtxY
    (.sel (.var (.there .here)) la) (.fld lb .top) = false := by decide +kernel
example : pathProbe { table := 2, views := 0, sub := 0, typer := 0, rows := 1 } X3_CtxY
    (.var .here) (.vfld lb .top) = true := by decide +kernel
example : pathProbe { table := 1, views := 0, sub := 0, typer := 0, rows := 1 } X3_CtxY
    (.var .here) (.vfld lb .top) = false := by decide +kernel

end Probes

end PathsFrontend
