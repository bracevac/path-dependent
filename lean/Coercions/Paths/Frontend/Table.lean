import Coercions.Paths.Frontend.Decide

/-!
# The path table

A *view* of a path is a type the path has, carried with its path typing
derivation.  The typer needs views of paths, not only of variables.  A field is
read off a path view (`HasTy.projP`), and a selection `p.A` is bounded through a
type member that the path `p` has (`Sub.selUpper`, `Sub.selLower`).  The *path
table* of a context holds those views.  It is a list of rows, one row per path,
each with the views found for that path so far.  The *declarations* of the table
are its views of the form `{A : S..T}`, keyed by their path.  They are the
middles the subtyping search tries for `Sub.trans`, whose middle is otherwise
undetermined.

## How the table grows

The table starts with one row per context variable, at the variable's declared
type (`PathTy.var`).  It then grows in rounds.  One round applies ten steps to
each view of each row.  Six of them add a view to the same row.

| step | view at `p` | new view at `p` | rule |
|---|---|---|---|
| open | `μ(z. T)`, `Ty.Decl T` decided | `T[z := p]` | `PathTy.recE` |
| left, right | `S ∧ T` | `S` and `T` | `PathTy.sub` with `Sub.and1`, `Sub.and2` |
| field | `{val a : T}` | `{a : T}` | `PathTy.sub` with `Sub.vfldToFld` |
| upper | `q.A`, a declaration of the table at `q.A` | its upper bound | `PathTy.sub` with `Sub.selUpper` |
| detour | `T`, a declaration whose lower bound the search puts above `T` | its upper bound | `PathTy.sub` with `Sub.trans`, `Sub.selLower`, `Sub.selUpper` |
| alias | `q.type` | every view of the row `q` | `PathTy.snglTrans` |

The other four add a view to another row, which may be new.

| step | view at `p` | new view | rule |
|---|---|---|---|
| child | `{val a : T}` | `T` at `p.a` | `PathTy.sel` |
| reverse | `q.type` | `p.type` at `q` | `PathTy.snglSym` with `PathTy.snglInv` |
| aliased | `q.type` | `⊤` at `q` | `PathTy.snglInv` |
| alias field | `q.type` and `{val a : T}` | `(q.a).type` at `p.a` | `PathTy.snglSel` |

The reverse step needs a view of `q` as its second premise.  It takes `⊤`, the
view the aliased step builds, so it does not wait for a row of `q`.

## Bounds

Three things bound the table.  Views are deduplicated by type after every
round, and the first view of each type is kept.  The number of rounds is a
counter of its own, `Budget.table`.  And the new rows one round may add are
capped by `Budget.rows`.  A view aimed at an existing row is always merged, cap
or not.

Deduplication does not bound the rows.  Under `x : μ(z. {val a : z.type})` the
row `x.a` aliases `x`, copies its stable field and grows the row `x.a.a`, and
so on, one new row every two rounds.  Every new row has a new path, so no type
is ever a duplicate there.  Only the round counter stops that growth.  The cap
bounds the rows a single round adds, in any context.

## The search the detour step consults

The detour step asks a subtyping search.  The search lives in a later module
and takes the declarations of the table as its own parameter.  So every
definition here takes the search as an argument, as a function from the
declarations of the current table to a search over the context.  The later
module instantiates it at the real search.  It also instantiates it at the
search that finds nothing, `noSub`, for the table it rebuilds under an
extended context when it compares two function types.

## Monotonicity

A round keeps every row and every type of every row.  The steps only append,
merging only appends, and deduplication keeps the first view of each type.  So
more rounds never lose a type at a path, which is `table_mono`.  The statement
is about types, not derivations.  Deduplication may keep another derivation of
the same type at a larger budget.

Every recursive definition is structural, so the table reduces in the kernel
and the tests at the end are `by decide`.  Nothing here is part of the
metatheory, and no definition lives in the `Paths.DotMNF` or `Paths.FCdot`
namespaces.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Ctx Sub PathTy)

/-! ## Views, rows and declarations -/

/-- A type a path has, with the path typing that it has it. -/
structure PView {s : Sig} (Γ : Ctx s) (p : Path s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : PathTy Γ p ty

/-- A view moved along an equation of paths.  The type does not change. -/
def castView {s : Sig} {Γ : Ctx s} {p q : Path s} (h : p = q) (v : PView Γ p) : PView Γ q :=
  ⟨v.ty, h ▸ v.deriv⟩

/-- A row of the table: a path and the views found for it so far. -/
structure Row {s : Sig} (Γ : Ctx s) where
  /-- The path. -/
  path : Path s
  /-- Its views, oldest first. -/
  views : List (PView Γ path)

/-- The types of a row, without their derivations. -/
def Row.tys {s : Sig} {Γ : Ctx s} (r : Row Γ) : List (Ty s) := r.views.map PView.ty

/-- The path table of a context. -/
abbrev PTable {s : Sig} (Γ : Ctx s) := List (Row Γ)

/-- Every view the table holds for a path, from every row of that path. -/
def PTable.viewsAt {s : Sig} {Γ : Ctx s} : PTable Γ → (q : Path s) → List (PView Γ q)
  | [], _ => []
  | r :: rs, q =>
      (if h : r.path = q then r.views.map (castView h) else []) ++ PTable.viewsAt rs q
termination_by structural tbl _ => tbl

/-- A type member a path has, with the path typing.  The four data fields are
what the search compares. -/
structure PDecl {s : Sig} (Γ : Ctx s) where
  /-- The path the member is read off. -/
  path : Path s
  /-- The label of the member. -/
  lbl : Label
  /-- The lower bound. -/
  lo : Ty s
  /-- The upper bound. -/
  hi : Ty s
  /-- The derivation. -/
  deriv : PathTy Γ path (.typ lbl lo hi)

/-- The selection a declaration licenses, `p.A`. -/
def pdeclSel {s : Sig} {Γ : Ctx s} (d : PDecl Γ) : Ty s := .sel d.path d.lbl

/-- `<:-Sel` at a declaration of the table. -/
def pdeclLower {s : Sig} {Γ : Ctx s} (d : PDecl Γ) : Sub Γ d.lo (pdeclSel d) :=
  Sub.selLower d.deriv

/-- `Sel-<:` at a declaration of the table. -/
def pdeclUpper {s : Sig} {Γ : Ctx s} (d : PDecl Γ) : Sub Γ (pdeclSel d) d.hi :=
  Sub.selUpper d.deriv

/-- The `.typ` views of one row, as declarations. -/
def declsOfViews {s : Sig} {Γ : Ctx s} {p : Path s} : List (PView Γ p) → List (PDecl Γ)
  | [] => []
  | v :: vs =>
      (match hv : v.ty with
        | .typ A L U => [⟨p, A, L, U, hv ▸ v.deriv⟩]
        | _ => []) ++ declsOfViews vs
termination_by structural vs => vs

/-- The declarations of a table, row by row. -/
def declsOf {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) : List (PDecl Γ) :=
  tbl.flatMap fun r => declsOfViews r.views

/-! ## The budget and the abstract search -/

/-- The five counters of the typer.  `table` and `rows` bound the path table,
`views` the views of a variable at term level, `sub` the subtyping search and
`typer` the typer.  The defaults are a starting point, not a measurement. -/
structure Budget where
  /-- Rounds of the path table. -/
  table : Nat := 5
  /-- Rounds of the term views of a variable. -/
  views : Nat := 3
  /-- Fuel of the subtyping search. -/
  sub : Nat := 4
  /-- Fuel of the typer. -/
  typer : Nat := 20
  /-- New rows one round of the path table may add. -/
  rows : Nat := 16
deriving Repr, Inhabited

/-- A subtyping search over a fixed context. -/
def SubSearch {s : Sig} (Γ : Ctx s) : Type := (S T : Ty s) → Option (Sub Γ S T)

/-- The search that finds nothing. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-! ## The steps that stay at one path -/

/-- Open, left, right and field: the steps read off the view alone. -/
def shapeSteps {s : Sig} {Γ : Ctx s} {p : Path s} (v : PView Γ p) : List (PView Γ p) :=
  match hv : v.ty with
  | .mu T => if hd : Ty.Decl T then [⟨T.substPath p, .recE (hv ▸ v.deriv) hd⟩] else []
  | .and S T => [⟨S, .sub (hv ▸ v.deriv) .and1⟩, ⟨T, .sub (hv ▸ v.deriv) .and2⟩]
  | .vfld a T => [⟨.fld a T, .sub (hv ▸ v.deriv) .vfldToFld⟩]
  | _ => []

/-- Upper: a view that is the selection of a declaration has its upper bound. -/
def upperSteps {s : Sig} {Γ : Ctx s} {p : Path s} (D : List (PDecl Γ)) (v : PView Γ p) :
    List (PView Γ p) :=
  D.filterMap fun d =>
    if h : v.ty = pdeclSel d then some ⟨d.hi, .sub (h ▸ v.deriv) (pdeclUpper d)⟩ else none

/-- Detour: a view below the lower bound of a declaration has its upper bound.
The derivation carries the evidence the search returns. -/
def detourSteps {s : Sig} {Γ : Ctx s} {p : Path s} (sub : SubSearch Γ) (D : List (PDecl Γ))
    (v : PView Γ p) : List (PView Γ p) :=
  D.filterMap fun d =>
    (sub v.ty d.lo).map fun e =>
      ⟨d.hi, .sub v.deriv (Sub.trans e (Sub.trans (pdeclLower d) (pdeclUpper d)))⟩

/-- Alias: a path at `q.type` has every view the table holds for `q`. -/
def aliasSteps {s : Sig} {Γ : Ctx s} {p : Path s} (tbl : PTable Γ) (v : PView Γ p) :
    List (PView Γ p) :=
  match hv : v.ty with
  | .sngl q => (tbl.viewsAt q).map fun w => ⟨w.ty, .snglTrans (hv ▸ v.deriv) w.deriv⟩
  | _ => []

/-- The six steps that add a view to the row of `p`, in the order of the
table in the module comment. -/
def localSteps {s : Sig} {Γ : Ctx s} (sub : SubSearch Γ) (D : List (PDecl Γ)) (tbl : PTable Γ)
    (p : Path s) (v : PView Γ p) : List (PView Γ p) :=
  shapeSteps v ++ upperSteps D v ++ detourSteps sub D v ++ aliasSteps tbl v

/-! ## The steps that reach another row -/

/-- Child: a stable field `{val a : T}` of `p` is the view `T` of `p.a`. -/
def childSteps {s : Sig} {Γ : Ctx s} {p : Path s} (v : PView Γ p) : List (Row Γ) :=
  match hv : v.ty with
  | .vfld a T => [⟨.sel p a, [⟨T, .sel (hv ▸ v.deriv)⟩]⟩]
  | _ => []

/-- Reverse: `p : q.type` gives `q : p.type`. -/
def reverseSteps {s : Sig} {Γ : Ctx s} {p : Path s} (v : PView Γ p) : List (Row Γ) :=
  match hv : v.ty with
  | .sngl q => [⟨q, [⟨.sngl p, .snglSym (hv ▸ v.deriv) (.snglInv (hv ▸ v.deriv))⟩]⟩]
  | _ => []

/-- Aliased: the path a singleton names is well typed, at `⊤`. -/
def aliasedSteps {s : Sig} {Γ : Ctx s} {p : Path s} (v : PView Γ p) : List (Row Γ) :=
  match hv : v.ty with
  | .sngl q => [⟨q, [⟨.top, .snglInv (hv ▸ v.deriv)⟩]⟩]
  | _ => []

/-- Alias field: `p : q.type` and a stable field `a` of `p` give
`p.a : (q.a).type`.  `vs` is the whole row of `p`, where the stable field is
looked for. -/
def aliasFieldSteps {s : Sig} {Γ : Ctx s} {p : Path s} (vs : List (PView Γ p))
    (v : PView Γ p) : List (Row Γ) :=
  match hv : v.ty with
  | .sngl q =>
      vs.filterMap fun w =>
        match hw : w.ty with
        | .vfld a _ =>
            some ⟨.sel p a, [⟨.sngl (.sel q a), .snglSel (hv ▸ v.deriv) (hw ▸ w.deriv)⟩]⟩
        | _ => none
  | _ => []

/-- The four steps that reach another row, in the order of the table in the
module comment. -/
def remoteSteps {s : Sig} {Γ : Ctx s} (p : Path s) (vs : List (PView Γ p)) (v : PView Γ p) :
    List (Row Γ) :=
  childSteps v ++ reverseSteps v ++ aliasedSteps v ++ aliasFieldSteps vs v

/-! ## Deduplication, merging and the row cap -/

/-- Membership of a type in a list of types, as a decision. -/
def tyMem? {s : Sig} (T : Ty s) : List (Ty s) → Bool
  | [] => false
  | U :: Us => if U = T then true else tyMem? T Us
termination_by structural Us => Us

theorem tyMem?_nil {s : Sig} (T : Ty s) : tyMem? T [] = false := rfl

theorem tyMem?_cons {s : Sig} (T U : Ty s) (Us : List (Ty s)) :
    tyMem? T (U :: Us) = true ↔ (U = T ∨ tyMem? T Us = true) := by
  by_cases h : U = T
  · simp [tyMem?, h]
  · simp [tyMem?, h]

/-- Views whose type is already in `seen` are dropped. -/
def dedupPViewsFrom {s : Sig} {Γ : Ctx s} {p : Path s} (seen : List (Ty s)) :
    List (PView Γ p) → List (PView Γ p)
  | [] => []
  | v :: vs =>
      if tyMem? v.ty seen then dedupPViewsFrom seen vs
      else v :: dedupPViewsFrom (v.ty :: seen) vs
termination_by structural vs => vs

/-- A row with the first view of each type kept. -/
def dedupRow {s : Sig} {Γ : Ctx s} (r : Row Γ) : Row Γ :=
  ⟨r.path, dedupPViewsFrom [] r.views⟩

/-- Append the views of `r` to the row of the same path, if the table has one. -/
def mergeRow? {s : Sig} {Γ : Ctx s} : PTable Γ → Row Γ → Option (PTable Γ)
  | [], _ => none
  | r0 :: rs, r =>
      if h : r.path = r0.path then some (⟨r0.path, r0.views ++ r.views.map (castView h)⟩ :: rs)
      else (mergeRow? rs r).map (r0 :: ·)
termination_by structural tbl _ => tbl

/-- Add rows to a table.  A row whose path the table has is merged into it.  A
row with a new path is appended while the allowance `k` lasts and dropped
after. -/
def addRows {s : Sig} {Γ : Ctx s} : Nat → PTable Γ → List (Row Γ) → PTable Γ
  | _, tbl, [] => tbl
  | k, tbl, r :: rs =>
      match mergeRow? tbl r with
      | some tbl' => addRows k tbl' rs
      | none =>
          match k with
          | 0 => addRows 0 tbl rs
          | k + 1 => addRows k (tbl ++ [r]) rs
termination_by structural _ _ rs => rs

/-! ## Rounds and the table -/

/-- The rows of a context before any round: one per variable, at its declared
type.  The self binder of an object literal is a variable like any other. -/
def seed {s : Sig} (Γ : Ctx s) : PTable Γ :=
  (ctxVars Γ).map fun x => ⟨.var x, [⟨Γ.lookup x, .var⟩]⟩

/-- One round.  Every row gets its local steps appended, computed against the
table and the declarations at the start of the round.  The views the remote
steps produce are then merged into their rows, new rows within the cap `rows`.
Last, every row is deduplicated by type. -/
def roundOf {s : Sig} {Γ : Ctx s} (srch : List (PDecl Γ) → SubSearch Γ) (rows : Nat)
    (tbl : PTable Γ) : PTable Γ :=
  let D := declsOf tbl
  let grown : PTable Γ := tbl.map fun r =>
    ⟨r.path, r.views ++ r.views.flatMap (localSteps (srch D) D tbl r.path)⟩
  let remote : List (Row Γ) := tbl.flatMap fun r => r.views.flatMap (remoteSteps r.path r.views)
  (addRows rows grown remote).map dedupRow

/-- The table after `k` rounds. -/
def tableOf {s : Sig} {Γ : Ctx s} (srch : List (PDecl Γ) → SubSearch Γ) (rows : Nat) :
    Nat → PTable Γ
  | 0 => seed Γ
  | k + 1 => roundOf srch rows (tableOf srch rows k)
termination_by structural k => k

/-- The table at a budget, against a family of searches indexed by their fuel.
The search module instantiates the family at its own search. -/
def tableAt {s : Sig} {Γ : Ctx s} (srch : Nat → List (PDecl Γ) → SubSearch Γ) (b : Budget) :
    PTable Γ :=
  tableOf (srch b.sub) b.rows b.table

/-- The table without the detour step, at a budget.  It is the table the search
rebuilds under an extended context, where calling the search itself would be
circular. -/
def baseTable {s : Sig} (b : Budget) (Γ : Ctx s) : PTable Γ :=
  tableOf (fun _ => noSub) b.rows b.table

/-! ## Monotonicity -/

/-- Every row of `tbl` has a row of the same path in `tbl'` with all its
types. -/
def RowsLe {s : Sig} {Γ : Ctx s} (tbl tbl' : PTable Γ) : Prop :=
  ∀ r ∈ tbl, ∃ r' ∈ tbl', r'.path = r.path ∧ ∀ T ∈ r.tys, T ∈ r'.tys

theorem rowsLe_refl {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) : RowsLe tbl tbl :=
  fun r hr => ⟨r, hr, rfl, fun _ hT => hT⟩

theorem rowsLe_trans {s : Sig} {Γ : Ctx s} {t1 t2 t3 : PTable Γ}
    (h1 : RowsLe t1 t2) (h2 : RowsLe t2 t3) : RowsLe t1 t3 := by
  intro r hr
  obtain ⟨r2, hr2, hp2, ht2⟩ := h1 r hr
  obtain ⟨r3, hr3, hp3, ht3⟩ := h2 r2 hr2
  exact ⟨r3, hr3, hp3.trans hp2, fun T hT => ht3 T (ht2 T hT)⟩

theorem map_castView_ty {s : Sig} {Γ : Ctx s} {p q : Path s} (h : p = q) :
    ∀ l : List (PView Γ p), (l.map (castView h)).map PView.ty = l.map PView.ty
  | [] => rfl
  | v :: l => congrArg (v.ty :: ·) (map_castView_ty h l)

/-- The types at a path are the types of the rows of that path. -/
theorem mem_viewsAt_ty {s : Sig} {Γ : Ctx s} (q : Path s) (T : Ty s) :
    ∀ tbl : PTable Γ, T ∈ (tbl.viewsAt q).map PView.ty ↔ ∃ r ∈ tbl, r.path = q ∧ T ∈ r.tys
  | [] => by simp [PTable.viewsAt]
  | r :: rs => by
      have ih := mem_viewsAt_ty q T rs
      by_cases h : r.path = q
      · rw [PTable.viewsAt, dif_pos h, List.map_append, List.mem_append, map_castView_ty, ih]
        constructor
        · rintro (hT | ⟨r', hr', hp, hT⟩)
          · exact ⟨r, List.mem_cons_self .., h, hT⟩
          · exact ⟨r', List.mem_cons_of_mem _ hr', hp, hT⟩
        · rintro ⟨r', hr', hp, hT⟩
          cases List.mem_cons.mp hr' with
          | inl he => subst he; exact Or.inl hT
          | inr hr'' => exact Or.inr ⟨r', hr'', hp, hT⟩
      · rw [PTable.viewsAt, dif_neg h, List.nil_append, ih]
        constructor
        · rintro ⟨r', hr', hp, hT⟩
          exact ⟨r', List.mem_cons_of_mem _ hr', hp, hT⟩
        · rintro ⟨r', hr', hp, hT⟩
          cases List.mem_cons.mp hr' with
          | inl he => subst he; exact absurd hp h
          | inr hr'' => exact ⟨r', hr'', hp, hT⟩

/-- `RowsLe` is what the monotonicity statement asks of the views at a path. -/
theorem rowsLe_viewsAt {s : Sig} {Γ : Ctx s} {tbl tbl' : PTable Γ} (h : RowsLe tbl tbl') :
    ∀ (p : Path s) (v : PView Γ p), v ∈ tbl.viewsAt p → ∃ w ∈ tbl'.viewsAt p, w.ty = v.ty := by
  intro p v hv
  obtain ⟨r, hr, hp, hT⟩ :=
    (mem_viewsAt_ty p v.ty tbl).mp (List.mem_map_of_mem (f := PView.ty) hv)
  obtain ⟨r', hr', hp', hT'⟩ := h r hr
  have hmem : v.ty ∈ (tbl'.viewsAt p).map PView.ty :=
    (mem_viewsAt_ty p v.ty tbl').mpr ⟨r', hr', hp'.trans hp, hT' _ hT⟩
  obtain ⟨w, hw, hwty⟩ := List.mem_map.mp hmem
  exact ⟨w, hw, hwty⟩

/-- A map that keeps the path of every row and all its types. -/
theorem rowsLe_map {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (f : Row Γ → Row Γ)
    (hf : ∀ r, (f r).path = r.path ∧ ∀ T ∈ r.tys, T ∈ (f r).tys) : RowsLe tbl (tbl.map f) :=
  fun r hr => ⟨f r, List.mem_map_of_mem hr, (hf r).1, (hf r).2⟩

/-- Appending views to every row keeps the old ones. -/
theorem rowsLe_grow {s : Sig} {Γ : Ctx s} (tbl : PTable Γ)
    (g : (r : Row Γ) → List (PView Γ r.path)) :
    RowsLe tbl (tbl.map fun r => (⟨r.path, r.views ++ g r⟩ : Row Γ)) := by
  intro r hr
  refine ⟨_, List.mem_map_of_mem hr, rfl, fun T hT => ?_⟩
  simp only [Row.tys, List.map_append, List.mem_append]
  exact Or.inl hT

theorem mergeRow?_rowsLe {s : Sig} {Γ : Ctx s} (r : Row Γ) :
    ∀ {tbl tbl' : PTable Γ}, mergeRow? tbl r = some tbl' → RowsLe tbl tbl'
  | [], _, h => by simp [mergeRow?] at h
  | r0 :: rs, tbl', h => by
      by_cases hp : r.path = r0.path
      · rw [mergeRow?, dif_pos hp, Option.some.injEq] at h
        subst h
        intro x hx
        cases List.mem_cons.mp hx with
        | inl he =>
            subst he
            refine ⟨_, List.mem_cons_self .., rfl, fun T hT => ?_⟩
            simp only [Row.tys, List.map_append, List.mem_append]
            exact Or.inl hT
        | inr hx' => exact ⟨x, List.mem_cons_of_mem _ hx', rfl, fun _ hT => hT⟩
      · rw [mergeRow?, dif_neg hp] at h
        cases hm : mergeRow? rs r with
        | none => rw [hm] at h; cases h
        | some rs' =>
            rw [hm, Option.map_some, Option.some.injEq] at h
            subst h
            have ih := mergeRow?_rowsLe r hm
            intro x hx
            cases List.mem_cons.mp hx with
            | inl he => subst he; exact ⟨x, List.mem_cons_self .., rfl, fun _ hT => hT⟩
            | inr hx' =>
                obtain ⟨x', hx'', hp', hT'⟩ := ih x hx'
                exact ⟨x', List.mem_cons_of_mem _ hx'', hp', hT'⟩

theorem addRows_rowsLe {s : Sig} {Γ : Ctx s} :
    ∀ (rs : List (Row Γ)) (k : Nat) (tbl : PTable Γ), RowsLe tbl (addRows k tbl rs)
  | [], _, tbl => by rw [addRows]; exact rowsLe_refl tbl
  | r :: rs, k, tbl => by
      cases hm : mergeRow? tbl r with
      | some tbl' =>
          simp only [addRows, hm]
          exact rowsLe_trans (mergeRow?_rowsLe r hm) (addRows_rowsLe rs k tbl')
      | none =>
          cases k with
          | zero =>
              simp only [addRows, hm]
              exact addRows_rowsLe rs 0 tbl
          | succ k =>
              simp only [addRows, hm]
              refine rowsLe_trans (fun x hx => ?_) (addRows_rowsLe rs k (tbl ++ [r]))
              exact ⟨x, List.mem_append_left _ hx, rfl, fun _ hT => hT⟩

theorem dedupPViewsFrom_covers {s : Sig} {Γ : Ctx s} {p : Path s} (l : List (PView Γ p)) :
    ∀ (seen : List (Ty s)) (v : PView Γ p), v ∈ l →
      tyMem? v.ty seen = true ∨ ∃ w ∈ dedupPViewsFrom seen l, w.ty = v.ty := by
  induction l with
  | nil => intro seen v hv; cases hv
  | cons u l ih =>
      intro seen v hv
      by_cases hs : tyMem? u.ty seen = true
      · have heq : dedupPViewsFrom seen (u :: l) = dedupPViewsFrom seen l := by
          simp [dedupPViewsFrom, hs]
        cases List.mem_cons.mp hv with
        | inl he => exact Or.inl (he ▸ hs)
        | inr hv' => rw [heq]; exact ih seen v hv'
      · have heq : dedupPViewsFrom seen (u :: l) = u :: dedupPViewsFrom (u.ty :: seen) l := by
          simp [dedupPViewsFrom, hs]
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

/-- Deduplication keeps every type of a row. -/
theorem dedupRow_tys {s : Sig} {Γ : Ctx s} (r : Row Γ) : ∀ T ∈ r.tys, T ∈ (dedupRow r).tys := by
  intro T hT
  obtain ⟨v, hv, hvty⟩ := List.mem_map.mp hT
  cases dedupPViewsFrom_covers r.views [] v hv with
  | inl h => exact absurd h (by simp [tyMem?])
  | inr h =>
      obtain ⟨w, hw, hwty⟩ := h
      exact List.mem_map.mpr ⟨w, hw, hwty.trans hvty⟩

/-- A round keeps every row and every type of every row. -/
theorem roundOf_rowsLe {s : Sig} {Γ : Ctx s} (srch : List (PDecl Γ) → SubSearch Γ) (rows : Nat)
    (tbl : PTable Γ) : RowsLe tbl (roundOf srch rows tbl) := by
  unfold roundOf
  exact rowsLe_trans (rowsLe_grow tbl _)
    (rowsLe_trans (addRows_rowsLe _ rows _) (rowsLe_map _ dedupRow (fun r => ⟨rfl, dedupRow_tys r⟩)))

/-- More rounds keep every row and every type of every row. -/
theorem tableOf_mono {s : Sig} {Γ : Ctx s} (srch : List (PDecl Γ) → SubSearch Γ) (rows : Nat)
    {k k' : Nat} (h : k ≤ k') : RowsLe (tableOf srch rows k) (tableOf srch rows k') := by
  induction h with
  | refl => exact rowsLe_refl _
  | step _ ih => exact rowsLe_trans ih (roundOf_rowsLe srch rows _)

/-- More rounds of the path table never lose a type at a path.  The search
fuel and the row cap are the same on both sides.  A different fuel changes
what the detour step finds, and a different cap changes which rows exist. -/
theorem table_mono {s : Sig} {Γ : Ctx s} (srch : Nat → List (PDecl Γ) → SubSearch Γ)
    {b b' : Budget} (h : b.table ≤ b'.table) (hs : b.sub = b'.sub) (hr : b.rows = b'.rows) :
    ∀ (p : Path s) (v : PView Γ p), v ∈ (tableAt srch b).viewsAt p →
      ∃ w ∈ (tableAt srch b').viewsAt p, w.ty = v.ty := by
  unfold tableAt
  rw [hs, hr]
  exact rowsLe_viewsAt (tableOf_mono (srch b'.sub) b'.rows h)

/-- The same for the table without the detour step. -/
theorem baseTable_mono {s : Sig} (Γ : Ctx s) {b b' : Budget} (h : b.table ≤ b'.table)
    (hr : b.rows = b'.rows) :
    ∀ (p : Path s) (v : PView Γ p), v ∈ (baseTable b Γ).viewsAt p →
      ∃ w ∈ (baseTable b' Γ).viewsAt p, w.ty = v.ty := by
  unfold baseTable
  rw [hr]
  exact rowsLe_viewsAt (tableOf_mono _ b'.rows h)

/-! ## Tests

Every test is `by decide`, so the table reduces in the kernel.  Each one names
the types at a path, or the paths of the rows, after a number of rounds. -/

section Tests

/-- The types at a path, without their derivations. -/
def tysAt {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (q : Path s) : List (Ty s) :=
  (tbl.viewsAt q).map PView.ty

/-- The search that finds `S <: ⊤` and nothing else. -/
def topSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ T =>
  if h : T = .top then some (h ▸ Sub.top) else none

/-- The seed: one row per variable, newest first, at the declared type. -/
example : (tableOf (Γ := (Ctx.nil.cons Ty.top).cons Ty.bot) (fun _ => noSub) 4 0).map Row.tys
    = [[Ty.bot], [Ty.top]] := by decide

/-- `x : μ(z. {val a : μ(w. {B : ⊥..⊤})})`.  Open at `x` in round one, the child
row `x.a` in round two, open at `x.a` and its declaration in round three. -/
def nestCtx : Ctx ([],x) :=
  Ctx.nil.cons (.mu (.vfld (Label.trm 0) (.mu (.typ (Label.typ 0) .bot .top))))

example : (tableOf (Γ := nestCtx) (fun _ => noSub) 4 1).map Row.path = [.var .here] := by decide
example : (tableOf (Γ := nestCtx) (fun _ => noSub) 4 2).map Row.path
    = [.var .here, .sel (.var .here) (Label.trm 0)] := by decide
example : (declsOf (tableOf (Γ := nestCtx) (fun _ => noSub) 4 3)).map pdeclSel
    = [.sel (.sel (.var .here) (Label.trm 0)) (Label.typ 0)] := by decide
/-- The stable field is also read as a field. -/
example : tysAt (tableOf (Γ := nestCtx) (fun _ => noSub) 4 2) (.var .here)
    = [.mu (.vfld (Label.trm 0) (.mu (.typ (Label.typ 0) .bot .top))),
       .vfld (Label.trm 0) (.mu (.typ (Label.typ 0) .bot .top)),
       .fld (Label.trm 0) (.mu (.typ (Label.typ 0) .bot .top))] := by decide
/-- With no new row allowed, `x.a` never appears. -/
example : (tableOf (Γ := nestCtx) (fun _ => noSub) 0 4).map Row.path = [.var .here] := by decide

/-- `x : {A : ⊥..⊤}, y : x.type`.  Alias, reverse and aliased in one round. -/
def aliasCtx : Ctx (([],x),x) :=
  (Ctx.nil.cons (.typ (Label.typ 0) .bot .top)).cons (.sngl (.var .here))

example : tysAt (tableOf (Γ := aliasCtx) (fun _ => noSub) 4 1) (.var .here)
    = [.sngl (.var (.there .here)), .typ (Label.typ 0) .bot .top] := by decide
example : tysAt (tableOf (Γ := aliasCtx) (fun _ => noSub) 4 1) (.var (.there .here))
    = [.typ (Label.typ 0) .bot .top, .sngl (.var .here), .top] := by decide
/-- In the second round `y` reads its own singleton and `⊤` back through `x`.
Each type is kept once. -/
example : tysAt (tableOf (Γ := aliasCtx) (fun _ => noSub) 4 2) (.var .here)
    = [.sngl (.var (.there .here)), .typ (Label.typ 0) .bot .top, .sngl (.var .here), .top] := by
  decide

/-- `x : {val a : ⊤}, y : x.type`.  Alias field gives `y.a : (x.a).type`. -/
def aliasFieldCtx : Ctx (([],x),x) :=
  (Ctx.nil.cons (.vfld (Label.trm 0) .top)).cons (.sngl (.var .here))

example : tysAt (tableOf (Γ := aliasFieldCtx) (fun _ => noSub) 4 2)
      (.sel (.var .here) (Label.trm 0))
    = [.sngl (.sel (.var (.there .here)) (Label.trm 0)), .top] := by decide

/-- `x : {A : ⊤..{a : ⊤}}, y : {b : ⊤}`.  The detour step puts `y` below the
lower bound `⊤` and gives it the upper bound `{a : ⊤}`, only if the search
answers. -/
def detourCtx : Ctx (([],x),x) :=
  (Ctx.nil.cons (.typ (Label.typ 0) .top (.fld (Label.trm 0) .top))).cons
    (.fld (Label.trm 1) .top)

example : tysAt (tableOf (Γ := detourCtx) (fun _ => topSub) 4 1) (.var .here)
    = [.fld (Label.trm 1) .top, .fld (Label.trm 0) .top] := by decide
example : tysAt (tableOf (Γ := detourCtx) (fun _ => noSub) 4 1) (.var .here)
    = [.fld (Label.trm 1) .top] := by decide

/-- `x : {A : ⊥..{a : ⊤}}, y : x.A`.  The upper step reads the bound. -/
def upperCtx : Ctx (([],x),x) :=
  (Ctx.nil.cons (.typ (Label.typ 0) .bot (.fld (Label.trm 0) .top))).cons
    (.sel (.var .here) (Label.typ 0))

example : tysAt (tableOf (Γ := upperCtx) (fun _ => noSub) 4 1) (.var .here)
    = [.sel (.var (.there .here)) (Label.typ 0), .fld (Label.trm 0) .top] := by decide

/-- `x : {a : ⊤} ∧ {b : ⊤}`.  Left and right. -/
example : tysAt (tableOf (Γ := Ctx.nil.cons (.and (.fld (Label.trm 0) .top)
      (.fld (Label.trm 1) .top))) (fun _ => noSub) 4 1) (.var .here)
    = [.and (.fld (Label.trm 0) .top) (.fld (Label.trm 1) .top),
       .fld (Label.trm 0) .top, .fld (Label.trm 1) .top] := by decide

end Tests

end PathsFrontend
