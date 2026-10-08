import Coercions.CapturesCC.Frontend.Decide
import Coercions.CapturesCC.Frontend.Surface

/-!
# Views, the declaration table, and the subtyping and subcapturing search

A *view* of a context variable is a type the variable has, with its use set
and derivation.  The typer reads fields and members off views, so a variable's
declared type need not display them.  A *declaration* is a type member or a
capture member of a context variable, again with its derivation.  The
*declaration table* of a context holds the middles the search tries for
`SubShape.trans` and `Subcap.trans`, which the rules leave undetermined.

Every search returns a derivation, so there is no soundness theorem.  The
result type is the statement.  The search is not complete.

## The three searches

A type is a shape with a capture set, `S ^ C`.  `Sub` has one rule, `capt`,
which pairs a `SubShape` on the shapes with a `Subcap` on the sets.  An answer
is a type or an existential over a capture binder, related by the three rules
of `ESub`.  So there are three functions.  `subcap?` searches sets.
`subShape?` searches shapes and calls `subcap?` for every set it meets.
`esub?` searches answers over the other two.

The arrow rule opens scopes.  Domains are compared under `Γ.scope` and
codomains, which are answers, under `Γ.body T₂`.  An existential packs under
`Γ.scopeInst C`, where an instance binder stands for the witness `C`, and two
existentials compare under `Γ.scope`.  The answer rules are written once, in
`esubWith`, against searches at those contexts.  The arrow rule of `subShape?`
passes its own recursive calls.

## Subcapturing rules

Besides inclusion, union, `sc-var` and the two capture-member rules, there are
two rules about capture binders.  The level rule puts `{e}` below a scope root
`κ` when `e` is at or outside the level of `κ`.  Both premises are `Bool`
equations of `Ctx.isRootB` and `Ctx.lvlLeB`, so the search decides them.  The
instance rule puts the set an instance binder stands for below that binder,
read off `Ctx.instSet?`.

## Fuel

`Budget` has six counters.  `decls` and `views` count rounds of the table and
of the view closure.  `cap` and `sub` are the fuel of the subcapturing and
shape searches.  `typer` is the fuel of the typer and `obj` bounds the passes
of the object rule.  An unbounded closure grows too fast, so duplicates are
dropped after every round and the table is computed once per context and
passed as a parameter.

## Order of definition

The view closure calls the search in its detour step, and the arrow rule of the
search builds a table under a scope.  That is a cycle.  It is cut by making the
table a parameter of the search and writing the view steps once, in
`viewStepOf`, against an abstract search.  Tables built under a scope use
`noSub`, the search that finds nothing.

Every function is structural on a fuel or a list, so the kernel reduces the
search and the checks at the end are `decide +kernel`.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy)
open scoped CapturesCC.DotMNF

/-! ## Views and declarations -/

/-- A type a context variable has, at a use set, with the derivation. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ty)

/-- A pure binder at its declared type, at the empty use set.  `Var` concludes
at `{x}` for both sets, and `sc-var` takes both down to the declared set, which
is empty. -/
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

/-- The first view of a variable, at the least use set and capture set the
rules give it.  A binder declared at the empty set is used at the empty set and
keeps its declared type.  Any other binder is used at `{x}` and has its declared
shape at `{x}`, by `Var`. -/
def varView {s : Sig} (Γ : Ctx s) (x : BVar s .var) : View Γ x :=
  if h : (Γ.lookup x).captureSet = [] then ⟨[], Γ.lookup x, pureVar Γ x h⟩
  else ⟨[.var x], (Γ.lookup x).shape ^ [.var x], .var⟩

/-- A type member a context variable has.  The fields `vr`, `lbl`, `lo`, `hi`
are the key for deduplication. -/
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

/-- A capture member a context variable has.  The fields `vr`, `lbl`, `lo`,
`hi` are the key for deduplication. -/
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

/-- The six counters, with their default values. -/
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
deriving Repr, Inhabited

/-! ## Deduplication

Both closures grow by rounds and drop duplicates after each round: views by
type, declarations by their four key fields.  The first entry of a key is kept.
One procedure serves all three lists, generic in the key. -/

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

A step takes one view of a variable to the views reachable from it by one rule.
`open` and the two `and` steps need only the derivation.  The `upper` and
`detour` steps consult the table, and `detour` also consults a search, so the
steps are written against an abstract search.  Every step keeps the use set and
capture set of the view and changes only the shape. -/

/-- One step of the view closure, uniform in the variable. -/
def ViewStep {s : Sig} (Γ : Ctx s) : Type :=
  (x : BVar s .var) → View Γ x → List (View Γ x)

/-- A search on shapes over a fixed context. -/
def SubSearch {s : Sig} (Γ : Ctx s) : Type := (S T : Shape s) → Option (SubShape Γ S T)

/-- The search that finds nothing.  Scope rules pass it when they build a table
under a scope, where the real search would be circular. -/
def noSub {s : Sig} {Γ : Ctx s} : SubSearch Γ := fun _ _ => none

/-- A shape subtyping lifted to the type it starts from. -/
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

The detour derivation carries the evidence for its own side condition. -/
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

/-- One round of the closure: every view of the list plus one step from each,
without duplicates. -/
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

/-- The members a list of views of one variable displays. -/
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

/-- The members the views of the listed variables display. -/
def tableOfVars {s : Sig} {Γ : Ctx s} (st : ViewStep Γ) (m : Nat) (ys : List (BVar s .var)) :
    DeclTable Γ :=
  match ys with
  | [] => .empty
  | y :: ys => DeclTable.append (tableOfViews (viewsOf st m y)) (tableOfVars st m ys)
termination_by structural ys

/-- One round of the table: the members already in it plus those the views of
every context variable display, deduplicated by key. -/
def declsRoundOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat)
    (D : DeclTable Γ) : DeclTable Γ :=
  let N := tableOfVars (stf D) m (ctxVars Γ)
  ⟨dedupBy declKey (D.typs ++ N.typs), dedupBy capDeclKey (D.caps ++ N.caps)⟩

/-- The table after `k` rounds, each running `m` rounds of the closure. -/
def declsOf {s : Sig} {Γ : Ctx s} (stf : DeclTable Γ → ViewStep Γ) (m : Nat) (k : Nat) :
    DeclTable Γ :=
  match k with
  | 0 => .empty
  | k + 1 => declsRoundOf stf m (declsOf stf m k)
termination_by structural k

/-- The detour-free table that scope rules build under the scopes they open.
The full table there would make the search mutual with the view closure. -/
def baseDecls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStepOf noSub D) b.views b.decls

/-! ## Helpers of the search

A shape rule is a decidable equality on a constructed shape, or a `match` whose
fall-through is `none`.  A fall-through that returns a derivation does not
typecheck, because a `match` on `S` or `T` generalizes them in the motive of a
result type that mentions them.

The helpers move a derivation across a decided equality.  They use `cases`
rather than `▸`, because a member's label occurs twice in the conclusion and a
rewrite would hit both. -/

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

/-- The rounds the scope rules give the detour-free table they build.  Small,
since the table is rebuilt at every application of a scope rule. -/
def allBudget : Budget := { decls := 1, views := 2, sub := 0, cap := 0, typer := 0, obj := 0 }

/-! ## The subcapturing search -/

/-- The level rule into one atom of the target: `{e} <: {κ} ⊆ C₂` when `κ` is a
scope root and `e` is at or outside its level.  Every premise is decided. -/
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

/-- The subcapturing search.  `subcap? D 0 C₁ C₂` is `none`.
`subcap? D (n+1) C₁ C₂` tries these rules in order, with searched premises at
fuel `n`.

1. `C₁ ⊆ C₂`, `Subcap.elem`.
2. `C₁ = a :: C` with `C` not empty, `Subcap.union`.
3. `C₁ = {e}` and `κ ∈ C₂` a scope root at or inside the level of `e`,
   `Subcap.level`, then the inclusion of `{κ}` in `C₂`.
4. `κ ∈ C₂` an instance binder standing for `C`: search `C₁ <: C`, then
   `Subcap.inst`, then the inclusion of `{κ}` in `C₂`.
5. `C₁ = {x}`: `sc-var`, then search from the set `x` is declared at.
6. `C₁ = {y.C}` at a capture member of the table: `sc-sel-upper`, then search
   from its upper bound.
7. `C₁ = {a}` and `y.C ∈ C₂` at a capture member of the table: search into its
   lower bound, then `sc-sel-lower`, then the inclusion of `{y.C}` in `C₂`.

The last alternative is not a rule.  It retries the search at the previous
fuel.  It changes no answer of the seven rules at this fuel, and it makes
`subcap?_le` an induction on the fuel alone. -/
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
        | [e] => firstSome (levelInto? e C2) C2
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 4
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
      -- 5
      ((match C1 with
        | [.var x] =>
            (subcap? D n (Γ.lookup x).captureSet C2).map (fun e => Subcap.trans Subcap.var e)
        | _ => none : Option (Subcap Γ C1 C2))).orElse fun _ =>
      -- 6
      (firstSome (fun d =>
        if h : C1 = [capSel d] then (subcap? D n d.hi C2).map (fun e => subcapFromSel h e)
        else none) D.caps).orElse fun _ =>
      -- 7
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

/-! ## Answers

`ESub` has three rules.  `ty` compares two plain answers by `Sub`.  `pack`
widens a plain answer `T'` to `∃ᶜ[C₀] T`: the witness `C` is below the bound
`C₀`, and `T'` is below `T` under a scope whose instance binder stands for `C`.
`exist` compares two existentials, the bounds covariantly and the bodies under
a scope.

The rules are written once, against four searches: plain answers and sets at
the context, and types under `Γ.scope` and under `Γ.scopeInst C`.  The arrow
rule of the shape search and `esub?` both instantiate them. -/

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
2. A plain answer below an existential, `ESub.pack`.  The witness is tried
   first as the plain answer's own capture set, then as the bound.  The first
   serves every answer `Ty.expandFresh` makes, whose witness binder sits in the
   top set only.  The second serves a written `∃` whose binder sits deeper,
   below a field or a box.
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

/-- The shape search.  `subShape? D c 0 S T` is `none`.
`subShape? D c (n+1) S T` tries these rules in order.  Shape premises are
searched at fuel `n` and set premises by `subcap?` at fuel `c`.

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
10. Two functions, `SubShape.all`: domains under `Γ.scope`, codomains by the
    answer rules under `Γ.body T2`, each against a table rebuilt there.
11. `T = y.A` at a type member of the table, `SubShape.selLower`.
12. `S = y.A` at a type member of the table, `SubShape.selUpper`.
13. The transitivity family, at a pair of type members of one variable at one
    label.

The last alternative is the retry at the previous fuel, as in `subcap?`. -/
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
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 9
      ((match S, T with
        | .box T1, .box T2 =>
            (subCapt (fun S S' => subShape? D c n S S') (fun C C' => subcap? D c C C') T1 T2).map
              (fun e => SubShape.box e)
        | _, _ => none : Option (SubShape Γ S T))).orElse fun _ =>
      -- 10
      ((match S, T with
        | .all T1 U1, .all T2 U2 => do
            let e1 ← subCapt (fun S S' => subShape? (baseDecls allBudget Γ.scope) c n S S')
              (fun C C' => subcap? (baseDecls allBudget Γ.scope) c C C')
              (Dom.underRoot (s := s) T2) (Dom.underRoot (s := s) T1)
            let e2 ← esubWith (Γ := Γ.body T2)
              (subCapt (fun S S' => subShape? (baseDecls allBudget (Γ.body T2)) c n S S')
                (fun C C' => subcap? (baseDecls allBudget (Γ.body T2)) c C C'))
              (fun C C' => subcap? (baseDecls allBudget (Γ.body T2)) c C C')
              (subCapt (fun S S' => subShape? (baseDecls allBudget (Γ.body T2).scope) c n S S')
                (fun C C' => subcap? (baseDecls allBudget (Γ.body T2).scope) c C C'))
              (fun W => subCapt
                (fun S S' => subShape? (baseDecls allBudget ((Γ.body T2).scopeInst W)) c n S S')
                (fun C C' => subcap? (baseDecls allBudget ((Γ.body T2).scopeInst W)) c C C'))
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

/-- The search on types: `Sub.capt` of the shape search at fuel `n` and the set
search at fuel `c`. -/
def sub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) (T U : Ty s) :
    Option (Sub Γ T U) :=
  subCapt (fun S S' => subShape? D c n S S') (fun C C' => subcap? D c C C') T U

/-- The search on answers: the answer rules over `sub?` at the context and at
the two kinds of scope, each against a detour-free table rebuilt there. -/
def esub? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) (E E' : ETy s) :
    Option (ESub Γ E E') :=
  esubWith (sub? D c n) (subcap? D c)
    (sub? (baseDecls allBudget Γ.scope) c n)
    (fun W => sub? (baseDecls allBudget (Γ.scopeInst W)) c n) E E'

/-! ## The closure at the real search

Each name is the generic body above at `viewStep D c n`. -/

/-- The five view steps at the real search. -/
def viewStep {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) : ViewStep Γ :=
  viewStepOf (fun S T => subShape? D c n S T) D

/-- One round of the view closure, iterated `b.views` times. -/
def viewsRound {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (c n : Nat) {x : BVar s .var}
    (vs : List (View Γ x)) : List (View Γ x) :=
  viewsRoundOf (viewStep D c n) x vs

/-- The views of a variable at a budget.  `Γ` is implicit: the table
determines it. -/
def views {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (x : BVar s .var) :
    List (View Γ x) :=
  viewsOf (viewStep D b.cap b.sub) b.views x

/-- One round of the declaration table, iterated `b.decls` times. -/
def declsRound {s : Sig} (b : Budget) (Γ : Ctx s) (D : DeclTable Γ) : DeclTable Γ :=
  declsRoundOf (fun D => viewStep D b.cap b.sub) b.views D

/-- The declaration table of a context at a budget. -/
def decls {s : Sig} (b : Budget) (Γ : Ctx s) : DeclTable Γ :=
  declsOf (fun D => viewStep D b.cap b.sub) b.views b.decls

/-! ## Round monotonicity

More rounds never lose a type or a member.  The statements are about keys, not
derivations: deduplication drops later derivations of a key, and a larger
budget may find a different derivation of the same judgment. -/

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

/-- A family that grows from each count to the next grows from any count to any
larger one. -/
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

/-- More rounds of the view closure never lose a type.  The fuels of the search
are fixed, since the detour step consults it. -/
theorem views_mono {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b b' : Budget}
    (h : b.views ≤ b'.views) (hs : b.sub = b'.sub) (hc : b.cap = b'.cap) (x : BVar s .var) :
    ∀ v ∈ views D b x, ∃ w ∈ views D b' x, w.ty = v.ty := by
  unfold views
  rw [hs, hc]
  exact viewsOf_mono (viewStep D b'.cap b'.sub) h x

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

/-- More rounds of the table never lose a member of either kind.  The closure
rounds and the fuels are fixed. -/
theorem decls_mono {s : Sig} {Γ : Ctx s} {b b' : Budget} (h : b.decls ≤ b'.decls)
    (hv : b.views = b'.views) (hs : b.sub = b'.sub) (hc : b.cap = b'.cap) :
    (∀ d ∈ (decls b Γ).typs, ∃ d' ∈ (decls b' Γ).typs,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) ∧
    (∀ d ∈ (decls b Γ).caps, ∃ d' ∈ (decls b' Γ).caps,
      d'.vr = d.vr ∧ d'.lbl = d.lbl ∧ d'.lo = d.lo ∧ d'.hi = d.hi) := by
  unfold decls
  rw [hv, hs, hc]
  obtain ⟨ht, hcs⟩ := declsOf_mono (fun D => viewStep D b'.cap b'.sub) b'.views h
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨d', hd', hk⟩ := ht d hd
    simp only [declKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩
  · obtain ⟨d', hd', hk⟩ := hcs d hd
    simp only [capDeclKey, Prod.mk.injEq] at hk
    exact ⟨d', hd', hk⟩

/-! ## Fuel monotonicity

The last alternative of `subShape?` and `subcap?` is the retry at the previous
fuel, so these are inductions on the fuel.  They are about `isSome`, not
derivations: more fuel may find another derivation of the same judgment, and
judgments are `Type`-valued without decidable equality.  `sub?` and `esub?`
are monotone in the shape fuel at a fixed set fuel, since their only recursion
is `subShape?`. -/

theorem isSome_orElse_right {α : Type} {a : Option α} {b : Unit → Option α}
    (h : (b ()).isSome = true) : (a.orElse b).isSome = true := by
  cases a with
  | none => simpa [Option.orElse] using h
  | some x => rfl

/-- A search that never loses an answer to one more unit of fuel never loses it
to any larger fuel. -/
theorem isSome_of_le {α : Type} (f : Nat → Option α)
    (hs : ∀ n, (f n).isSome = true → (f (n + 1)).isSome = true) {n n' : Nat} (h : n ≤ n') :
    (f n).isSome = true → (f n').isSome = true := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun x => hs _ (ih x)

/-- One more unit of fuel never loses a subcapturing. -/
theorem subcap?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {n : Nat} {C C' : CaptureSet s}
    (h : (subcap? D n C C').isSome) : (subcap? D (n + 1) C C').isSome := by
  rw [subcap?.eq_def]
  iterate 7 refine isSome_orElse_right ?_
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

Failure of the search does not show that no derivation exists.  The level rule
is the one rule that relates a binder to a root, and its failure has a semantic
witness.  `source_lvl_safety`
(`lean/Coercions/CapturesCC/DotToFCdot/EvidenceTyped.lean`) says that a
member-free subcapturing keeps every resolved atom of `C` confined to whatever
atom `r` confines every resolved atom of `D`.  So one depth `n` at which the
resolution of `C` is not confined to `r`, while that of `D` is at every depth,
rules out every member-free derivation of `C <: D`.  The statement holds for
any target set and any atom of the target, so it also decides the escape at the
top of a program, where `r` is the target's universal root. -/

/-- No member-free subcapturing puts `C` below `D` when `D` is confined to
`r` at every depth and `C` is not at one depth `n`. -/
theorem escape_rejected_at {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf)
    (r : CapturesCC.FCdot.CapAtom s)
    (hD : ∀ m, Γ.translate.Confined (Γ.translate.caps m D.translate) r)
    (n : Nat) (hn : ¬ Γ.translate.Confined (Γ.translate.caps n C.translate) r) :
    ¬ ∃ d : Subcap Γ C D, d.MemberFree :=
  fun ⟨_, hd⟩ => hn (CapturesCC.DotMNF.source_lvl_safety hwf hd hD n)

/-! ## Checks

Checks of `subcap?`, `sub?` and `esub?` at the examples of
`lean/Coercions/CapturesCC/DotMNF/Examples.lean`.  Each names the derivation it
reproduces.  Every check is `decide +kernel`.

The budget of a check is one at which the search finds the chain.  The retry
clauses make every larger fuel find it too (`subcap?_le`, `sub?_le`,
`esub?_le`). -/

section Probes

open CapturesCC.DotMNF.Examples

/-! ### The level rule and the instance rule -/

/-- `W5_level_own`: inside the callback's body the parameter is below the body
root, by the level rule. -/
example : (subcap? DeclTable.empty 1 [CapAtom.var W5f] [CapAtom.cvar W5kb] (Γ := W5Ctx)).isSome
    = true := by
  decide +kernel

/-- It is not below the root of the scope outside the call at the default
budget.  The failure of the search is not the rejection, which is
`escape_rejected_at` at a reached goal. -/
example : (subcap? (decls {} W5Ctx) (({} : Budget).cap) [CapAtom.var W5f]
    [CapAtom.cvar W5kout]).isSome = false := by
  decide +kernel

/-- `W2_level`: the arrow binder is below the body root. -/
example : (subcap? DeclTable.empty 1 [CapAtom.cvar (.there .here)]
    [CapAtom.cvar (.there (.there .here))] (Γ := W2BodyCtx)).isSome = true := by
  decide +kernel

/-- `W2_level_param`: the parameter is below the body root. -/
example : (subcap? DeclTable.empty 1 [CapAtom.var .here]
    [CapAtom.cvar (.there (.there .here))] (Γ := W2BodyCtx)).isSome = true := by
  decide +kernel

/-- The level rule is directional: the body root is not below the arrow binder,
which is no root. -/
example : (subcap? (decls {} W2BodyCtx) (({} : Budget).cap)
    [CapAtom.cvar (.there (.there .here))] [CapAtom.cvar (.there .here)]).isSome = false := by
  decide +kernel

/-- At the top of a program there is no root, so `{c} <: {}` is not found for
the witness of an unpacked `fresh` result at the default budget. -/
example : (subcap? (decls {} ((Z1Ctx.consC).cons (fileS ^ [CapAtom.cvar .here])))
    (({} : Budget).cap) [CapAtom.var .here] []).isSome = false := by
  decide +kernel

/-- The instance rule, the residual of `Z1Pack`: under a pack's scope the
witness `{u}` is below the instance binder.  The rule searches the witness
below the set the binder stands for, so it takes two units of fuel. -/
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

/-- The function of `Z1call` is below the platform binder it is declared at, by
`sc-var`. -/
example : (subcap? DeclTable.empty 2 [CapAtom.var (.there .here)] [CapAtom.cvar fs2]
    (Γ := Z1Ctx)).isSome = true := by
  decide +kernel

/-- C2, `{g} <: {κ₁,κ₂}` in the client: `sc-var` takes `{g}` to `{x.C}`, and
`sc-sel-upper` at the abstract member of `x` takes it to `{κ₁,κ₂}`
(`C2call`). -/
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

/-- S1, `{fs} <: {cp.C}` at the caller: the lower bound of the precise member
of `cp` is `{fs}`, so `sc-sel-lower` puts `{fs}` below `{cp.C}` (`S1op`). -/
def probeS1 : Budget := { decls := 1, views := 1, sub := 0, cap := 2, typer := 0, obj := 0 }

example : (subcap? (decls probeS1 S1Ctx2) probeS1.cap [CapAtom.cvar fs2]
    [CapAtom.sel .here lC]).isSome = true := by
  decide +kernel

/-- C5, `{n} <: {fs}` at the caller of `mk`: `sc-var` takes `{n}` to `{it.C}`,
and `sc-sel-upper` at the abstract member of `it` takes it to `{fs}`
(`S2nVar`). -/
def probeC5 : Budget := { decls := 1, views := 2, sub := 0, cap := 3, typer := 0, obj := 0 }

example : (subcap? (decls probeC5 S2Ctx4) probeC5.cap [CapAtom.var .here]
    [CapAtom.cvar fs4]).isSome = true := by
  decide +kernel

/-! ### Shapes -/

/-- E1, the transitivity family at one member: `{A : ⊤..⊥} <: {B : …}` through
`⊤ <: x.A <: ⊥`, the chain of `badBounds`. -/
def probeE1 : Budget := { decls := 1, views := 0, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE1 E1Ctx) probeE1.cap probeE1.sub
    (E1Dom : Ty (Sig.body ([] : Sig))) E1Res).isSome = true := by
  decide +kernel

/-- The same at one unit less shape fuel finds nothing. -/
example : (sub? (decls probeE1 E1Ctx) probeE1.cap 1
    (E1Dom : Ty (Sig.body ([] : Sig))) E1Res).isSome = false := by
  decide +kernel

/-- E3, the transitivity family at two members of one variable at one label:
`{b : ⊤} <: x.A <: {a : ⊤}`, the chain of `E3sub`. -/
def probeE3 : Budget := { decls := 1, views := 1, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE3 E3Ctx2) probeE3.cap probeE3.sub
    (E3T2 : Ty (Sig.body (Sig.body ([] : Sig)))) E3T1).isSome = true := by
  decide +kernel

/-- E4, the detour view step followed by `<:-Sel`: `w` reaches `{A : Int..⊤}`
through `S <: x.B <: T`, and then `Int <: w.A`, the chain of `E4nA`. -/
def probeE4 : Budget := { decls := 2, views := 1, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE4 E4Ctx4) probeE4.cap probeE4.sub
    (E4Int : Ty (Sig.body (Sig.body (Sig.body ([] : Sig))),x))
    ((Shape.sel (.var (.there (up .here))) lA) ^ [])).isSome = true := by
  decide +kernel

/-- E6, `<:-Sel` through the self binder's own member: `Int <: z.T` where `z` is
the literal's self binder, the chain of `E6nT`. -/
def probeE6 : Budget := { decls := 1, views := 2, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE6 E6Ctxz) probeE6.cap probeE6.sub
    (E6Int : Ty (([],x,c),x)) ((Shape.sel (.var .here) lT) ^ [])).isSome = true := by
  decide +kernel

/-- E8, the right view step: `y : x.A ∧ {a : ⊤}` has a view at `{a : ⊤}`, which
is `E8yFld2`. -/
def probeE8views : Budget := { decls := 0, views := 1, sub := 0, cap := 0, typer := 0, obj := 0 }

example : ((views (decls probeE8views E8Ctx2) probeE8views
    (.here : BVar (Sig.body (Sig.body ([] : Sig))) .var)).any
    (fun v => decide (v.ty = ((Shape.fld la (.top ^ [])) ^ [] :
      Ty (Sig.body (Sig.body ([] : Sig))))))) = true := by
  decide +kernel

/-- E8, `Sel-<:`: `x.A <: {a : ⊤}` by the upper bound of `x`'s member `A`, which
is `E8Upper`. -/
def probeE8sub : Budget := { decls := 1, views := 0, sub := 2, cap := 1, typer := 0, obj := 0 }

example : (sub? (decls probeE8sub E8Ctx2) probeE8sub.cap probeE8sub.sub
    ((Shape.sel (.var (up .here)) lA) ^ [] : Ty (Sig.body (Sig.body ([] : Sig))))
    ((Shape.fld la (.top ^ [])) ^ [])).isSome = true := by
  decide +kernel

/-! ### The arrow rule and answers -/

/-- `Z1_widen`: the arrow rule opens its two scopes, and the codomains compare
by `ESub.exist`, the bodies under a scope of their own. -/
example : (sub? DeclTable.empty 1 2 (Z1Ty k1) (Z1TyTop k1) (Γ := platCtx)).isSome = true := by
  decide +kernel

/-- `Z1Pack`: the body's plain answer packs into the existential that the result
`fresh` reads as, with the answer's own capture set as witness and the residual
by the instance rule. -/
example : (esub? DeclTable.empty 2 1 (Γ := platCtx.body unitTy)
    (.ty (fileS ^ [CapAtom.var .here]))
    (∃ᶜ[[CapAtom.cvar (up k1), CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))).isSome
    = true := by
  decide +kernel

/-- A written `∃` whose binder sits below a field: the answer's own capture set,
here empty, is no witness, and the bound is.  The context is the body of
`process`, whose parameter `f` is declared at the arrow binder. -/
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

end Probes

end CapturesCCFrontend
