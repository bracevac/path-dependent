import Coercions.Frontend.Ann
import Coercions.Frontend.Resolve
import Coercions.Frontend.Search

/-!
# The derivation producing typer

Stages F1.4 and F1.5 of `plan-5e-frontend-stages.md`.  This is the module that
replaces the hand assembly of `lean/Coercions/DotMNF/Examples.lean`.  It is fuel
bounded, `Option` valued, and sound by construction: `synth?` returns a `Synth`,
whose second field *is* the `DotMNF.HasTy` derivation, so soundness is the result
type and there is no soundness theorem to prove.  This is the shape the target's
own checker already uses, `FCdot.TmChecked`
(`lean/Coercions/FCdot/Checker.lean:465`).

It is incomplete by necessity, since DOT subtyping is undecidable.  No
completeness theorem is attempted or claimed.  What the typer will not find is a
list, not a theorem: a subtyping whose middle is outside the one family of F1.3,
a `Rec-I` folding other than the goal's own body, an `And-I` at a position where
neither conjunct is separately checkable, an avoidance result other than the
annotation, the strengthening or `⊤`, an object literal without a self
annotation, an application whose function variable reaches `∀` only through a
subtyping step the view closure does not perform, and anything past the budget.

## The four functions

`synth?` reads a type off a term.  `check?` tests a term against a type.
`checkVar?` tests a *variable* against a type, which is a separate function
because two rules of the calculus conclude about a variable and are not reached
by subsumption: `And-I` and `Rec-I` (`lean/Coercions/DotMNF/Typing.lean:109-120`).
`checkDefs?` matches a definition list against a type in lockstep, which is what
`DefsTy` does (`Typing.lean:124-127`).

The block is well-founded on `(fuel, size, tag)`, lexicographically, the second
and last well-founded site of the stage.  `check?` calls `synth?` on the same
term at a lower tag, `synth?` calls `check?` on proper subterms at a smaller
size, `checkDefs?` calls `check?` on a field body which is smaller than the
definition list that holds it, `check?` and `synth?` call `checkVar?` at second
component zero, which is smaller because `sizeATm` is at least one, and
`checkVar?` recurses either at a smaller type or at a smaller fuel.

## The avoidance ladder

`HasTy.let` takes `HasTy (Γ.cons T) u U.weaken` for a `U` the rule does not
determine (`Typing.lean:103-108`).  Three rungs are tried in order: the surface
annotation, the strengthening of the body's synthesized type, and `⊤`.  The
third always applies and always loses information, which is what the vanilla E2
derivation does at its outer `let` (`Examples.lean:124-129`).

## The kernel

`synth?` and its three companions are well-founded, so they do not reduce in the
kernel, exactly as `sub?` does not (F1.7).  The checks at the end of this module
run compiled code through `expect`, never `by decide` and never `by rfl`.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Value Defs Ctx Sub HasTy DefsTy)

/-! ## The result of a synthesis

The derivation is a field, so a caller that gets a `Synth` has the typing and
not merely an answer. -/

/-- A type a term has, with the derivation that it has it. -/
structure Synth {s : Sig} (Γ : Ctx s) (t : Tm s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ t ty

/-! ## The size of a type

The third component of the measure.  `checkVar?` recurses on the two operands of
an intersection, which are strictly smaller, and every other clause of the block
measures a term or a definition list with the functions of `Ann.lean`. -/

/-- The node count of a type. -/
def sizeTy : {s : Sig} → Ty s → Nat
  | _, .top => 1
  | _, .bot => 1
  | _, .typ _ S T => sizeTy S + sizeTy T + 1
  | _, .fld _ T => sizeTy T + 1
  | _, .sel _ _ => 1
  | _, .mu T => sizeTy T + 1
  | _, .all S T => sizeTy S + sizeTy T + 1
  | _, .and S T => sizeTy S + sizeTy T + 1

/-- Every type has at least one node. -/
theorem sizeTy_pos : ∀ {s : Sig} (T : Ty s), 0 < sizeTy T
  | _, .top => Nat.zero_lt_one
  | _, .bot => Nat.zero_lt_one
  | _, .typ _ _ _ => Nat.succ_pos _
  | _, .fld _ _ => Nat.succ_pos _
  | _, .sel _ _ => Nat.zero_lt_one
  | _, .mu _ => Nat.succ_pos _
  | _, .all _ _ => Nat.succ_pos _
  | _, .and _ _ => Nat.succ_pos _

/-- The left operand of an intersection is smaller. -/
theorem sizeTy_lt_andLeft {s : Sig} (S T : Ty s) : sizeTy S < sizeTy (.and S T) := by
  show sizeTy S < sizeTy S + sizeTy T + 1
  omega

/-- The right operand of an intersection is smaller. -/
theorem sizeTy_lt_andRight {s : Sig} (S T : Ty s) : sizeTy T < sizeTy (.and S T) := by
  show sizeTy T < sizeTy S + sizeTy T + 1
  omega

/-! ## Casts across a decided equality

Three derivations that move across an equality of labels or of types.  They are
written with `cases` rather than with `▸` because a label occurs twice in the
conclusion of the rule that carries it, and a rewrite would hit both
occurrences.  This is the idiom `Search.lean` uses for the same reason. -/

/-- A field view read at the label the projection asks for. -/
def hasFldAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a c : Label} {T : Ty s}
    (h : c = a) (d : HasTy Γ (.path (.var x)) (.fld c T)) :
    HasTy Γ (.path (.var x)) (.fld a T) := by
  cases h; exact d

/-- A type member definition against a declaration whose two bounds are the
definition's own type.  `DefsTy.typ` is the only rule for a type member and it
concludes at exactly those bounds (`lean/Coercions/DotMNF/Typing.lean:125`). -/
def defsTypAt {s : Sig} {Γ : Ctx s} {A B : Label} {S L U : Ty s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- `⊤` is its own weakening, which is what the third rung of the avoidance
ladder needs to hand `HasTy.let` a body typing at `U.weaken`. -/
theorem weaken_top {s : Sig} {k : Kind} : (Ty.top : Ty s).weaken (k := k) = .top := rfl

/-! ## Reading a view

Four ways the typer consults the closure of F1.2.  All four walk a list with
`List.findSome?`, none of them recurses, and none is part of the well-founded
block. -/

/-- A function type a variable has, with the derivation. -/
structure AllView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The domain. -/
  dom : Ty s
  /-- The codomain, under the domain's binder. -/
  cod : Ty (s,x)
  /-- The derivation. -/
  deriv : HasTy Γ (.path (.var x)) (.all dom cod)

/-- A field a variable has at a given label, with the derivation. -/
structure FldView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) where
  /-- The type of the field. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ (.path (.var x)) (.fld a ty)

/-- The first view that is a function type.  Only the first is tried: an
application whose function variable reaches `∀` further down the list is on the
list of what the typer will not find. -/
def allView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (AllView Γ x) :=
  vs.findSome? (fun v =>
    match hv : v.ty with
    | .all S T => some ⟨S, T, hv ▸ v.deriv⟩
    | _ => none)

/-- The first view that is a field declaration at the label asked for. -/
def fldView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (a : Label)
    (vs : List (View Γ x)) : Option (FldView Γ x a) :=
  vs.findSome? (fun v =>
    match hv : v.ty with
    | .fld c T => if h : c = a then some ⟨T, hasFldAt h (hv ▸ v.deriv)⟩ else none
    | _ => none)

/-- The first view at exactly the type asked for. -/
def viewAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} (T : Ty s)
    (vs : List (View Γ x)) : Option (HasTy Γ (.path (.var x)) T) :=
  vs.findSome? (fun v => if h : v.ty = T then some (h ▸ v.deriv) else none)

/-- The first view that the subtyping search takes to the type asked for,
through `HasTy.sub` (`lean/Coercions/DotMNF/Typing.lean:121`). -/
def viewSub {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (n : Nat)
    (T : Ty s) (vs : List (View Γ x)) : Option (HasTy Γ (.path (.var x)) T) :=
  vs.findSome? (fun v => (sub? D n v.ty T).map (fun e => .sub v.deriv e))

/-! ## The typer

Four mutually recursive functions, well-founded on `(fuel, size, tag)`.  The
fuel is the typer's own, `Budget.typer` at the entry point; the subtyping search
is always called at `Budget.sub`, its own counter, never at the typer's fuel.

Like `sub?`, `synth?` ends its fuel level with a retry at the previous level.
That is not a rule of the calculus and changes no answer the clauses give, since
every clause is tried here at strictly more fuel than it was tried there.  What
it buys is `synth?_le`, which is otherwise an induction through every clause of
every function. -/

/-- The three size functions of the measure are ordinary definitions, so the
default tactic that discharges the decreasing goals has to be told to unfold
them.  This is the documented extension point, and it is local to this file.  No
`decreasing_by` appears below: every goal of the block is closed by this. -/
local macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| simp only [sizeTy, sizeATm, sizeADefs]; omega)

mutual

/-- Synthesis, clause by clause.

- a variable returns `Ctx.lookup` and `HasTy.var` (`Typing.lean:88`), exact,
  nothing guessed;
- `λ(x : S). t` decides `Ty.Wf S` with F1.1 and synthesizes the body under
  `Γ.cons S` against a table rebuilt there (`Typing.lean:90`);
- `ν(x : T. d)` checks the definitions under `Γ.consSelf d.erase T` against a
  table rebuilt there and decides `Defs.Distinct` (`Typing.lean:97-101`);
- `x y` reads the first function view of `x` off the closure and checks `y`
  against its domain (`Typing.lean:92-96`);
- `x.a` reads the first field view of `x` at `a` (`Typing.lean:102`);
- `let x (: U)? = t in u` climbs the three rung avoidance ladder
  (`Typing.lean:103-108`). -/
def synth? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat)
    (a : ATm s) : Option (Synth Γ a.erase) :=
  match n with
  | 0 => none
  | n + 1 =>
      ((match a with
        | .path (.var x) => some ⟨Ctx.lookup Γ x, .var⟩
        | .lam S t =>
            if hwf : Ty.Wf S then
              (synth? (decls b (Γ.cons S)) b (n + 1) t).map (fun c =>
                ⟨.all S c.ty, .lam c.deriv hwf⟩)
            else none
        | .obj T d =>
            (checkDefs? (decls b (Γ.consSelf d.erase T)) b (n + 1) d T).bind (fun hd =>
              if hdist : Defs.Distinct d.erase then some ⟨.mu T, .obj hd hdist⟩
              else none)
        | .app x y =>
            (allView (views D b x)).bind (fun v =>
              (checkVar? D b (n + 1) y v.dom).map (fun hy =>
                ⟨v.cod.substVar y, .app v.deriv hy⟩))
        | .proj x a => (fldView a (views D b x)).map (fun v => ⟨v.ty, .proj v.deriv⟩)
        | .let ann t u =>
            (synth? D b (n + 1) t).bind (fun c1 =>
              -- rung one: the surface annotation
              ((match ann with
                | some U =>
                    (check? (decls b (Γ.cons c1.ty)) b (n + 1) u U.weaken).bind (fun h2 =>
                      if hwf : Ty.Wf U then some ⟨U, .let c1.deriv h2 hwf⟩ else none)
                | none => none) :
                  Option (Synth Γ (ATm.let ann t u).erase)).orElse fun _ =>
              ((synth? (decls b (Γ.cons c1.ty)) b (n + 1) u).bind (fun c2 =>
                -- rung two: the strengthening of the body's type
                ((match tyStrengthenW? c2.ty with
                  | some w =>
                      if hwf : Ty.Wf w.val then
                        some ⟨w.val, .let c1.deriv (w.property ▸ c2.deriv) hwf⟩
                      else none
                  | none => none) :
                    Option (Synth Γ (ATm.let ann t u).erase)).orElse fun _ =>
                -- rung three: `⊤`, which always applies and always loses
                some ⟨.top, .let c1.deriv (weaken_top ▸ HasTy.sub c2.deriv Sub.top) .top⟩) :
                  Option (Synth Γ (ATm.let ann t u).erase)))
        : Option (Synth Γ a.erase))).orElse fun _ => synth? D b n a
termination_by (n, sizeATm a, 1)

/-- Checking.  A variable goes to `checkVar?`, which reaches the two rules
subsumption does not.  Everything else is synthesized and then moved to the goal
by a decided equality or by the subtyping search, through `HasTy.sub`
(`lean/Coercions/DotMNF/Typing.lean:121`). -/
def check? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat)
    (a : ATm s) (T : Ty s) : Option (HasTy Γ a.erase T) :=
  ((match a with
    | .path (.var x) => checkVar? D b n x T
    | _ => none) : Option (HasTy Γ a.erase T)).orElse fun _ =>
  (synth? D b n a).bind (fun c =>
    if h : c.ty = T then some (h ▸ c.deriv)
    else (sub? D b.sub c.ty T).map (fun e => .sub c.deriv e))
termination_by (n, sizeATm a, 2)

/-- Checking a variable.  Three rules, in order.

1. an intersection goal splits by `HasTy.andI` (`Typing.lean:117-120`), the one
   rule that combines two typings of a single variable; it recurses at a
   strictly smaller type;
2. a `μ` goal whose body is declaration shaped folds by `HasTy.recI`
   (`Typing.lean:109-111`).  `Sub` has no rule for `μ` (`Typing.lean:69`), so a
   `μ` goal is otherwise unreachable from an opened type.  `Ty.substVar` is a
   renaming, so the type does not shrink and the fuel must;
3. otherwise the closure is consulted, first for a view at exactly the goal and
   then for a view the subtyping search takes there. -/
def checkVar? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat)
    (x : BVar s .var) (T : Ty s) : Option (HasTy Γ (.path (.var x)) T) :=
  ((match T with
    | .and T1 T2 =>
        (checkVar? D b n x T1).bind (fun h1 =>
          (checkVar? D b n x T2).map (fun h2 => .andI h1 h2))
    | _ => none) : Option (HasTy Γ (.path (.var x)) T)).orElse fun _ =>
  ((match n, T with
    | m + 1, .mu U =>
        if hd : Ty.Decl U then
          (checkVar? D b m x (U.substVar x)).map (fun h => .recI h hd)
        else none
    | _, _ => none) : Option (HasTy Γ (.path (.var x)) T)).orElse fun _ =>
  (viewAt T (views D b x)).orElse fun _ => viewSub D b.sub T (views D b x)
termination_by (n, 0, sizeTy T)

/-- Checking a definition list.  `DefsTy` is syntax directed on both the
definitions and the type (`lean/Coercions/DotMNF/Typing.lean:124-127`), so the
two are matched in lockstep: a type member against a declaration with its own
type on both bounds, a term member against a field declaration at the same
label, and an intersection against an intersection. -/
def checkDefs? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat)
    (d : ADefs s) (T : Ty s) : Option (DefsTy Γ d.erase T) :=
  match d, T with
  | .typ A S, .typ B L U =>
      if hA : A = B then
        if hL : S = L then
          if hU : S = U then some (defsTypAt hA hL hU) else none
        else none
      else none
  | .trm a t, .fld c U =>
      if h : a = c then (check? D b n t U).map (fun ht => defsTrmAt h ht) else none
  | .and d1 d2, .and T1 T2 =>
      (checkDefs? D b n d1 T1).bind (fun h1 =>
        (checkDefs? D b n d2 T2).map (fun h2 => .and h1 h2))
  | _, _ => none
termination_by (n, sizeADefs d, 2)

end

/-- The entry point.  It builds the declaration table of the context once and
runs the typer at `Budget.typer`. -/
def synthTop? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Synth Γ a.erase) :=
  synth? (decls b Γ) b b.typer a

/-! ## Fuel monotonicity

The theorem of F1.5 for this module, so that a caller may raise the typer's fuel
without redoing the argument.  It is the shape the target already uses for its
normalizer, `FCdot.closedAtomForm_le`
(`lean/Coercions/FCdot/FormAlgebra.lean:1472-1473`).  The statement is about
`isSome` and not about derivations, because more fuel may find another
derivation of the same judgment and `HasTy` is `Type` valued with no decidable
equality (`lean/Coercions/DotMNF/Typing.lean:7-9,67-129`).

The retry at the end of `synth?`'s fuel level is what makes this an induction on
the difference rather than a walk through every clause of all four functions.
`isSome_orElse_right` is `Search.lean`'s. -/

/-- One more unit of fuel never loses an answer. -/
theorem synth?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {n : Nat}
    {a : ATm s} (h : (synth? D b n a).isSome) : (synth? D b (n + 1) a).isSome := by
  rw [synth?.eq_def]
  exact isSome_orElse_right h

/-- More fuel never loses an answer (F1.5). -/
theorem synth?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} :
    ∀ {n n' : Nat}, n ≤ n' → ∀ {a : ATm s},
      (synth? D b n a).isSome → (synth? D b n' a).isSome := by
  intro n n'
  induction n' with
  | zero =>
      intro h a hs
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn
      exact hs
  | succ k ih =>
      intro h a hs
      cases Nat.lt_or_ge n (k + 1) with
      | inl hlt => exact synth?_succ (ih (Nat.lt_succ_iff.mp hlt) hs)
      | inr hge =>
          have hn : n = k + 1 := Nat.le_antisymm h hge
          subst hn
          exact hs

/-! ## The eight programs of F1.8

The deliverable of this group.  `synthTop? b .nil` is run on each of the eight
surface programs of F0, resolved by `Frontend.resolve`
(`lean/Coercions/Frontend/Resolve.lean`), and the type it returns is compared
against the type the hand written derivation of
`lean/Coercions/DotMNF/Examples.lean` concludes.  The typer returns the
derivation, so a success here is a `DotMNF.HasTy` and not an answer.

None of these is a `decide` or a `rfl`.  The typer is well-founded and does not
reduce in the kernel (F1.7), so every check runs compiled code through `expect`,
where a false result throws and fails the build.

The budget of each is the smallest at which it passes, measured over all
budgets with `decls` and `views` in `0..3`, `sub` in `0..4` and `typer` in
`1..3`, ordered by the sum.  The stage report carries the table and the timings.
Every one of the eight also passes at the single budget
`(decls 2, views 2, sub 2, typer 2)`, where the slowest is E4 at about two and a
half milliseconds.  The nominal defaults of `Budget` are not that budget and
should not be passed: E7, which searches for nothing at all, takes 0.4 seconds
at `(3, 3, 6, 8)` against 8 microseconds at its own budget.  A caller measures.

Three of the checks are negative, one unit of one counter short of the budget
above it, so that each of those three budgets measures the search and not an
accident of the table. -/

section Checks

open DotMNF.Examples

/-- The check: the typer synthesizes the type the hand written derivation
concludes.  `Ty` has `DecidableEq` (`lean/Coercions/DotMNF/Syntax.lean:62`), so
the comparison is a decision on the type, not on the derivation. -/
def synthsAt {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (T : Ty s) : Bool :=
  match synthTop? b Γ a with
  | some c => decide (c.ty = T)
  | none => false

/-- The whole front end so far, end to end: a surface program is resolved by
F0.5 and then typed by F1.4, and the type is compared against the vanilla one.
`Resolve.lean` proves `resolve exampleTable E1src = some E1ann` and its seven
companions by `rfl`, so this runs on exactly the resolutions named there. -/
def compilesAt (b : Budget) (tbl : LabelTable) (e : STm) (T : Ty []) : Bool :=
  match resolve tbl e with
  | some a => synthsAt b Ctx.nil a T
  | none => false

/-- E1, `λ(x : {A : ⊤..⊥}). let y : {B : Int..Int} = x in y`.  The `let` is
annotated, so the first rung of the ladder applies, and the body is retyped by
the bad bounds chain of `badBounds` (`Examples.lean:53-57`).  The type is the
one `E1` concludes (`Examples.lean:68-71`). -/
def bE1 : Budget := { decls := 1, views := 0, sub := 2, typer := 1 }

#eval expect (compilesAt bE1 exampleTable E1src (.all E1Dom E1Res))
  "E1: the typer does not conclude ∀(x : E1Dom) E1Res"

-- One round of `sub` short, the chain is not found, so the budget measures the
-- search and not an accident of the table.
#eval expect
  (! compilesAt { bE1 with sub := 1 } exampleTable E1src (.all E1Dom E1Res))
  "E1: the typer succeeds at sub fuel 1, so the budget is not measured"

/-- E2, the recursive literal allocated by a `let`, its member selected and
applied to itself.  The inner `let` takes the second rung of the ladder and is
typed at `x.A`; the outer one falls to the third rung, since `x.A` mentions the
binder it would escape, and is typed at `⊤`, which is what `E2` concludes
(`Examples.lean:124-129`). -/
def bE2 : Budget := { decls := 1, views := 2, sub := 2, typer := 1 }

#eval expect (compilesAt bE2 exampleTable E2src .top)
  "E2: the typer does not conclude ⊤"

-- One round of the closure short: the literal's `μ` is opened but its field is
-- not reached, so `x.a` has no view to read.
#eval expect (! compilesAt { bE2 with views := 1 } exampleTable E2src .top)
  "E2: the typer succeeds at one round of the closure, so the budget is not measured"

/-- E3, the intersection with a shared member.  The annotated `let` is checked
against `{a : ⊤}` through the two declarations of one variable at one label,
which is rule 11 of F1.3 with `d₁ ≠ d₂` and the chain of `E3sub`
(`Examples.lean:151`).  The type is `E3`'s (`Examples.lean:162-166`). -/
def bE3 : Budget := { decls := 1, views := 1, sub := 2, typer := 1 }

#eval expect (compilesAt bE3 exampleTable E3src (.all E3Dom (.all E3T2 E3T1)))
  "E3: the typer does not conclude ∀(x : E3Dom) ∀(z : E3T2) E3T1"

/-- E4, the counterexample of the paper's first section.  Two rounds of the
table are the minimum: the second adds `w`'s member `A` at `Int..⊤` through the
detour view step, and `g n` then typechecks by `E4nA` (`Examples.lean:213-216`).
The unannotated `let` takes the second rung of the ladder, since `w.A` does not
mention `g`.  The type is `E4`'s (`Examples.lean:228-234`). -/
def bE4 : Budget := { decls := 2, views := 1, sub := 2, typer := 1 }

#eval expect
  (compilesAt bE4 exampleTable E4src
    (.all E4X (.all E4S (.all E4Int (.sel (.var (.there .here)) lA)))))
  "E4: the typer does not conclude E4's type"

-- One round of the table short: `w` never reaches `{A : Int..⊤}`, so `g n`
-- has no argument derivation.
#eval expect
  (! compilesAt { bE4 with decls := 1 } exampleTable E4src
    (.all E4X (.all E4S (.all E4Int (.sel (.var (.there .here)) lA)))))
  "E4: the typer succeeds at one round of the table, so the budget is not measured"

/-- E5, an object returned from a function and selected after a `let`.  Both
`let`s take the second rung: the result `w.A` mentions neither binder, so
strengthening carries it out twice.  The type is `E5`'s
(`Examples.lean:296-300`). -/
def bE5 : Budget := { decls := 1, views := 1, sub := 2, typer := 1 }

#eval expect (compilesAt bE5 exampleTable E5src (.all E5AT (.sel (.var .here) lA)))
  "E5: the typer does not conclude ∀(w : E5AT) w.A"

/-- E6, a field typed at its own literal's type member.  The surface program is
`E6` under the lambda that binds the `n` its context holds, so the type is
`E6`'s conclusion under one `∀` (`Examples.lean:341-342`).  The field `v` is
checked against `x.T` by rule 9 of F1.3 through the self binder's own member,
which is `E6nT` (`Examples.lean:335-337`). -/
def bE6 : Budget := { decls := 1, views := 2, sub := 2, typer := 1 }

#eval expect (compilesAt bE6 exampleTable E6src (.all E6Int (.mu E6Self)))
  "E6: the typer does not conclude ∀(n : Int) μ(x. E6Self)"

/-- E7, the two element alias cycle.  Nothing is searched: both definitions are
type members and `DefsTy.typ` reads them off directly.  The type is `E7`'s
(`Examples.lean:367`). -/
def bE7 : Budget := { decls := 0, views := 0, sub := 0, typer := 1 }

#eval expect (compilesAt bE7 exampleTable E7src (.mu E7Self))
  "E7: the typer does not conclude μ(x. E7Self)"

/-- E8, refining an abstract type.  One round of the closure takes the right
operand of the intersection, which is `E8yFld2` (`Examples.lean:405`), and the
projection reads the field off it.  The type is `E8`'s
(`Examples.lean:427-430`). -/
def bE8 : Budget := { decls := 0, views := 1, sub := 0, typer := 1 }

#eval expect (compilesAt bE8 exampleTable E8src (.all E8Dom (.all (E8Ref .here) .top)))
  "E8: the typer does not conclude E8's type"

end Checks

end Frontend
