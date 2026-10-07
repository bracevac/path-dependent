import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.Frontend.Search

/-!
# The derivation producing typer

This module types an annotated term of the paths line.  It is fuel bounded,
`Option` valued, and sound by construction: `synth?` returns a `Synth`, whose
second field is the `Paths.DotMNF.HasTy` derivation, so soundness is the
result type and there is no soundness theorem to prove.

It is incomplete by necessity, since DOT subtyping is undecidable.  No
completeness theorem is attempted or claimed.  What the typer will not find is
a list, not a theorem.  It does not find a subtyping whose middle is outside
the selections of the path table, a `Rec-I` folding other than the goal's own
body, an `And-I` at a position where neither conjunct is checkable on its own,
or an avoidance result other than the annotation, the strengthening or `⊤`.  It
does not type an object literal without a self annotation, or an application
whose function variable reaches `∀` only past the first function view.  It
does not pose a `PathTy.recI` or a `PathTy.andI` goal at a path.  It does not
reach a path the table does not reach within its rounds, or a goal that only
replacement of a path by its alias would reach, since the version has no rule
for that.  And it finds nothing past the budget.

## The four functions

`synth?` reads a type off a term.  `check?` tests a term against a type.
`checkVar?` tests a variable against a type.  It is a function of its own
because three rules of the calculus conclude about a variable and are not
reached by subsumption: `HasTy.andI`, `HasTy.recI` and `HasTy.sngl`, the
bridge from a path typing at a singleton.  `checkDefs?` matches a definition
list against a type in lockstep, which is what `DefsTy` does.

## The path table

Every function takes the path table of its context, `PTable Γ`, built once by
the caller.  Under a binder the table is rebuilt at the extended context:
`Γ.cons S` for a lambda and for a `let` body, `Γ.consSelf d T` for the
definitions of a literal.  Projection reads a field off a view of the table
(`HasTy.projP`).  A singleton goal at a variable is a path typing, asked of
`checkPath?`.  The declarations of the table are the middles the subtyping
search tries.

## Two checking clauses

`check?` has two clauses that synthesis does not cover.  A lambda against
`∀(x : S) T` with the same domain checks its body against `T` by
`HasTy.lam`.  A `let` without annotation against a goal `U` checks its body
against `U` weakened by `HasTy.let`.  The body then sees its own binder at the
type the bound term synthesized, which the synthesized type of the whole term
may have lost.  When either clause fails, the term is synthesized and moved to
the goal, as every other term is.

## The avoidance ladder

`HasTy.let` takes `HasTy (Γ.cons T) u U.weaken` for a `U` the rule does not
determine.  Three rungs are tried in order: the surface annotation, the
strengthening of the body's synthesized type, and `⊤`.  Every rung decides
`Ty.Wf` of its result, a premise of the rule.  The third always applies and
always loses information.

## Fuel

The four functions form one block, structural on the typer's fuel.  Every
recursive call is at the fuel one below, so the fuel bounds the depth of the
term and of the goal together, and costs nothing else.  The subtyping search
is always called at `Budget.sub`, its own counter, never at the typer's fuel.

Each function ends its fuel level with a retry at the level below.  The retry
is not a rule of the calculus and changes no answer the clauses give, since
every clause is tried at the higher level with more fuel than at the lower
one.  What it buys is a monotonicity theorem per function, an induction on the
difference of the fuels.

The whole block reduces in the kernel, so the checks at the end are
`decide +kernel` facts.  Nothing of this module is part of the metatheory, and
no definition lives in the `Paths.DotMNF` or `Paths.FCdot` namespaces.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Tm Defs Ctx Sub PathTy HasTy DefsTy)

/-! ## The result of a synthesis

The derivation is a field, so a caller that gets a `Synth` has the typing and
not merely an answer. -/

/-- A type a term has, with the derivation that it has it. -/
structure Synth {s : Sig} (Γ : Ctx s) (t : Tm s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ t ty

/-! ## Casts across a decided equality

The derivations below move across a decided equality of labels or of types.
They are written with `cases` rather than with `▸` because a label occurs
twice in the conclusion of the rule that carries it, and a rewrite would hit
both occurrences. -/

/-- A projection read off a path view of the receiver at the label asked for. -/
def projAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a c : Label} {T : Ty s}
    (h : c = a) (d : PathTy Γ (.var x) (.fld c T)) : HasTy Γ (.proj x a) T := by
  cases h; exact .projP d

/-- A projection read off a stable field of the receiver at the label asked
for, through `Sub.vfldToFld`. -/
def projVAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a c : Label} {T : Ty s}
    (h : c = a) (d : PathTy Γ (.var x) (.vfld c T)) : HasTy Γ (.proj x a) T := by
  cases h; exact .projP (.sub d .vfldToFld)

/-- A type member definition against a declaration whose two bounds are the
definition's own type.  `DefsTy.typ` is the only rule for a type member and it
concludes at exactly those bounds. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {A B : Label} {S L U : Ty s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- A member whose body is an object literal against a stable field declared
at the literal's own self type, `DefsTy.trmObj`. -/
def defsObjAt {s : Sig} {Γ : Ctx s} {a c : Label} {d : Defs (s,x)} {T U : Ty (s,x)}
    (h : a = c) (hT : T = U) (hd : DefsTy (Γ.consSelf d T) d T) (hdist : Defs.Distinct d) :
    DefsTy Γ (.trm a (.val (.obj d))) (.vfld c (.mu U)) := by
  cases h; cases hT; exact .trmObj hd hdist

/-- A lambda checked against a function type with the same domain. -/
def lamAt {s : Sig} {Γ : Ctx s} {S S' : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (h : S = S') (ht : HasTy (Γ.cons S) t T) (hwf : Ty.Wf S) :
    HasTy Γ (.val (.lam S t)) (.all S' T) := by
  cases h; exact .lam ht hwf

/-- `⊤` is its own weakening, which is what the third rung of the avoidance
ladder needs to hand `HasTy.let` a body typing at `U.weaken`. -/
theorem weaken_top {s : Sig} {k : Kind} : (Ty.top : Ty s).weaken (k := k) = .top := rfl

/-! ## Reading a view

The typer consults the term views of `Search.lean` and the path table.  The
readers walk a list with `List.findSome?`, none of them recurses, and none is
part of the block. -/

/-- A function type a variable has, with the derivation. -/
structure AllView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The domain. -/
  dom : Ty s
  /-- The codomain, under the domain's binder. -/
  cod : Ty (s,x)
  /-- The derivation. -/
  deriv : HasTy Γ (.path x) (.all dom cod)

/-- The first term view that is a function type.  Only the first is tried: an
application whose function variable reaches `∀` further down the list is on the
list of what the typer will not find. -/
def allView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (AllView Γ x) :=
  vs.findSome? (fun v =>
    match hv : v.ty with
    | .all S T => some ⟨S, T, hv ▸ v.deriv⟩
    | _ => none)

/-- A projection `x.a`, from the first view of the row of `x` in the path table
that is a field or a stable field at `a`. -/
def projView {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (x : BVar s .var) (a : Label) :
    Option (Synth Γ (.proj x a)) :=
  (tbl.viewsAt (.var x)).findSome? fun v =>
    match hv : v.ty with
    | .fld c T => if h : c = a then some ⟨T, projAt h (hv ▸ v.deriv)⟩ else none
    | .vfld c T => if h : c = a then some ⟨T, projVAt h (hv ▸ v.deriv)⟩ else none
    | _ => none

/-- The first term view at exactly the type asked for. -/
def viewAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} (T : Ty s)
    (vs : List (View Γ x)) : Option (HasTy Γ (.path x) T) :=
  vs.findSome? (fun v => if h : v.ty = T then some (h ▸ v.deriv) else none)

/-- The first term view that the subtyping search takes to the type asked for,
through `HasTy.sub`. -/
def viewSub {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : List (PDecl Γ)) (n : Nat)
    (T : Ty s) (vs : List (View Γ x)) : Option (HasTy Γ (.path x) T) :=
  vs.findSome? (fun v => (sub? D n v.ty T).map (fun e => .sub v.deriv e))

/-- A synthesized type moved to the goal: by a decided equality, or by the
subtyping search through `HasTy.sub`. -/
def toGoal {s : Sig} {Γ : Ctx s} {t : Tm s} (D : List (PDecl Γ)) (n : Nat) (T : Ty s)
    (c : Synth Γ t) : Option (HasTy Γ t T) :=
  if h : c.ty = T then some (h ▸ c.deriv)
  else (sub? D n c.ty T).map (fun e => .sub c.deriv e)

/-! ## The typer -/

mutual

/-- Synthesis, clause by clause, every premise at the fuel one below.

- A variable returns `Ctx.lookup` and `HasTy.var`, exact, nothing guessed.
- `λ(x : S). t` decides `Ty.Wf S` and synthesizes the body under `Γ.cons S`
  against a table rebuilt there.
- `ν(x : T. d)` checks the definitions under `Γ.consSelf d.erase T` against a
  table rebuilt there and decides `Defs.Distinct`.
- `x y` reads the first function view of `x` and checks `y` against its
  domain.
- `x.a` reads a field of `x` off the path table, by `HasTy.projP`.
- `let x (: U)? = t in u` climbs the three rung avoidance ladder.

The last alternative retries at the fuel one below. -/
def synth? {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (b : Budget) :
    (n : Nat) → (a : ATm s) → Option (Synth Γ a.erase)
  | 0, _ => none
  | n + 1, a =>
      ((match a with
        | .path x => some ⟨Ctx.lookup Γ x, .var⟩
        | .lam S t =>
            if hwf : Ty.Wf S then
              (synth? (table b (Γ.cons S)) b n t).map (fun c =>
                ⟨.all S c.ty, .lam c.deriv hwf⟩)
            else none
        | .obj T d =>
            (checkDefs? (table b (Γ.consSelf d.erase T)) b n d T).bind (fun hd =>
              if hdist : Defs.Distinct d.erase then some ⟨.mu T, .obj hd hdist⟩
              else none)
        | .app x y =>
            (allView (views (declsOf tbl) b x)).bind (fun v =>
              (checkVar? tbl b n y v.dom).map (fun hy =>
                ⟨v.cod.substVar y, .app v.deriv hy⟩))
        | .proj x a => projView tbl x a
        | .let ann t u =>
            (synth? tbl b n t).bind (fun c1 =>
              let tbl' := table b (Γ.cons c1.ty)
              -- rung one: the surface annotation
              ((match ann with
                | some U =>
                    if hwf : Ty.Wf U then
                      (check? tbl' b n u U.weaken).map (fun h2 => ⟨U, .let c1.deriv h2 hwf⟩)
                    else none
                | none => none) :
                  Option (Synth Γ (ATm.let ann t u).erase)).orElse fun _ =>
              ((synth? tbl' b n u).bind (fun c2 =>
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
        : Option (Synth Γ a.erase))).orElse fun _ => synth? tbl b n a
termination_by structural n => n

/-- Checking, every premise at the fuel one below.

- A variable goes to `checkVar?`, which reaches the rules subsumption does
  not.
- A lambda against `∀(x : S') T` with `S = S'` checks its body against `T`
  under `Γ.cons S`, by `HasTy.lam`.
- A `let` without annotation against `U` synthesizes the bound term and checks
  the body against `U.weaken`, by `HasTy.let`.
- Every term, those three included when their clause fails, is synthesized
  and moved to the goal by a decided equality or by the subtyping search.

The last alternative retries at the fuel one below. -/
def check? {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (b : Budget) :
    (n : Nat) → (a : ATm s) → (T : Ty s) → Option (HasTy Γ a.erase T)
  | 0, _, _ => none
  | n + 1, a, T =>
      ((match a, T with
        | .path x, T => checkVar? tbl b n x T
        | .lam S t, .all S' T' =>
            if h : S = S' then
              if hwf : Ty.Wf S then
                (check? (table b (Γ.cons S)) b n t T').map (fun ht => lamAt h ht hwf)
              else none
            else none
        | .let none t u, T =>
            if hwf : Ty.Wf T then
              (synth? tbl b n t).bind (fun c1 =>
                (check? (table b (Γ.cons c1.ty)) b n u T.weaken).map (fun h2 =>
                  .let c1.deriv h2 hwf))
            else none
        | _, _ => none) : Option (HasTy Γ a.erase T)).orElse fun _ =>
      ((synth? tbl b n a).bind (toGoal (declsOf tbl) b.sub T)).orElse fun _ =>
      check? tbl b n a T
termination_by structural n => n

/-- Checking a variable, every premise at the fuel one below.  Four rules, in
order.

1. A singleton goal `q.type` is a path typing of the variable, asked of
   `checkPath?` and bridged by `HasTy.sngl`.
2. An intersection goal splits by `HasTy.andI`, the one rule that combines two
   typings of a single variable.
3. A `μ` goal whose body is declaration shaped folds by `HasTy.recI`.  `Sub`
   relates two `μ` types only through the abstract view, so a `μ` goal is
   otherwise out of reach from an opened type.
4. Otherwise the term views are consulted, first for a view at exactly the
   goal and then for a view the subtyping search takes there.

The last alternative retries at the fuel one below. -/
def checkVar? {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (b : Budget) :
    (n : Nat) → (x : BVar s .var) → (T : Ty s) → Option (HasTy Γ (.path x) T)
  | 0, _, _ => none
  | n + 1, x, T =>
      ((match T with
        | .sngl q =>
            (checkPath? tbl (declsOf tbl) b.sub (.var x) (.sngl q)).map HasTy.sngl
        | _ => none) : Option (HasTy Γ (.path x) T)).orElse fun _ =>
      ((match T with
        | .and T1 T2 =>
            (checkVar? tbl b n x T1).bind (fun h1 =>
              (checkVar? tbl b n x T2).map (fun h2 => .andI h1 h2))
        | _ => none) : Option (HasTy Γ (.path x) T)).orElse fun _ =>
      ((match T with
        | .mu U =>
            if hd : Ty.Decl U then
              (checkVar? tbl b n x (U.substVar x)).map (fun h => .recI h hd)
            else none
        | _ => none) : Option (HasTy Γ (.path x) T)).orElse fun _ =>
      (let vs := views (declsOf tbl) b x
       (viewAt T vs).orElse fun _ => viewSub (declsOf tbl) b.sub T vs).orElse fun _ =>
      checkVar? tbl b n x T
termination_by structural n => n

/-- Checking a definition list, every premise at the fuel one below.
`DefsTy` is syntax directed on both the definitions and the type, so the two
are matched in lockstep:

- A type member against a declaration with its own type on both bounds.
- A member whose body is an object literal against a stable field declared at
  the literal's self type, by `DefsTy.trmObj`, the literal's definitions
  checked under its own self binder against a table rebuilt there.
- A term member against a field declaration at the same label.
- An intersection against an intersection.

The last alternative retries at the fuel one below. -/
def checkDefs? {s : Sig} {Γ : Ctx s} (tbl : PTable Γ) (b : Budget) :
    (n : Nat) → (d : ADefs s) → (T : Ty s) → Option (DefsTy Γ d.erase T)
  | 0, _, _ => none
  | n + 1, d, T =>
      ((match d, T with
        | .typ A S, .typ B L U =>
            if hA : A = B then
              if hL : S = L then
                if hU : S = U then some (defsTypAt hA hL hU) else none
              else none
            else none
        | .trm a (.obj T' d'), .vfld c (.mu U) =>
            if h : a = c then
              if hT : T' = U then
                (checkDefs? (table b (Γ.consSelf d'.erase T')) b n d' T').bind (fun hd =>
                  if hdist : Defs.Distinct d'.erase then some (defsObjAt h hT hd hdist)
                  else none)
              else none
            else none
        | .trm a t, .fld c U =>
            if h : a = c then (check? tbl b n t U).map (fun ht => defsTrmAt h ht) else none
        | .and d1 d2, .and T1 T2 =>
            (checkDefs? tbl b n d1 T1).bind (fun h1 =>
              (checkDefs? tbl b n d2 T2).map (fun h2 => .and h1 h2))
        | _, _ => none) : Option (DefsTy Γ d.erase T)).orElse fun _ =>
      checkDefs? tbl b n d T
termination_by structural n => n

end

/-- The entry point at a context.  It builds the path table of the context
once and runs the typer at `Budget.typer`.  A program the version types under
a context is typed here at that context. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Synth Γ a.erase) :=
  synth? (table b Γ) b b.typer a

/-- The entry point for a closed program. -/
def synthTop? (b : Budget) (a : ATm []) : Option (Synth Ctx.nil a.erase) :=
  synthIn? b .nil a

/-- Checking at a context against a given type, with the path table of the
context built once.  Synthesis keeps the most precise type the ladder finds.
This entry point asks for a given judgment instead, which may be weaker. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (T : Ty s) :
    Option (HasTy Γ a.erase T) :=
  check? (table b Γ) b b.typer a T

/-! ## Fuel monotonicity

One theorem per function, so that a caller may raise the typer's fuel without
redoing the argument.  The statement is about `isSome` and not about
derivations, because more fuel may find another derivation of the same
judgment, and `HasTy` is `Type` valued with no decidable equality.  The retry
at the end of each fuel level makes each an induction on the difference.
Nothing is claimed for the other counters of the budget. -/

/-- One more unit of fuel never loses a synthesis. -/
theorem synth?_succ {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} {n : Nat}
    {a : ATm s} (h : (synth? tbl b n a).isSome) : (synth? tbl b (n + 1) a).isSome := by
  rw [synth?.eq_def]
  exact isSome_orElse_right h

/-- More fuel never loses a synthesis. -/
theorem synth?_le {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} :
    ∀ {n n' : Nat}, n ≤ n' → ∀ {a : ATm s},
      (synth? tbl b n a).isSome → (synth? tbl b n' a).isSome := by
  intro n n' h
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => synth?_succ (ih hs)

/-- One more unit of fuel never loses a check. -/
theorem check?_succ {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} {n : Nat}
    {a : ATm s} {T : Ty s} (h : (check? tbl b n a T).isSome) :
    (check? tbl b (n + 1) a T).isSome := by
  rw [check?.eq_def]
  iterate 2 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a check. -/
theorem check?_le {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} :
    ∀ {n n' : Nat}, n ≤ n' → ∀ {a : ATm s} {T : Ty s},
      (check? tbl b n a T).isSome → (check? tbl b n' a T).isSome := by
  intro n n' h
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => check?_succ (ih hs)

/-- One more unit of fuel never loses a check of a variable. -/
theorem checkVar?_succ {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} {n : Nat}
    {x : BVar s .var} {T : Ty s} (h : (checkVar? tbl b n x T).isSome) :
    (checkVar? tbl b (n + 1) x T).isSome := by
  rw [checkVar?.eq_def]
  iterate 4 refine isSome_orElse_right ?_
  exact h

/-- More fuel never loses a check of a variable. -/
theorem checkVar?_le {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} :
    ∀ {n n' : Nat}, n ≤ n' → ∀ {x : BVar s .var} {T : Ty s},
      (checkVar? tbl b n x T).isSome → (checkVar? tbl b n' x T).isSome := by
  intro n n' h
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => checkVar?_succ (ih hs)

/-- One more unit of fuel never loses a check of a definition list. -/
theorem checkDefs?_succ {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} {n : Nat}
    {d : ADefs s} {T : Ty s} (h : (checkDefs? tbl b n d T).isSome) :
    (checkDefs? tbl b (n + 1) d T).isSome := by
  rw [checkDefs?.eq_def]
  exact isSome_orElse_right h

/-- More fuel never loses a check of a definition list. -/
theorem checkDefs?_le {s : Sig} {Γ : Ctx s} {tbl : PTable Γ} {b : Budget} :
    ∀ {n n' : Nat}, n ≤ n' → ∀ {d : ADefs s} {T : Ty s},
      (checkDefs? tbl b n d T).isSome → (checkDefs? tbl b n' d T).isSome := by
  intro n n' h
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => checkDefs?_succ (ih hs)

/-! ## The programs of the version

Every surface program of `Notation.lean` is resolved by `resolve` and typed by
`synthTop?`, and the type it synthesizes is compared with the type the
version's own derivation concludes in
`lean/Coercions/Paths/DotMNF/Examples.lean`.  The typer returns the
derivation, so a success here is a `Paths.DotMNF.HasTy` and not an answer.
`Ty` has decidable equality, so the comparison is a decision on the type,
not on the derivation.  Resolution and the typer are structural, so every
check is a `decide +kernel` fact.

Each budget is one at which the program types.  Beside it, each counter that is
not zero is lowered by one with the others kept, and the program does not type
there.  So each budget is least in each counter on its own.  It is not claimed
that no smaller budget types the program, since the counters trade off: Fig. 2
types at views 2 and search 3, and at views 1 and search 4, and not at views 1
and search 3.  Nor is it claimed that the program fails below the budget in
general, since only the typer's own fuel is monotone.

Three programs are written closed where the version types them under a
context, X3, E6 and X4.  The context entry becomes a lambda, and the type is
the version's type under one `∀`.  The same three are typed at the version's
own context further below, through `synthIn?`. -/

section Checks

open Paths.DotMNF.Examples

/-- The type a derivation of the version concludes. -/
def versionTy {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Ty s := T

/-- The check: the program resolves, the typer synthesizes a type at the
budget, and that type is `T`. -/
def typesAt (b : Budget) (e : STm) (T : Ty []) : Bool :=
  match resolve pathsTable e with
  | some a =>
      match synthTop? b a with
      | some c => decide (c.ty = T)
      | none => false
  | none => false

/-- The program resolves and the typer synthesizes some type at the budget. -/
def typesSome (b : Budget) (e : STm) : Bool :=
  match resolve pathsTable e with
  | some a => (synthTop? b a).isSome
  | none => false

/-- The type Fig. 1 synthesizes: the self type of `pcore`, strengthened past
the binder of `o`, which it does not mention. -/
def Fig1_ty : Ty [] := (tyStrengthen? (Ty.mu Fig1_pBody)).getD .bot

/-- E1, bad bounds at a variable.  The annotated `let` is checked through the
chain `⊤ <: x.A <: ⊥` of the one declaration of `x`. -/
def bE1 : Budget := { table := 0, views := 1, sub := 1, typer := 4, rows := 0 }

example : typesAt bE1 E1_src (versionTy E1) = true := by decide +kernel
example : typesAt { bE1 with views := 0 } E1_src (versionTy E1) = false := by
  decide +kernel
example : typesAt { bE1 with sub := 0 } E1_src (versionTy E1) = false := by
  decide +kernel
example : typesAt { bE1 with typer := 3 } E1_src (versionTy E1) = false := by
  decide +kernel

/-- E2, a recursive literal allocated by a `let`, its member selected and
applied to itself.  The outer `let` falls to `⊤`, as the version's does. -/
def bE2 : Budget := { table := 2, views := 0, sub := 2, typer := 7, rows := 0 }

example : typesAt bE2 E2_src (versionTy E2) = true := by decide +kernel
example : typesAt { bE2 with table := 1 } E2_src (versionTy E2) = false := by
  decide +kernel
example : typesAt { bE2 with sub := 1 } E2_src (versionTy E2) = false := by
  decide +kernel
example : typesAt { bE2 with typer := 6 } E2_src (versionTy E2) = false := by
  decide +kernel

/-- E3, two declarations of one label at one variable, the pair rule of the
search. -/
def bE3 : Budget := { table := 1, views := 0, sub := 2, typer := 5, rows := 0 }

example : typesAt bE3 E3_src (versionTy E3) = true := by decide +kernel
example : typesAt { bE3 with table := 0 } E3_src (versionTy E3) = false := by
  decide +kernel
example : typesAt { bE3 with sub := 1 } E3_src (versionTy E3) = false := by
  decide +kernel
example : typesAt { bE3 with typer := 4 } E3_src (versionTy E3) = false := by
  decide +kernel

/-- E4, the counterexample of the paper's first section.  The detour step of the
table gives `w` its member `A` at `Int..⊤`. -/
def bE4 : Budget := { table := 1, views := 0, sub := 2, typer := 6, rows := 0 }

example : typesAt bE4 E4_src (versionTy E4) = true := by decide +kernel
example : typesAt { bE4 with table := 0 } E4_src (versionTy E4) = false := by
  decide +kernel
example : typesAt { bE4 with sub := 1 } E4_src (versionTy E4) = false := by
  decide +kernel
example : typesAt { bE4 with typer := 5 } E4_src (versionTy E4) = false := by
  decide +kernel

/-- E5, an object returned from a function and selected after a `let`.  Both
`let`s take the strengthening rung, so the result is `w.A` and not `⊤`. -/
def bE5 : Budget := { table := 1, views := 0, sub := 2, typer := 7, rows := 0 }

example : typesAt bE5 E5_src (versionTy E5) = true := by decide +kernel
example : typesAt { bE5 with table := 0 } E5_src (versionTy E5) = false := by
  decide +kernel
example : typesAt { bE5 with sub := 1 } E5_src (versionTy E5) = false := by
  decide +kernel
example : typesAt { bE5 with typer := 6 } E5_src (versionTy E5) = false := by
  decide +kernel

/-- E6, a field typed at its own literal's type member, under the lambda that
binds the version's context entry. -/
def bE6 : Budget := { table := 2, views := 0, sub := 2, typer := 6, rows := 0 }

example : typesAt bE6 E6_src (.all E6Int (versionTy E6)) = true := by decide +kernel
example : typesAt { bE6 with table := 1 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel
example : typesAt { bE6 with sub := 1 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel
example : typesAt { bE6 with typer := 5 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel

/-- E7, a two element alias cycle of type members.  Nothing is searched. -/
def bE7 : Budget := { table := 0, views := 0, sub := 0, typer := 3, rows := 0 }

example : typesAt bE7 E7_src (versionTy E7) = true := by decide +kernel
example : typesAt { bE7 with typer := 2 } E7_src (versionTy E7) = false := by
  decide +kernel

/-- E8, refining an abstract type.  The projection reads the field off the right
side of the intersection. -/
def bE8 : Budget := { table := 1, views := 0, sub := 0, typer := 3, rows := 0 }

example : typesAt bE8 E8_src (versionTy E8) = true := by decide +kernel
example : typesAt { bE8 with table := 0 } E8_src (versionTy E8) = false := by
  decide +kernel
example : typesAt { bE8 with typer := 2 } E8_src (versionTy E8) = false := by
  decide +kernel

/-- E1p, bad bounds at the path `w.f`. -/
def bE1p : Budget := { table := 1, views := 1, sub := 1, typer := 4, rows := 1 }

example : typesAt bE1p E1p_src (versionTy E1p) = true := by decide +kernel
example : typesAt { bE1p with table := 0 } E1p_src (versionTy E1p) = false := by
  decide +kernel
example : typesAt { bE1p with views := 0 } E1p_src (versionTy E1p) = false := by
  decide +kernel
example : typesAt { bE1p with sub := 0 } E1p_src (versionTy E1p) = false := by
  decide +kernel
example : typesAt { bE1p with typer := 3 } E1p_src (versionTy E1p) = false := by
  decide +kernel
example : typesAt { bE1p with rows := 0 } E1p_src (versionTy E1p) = false := by
  decide +kernel

/-- E2p, a function at a member of the path `x.c`, applied to itself. -/
def bE2p : Budget := { table := 4, views := 0, sub := 2, typer := 8, rows := 1 }

example : typesAt bE2p E2p_src (versionTy E2p) = true := by decide +kernel
example : typesAt { bE2p with table := 3 } E2p_src (versionTy E2p) = false := by
  decide +kernel
example : typesAt { bE2p with sub := 1 } E2p_src (versionTy E2p) = false := by
  decide +kernel
example : typesAt { bE2p with typer := 7 } E2p_src (versionTy E2p) = false := by
  decide +kernel
example : typesAt { bE2p with rows := 0 } E2p_src (versionTy E2p) = false := by
  decide +kernel

/-- E3p, the pair rule at two declarations of a path. -/
def bE3p : Budget := { table := 2, views := 0, sub := 2, typer := 5, rows := 1 }

example : typesAt bE3p E3p_src (versionTy E3p) = true := by decide +kernel
example : typesAt { bE3p with table := 1 } E3p_src (versionTy E3p) = false := by
  decide +kernel
example : typesAt { bE3p with sub := 1 } E3p_src (versionTy E3p) = false := by
  decide +kernel
example : typesAt { bE3p with typer := 4 } E3p_src (versionTy E3p) = false := by
  decide +kernel
example : typesAt { bE3p with rows := 0 } E3p_src (versionTy E3p) = false := by
  decide +kernel

/-- E4p, the counterexample of E4 with the two bounds read off the path `x.f`. -/
def bE4p : Budget := { table := 2, views := 0, sub := 2, typer := 6, rows := 1 }

example : typesAt bE4p E4p_src (versionTy E4p) = true := by decide +kernel
example : typesAt { bE4p with table := 1 } E4p_src (versionTy E4p) = false := by
  decide +kernel
example : typesAt { bE4p with sub := 1 } E4p_src (versionTy E4p) = false := by
  decide +kernel
example : typesAt { bE4p with typer := 5 } E4p_src (versionTy E4p) = false := by
  decide +kernel
example : typesAt { bE4p with rows := 0 } E4p_src (versionTy E4p) = false := by
  decide +kernel

/-- E5p, an object returned from a function and selected through a stable
field. -/
def bE5p : Budget := { table := 1, views := 0, sub := 2, typer := 8, rows := 0 }

example : typesAt bE5p E5p_src (versionTy E5p) = true := by decide +kernel
example : typesAt { bE5p with table := 0 } E5p_src (versionTy E5p) = false := by
  decide +kernel
example : typesAt { bE5p with sub := 1 } E5p_src (versionTy E5p) = false := by
  decide +kernel
example : typesAt { bE5p with typer := 7 } E5p_src (versionTy E5p) = false := by
  decide +kernel

/-- E6p, a stable field whose body is a literal, `DefsTy.trmObj`. -/
def bE6p : Budget := { table := 4, views := 0, sub := 2, typer := 6, rows := 1 }

example : typesAt bE6p E6p_src (versionTy E6p) = true := by decide +kernel
example : typesAt { bE6p with table := 3 } E6p_src (versionTy E6p) = false := by
  decide +kernel
example : typesAt { bE6p with sub := 1 } E6p_src (versionTy E6p) = false := by
  decide +kernel
example : typesAt { bE6p with typer := 5 } E6p_src (versionTy E6p) = false := by
  decide +kernel
example : typesAt { bE6p with rows := 0 } E6p_src (versionTy E6p) = false := by
  decide +kernel

/-- E7p, a two element alias cycle below a stable field. -/
def bE7p : Budget := { table := 0, views := 0, sub := 0, typer := 4, rows := 0 }

example : typesAt bE7p E7p_src (versionTy E7p_lit) = true := by decide +kernel
example : typesAt { bE7p with typer := 3 } E7p_src (versionTy E7p_lit) = false := by
  decide +kernel

/-- E8p, refining an abstract type at the path `x.f`. -/
def bE8p : Budget := { table := 1, views := 0, sub := 0, typer := 3, rows := 0 }

example : typesAt bE8p E8p_src (versionTy E8p) = true := by decide +kernel
example : typesAt { bE8p with table := 0 } E8p_src (versionTy E8p) = false := by
  decide +kernel
example : typesAt { bE8p with typer := 2 } E8p_src (versionTy E8p) = false := by
  decide +kernel

/-- X1, a literal whose member is bounded by a selection at a path of length
two. -/
def bX1 : Budget := { table := 0, views := 0, sub := 0, typer := 4, rows := 0 }

example : typesAt bX1 X1_src (versionTy (X1_lit (Γ := Ctx.nil))) = true := by decide +kernel
example : typesAt { bX1 with typer := 3 } X1_src (versionTy (X1_lit (Γ := Ctx.nil))) = false := by
  decide +kernel

/-- X2, a computation field, typed by `DefsTy.trm` and not by the stable rule. -/
def bX2 : Budget := { table := 1, views := 0, sub := 0, typer := 4, rows := 0 }

example : typesAt bX2 X2_src (versionTy (X2_lit (Γ := Ctx.nil))) = true := by decide +kernel
example : typesAt { bX2 with table := 0 } X2_src (versionTy (X2_lit (Γ := Ctx.nil))) = false := by
  decide +kernel
example : typesAt { bX2 with typer := 3 } X2_src (versionTy (X2_lit (Γ := Ctx.nil))) = false := by
  decide +kernel

/-- X3, `projP` through two stable fields, under the lambda that binds the
version's context entry. -/
def bX3 : Budget := { table := 0, views := 0, sub := 0, typer := 3, rows := 0 }

example : typesAt bX3 X3_src (.all X3_A (versionTy X3)) = true := by decide +kernel
example : typesAt { bX3 with typer := 2 } X3_src (.all X3_A (versionTy X3)) = false := by
  decide +kernel

/-- X4, the `types` module of gDOT Fig. 2 alone, under the lambda that binds the
version's context entry. -/
def bX4 : Budget := { table := 5, views := 2, sub := 3, typer := 10, rows := 0 }

example : typesAt bX4 X4_src (.all .top (versionTy X4_lit0)) = true := by decide +kernel
example : typesAt { bX4 with table := 4 } X4_src (.all .top (versionTy X4_lit0)) = false := by
  decide +kernel
example : typesAt { bX4 with views := 1 } X4_src (.all .top (versionTy X4_lit0)) = false := by
  decide +kernel
example : typesAt { bX4 with sub := 2 } X4_src (.all .top (versionTy X4_lit0)) = false := by
  decide +kernel
example : typesAt { bX4 with typer := 9 } X4_src (.all .top (versionTy X4_lit0)) = false := by
  decide +kernel

/-- E9, a singleton field and a `let` at a singleton. -/
def bE9 : Budget := { table := 1, views := 0, sub := 0, typer := 6, rows := 0 }

example : typesAt bE9 E9_src (versionTy E9) = true := by decide +kernel
example : typesAt { bE9 with table := 0 } E9_src (versionTy E9) = false := by
  decide +kernel
example : typesAt { bE9 with typer := 5 } E9_src (versionTy E9) = false := by
  decide +kernel

/-- E11, a stable field beside a singleton field. -/
def bE11 : Budget := { table := 0, views := 0, sub := 0, typer := 6, rows := 0 }

example : typesAt bE11 E11_src (versionTy E11) = true := by decide +kernel
example : typesAt { bE11 with typer := 5 } E11_src (versionTy E11) = false := by
  decide +kernel

/-- P3e, bad bounds through a computation field. -/
def bP3e : Budget := { table := 2, views := 0, sub := 0, typer := 6, rows := 0 }

example : typesAt bP3e P3e_src (versionTy P3e_lit) = true := by decide +kernel
example : typesAt { bP3e with table := 1 } P3e_src (versionTy P3e_lit) = false := by
  decide +kernel
example : typesAt { bP3e with typer := 5 } P3e_src (versionTy P3e_lit) = false := by
  decide +kernel

/-- gDOT Fig. 2, the `Option` encoding.  The type mentions the binder of `o`, so
the outer `let` falls to `⊤`, the version's type. -/
def bFig2 : Budget := { table := 5, views := 2, sub := 3, typer := 15, rows := 0 }

example : typesAt bFig2 Fig2_src (versionTy Fig2_prog_ty) = true := by decide +kernel
example : typesAt { bFig2 with table := 4 } Fig2_src (versionTy Fig2_prog_ty) = false := by
  decide +kernel
example : typesAt { bFig2 with views := 1 } Fig2_src (versionTy Fig2_prog_ty) = false := by
  decide +kernel
example : typesAt { bFig2 with sub := 2 } Fig2_src (versionTy Fig2_prog_ty) = false := by
  decide +kernel
example : typesAt { bFig2 with typer := 14 } Fig2_src (versionTy Fig2_prog_ty) = false := by
  decide +kernel

/-- pDOT Fig. 1.  Its self type mentions neither `let` binder, so both `let`s
take the strengthening rung and the program synthesizes `Fig1_ty`. -/
def bFig1 : Budget := { table := 5, views := 2, sub := 3, typer := 15, rows := 0 }

example : typesAt bFig1 Fig1_src (Fig1_ty) = true := by decide +kernel
example : typesAt { bFig1 with table := 4 } Fig1_src (Fig1_ty) = false := by
  decide +kernel
example : typesAt { bFig1 with views := 1 } Fig1_src (Fig1_ty) = false := by
  decide +kernel
example : typesAt { bFig1 with sub := 2 } Fig1_src (Fig1_ty) = false := by
  decide +kernel
example : typesAt { bFig1 with typer := 14 } Fig1_src (Fig1_ty) = false := by
  decide +kernel

/-- The strengthening `Fig1_ty` exists: the self type of `pcore` does not
mention `o`. -/
example : (tyStrengthen? (Ty.mu Fig1_pBody)).isSome = true := by decide +kernel

/-- The version types Fig. 1 at `⊤`.  The typer reaches that judgment too, by
checking against `⊤`, where the synthesized `Fig1_ty` is moved by `Sub.top`. -/
example : (match resolve pathsTable Fig1_src with
    | some a => (checkIn? bFig1 .nil a .top).isSome
    | none => false) = true := by decide +kernel

/-! ### The programs at the version's contexts

X3, E6 and X4 are typed by the version under a context.  Here the body of the
closed program, under its one lambda, is typed by `synthIn?` at that context,
and the type is the version's own. -/

/-- The body of a closed program under its outer lambda, typed at a context. -/
def bodyTypesIn (b : Budget) (Γ : Ctx ([],x)) (e : STm) (T : Ty ([],x)) : Bool :=
  match resolve pathsTable e with
  | some (.lam _ a) =>
      match synthIn? b Γ a with
      | some c => decide (c.ty = T)
      | none => false
  | _ => false

/-- X3, E6 and X4 at the contexts of the version, each at the type of the
version's derivation. -/
example : bodyTypesIn bX3 X3_Ctx X3_src (versionTy X3) = true := by decide +kernel
example : bodyTypesIn bE6 E6Ctx1 E6_src (versionTy E6) = true := by decide +kernel
example : bodyTypesIn bX4 X4_Ctx X4_src (versionTy X4_lit0) = true := by decide +kernel

/-- X3 resolved open, at the name of its context's one entry, then typed at
that context. -/
example : (match resolveIn pathsTable (.cons .nil "x") (pdot% let y = x.a in y.b) with
    | some a =>
        match synthIn? bX3 X3_Ctx a with
        | some c => decide (c.ty = versionTy X3)
        | none => false
    | none => false) = true := by decide +kernel

/-! ### The restriction account

R1 and R2 reach the alias of a singleton through a type member whose bounds
are singletons.  The version relates the two by `Sub.selLower` and
`Sub.selUpper`, and the typer finds that chain.  No rule replaces a path by
its alias, and none is needed here.  R7 is the direct-style path whose prefix
the `let` insertion binds opaquely: the member read through it is a selection
at the inserted binder, which is not below the selection at `x.a` the function
asks for. -/

/-- `∀(f : ⊤) ∀(g : ⊤) ∀(m : {A : f.type..g.type}) ∀(x : f.type) g.type`. -/
def R1_ty : Ty [] :=
  .all .top (.all .top (.all (.typ lA (.sngl (.var (.there .here))) (.sngl (.var .here)))
    (.all (.sngl (.var (.there (.there .here)))) (.sngl (.var (.there (.there .here)))))))

/-- `∀(z : ⊤) ⊤`, the function type R2 aliases. -/
def R2_F {s : Sig} : Ty s := .all .top .top

/-- `∀(f : F) ∀(p : {A : f.type..F}) ∀(x : f.type) ∀(h : ∀(k : F) ⊤) ⊤`. -/
def R2_ty : Ty [] :=
  .all R2_F (.all (.typ lA (.sngl (.var .here)) R2_F)
    (.all (.sngl (.var (.there .here))) (.all (.all R2_F .top) .top)))

/-- R1: `x : f.type` is checked at `g.type` through the declaration `m.A`. -/
def bR1 : Budget := { table := 1, views := 0, sub := 1, typer := 7, rows := 0 }

example : typesAt bR1 R1_src R1_ty = true := by decide +kernel
example : typesAt { bR1 with table := 0 } R1_src R1_ty = false := by decide +kernel
example : typesAt { bR1 with sub := 0 } R1_src R1_ty = false := by decide +kernel
example : typesAt { bR1 with typer := 6 } R1_src R1_ty = false := by decide +kernel

/-- R2: `x : f.type` is passed where `∀(z : ⊤) ⊤` is expected, through the
declaration `p.A`. -/
def bR2 : Budget := { table := 0, views := 1, sub := 1, typer := 6, rows := 0 }

example : typesAt bR2 R2_src R2_ty = true := by decide +kernel
example : typesAt { bR2 with views := 0 } R2_src R2_ty = false := by decide +kernel
example : typesAt { bR2 with sub := 0 } R2_src R2_ty = false := by decide +kernel
example : typesAt { bR2 with typer := 5 } R2_src R2_ty = false := by decide +kernel

/-- R7 resolves and does not type, at the default budget. -/
example : typesSome {} R7_src = false := by decide +kernel

end Checks

end PathsFrontend
