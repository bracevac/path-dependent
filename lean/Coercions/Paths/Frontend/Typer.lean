import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.Frontend.Search

/-!
# The derivation producing typer

This module types an annotated term.  It is fuel bounded and `Option` valued.
It is sound by construction: `synth?` returns a `Synth`, whose second field is
the `Paths.DotMNF.HasTy` derivation, so there is no soundness theorem to prove.
It is incomplete, since DOT subtyping is undecidable.

There are four functions.  `synth?` reads a type off a term and `check?` tests a
term against a type.  `checkVar?` tests a variable against a type.  It is
separate because `HasTy.andI`, `HasTy.recI` and `HasTy.sngl` conclude about a
variable and subsumption does not reach them.  `checkDefs?` matches a
definition list against a type in lockstep, as `DefsTy` does.

Every function takes the path table of its context, built by the caller.  Under
a binder the table is rebuilt at the extended context, `Γ.cons S` for a lambda
and a `let` body and `Γ.consSelf d T` for the definitions of a literal.
Projection reads a field off a view of the table (`HasTy.projP`).  A singleton
goal at a variable is a path typing, asked of `checkPath?`.

`check?` has two clauses that synthesis does not cover.  A lambda against
`∀(x : S) T` with the same domain checks its body against `T`.  An unannotated
`let` against `U` checks its body against `U` weakened, so the body sees its
binder at the type the bound term synthesized.  If a clause fails the term is
synthesized and moved to the goal.

`HasTy.let` needs a body typing at `U.weaken` for a `U` the rule does not
determine.  Three rungs are tried in order: the annotation, the strengthening
of the body's type, and `⊤`.  Each decides `Ty.Wf` of its result.  The third
always applies and loses information.

The four functions form one block, structural on the typer's fuel.  Each
recursive call uses the fuel one below, so the fuel bounds the depth of term and
goal together.  The subtyping search runs at its own counter `Budget.sub`.  Each
function ends a fuel level with a retry at the level below.  The retry is not a
rule of the calculus and changes no answer.  It makes the monotonicity theorem
of each function an induction on the difference of fuels.

The typer does not find a subtyping whose middle is outside the selections of
the path table, a `Rec-I` folding other than the goal's own body, an `And-I`
where neither conjunct is checkable alone, or an avoidance result other than the
annotation, the strengthening or `⊤`.  It does not type an object literal
without a self annotation, an application whose function variable reaches `∀`
past the first function view, or a goal that needs a path replaced by its alias.
It does not pose a `PathTy.recI` or `PathTy.andI` goal at a path.  It finds
nothing past the budget.

The block reduces in the kernel, so the checks at the end are `decide +kernel`.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Tm Defs Ctx Sub PathTy HasTy DefsTy)

/-! ## The result of a synthesis -/

/-- A type a term has, with the derivation that it has it. -/
structure Synth {s : Sig} (Γ : Ctx s) (t : Tm s) where
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy Γ t ty

/-! ## Casts across a decided equality

These use `cases` and not `▸`, because a label occurs twice in the conclusion
of the rule and a rewrite would hit both. -/

/-- A projection read off a path view of the receiver. -/
def projAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a c : Label} {T : Ty s}
    (h : c = a) (d : PathTy Γ (.var x) (.fld c T)) : HasTy Γ (.proj x a) T := by
  cases h; exact .projP d

/-- A projection read off a stable field of the receiver, by `Sub.vfldToFld`. -/
def projVAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a c : Label} {T : Ty s}
    (h : c = a) (d : PathTy Γ (.var x) (.vfld c T)) : HasTy Γ (.proj x a) T := by
  cases h; exact .projP (.sub d .vfldToFld)

/-- A type member definition against a declaration whose two bounds are the
definition's type, as `DefsTy.typ` requires. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {A B : Label} {S L U : Ty s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- A member whose body is an object literal against a stable field declared at
the literal's self type, by `DefsTy.trmObj`. -/
def defsObjAt {s : Sig} {Γ : Ctx s} {a c : Label} {d : Defs (s,x)} {T U : Ty (s,x)}
    (h : a = c) (hT : T = U) (hd : DefsTy (Γ.consSelf d T) d T) (hdist : Defs.Distinct d) :
    DefsTy Γ (.trm a (.val (.obj d))) (.vfld c (.mu U)) := by
  cases h; cases hT; exact .trmObj hd hdist

/-- A lambda checked against a function type with the same domain. -/
def lamAt {s : Sig} {Γ : Ctx s} {S S' : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (h : S = S') (ht : HasTy (Γ.cons S) t T) (hwf : Ty.Wf S) :
    HasTy Γ (.val (.lam S t)) (.all S' T) := by
  cases h; exact .lam ht hwf

/-- `⊤` is its own weakening.  The third rung of the ladder needs this. -/
theorem weaken_top {s : Sig} {k : Kind} : (Ty.top : Ty s).weaken (k := k) = .top := rfl

/-! ## Reading a view

These read the term views of `Search.lean` and the path table. -/

/-- A function type a variable has, with the derivation. -/
structure AllView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The domain. -/
  dom : Ty s
  /-- The codomain, under the domain's binder. -/
  cod : Ty (s,x)
  /-- The derivation. -/
  deriv : HasTy Γ (.path x) (.all dom cod)

/-- The first term view that is a function type.  Only the first is tried. -/
def allView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (AllView Γ x) :=
  vs.findSome? (fun v =>
    match hv : v.ty with
    | .all S T => some ⟨S, T, hv ▸ v.deriv⟩
    | _ => none)

/-- A projection `x.a`, from the first view of `x` in the path table that is a
field or a stable field at `a`. -/
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

/-- The first term view that the subtyping search takes to the type asked for. -/
def viewSub {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : List (PDecl Γ)) (n : Nat)
    (T : Ty s) (vs : List (View Γ x)) : Option (HasTy Γ (.path x) T) :=
  vs.findSome? (fun v => (sub? D n v.ty T).map (fun e => .sub v.deriv e))

/-- A synthesized type moved to the goal, by equality or by the search. -/
def toGoal {s : Sig} {Γ : Ctx s} {t : Tm s} (D : List (PDecl Γ)) (n : Nat) (T : Ty s)
    (c : Synth Γ t) : Option (HasTy Γ t T) :=
  if h : c.ty = T then some (h ▸ c.deriv)
  else (sub? D n c.ty T).map (fun e => .sub c.deriv e)

/-! ## The typer -/

mutual

/-- Synthesis, clause by clause, every premise at the fuel one below.

- A variable returns `Ctx.lookup` and `HasTy.var`.
- `λ(x : S). t` decides `Ty.Wf S` and synthesizes the body under `Γ.cons S`.
- `ν(x : T. d)` checks the definitions under `Γ.consSelf d.erase T` and decides
  `Defs.Distinct`.
- `x y` reads the first function view of `x` and checks `y` against its domain.
- `x.a` reads a field of `x` off the path table.
- `let x (: U)? = t in u` climbs the avoidance ladder.

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
              -- rung one: the annotation
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
                -- rung three: `⊤`
                some ⟨.top, .let c1.deriv (weaken_top ▸ HasTy.sub c2.deriv Sub.top) .top⟩) :
                  Option (Synth Γ (ATm.let ann t u).erase)))
        : Option (Synth Γ a.erase))).orElse fun _ => synth? tbl b n a
termination_by structural n => n

/-- Checking, every premise at the fuel one below.

- A variable goes to `checkVar?`.
- A lambda against `∀(x : S') T` with `S = S'` checks its body against `T`.
- An unannotated `let` against `U` synthesizes the bound term and checks the
  body against `U.weaken`.
- Every term, those three included when their clause fails, is synthesized and
  moved to the goal.

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

1. A singleton goal `q.type` is a path typing, asked of `checkPath?` and
   bridged by `HasTy.sngl`.
2. An intersection goal splits by `HasTy.andI`.
3. A `μ` goal whose body is declaration shaped folds by `HasTy.recI`.  `Sub`
   relates two `μ` types only through the abstract view, so this goal is
   otherwise out of reach from an opened type.
4. Otherwise the term views are consulted, for a view at exactly the goal and
   then for a view the subtyping search takes there.

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

/-- Checking a definition list, every premise at the fuel one below.  The
definitions and the type are matched in lockstep:

- A type member against a declaration with its type on both bounds.
- A member whose body is an object literal against a stable field declared at
  the literal's self type, by `DefsTy.trmObj`.
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

/-- The entry point at a context.  It builds the path table once and runs the
typer at `Budget.typer`. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Synth Γ a.erase) :=
  synth? (table b Γ) b b.typer a

/-- The entry point for a closed program. -/
def synthTop? (b : Budget) (a : ATm []) : Option (Synth Ctx.nil a.erase) :=
  synthIn? b .nil a

/-- Checking at a context against a given type, which may be weaker than the
synthesized one. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (T : Ty s) :
    Option (HasTy Γ a.erase T) :=
  check? (table b Γ) b b.typer a T

/-! ## Fuel monotonicity

One theorem per function.  Each is about `isSome` and not about derivations,
since more fuel may find another derivation of the same judgment.  The other
counters of the budget are not covered. -/

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

/-! ## The example programs

Each surface program of `Notation.lean` is resolved and typed by `synthTop?`.
The type is compared with the one concluded by the derivation in
`Paths.DotMNF.Examples`.

Each budget is one at which the program types.  Lowering any one nonzero
counter by one, with the others kept, makes it fail.  A smaller budget with
several counters changed may still succeed, since the counters trade off.
Fig. 2 types at views 2 and search 3, and at views 1 and search 4, and not at
views 1 and search 3.

X3, E6 and X4 are typed in `Paths.DotMNF.Examples` under a context.  Here they
are written closed, the context entry becomes a lambda, and the expected type
is the original type under one `∀`.  They are also typed at their own contexts
further below, through `synthIn?`. -/

section Checks

open Paths.DotMNF.Examples

/-- The type a derivation concludes. -/
def versionTy {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Ty s := T

/-- The program resolves and the typer synthesizes `T` at the budget. -/
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

/-- The type Fig. 1 synthesizes: the self type of `pcore`, strengthened past the
binder of `o`. -/
def Fig1_ty : Ty [] := (tyStrengthen? (Ty.mu Fig1_pBody)).getD .bot

/-- E1, bad bounds at a variable.  The annotated `let` is checked through the
chain `⊤ <: x.A <: ⊥`. -/
def bE1 : Budget := { table := 0, views := 1, sub := 1, typer := 4, rows := 0 }

example : typesAt bE1 E1_src (versionTy E1) = true := by decide +kernel
example : typesAt { bE1 with views := 0 } E1_src (versionTy E1) = false := by
  decide +kernel
example : typesAt { bE1 with sub := 0 } E1_src (versionTy E1) = false := by
  decide +kernel
example : typesAt { bE1 with typer := 3 } E1_src (versionTy E1) = false := by
  decide +kernel

/-- E2, a recursive literal bound by a `let`, its member selected and applied to
itself.  The outer `let` falls to `⊤`. -/
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

/-- E4, the counterexample of the paper's first section.  The detour step gives
`w` its member `A` at `Int..⊤`. -/
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

/-- E6, a field typed at its own literal's type member. -/
def bE6 : Budget := { table := 2, views := 0, sub := 2, typer := 6, rows := 0 }

example : typesAt bE6 E6_src (.all E6Int (versionTy E6)) = true := by decide +kernel
example : typesAt { bE6 with table := 1 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel
example : typesAt { bE6 with sub := 1 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel
example : typesAt { bE6 with typer := 5 } E6_src (.all E6Int (versionTy E6)) = false := by
  decide +kernel

/-- E7, a two element alias cycle of type members. -/
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

/-- X1, a literal whose member is bounded by a selection at a path of length two. -/
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

/-- X3, `projP` through two stable fields. -/
def bX3 : Budget := { table := 0, views := 0, sub := 0, typer := 3, rows := 0 }

example : typesAt bX3 X3_src (.all X3_A (versionTy X3)) = true := by decide +kernel
example : typesAt { bX3 with typer := 2 } X3_src (.all X3_A (versionTy X3)) = false := by
  decide +kernel

/-- X4, the `types` module of gDOT Fig. 2 alone. -/
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
the outer `let` falls to `⊤`. -/
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
take the strengthening rung. -/
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

/-- The strengthening exists, since the self type of `pcore` does not mention
`o`. -/
example : (tyStrengthen? (Ty.mu Fig1_pBody)).isSome = true := by decide +kernel

/-- Fig. 1 also checks against `⊤`, where `Fig1_ty` is moved by `Sub.top`. -/
example : (match resolve pathsTable Fig1_src with
    | some a => (checkIn? bFig1 .nil a .top).isSome
    | none => false) = true := by decide +kernel

/-! ### The programs at their contexts

The body of the closed program is typed by `synthIn?` at the context of
`Paths.DotMNF.Examples`. -/

/-- The body of a closed program under its outer lambda, typed at a context. -/
def bodyTypesIn (b : Budget) (Γ : Ctx ([],x)) (e : STm) (T : Ty ([],x)) : Bool :=
  match resolve pathsTable e with
  | some (.lam _ a) =>
      match synthIn? b Γ a with
      | some c => decide (c.ty = T)
      | none => false
  | _ => false

/-- X3, E6 and X4 at their contexts. -/
example : bodyTypesIn bX3 X3_Ctx X3_src (versionTy X3) = true := by decide +kernel
example : bodyTypesIn bE6 E6Ctx1 E6_src (versionTy E6) = true := by decide +kernel
example : bodyTypesIn bX4 X4_Ctx X4_src (versionTy X4_lit0) = true := by decide +kernel

/-- X3 resolved open at the name of its context entry, then typed there. -/
example : (match resolveIn pathsTable (.cons .nil "x") (pdot% let y = x.a in y.b) with
    | some a =>
        match synthIn? bX3 X3_Ctx a with
        | some c => decide (c.ty = versionTy X3)
        | none => false
    | none => false) = true := by decide +kernel

/-! ### R1, R2 and R7

R1 and R2 reach the alias of a singleton through a type member whose bounds are
singletons.  `Sub.selLower` and `Sub.selUpper` relate the two and the typer
finds that chain.  No rule replaces a path by its alias.  R7 is a direct-style
path whose prefix the `let` insertion binds opaquely.  The member read through
it is a selection at the inserted binder, which is not below the selection at
`x.a` that the function asks for. -/

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
