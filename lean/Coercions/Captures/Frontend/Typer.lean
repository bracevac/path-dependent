import Coercions.Captures.Frontend.Adapt
import Coercions.Captures.Frontend.Alg
import Coercions.Captures.Frontend.Resolve

/-!
# The typer

The typer reads a type and a use set off an annotated term and returns the
calculus's derivation (`DotMNF/Typing.lean`) about the erasure of the term.
Every result carries its `HasTy` derivation, so the result type is the
soundness statement.

It runs on the tank of `Fuel.lean`.  One tank is threaded through every goal
it asks: each subtyping, subcapturing and variable goal of `Sub.lean`, each
member lookup of `Look.lean`, and each avoidance of `Avoid.lean`.  So the fuel
counts the work of the whole typing, and a goal that finds the tank short
marks it.  A marked tank is the recursion limit.  It is never a rejection by
the rules.

## Least sets

The typer computes the least use set and capture set the rules allow.  A
variable declared at the empty set is used at the empty set and keeps its
declared type.  Any other variable is used at `{x}` with its declared shape at
`{x}`.  A value is used at `{}`.  Application, projection and unboxing join
the sets of their premises with `capJoin`.  At the three binders the set is a
candidate followed by evidence.

- `λ(x : T). t` drops `{x}` from the body's set and reads `{x.C}` at the
  upper bound of `x`'s capture member, found by the lookup.  The
  subcapturing goal checks the inclusion the rule asks for.
- `let x = t in u` approximates the body's set from above (`avoidUses`):
  `{x}` becomes the capture set of `t`'s type (`sc-var`) and `{x.C}` the
  member's upper bound.  Both premises are widened to the join of the two
  sets.
- `ν(z : S. d)` is typed by a least fixpoint on its capture set (`objFixF`).

## Candidates

Synthesis returns a list of candidates, each an elaborated term with its use
set, its type and its derivation.  The version has no rule that merges two
members of one name, which the compiler does (`Types.scala:5759`).  So the
typer keeps every choice instead.

- A variable has its first view.
- `x y` tries every function type the lookup finds in `x`, and keeps each one
  whose domain `y` meets.  An argument that fails is adapted by box inference
  and bound by a `let`, `let y' = □ y in x y'` or `let y' = C ⊸ y in x y'`.  A
  function with a box and no function type is unboxed and bound by a `let`.
- `x.a` returns every field at `a` the lookup finds.  A receiver with a box
  and no such field is unboxed and bound by a `let`.
- `let x = t in u` without annotation returns every pair of a candidate of
  `t` and a candidate of `u`.  The body's type is approximated by a type free
  of `x` (`avoidLet`), as the compiler's `avoid` does
  (`TypeOps.scala:474-509,565-583`).
- `let x : A = t in u` has the type `A`.  The annotation binds.  The body is
  checked against it and is never approximated.
- `□ x` is the box of the first view, and `C ⊸ x` unboxes every box the
  lookup finds with the boxed set `C`.
- `(t : T)` checks `t` against `T`.

The skeleton inlines a `let` of a variable, so the elaborated term keeps the
program's skeleton.

## Checking

Synthesis and checking are one function, `inferF`, with an optional goal, so
that checking never asks synthesis on the same term and the function is
structural on the term.  Checking a variable goes through box inference
(`adaptVarF`), whose plain checking is the `var` goal.  That goal reaches the
two rules that subsumption does not, `HasTy.andI` and `HasTy.recI`.  Three
forms are checked against the goal's form first: a `λ` against a function
type checks its body against the codomain, a `let` with no annotation checks
its body against the goal, and a box value against a box goal checks the
variable against the boxed type.  Every other candidate is moved to the goal
by the subtyping goal.

## The object rule

`HasTy.obj` types the definitions of a literal under a self binder that holds
the same definitions and capture set as the conclusion.  Box inference
changes the definitions, and the set of a literal with no written set is
known only after its definitions are typed.  `objFixF` iterates: it types the
definitions under a binder at the current definitions and set, and stops when
the elaborated definitions erase to the ones the binder holds and their use
set is below the current set and the self variable.  Otherwise the next pass
takes the elaborated definitions and the current set joined with the atoms
of the set they used, the self variable dropped, that the current set does
not account for.  An atom is accounted for when the subcapturing goal from
it to the current set has an answer.  A written set never changes.  This is
the compiler's class use set, a variable grown until it is solved
(`cc/CheckCaptures.scala:1501-1515`, `cc/CaptureSet.scala:880-912`).  A pass
that goes on adds an atom the set does not account for, or other
definitions (`objFix_progress`).  The number of passes is bounded by
`objBound`, a size of the program.  A pass that reaches the bound marks the
tank, so the bound never causes a rejection.

## The theorems

Every computation here is framed: it keeps a marked tank, never adds fuel,
and does the same with more fuel (`synthF_frame`).  So a typing that ends
unmarked gives the same answer at every larger fuel (`synthTop?_mono`,
`synthTop?_stable`).  A rejection that ends unmarked is a rejection at every
fuel.  The typer has no completeness theorem.  It does not find a derivation
through a middle type the program does not write, as the compiler does not.
It does not merge two members, so it tries each.  It does not find a
judgment whose search needs more than the fuel.  And a lookup through a
cyclic member is cut, as the compiler's cyclic reference.

Every definition is structural, so the kernel evaluates the typer.  The checks
at the end of the module type the example programs at `defaultFuel` by
`decide +kernel`.
-/

namespace CapturesFrontend

open Frontend.Fuel CapturesFrontend.Core
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Ctx Sub SubShape Subcap
  HasTy DefsTy Platform)
open scoped Captures.DotMNF

/-- The fuel of a typing.  One field, the size of the tank every entry point
starts from. -/
structure Budget where
  fuel : Nat := defaultFuel

/-! ## Moving a derivation across a decided equality

The label of a member occurs twice in the conclusion, so these use `cases`
and not a rewrite. -/

/-- A type member definition against a declaration with its shape as both bounds. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {S L U : Shape s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy V Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A capture member definition against a declaration with its set as both bounds. -/
def defsCapAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {c c1 c2 : CaptureSet s}
    (hA : A = B) (h1 : c = c1) (h2 : c = c2) : DefsTy V Γ (.cap A c) (.cap B c1 c2) := by
  cases hA; cases h1; cases h2; exact .cap

/-- A term member definition against a field declaration at the same label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy V Γ t T) : DefsTy V Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- `{}-I` for definitions equal to the ones the self binder holds. -/
def objOf {s : Sig} {Γ : Ctx s} {d e : Defs (s,x)} {S : Shape (s,x)} {U : CaptureSet s}
    (h : e = d) (dt : DefsTy (CaptureSet.weaken U ∪ [.var .here]) (Γ.consSelf d S U) e S)
    (hd : Defs.Distinct d) : HasTy [] Γ (.val (.obj e)) ((Shape.mu S) ^ U) := by
  cases h; exact .obj dt hd

/-- Weakening keeps an inclusion of sets. -/
theorem weaken_subset {s : Sig} {C D : CaptureSet s} (h : CaptureSet.Subset C D) :
    CaptureSet.Subset (CaptureSet.weaken (k := .var) C) (CaptureSet.weaken (k := .var) D) := by
  intro a ha
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at ha ⊢
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨b, h b hb, rfl⟩

/-! ## Pieces the clauses use -/

/-- Run `c`, and return its answer as a list of at most one, mapped by `f`. -/
def mapL {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (List β) :=
  Fu.bind c fun o => Fu.ret (listO (o.map f))

/-- The candidates of `a`, or those of `b` when `a` has none. -/
def orElseL {α : Type} (a b : Fu (List α)) : Fu (List α) :=
  Fu.bind a fun
    | [] => b
    | l => Fu.ret l

/-- Keep the first candidate of each use set and type. -/
def dedupE {s : Sig} {Γ : Ctx s} : List (Elab Γ) → List (Elab Γ)
  | [] => []
  | r :: rs => r :: (dedupE rs).filter fun r' => !decide (r'.uses = r.uses ∧ r'.ty = r.ty)

/-- A candidate at exactly the type asked for. -/
def toChecked {s : Sig} {Γ : Ctx s} (r : Elab Γ) (T : Ty s) : Option (Checked Γ T) :=
  if h : r.ty = T then some ⟨r.tm, r.uses, h ▸ r.deriv⟩ else none

/-- The first candidate at exactly the type asked for. -/
def firstChecked {s : Sig} {Γ : Ctx s} (rs : List (Elab Γ)) (T : Ty s) : Option (Checked Γ T) :=
  rs.findSome? fun r => toChecked r T

/-- The candidates moved to a goal: all of them when there is none, and each
one the subtyping goal takes to `T` otherwise. -/
def finishF {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (rs : List (Elab Γ)) : Fu (List (Elab Γ)) :=
  match G with
  | none => Fu.ret rs
  | some T => Fu.flatMapL (fun r => mapL (subsumeF Γ r T) Checked.toElab) rs

/-! ## The binders of a set

`All-I` and `{}-I` drop the binder `x` from a set over `(s,x)`, and read each
`{x.C}` at the upper bound of the capture member `C` of `x`. -/

/-- The upper bound of the first capture member of the innermost binder at each
label `{x.C}` of `V` names, found by the lookup. -/
def hereBoundsF {s : Sig} (Γ : Ctx (s,x)) (V : CaptureSet (s,x)) :
    Fu (List (Label × CaptureSet (s,x))) :=
  Fu.flatMapL (fun a =>
    match a with
    | .sel .here C => Fu.bind (capsAt Γ .here C) fun ds =>
        Fu.ret (listO (ds.head?.map fun d => (C, d.2.1)))
    | _ => Fu.ret []) V

/-- The bound found at a label. -/
def selOf {s : Sig} (bs : List (Label × CaptureSet s)) (C : Label) : Option (CaptureSet s) :=
  (bs.find? fun p => decide (p.1 = C)).map (·.2)

/-- The set of a function: the body's set `V` without the parameter, with the
evidence `V <: U↑ ∪ {x}` that `All-I` asks for. -/
def lamUsesF {s : Sig} (Γ : Ctx s) (T : Ty s) (V : CaptureSet (s,x)) :
    Fu (Option ((U : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken U ∪ [.var .here]))) :=
  Fu.bind (hereBoundsF (Γ.cons T) V) fun bs =>
    match capDropHere? (selOf bs) V with
    | some U => mapO (subcapF (Γ.cons T) V (CaptureSet.weaken U ∪ [.var .here])) fun e => ⟨U, e⟩
    | none => Fu.ret none

/-! ## Assembling a `let` -/

/-- `HasTy.let` at the result type `A`, with the body's use set approximated
from above and both premises widened to the join. -/
def letAtF {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s) (r1 : Elab Γ)
    (r2 : Checked (Γ.cons r1.ty) A.weaken) : Fu (Option (Elab Γ)) :=
  if hwf : Ty.Wf A then
    mapO (avoidUses Γ r1.ty r2.uses) fun p =>
      ⟨.let ann r1.tm r2.tm, capJoin r1.uses p.1, A,
        HasTy.let (widenLeft r1.deriv p.1)
          (widenUses r2.deriv (p.2.trans (.elem (weaken_subset (capJoin_right r1.uses p.1))))) hwf⟩
  else Fu.ret none

/-- `HasTy.let` at the avoided type of its body. -/
def letFinishF {s : Sig} (Γ : Ctx s) (r1 : Elab Γ) (r2 : Elab (Γ.cons r1.ty)) :
    Fu (Option (Elab Γ)) :=
  bindO (avoidLet Γ r1.ty r2.ty) fun a =>
    letAtF Γ none a.1 r1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv a.2 Subcap.refl⟩

/-- Every candidate of a body under the binder of `r1`, each closed by
`letFinishF`. -/
def letPairsF {s : Sig} (Γ : Ctx s) (r1 : Elab Γ) (body : Fu (List (Elab (Γ.cons r1.ty)))) :
    Fu (List (Elab Γ)) :=
  Fu.bind body fun r2s => Fu.flatMapL (fun r2 => mapL (letFinishF Γ r1 r2) id) r2s

/-- The first candidate of the bound term whose body checks against `A`
under its binder, at the type `A`. -/
def letCheckF {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s) (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))) :
    Fu (Option (Elab Γ)) :=
  Fu.firstSome (fun r1 =>
    Fu.bind (body r1 (some A.weaken)) fun r2s =>
      match firstChecked r2s A.weaken with
      | some c => letAtF Γ ann A r1 c
      | none => Fu.ret none) r1s

/-- A `let` without annotation checked against a goal: its body checked
against the goal under the binder. -/
def letSpecialF {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s))
    (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))) :
    Fu (List (Elab Γ)) :=
  match ann, G with
  | none, some T => if tyWf? T then mapL (letCheckF Γ none T r1s body) id else Fu.ret []
  | _, _ => Fu.ret []

/-- A `let` synthesized: at its annotation, or every pair of candidates with
the body's type avoided. -/
def letGenF {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (r1s : List (Elab Γ))
    (body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))) :
    Fu (List (Elab Γ)) :=
  match ann with
  | some A => mapL (letCheckF Γ (some A) A r1s body) id
  | none => Fu.bind (Fu.flatMapL (fun r1 => letPairsF Γ r1 (body r1 none)) r1s) fun cs =>
      Fu.ret (dedupE cs)

/-! ## Application and projection -/

/-- `x y` at each function type found, the argument checked plainly. -/
def appWithF {s : Sig} (Γ : Ctx s) {x : BVar s .var} (fs : List (FnView Γ x)) (y : BVar s .var) :
    Fu (List (Elab Γ)) :=
  Fu.flatMapL (fun f => mapL (checkVarF Γ y f.dom) fun r =>
    (⟨.app x y, capJoin f.uses r.uses, f.cod.substVar y,
      HasTy.app (widenLeft f.deriv r.uses) (widenRight f.uses r.deriv)⟩ : Elab Γ)) fs

/-- `x y` at each function type the lookup finds. -/
def appCoreF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Fu (List (Elab Γ)) :=
  Fu.bind (fnViewsF Γ x) fun fs => appWithF Γ fs y

/-- `x y` at the function types `fs`.  If no domain takes `y` plainly, `y` is
adapted against each domain by box inference and bound by a `let`. -/
def appStepWithF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) (fs : List (FnView Γ x)) :
    Fu (List (Elab Γ)) :=
  orElseL (appWithF Γ fs y)
    (Fu.flatMapL (fun f =>
      Fu.bind (adaptInsertF Γ y f.dom) fun
        | some r => letPairsF Γ r.toElab (appCoreF (Γ.cons r.toElab.ty) (.there x) .here)
        | none => Fu.ret []) fs)

/-- `x y` at the function types the lookup finds, with the argument adapted. -/
def appStepF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Fu (List (Elab Γ)) :=
  Fu.bind (fnViewsF Γ x) fun fs => appStepWithF Γ x y fs

/-- An application.  A function with no function type but a box is unboxed at
the set of its first box and bound by a `let`. -/
def appAllF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Fu (List (Elab Γ)) :=
  Fu.bind (fnViewsF Γ x) fun fs =>
    Fu.bind (match fs with
      | [] => Fu.bind (boxViewsF Γ x) fun bs =>
          match firstBoxSet bs with
          | some C => Fu.flatMapL (fun r1 =>
              letPairsF Γ r1 (appStepF (Γ.cons r1.ty) .here (.there y))) (unboxAll C bs)
          | none => Fu.ret []
      | _ => appStepWithF Γ x y fs) fun cs =>
      Fu.ret (dedupE cs)

/-- The projection at a field found. -/
def projOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} (f : FldView Γ x a) : Elab Γ :=
  ⟨.proj x a, f.uses, f.ty, HasTy.proj f.deriv⟩

/-- A projection: one candidate per field the lookup finds.  A receiver with
no field but a box is unboxed at the set of its first box and bound by a
`let`. -/
def projAllF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) : Fu (List (Elab Γ)) :=
  Fu.bind (fldViewsF Γ x a) fun fs =>
    Fu.bind (match fs with
      | [] => Fu.bind (boxViewsF Γ x) fun bs =>
          match firstBoxSet bs with
          | some C => Fu.flatMapL (fun r1 =>
              letPairsF Γ r1 (Fu.bind (fldViewsF (Γ.cons r1.ty) .here a) fun gs =>
                Fu.ret (gs.map projOf))) (unboxAll C bs)
          | none => Fu.ret []
      | fs => Fu.ret (fs.map projOf)) fun cs =>
      Fu.ret (dedupE cs)

/-! ## A function -/

/-- The goal's function type, if it is one. -/
def funGoal? {s : Sig} : Option (Ty s) → Option (CaptureSet s × Ty s × Ty (s,x))
  | some (.capt C (.all T1 T2)) => some (C, T1, T2)
  | _ => none

/-- `λ(x : T). t` from the candidates of its body. -/
def lamGenF {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T) (rs : List (Elab (Γ.cons T))) :
    Fu (List (Elab Γ)) :=
  Fu.flatMapL (fun (r : Elab (Γ.cons T)) => mapL (lamUsesF Γ T r.uses) fun p =>
    (⟨.lam T r.tm, [], (Shape.all T r.ty) ^ p.1, HasTy.lam (widenUses r.deriv p.2) hwf⟩ :
      Elab Γ)) rs

/-- `λ(x : T). t` against `(∀(x : T1') T2) ^ C`, from the candidates of its
body checked against `T2`: the body's set below `C↑ ∪ {x}`, and `T1'` below
`T`. -/
def lamCheckF {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T) (C : CaptureSet s) (T1' : Ty s)
    (T2 : Ty (s,x)) (rs : List (Elab (Γ.cons T))) : Fu (List (Elab Γ)) :=
  match firstChecked rs T2 with
  | some r =>
      mapL (bindO (subcapF (Γ.cons T) r.uses (CaptureSet.weaken C ∪ [.var .here])) fun e =>
        mapO (subF Γ T1' T) fun eD =>
          (⟨.lam T r.tm, [], (Shape.all T1' T2) ^ C,
            HasTy.sub (HasTy.lam (widenUses r.deriv e) hwf)
              (Sub.capt (SubShape.all eD (Sub.refl T2)) .refl) .refl⟩ : Elab Γ)) id
  | none => Fu.ret []

/-! ## The object rule -/

/-- The final pass of the object rule: the elaborated definitions are the ones
the binder holds and their set is below the binder's set and the self
variable. -/
def objDoneF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs (s,x)) (U : CaptureSet s)
    (r : DefsElab (Γ.consSelf e S U) S) : Fu (Option (Elab Γ)) :=
  if hd : r.tm.erase = e then
    if hdist : Defs.Distinct e then
      mapO (subcapF (Γ.consSelf e S U) r.uses (CaptureSet.weaken U ∪ [.var .here])) fun ev =>
        ⟨.obj S (some U) r.tm, [], (Shape.mu S) ^ U, objOf hd (r.deriv _ ev) hdist⟩
    else Fu.ret none
  else Fu.ret none

/-- The atom `a` alone if the set `U` does not account for it, and nothing
otherwise. -/
def newAtomF {s : Sig} (Γ : Ctx s) (U : CaptureSet s) (a : CapAtom s) : Fu (CaptureSet s) :=
  if CaptureSet.elem U a then Fu.ret []
  else Fu.bind (subcapF Γ [a] U) fun
    | some _ => Fu.ret []
    | none => Fu.ret [a]

/-- The atoms of `D` that the set `U` does not account for.  An atom of `U` is
skipped at no cost.  Any other atom `a` is kept when the subcapturing goal
`{a} <: U` has no answer.  The compiler adds an element to a set variable
only when the set does not account for it (`tryInclude` and `accountsFor`,
`cc/CaptureSet.scala:197-198,251-272`). -/
def newAtomsF {s : Sig} (Γ : Ctx s) (U D : CaptureSet s) : Fu (CaptureSet s) :=
  Fu.flatMapL (newAtomF Γ U) D

/-- The set of the next pass: the current set, joined with the atoms it does
not account for of the set the definitions used, with the self variable
dropped.  A written set stays. -/
def objNextF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (fix : Bool) (e : Defs (s,x))
    (U : CaptureSet s) (r : DefsElab (Γ.consSelf e S U) S) : Fu (CaptureSet s) :=
  if fix then Fu.ret U
  else Fu.bind (hereBoundsF (Γ.consSelf e S U) r.uses) fun bs =>
    Fu.bind (newAtomsF Γ U ((capDropHere? (selOf bs) r.uses).getD [])) fun N =>
      Fu.ret (capJoin U N)

/-- The object rule as a least fixpoint on the literal's set.  `chk` types the
definitions under a binder, `fix` says whether the set was written, and the
index counts the passes left.  A pass that changes neither the set nor the
definitions ends with no answer.  The last pass marks the tank. -/
def objFixF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (fix : Bool)
    (chk : (e : Defs (s,x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.consSelf e S U) S))) :
    Nat → Defs (s,x) → CaptureSet s → Fu (Option (Elab Γ))
  | 0, _, _ => fun t => (none, { t with out := true })
  | k + 1, e, U =>
      bindO (chk e U) fun r =>
        Fu.orElse (objDoneF Γ S e U r) fun _ =>
          Fu.bind (objNextF Γ S fix e U r) fun U' =>
            if U' = U ∧ r.tm.erase = e then Fu.ret none
            else objFixF Γ S fix chk k r.tm.erase U'
termination_by structural k _ _ => k

/-! ### The bound of the object fixpoint -/

/-- The labels of the capture members a set selects. -/
def capLabelsC {s : Sig} (C : CaptureSet s) : List Label :=
  C.filterMap fun a =>
    match a with
    | .sel _ A => some A
    | _ => none

mutual
/-- The labels of the capture members a shape declares or selects. -/
def capLabelsS {s : Sig} : Shape s → List Label
  | .top => []
  | .bot => []
  | .typ _ L H => capLabelsS L ++ capLabelsS H
  | .fld _ T => capLabelsT T
  | .cap A c1 c2 => A :: (capLabelsC c1 ++ capLabelsC c2)
  | .sel _ _ => []
  | .mu B => capLabelsS B
  | .all T U => capLabelsT T ++ capLabelsT U
  | .and S T => capLabelsS S ++ capLabelsS T
  | .box T => capLabelsT T
/-- The labels of the capture members a type declares or selects. -/
def capLabelsT {s : Sig} : Ty s → List Label
  | .capt C S => capLabelsC C ++ capLabelsS S
end

mutual
/-- The labels of the capture members a term declares or selects. -/
def capLabelsA {s : Sig} : ATm s → List Label
  | .path _ => []
  | .lam T t => capLabelsT T ++ capLabelsA t
  | .obj S U d => capLabelsS S ++ capLabelsC (U.getD []) ++ capLabelsD d
  | .app _ _ => []
  | .proj _ _ => []
  | .let ann t u => capLabelsT (ann.getD (.top ^ [])) ++ capLabelsA t ++ capLabelsA u
  | .box _ => []
  | .unbox C _ => capLabelsC C
  | .asc t T => capLabelsA t ++ capLabelsT T
/-- The labels of the capture members definitions declare or select. -/
def capLabelsD {s : Sig} : ADefs s → List Label
  | .typ _ S => capLabelsS S
  | .cap A c => A :: capLabelsC c
  | .trm _ t => capLabelsA t
  | .and d e => capLabelsD d ++ capLabelsD e
end

mutual
/-- The variable occurrences of a term: the sites where box inference may
insert a box or an unboxing. -/
def occA {s : Sig} : ATm s → Nat
  | .path _ => 1
  | .lam _ t => occA t
  | .obj _ _ d => occD d
  | .app _ _ => 2
  | .proj _ _ => 1
  | .let _ t u => occA t + occA u
  | .box _ => 1
  | .unbox _ _ => 1
  | .asc t _ => occA t
/-- The variable occurrences of definitions. -/
def occD {s : Sig} : ADefs s → Nat
  | .typ _ _ => 0
  | .cap _ _ => 0
  | .trm _ t => occA t
  | .and d e => occD d + occD e
end

/-- The labels of the capture members a context declares or selects. -/
def capLabelsCtx {s : Sig} : Ctx s → List Label
  | .nil => []
  | .cons Γ T => capLabelsCtx Γ ++ capLabelsT T
  | .consSelf Γ _ S U => capLabelsCtx Γ ++ capLabelsS S ++ capLabelsC U
  | .consC Γ => capLabelsCtx Γ

/-- The number of atoms over `s` a literal's capture set can hold (a term
variable, a capture binder, or a capture member of a term variable at a label
of the program), plus the insertion sites of box inference, plus two.  It is
a size of the program, not a fuel. -/
def objBound {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (d : ADefs (s,x)) : Nat :=
  let V := (ctxVars Γ).length
  let K := (ctxCaps Γ).length
  let L := (capLabelsCtx Γ ++ capLabelsS S ++ capLabelsD d).length
  V + K + V * L + occD d + 2

/-! ## Synthesis and checking

Two functions, structural on the term.  `inferF` returns the candidates of a
term: every candidate with no goal, and every candidate at the goal with one.
`checkDefsF` matches a definition list against a declaration shape in
lockstep, as `DefsTy` does (`DotMNF/Typing.lean`). -/

mutual

/-- The candidates of a term, each with its derivation, on the tank.  With a
goal `some T`, every candidate is at `T`. -/
def inferF {s : Sig} (Γ : Ctx s) : (a : ATm s) → (G : Option (Ty s)) → Fu (List (Elab Γ))
  | .path (.var x), G =>
      match G with
      | none => Fu.ret [varSynth Γ x]
      | some T => mapL (adaptVarF Γ x T) Checked.toElab
  | .lam T t, G =>
      if hwf : Ty.Wf T then
        orElseL
          (match funGoal? G with
            | some (C, T1', T2) =>
                Fu.bind (inferF (Γ.cons T) t (some T2)) (lamCheckF Γ T hwf C T1' T2)
            | none => Fu.ret [])
          (Fu.bind (inferF (Γ.cons T) t none) fun rs =>
            Fu.bind (lamGenF Γ T hwf rs) (finishF Γ G))
      else Fu.ret []
  | .obj S U0 d, G =>
      Fu.bind (objFixF Γ S U0.isSome (fun e U => checkDefsF (Γ.consSelf e S U) d S)
          (objBound Γ S d) d.erase (U0.getD [])) fun o =>
        finishF Γ G (listO o)
  | .app x y, G => Fu.bind (appAllF Γ x y) (finishF Γ G)
  | .proj x a, G => Fu.bind (projAllF Γ x a) (finishF Γ G)
  | .let ann t u, G =>
      Fu.bind (inferF Γ t none) fun r1s =>
        orElseL (letSpecialF Γ ann G r1s fun r1 o => inferF (Γ.cons r1.ty) u o)
          (Fu.bind (letGenF Γ ann r1s fun r1 o => inferF (Γ.cons r1.ty) u o) (finishF Γ G))
  | .box x, G =>
      orElseL
        (match G with
          | some T => mapL (boxCheckF Γ x T) fun d => (⟨.box x, [], T, d⟩ : Elab Γ)
          | none => Fu.ret [])
        (finishF Γ G [boxValue Γ x])
  | .unbox C x, G => Fu.bind (boxViewsF Γ x) fun bs => finishF Γ G (unboxAll C bs)
  | .asc t T, G =>
      Fu.bind (inferF Γ t (some T)) fun rs =>
        finishF Γ G (listO ((firstChecked rs T).map fun c =>
          (⟨.asc c.tm T, c.uses, T, c.deriv⟩ : Elab Γ)))

/-- A definition list against a declaration shape, in lockstep: a type member
against a declaration with its shape on both bounds, a capture member against
one with its set on both bounds, a term member against a field at the same
label, an intersection against an intersection.  The result holds the least
use set and the derivation at every set above it. -/
def checkDefsF {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (S : Shape s) →
    Fu (Option (DefsElab Γ S))
  | .typ A S0, .typ B L U =>
      Fu.ret (if hA : A = B then
        if hL : S0 = L then
          if hU : S0 = U then some ⟨.typ A S0, [], fun _ _ => defsTypAt hA hL hU⟩ else none
        else none
      else none)
  | .cap A c, .cap B c1 c2 =>
      Fu.ret (if hA : A = B then
        if h1 : c = c1 then
          if h2 : c = c2 then some ⟨.cap A c, [], fun _ _ => defsCapAt hA h1 h2⟩ else none
        else none
      else none)
  | .trm a t, .fld c T =>
      if h : a = c then
        Fu.bind (inferF Γ t (some T)) fun rs =>
          Fu.ret ((firstChecked rs T).map fun (r : Checked Γ T) =>
            ⟨.trm a r.tm, r.uses, fun _ e => defsTrmAt h (widenUses r.deriv e)⟩)
      else Fu.ret none
  | .and d1 d2, .and S1 S2 =>
      bindO (checkDefsF Γ d1 S1) fun r1 =>
        mapO (checkDefsF Γ d2 S2) fun r2 =>
          ⟨.and r1.tm r2.tm, capJoin r1.uses r2.uses, fun U e =>
            DefsTy.and (r1.deriv U (.trans (.elem (capJoin_left r1.uses r2.uses)) e))
              (r2.deriv U (.trans (.elem (capJoin_right r1.uses r2.uses)) e))⟩
  | _, _ => Fu.ret none

end

/-- Synthesis on the tank: the candidates of a term with no goal. -/
def synthF {s : Sig} (Γ : Ctx s) (a : ATm s) : Fu (List (Elab Γ)) := inferF Γ a none

/-- Checking on the tank: the candidates of a term at the goal `T`. -/
def checkF {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Fu (List (Elab Γ)) :=
  inferF Γ a (some T)

/-! ## The entry points -/

/-- The first candidate, and `none` if the tank ended marked. -/
def firstCand {α : Type} : List α × Tank → Option α × Tank
  | (c :: _, t) => if t.out then (none, t) else (some c, t)
  | ([], t) => (none, t)

/-- The first candidate of a term in `Γ`, from a full tank of `n` units, with
the tank left. -/
def synthInF {s : Sig} (Γ : Ctx s) (a : ATm s) (n : Nat) : Option (Elab Γ) × Tank :=
  firstCand (synthF Γ a ⟨n, false⟩)

/-- A type of a term in `Γ`, at the budget's fuel. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Elab Γ) :=
  (synthInF Γ a b.fuel).1

/-- The context of a platform: one capture binder per capability.  It
mirrors `Platform.ctx`. -/
def platformCtx {s : Sig} (P : Platform s) : Ctx s :=
  match P with
  | .nil => .nil
  | .cons P => .consC (platformCtx P)
termination_by structural P

/-- The first candidate of a closed program over a platform, from a full tank
of `n` units, with the tank left. -/
def synthTopF (n : Nat) (π : PlatformNames) (a : ATm π.sig) :
    Option (Elab (platformCtx π.plat)) × Tank :=
  synthInF (platformCtx π.plat) a n

/-- A type of a closed program over a platform, at the budget's fuel. -/
def synthTop? (b : Budget) (π : PlatformNames) (a : ATm π.sig) :
    Option (Elab (platformCtx π.plat)) :=
  (synthTopF b.fuel π a).1

/-- The first candidate of a term in `Γ`, then the subcapturing and
subtyping goals to a given use set and type, on the same tank.  The typer
returns the least sets, and a judgment with larger ones is reached this
way. -/
def checkInF {s : Sig} (Γ : Ctx s) (a : ATm s) (U : CaptureSet s) (T : Ty s) :
    Fu (Option ((t : ATm s) × HasTy U Γ t.erase T)) :=
  Fu.bind (synthF Γ a) fun
    | r :: _ => bindO (subcapF Γ r.uses U) fun eU =>
        mapO (subF Γ r.ty T) fun eT => ⟨r.tm, HasTy.sub r.deriv eT eU⟩
    | [] => Fu.ret none

/-- `checkInF` at the budget's fuel. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (U : CaptureSet s) (T : Ty s) :
    Option ((t : ATm s) × HasTy U Γ t.erase T) :=
  (checkInF Γ a U T ⟨b.fuel, false⟩).1

/-! ## The frame lemmas

Each clause is built from the combinators of `Fuel.lean` and from framed
computations of the other modules: the goals of `Sub.lean`, the lookups,
box inference of `Adapt.lean` and avoidance.  So each clause is framed, by
induction on the term. -/

section Frames

variable {α β : Type}

theorem mapL_framed {c : Fu (Option α)} (f : α → β) (hc : Framed c) : Framed (mapL c f) :=
  bind_framed hc fun _ => ret_framed _

theorem orElseL_framed {a b : Fu (List α)} (ha : Framed a) (hb : Framed b) :
    Framed (orElseL a b) :=
  bind_framed ha fun l => by
    cases l with
    | nil => exact hb
    | cons _ _ => exact ret_framed _

theorem finishF_framed {s : Sig} (Γ : Ctx s) (G : Option (Ty s)) (rs : List (Elab Γ)) :
    Framed (finishF Γ G rs) := by
  cases G with
  | none => exact ret_framed _
  | some T => exact flatMapL_framed (fun _ => mapL_framed _ (subsumeF_framed _ _ _)) _

theorem hereBoundsF_framed {s : Sig} (Γ : Ctx (s,x)) (V : CaptureSet (s,x)) :
    Framed (hereBoundsF Γ V) := by
  refine flatMapL_framed (fun a => ?_) V
  dsimp only
  split
  · exact bind_framed (capsAt_framed _ _ _) fun _ => ret_framed _
  · exact ret_framed _

theorem lamUsesF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (V : CaptureSet (s,x)) :
    Framed (lamUsesF Γ T V) := by
  refine bind_framed (hereBoundsF_framed _ _) fun bs => ?_
  dsimp only
  split
  · exact mapO_framed _ (subcapF_framed _ _ _)
  · exact ret_framed _

theorem letAtF_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s) (r1 : Elab Γ)
    (r2 : Checked (Γ.cons r1.ty) A.weaken) : Framed (letAtF Γ ann A r1 r2) :=
  dite_framed (fun _ => mapO_framed _ (avoidUses_framed _ _ _)) (fun _ => ret_framed _)

theorem letFinishF_framed {s : Sig} (Γ : Ctx s) (r1 : Elab Γ) (r2 : Elab (Γ.cons r1.ty)) :
    Framed (letFinishF Γ r1 r2) :=
  bindO_framed (avoidLet_framed _ _ _) fun _ => letAtF_framed _ _ _ _ _

theorem letPairsF_framed {s : Sig} (Γ : Ctx s) (r1 : Elab Γ)
    {body : Fu (List (Elab (Γ.cons r1.ty)))} (hb : Framed body) : Framed (letPairsF Γ r1 body) :=
  bind_framed hb fun _ => flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _)) _

theorem letCheckF_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (A : Ty s)
    (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letCheckF Γ ann A r1s body) := by
  refine firstSome_framed (fun r1 => bind_framed (hb _ _) fun r2s => ?_) r1s
  dsimp only
  split
  · exact letAtF_framed _ _ _ _ _
  · exact ret_framed _

theorem letSpecialF_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (G : Option (Ty s))
    (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letSpecialF Γ ann G r1s body) := by
  unfold letSpecialF
  split
  · exact ite_framed (mapL_framed _ (letCheckF_framed _ _ _ _ hb)) (ret_framed _)
  · exact ret_framed _

theorem letGenF_framed {s : Sig} (Γ : Ctx s) (ann : Option (Ty s)) (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : ∀ r1 o, Framed (body r1 o)) : Framed (letGenF Γ ann r1s body) := by
  cases ann with
  | some A => exact mapL_framed _ (letCheckF_framed _ _ _ _ hb)
  | none =>
    exact bind_framed (flatMapL_framed (fun _ => letPairsF_framed _ _ (hb _ _)) _)
      fun _ => ret_framed _

theorem appWithF_framed {s : Sig} (Γ : Ctx s) {x : BVar s .var} (fs : List (FnView Γ x))
    (y : BVar s .var) : Framed (appWithF Γ fs y) :=
  flatMapL_framed (fun _ => mapL_framed _ (checkVarF_framed _ _ _)) _

theorem appCoreF_framed {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Framed (appCoreF Γ x y) :=
  bind_framed (fnViewsF_framed _ _) fun _ => appWithF_framed _ _ _

theorem appStepWithF_framed {s : Sig} (Γ : Ctx s) (x y : BVar s .var) (fs : List (FnView Γ x)) :
    Framed (appStepWithF Γ x y fs) := by
  refine orElseL_framed (appWithF_framed _ _ _) (flatMapL_framed (fun f => ?_) fs)
  refine bind_framed (adaptInsertF_framed _ _ _) fun o => ?_
  cases o with
  | some r => exact letPairsF_framed _ _ (appCoreF_framed _ _ _)
  | none => exact ret_framed _

theorem appStepF_framed {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Framed (appStepF Γ x y) :=
  bind_framed (fnViewsF_framed _ _) fun _ => appStepWithF_framed _ _ _ _

theorem appAllF_framed {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Framed (appAllF Γ x y) := by
  refine bind_framed (fnViewsF_framed _ _) fun fs => bind_framed ?_ fun _ => ret_framed _
  cases fs with
  | nil =>
    refine bind_framed (boxViewsF_framed _ _) fun bs => ?_
    dsimp only
    split
    · exact flatMapL_framed (fun _ => letPairsF_framed _ _ (appStepF_framed _ _ _)) _
    · exact ret_framed _
  | cons f fs => exact appStepWithF_framed _ _ _ _

theorem projAllF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) :
    Framed (projAllF Γ x a) := by
  refine bind_framed (fldViewsF_framed _ _ _) fun fs => bind_framed ?_ fun _ => ret_framed _
  cases fs with
  | nil =>
    refine bind_framed (boxViewsF_framed _ _) fun bs => ?_
    dsimp only
    split
    · exact flatMapL_framed (fun _ => letPairsF_framed _ _
        (bind_framed (fldViewsF_framed _ _ _) fun _ => ret_framed _)) _
    · exact ret_framed _
  | cons f fs => exact ret_framed _

theorem lamGenF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T)
    (rs : List (Elab (Γ.cons T))) : Framed (lamGenF Γ T hwf rs) :=
  flatMapL_framed (fun _ => mapL_framed _ (lamUsesF_framed _ _ _)) _

theorem lamCheckF_framed {s : Sig} (Γ : Ctx s) (T : Ty s) (hwf : Ty.Wf T) (C : CaptureSet s)
    (T1' : Ty s) (T2 : Ty (s,x)) (rs : List (Elab (Γ.cons T))) :
    Framed (lamCheckF Γ T hwf C T1' T2 rs) := by
  unfold lamCheckF
  split
  · exact mapL_framed _ (bindO_framed (subcapF_framed _ _ _) fun _ =>
      mapO_framed _ (subF_framed _ _ _))
  · exact ret_framed _

theorem objDoneF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs (s,x))
    (U : CaptureSet s) (r : DefsElab (Γ.consSelf e S U) S) : Framed (objDoneF Γ S e U r) :=
  dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (subcapF_framed _ _ _))
    (fun _ => ret_framed _)) (fun _ => ret_framed _)

theorem newAtomF_framed {s : Sig} (Γ : Ctx s) (U : CaptureSet s) (a : CapAtom s) :
    Framed (newAtomF Γ U a) := by
  refine ite_framed (ret_framed _) (bind_framed (subcapF_framed _ _ _) fun o => ?_)
  cases o with
  | some _ => exact ret_framed _
  | none => exact ret_framed _

theorem newAtomsF_framed {s : Sig} (Γ : Ctx s) (U D : CaptureSet s) :
    Framed (newAtomsF Γ U D) :=
  flatMapL_framed (newAtomF_framed Γ U) D

theorem objNextF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (fix : Bool) (e : Defs (s,x))
    (U : CaptureSet s) (r : DefsElab (Γ.consSelf e S U) S) : Framed (objNextF Γ S fix e U r) :=
  ite_framed (ret_framed _) (bind_framed (hereBoundsF_framed _ _) fun _ =>
    bind_framed (newAtomsF_framed _ _ _) fun _ => ret_framed _)

theorem objFixF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (fix : Bool)
    {chk : (e : Defs (s,x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.consSelf e S U) S))}
    (hchk : ∀ e U, Framed (chk e U)) :
    ∀ k e U, Framed (objFixF Γ S fix chk k e U)
  | 0, e, U => by
    rw [objFixF]
    exact zero_framed
  | k + 1, e, U => by
    rw [objFixF]
    exact bindO_framed (hchk _ _) fun r => orElse_framed (objDoneF_framed _ _ _ _ _)
      (bind_framed (objNextF_framed _ _ _ _ _ _) fun _ =>
        ite_framed (ret_framed _) (objFixF_framed Γ S fix hchk k _ _))

end Frames

mutual

theorem inferF_framed {s : Sig} (Γ : Ctx s) : (a : ATm s) → (G : Option (Ty s)) →
    Framed (inferF Γ a G)
  | .path (.var x), G => by
    cases G with
    | none => rw [inferF]; exact ret_framed _
    | some T => rw [inferF]; exact mapL_framed _ (adaptVarF_framed _ _ _)
  | .lam T t, G => by
    rw [inferF]
    refine dite_framed (fun hwf => orElseL_framed ?_ ?_) (fun _ => ret_framed _)
    · split
      · exact bind_framed (inferF_framed _ t _) fun _ => lamCheckF_framed _ _ _ _ _ _ _
      · exact ret_framed _
    · exact bind_framed (inferF_framed _ t _) fun _ =>
        bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _
  | .obj S U0 d, G => by
    rw [inferF]
    exact bind_framed (objFixF_framed _ _ _ (fun _ _ => checkDefsF_framed _ d S) _ _ _) fun _ =>
      finishF_framed _ _ _
  | .app x y, G => by
    rw [inferF]
    exact bind_framed (appAllF_framed _ _ _) fun _ => finishF_framed _ _ _
  | .proj x a, G => by
    rw [inferF]
    exact bind_framed (projAllF_framed _ _ _) fun _ => finishF_framed _ _ _
  | .let ann t u, G => by
    rw [inferF]
    exact bind_framed (inferF_framed _ t _) fun r1s => orElseL_framed
      (letSpecialF_framed _ _ _ _ fun r1 o => inferF_framed _ u o)
      (bind_framed (letGenF_framed _ _ _ fun r1 o => inferF_framed _ u o) fun _ =>
        finishF_framed _ _ _)
  | .box x, G => by
    cases G with
    | some T =>
      rw [inferF]
      exact orElseL_framed (mapL_framed _ (boxCheckF_framed _ _ _)) (finishF_framed _ _ _)
    | none =>
      rw [inferF]
      exact orElseL_framed (ret_framed _) (finishF_framed _ _ _)
  | .unbox C x, G => by
    rw [inferF]
    exact bind_framed (boxViewsF_framed _ _) fun _ => finishF_framed _ _ _
  | .asc t T, G => by
    rw [inferF]
    exact bind_framed (inferF_framed _ t _) fun _ => finishF_framed _ _ _

theorem checkDefsF_framed {s : Sig} (Γ : Ctx s) : (d : ADefs s) → (S : Shape s) →
    Framed (checkDefsF Γ d S)
  | .typ A S0, S => by
    cases S with
    | typ B L U => rw [checkDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | .cap A c, S => by
    cases S with
    | cap B c1 c2 => rw [checkDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | .trm a t, S => by
    cases S with
    | fld c T =>
      rw [checkDefsF]
      exact dite_framed (fun _ => bind_framed (inferF_framed _ t _) fun _ => ret_framed _)
        (fun _ => ret_framed _)
    | _ => exact ret_framed _
  | .and d1 d2, S => by
    cases S with
    | and S1 S2 =>
      rw [checkDefsF]
      exact bindO_framed (checkDefsF_framed _ d1 S1) fun _ =>
        mapO_framed _ (checkDefsF_framed _ d2 S2)
    | _ => exact ret_framed _

end

/-- A typing that ends unmarked does the same with more fuel. -/
theorem synthF_frame {s : Sig} {Γ : Ctx s} {a : ATm s} {t t' : Tank}
    {r : List (Elab Γ)} (h : synthF Γ a t = (r, t')) (ho : t'.out = false) (k : Nat) :
    synthF Γ a (t.add k) = (r, t'.add k) :=
  (inferF_framed Γ a none).shift t r t' h ho k

theorem checkF_framed {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Framed (checkF Γ a T) :=
  inferF_framed Γ a (some T)

theorem checkInF_framed {s : Sig} (Γ : Ctx s) (a : ATm s) (U : CaptureSet s) (T : Ty s) :
    Framed (checkInF Γ a U T) := by
  refine bind_framed (inferF_framed Γ a none) fun rs => ?_
  cases rs with
  | cons r _ => exact bindO_framed (subcapF_framed _ _ _) fun _ => mapO_framed _ (subF_framed _ _ _)
  | nil => exact ret_framed _

/-- A first candidate leaves the tank unmarked. -/
theorem firstCand_some {α : Type} {r : List α × Tank} {c : α} (h : (firstCand r).1 = some c) :
    (firstCand r).2.out = false := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => simp [firstCand] at h
  | cons c' l =>
    cases ht : t.out with
    | false => simp [firstCand, ht]
    | true => simp [firstCand, ht] at h

theorem firstCand_add {α : Type} (l : List α) (t : Tank) (k : Nat) :
    firstCand (l, t.add k) = ((firstCand (l, t)).1, (firstCand (l, t)).2.add k) := by
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, Tank.add, ht]

/-- The tank `firstCand` leaves is the one it is handed. -/
theorem firstCand_snd {α : Type} (r : List α × Tank) : (firstCand r).2 = r.2 := by
  obtain ⟨l, t⟩ := r
  cases l with
  | nil => rfl
  | cons c l => cases ht : t.out <;> simp [firstCand, ht]

theorem synthInF_stable {s : Sig} {Γ : Ctx s} {a : ATm s} {n k : Nat} {r : Option (Elab Γ)}
    (h : synthInF Γ a n = (r, ⟨k, false⟩)) (m : Nat) : (synthInF Γ a (n + m)).1 = r := by
  unfold synthInF at h ⊢
  cases hs : synthF Γ a ⟨n, false⟩ with
  | mk l t' =>
    have ht' : t' = ⟨k, false⟩ := by
      have := firstCand_snd (synthF Γ a ⟨n, false⟩)
      rw [h, hs] at this
      exact this.symm
    have hf := synthF_frame hs (by rw [ht']) m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf, firstCand_add]
    rw [hs] at h
    rw [h]

theorem synthInF_mono {s : Sig} {Γ : Ctx s} {a : ATm s} {n m : Nat} {c : Elab Γ}
    (h : (synthInF Γ a n).1 = some c) (hnm : n ≤ m) : (synthInF Γ a m).1 = some c := by
  have ho : (synthInF Γ a n).2.out = false := firstCand_some h
  have he : synthInF Γ a n = (some c, ⟨(synthInF Γ a n).2.left, false⟩) := by
    rw [← h, ← ho]
  have := synthInF_stable he (m - n)
  rw [Nat.add_sub_cancel' hnm] at this
  exact this

/-- More fuel keeps the answer of a closed typing. -/
theorem synthTop?_mono {n m : Nat} {π : PlatformNames} {a : ATm π.sig}
    {c : Elab (platformCtx π.plat)} (h : (synthTopF n π a).1 = some c) (hnm : n ≤ m) :
    (synthTopF m π a).1 = some c :=
  synthInF_mono h hnm

/-- A closed typing that ends unmarked gives the same verdict at every larger
fuel.  So a rejection that ends unmarked is a rejection by the rules. -/
theorem synthTop?_stable {n k : Nat} {π : PlatformNames} {a : ATm π.sig}
    {r : Option (Elab (platformCtx π.plat))} (h : synthTopF n π a = (r, ⟨k, false⟩)) (m : Nat) :
    (synthTopF (n + m) π a).1 = r :=
  synthInF_stable h m

/-! ## Progress of the object fixpoint

A pass of `objFixF` that does not stop goes on with the set `objNextF` gives
and with the definitions it elaborated.  It goes on only when one of the two
changed.  When the set changed, it gained an atom that the current set does
not account for: an atom outside the set whose subcapturing goal `{a} <: U`
ended unmarked with no answer, so that no algorithmic derivation of it exists
(`subcapF_complete`).  A written set never changes, so a pass at a written set
goes on only with other definitions.

These facts do not bound the number of passes.  A pass elaborates the
literal's definitions afresh under its own self binder, and box inference
under one binder need not keep the insertions it made under another.  So the
definitions are not known to grow.  The bound `objBound` is a size of the
program, and the pass that reaches it marks the tank (`objFixF_zero`).  So a
literal that runs out of passes is at the recursion limit, never rejected by
the rules. -/

section Progress

variable {s : Sig} {Γ : Ctx s}

/-- The last pass marks the tank. -/
theorem objFixF_zero (S : Shape (s,x)) (fix : Bool)
    (chk : (e : Defs (s,x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.consSelf e S U) S)))
    (e : Defs (s,x)) (U : CaptureSet s) (t : Tank) :
    objFixF Γ S fix chk 0 e U t = (none, { t with out := true }) := rfl

/-- A pass: type the definitions, stop if they are final, else go on at the
next set and the elaborated definitions unless both are unchanged. -/
theorem objFixF_succ (S : Shape (s,x)) (fix : Bool)
    (chk : (e : Defs (s,x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.consSelf e S U) S)))
    (k : Nat) (e : Defs (s,x)) (U : CaptureSet s) :
    objFixF Γ S fix chk (k + 1) e U =
      bindO (chk e U) fun r =>
        Fu.orElse (objDoneF Γ S e U r) fun _ =>
          Fu.bind (objNextF Γ S fix e U r) fun U' =>
            if U' = U ∧ r.tm.erase = e then Fu.ret none
            else objFixF Γ S fix chk k r.tm.erase U' := by
  rw [objFixF]

/-- An atom `newAtomF` keeps, on a tank it leaves unmarked, is outside the set
and has no algorithmic derivation below it. -/
theorem newAtomF_new {U : CaptureSet s} {b : CapAtom s} {t : Tank} {N : CaptureSet s}
    {t' : Tank} (h : newAtomF Γ U b t = (N, t')) (ho : t'.out = false) :
    ∀ a ∈ N, a ∉ U ∧ ¬ Alg ⟨s, Γ, .cap [a] U⟩ := by
  intro a ha
  cases he : CaptureSet.elem U b with
  | true =>
    have hu : newAtomF Γ U b t = ([], t) := by
      unfold newAtomF
      rw [he, if_pos rfl]
      rfl
    rw [hu] at h
    cases h
    cases ha
  | false =>
    have hu : newAtomF Γ U b t =
        match subcapF Γ [b] U t with
        | (some _, t1) => ([], t1)
        | (none, t1) => ([b], t1) := by
      unfold newAtomF
      rw [he, if_neg (by decide)]
      unfold Fu.bind
      rcases subcapF Γ [b] U t with ⟨_ | _, _⟩ <;> rfl
    rw [hu] at h
    rcases hs : subcapF Γ [b] U t with ⟨o, t1⟩
    rw [hs] at h
    cases o with
    | some _ =>
      cases h
      cases ha
    | none =>
      cases h
      have hab : a = b := List.mem_singleton.mp ha
      subst hab
      refine ⟨fun hm => ?_, fun hA => ?_⟩
      · rw [(CaptureSet.elem_iff U).mpr hm] at he
        cases he
      · have hc := subcapF_complete hA t (by rw [hs]; exact ho)
        rw [hs] at hc
        cases hc

/-- Every atom `newAtomsF` keeps, on a tank it leaves unmarked, is outside the
set and has no algorithmic derivation below it. -/
theorem newAtomsF_new {U : CaptureSet s} :
    ∀ (D : CaptureSet s) {t : Tank} {N : CaptureSet s} {t' : Tank},
      newAtomsF Γ U D t = (N, t') → t'.out = false → ∀ a ∈ N, a ∉ U ∧ ¬ Alg ⟨s, Γ, .cap [a] U⟩
  | [], t, N, t', h, _, a, ha => by
    have h0 : newAtomsF Γ U [] t = ([], t) := rfl
    rw [h0] at h
    cases h
    cases ha
  | b :: D, t, N, t', h, ho, a, ha => by
    have hu : newAtomsF Γ U (b :: D) t =
        match newAtomF Γ U b t with
        | (ys, t1) => match newAtomsF Γ U D t1 with
          | (zs, t2) => (ys ++ zs, t2) := rfl
    rw [hu] at h
    rcases hb : newAtomF Γ U b t with ⟨ys, t1⟩
    rcases hD : newAtomsF Γ U D t1 with ⟨zs, t2⟩
    rw [hb] at h
    dsimp only at h
    rw [hD] at h
    cases h
    have ho1 : t1.out = false := by
      cases h1 : t1.out with
      | false => rfl
      | true =>
        have hab := (newAtomsF_framed Γ U D).absorbs t1 h1
        rw [hD] at hab
        dsimp only at hab
        rw [hab, h1] at ho
        cases ho
    rcases List.mem_append.mp ha with ha | ha
    · exact newAtomF_new hb ho1 a ha
    · exact newAtomsF_new D hD ho a ha

/-- The set of the next pass contains the current set.  An atom it adds is
outside the current set and has no algorithmic derivation below it.  A set
with no atom outside the current one is the current set. -/
theorem objNextF_new {S : Shape (s,x)} {fix : Bool} {e : Defs (s,x)} {U : CaptureSet s}
    {r : DefsElab (Γ.consSelf e S U) S} {t : Tank} {U' : CaptureSet s} {t' : Tank}
    (h : objNextF Γ S fix e U r t = (U', t')) (ho : t'.out = false) :
    CaptureSet.Subset U U' ∧ (∀ a ∈ U', a ∉ U → ¬ Alg ⟨s, Γ, .cap [a] U⟩) ∧
      ((∀ a ∈ U', a ∈ U) → U' = U) := by
  cases fix with
  | true =>
    have hu : objNextF Γ S true e U r t = (U, t) := rfl
    rw [hu] at h
    cases h
    exact ⟨fun _ h => h, fun _ h hn => absurd h hn, fun _ => rfl⟩
  | false =>
    have hu : objNextF Γ S false e U r t =
        match hereBoundsF (Γ.consSelf e S U) r.uses t with
        | (bs, t1) => match newAtomsF Γ U ((capDropHere? (selOf bs) r.uses).getD []) t1 with
          | (N, t2) => (capJoin U N, t2) := rfl
    rw [hu] at h
    rcases hh : hereBoundsF (Γ.consSelf e S U) r.uses t with ⟨bs, t1⟩
    rw [hh] at h
    dsimp only at h
    rcases hn : newAtomsF Γ U ((capDropHere? (selOf bs) r.uses).getD []) t1 with ⟨N, t2⟩
    rw [hn] at h
    cases h
    have hnew := newAtomsF_new _ hn ho
    refine ⟨capJoin_left U N, fun a ha hnu => ?_, fun hall => ?_⟩
    · rcases List.mem_append.mp ha with ha | ha
      · exact absurd ha hnu
      · exact (hnew a (List.mem_filter.mp ha).1).2
    · show U ++ N.filter (fun a => !(CaptureSet.elem U a)) = U
      cases hf : N.filter (fun a => !(CaptureSet.elem U a)) with
      | nil => exact List.append_nil U
      | cons a F =>
        have hmem : a ∈ N.filter (fun a => !(CaptureSet.elem U a)) := by
          rw [hf]
          exact List.mem_cons_self
        have hin : a ∈ U := hall a (List.mem_append_right U hmem)
        have hp := (List.mem_filter.mp hmem).2
        rw [(CaptureSet.elem_iff U).mpr hin] at hp
        cases hp

/-- A pass of the object fixpoint that does not stop and goes on to another
pass adds an atom that the current set does not account for, or goes on with
other definitions.  `h` is the pass's `objNextF`, on a tank it leaves
unmarked, and `hgo` says the pass goes on (`objFixF_succ`). -/
theorem objFix_progress {S : Shape (s,x)} {fix : Bool} {e : Defs (s,x)} {U : CaptureSet s}
    {r : DefsElab (Γ.consSelf e S U) S} {t : Tank} {U' : CaptureSet s} {t' : Tank}
    (h : objNextF Γ S fix e U r t = (U', t')) (ho : t'.out = false)
    (hgo : ¬ (U' = U ∧ r.tm.erase = e)) :
    (∃ a, a ∈ U' ∧ a ∉ U ∧ ¬ Alg ⟨s, Γ, .cap [a] U⟩) ∨ r.tm.erase ≠ e := by
  obtain ⟨_, hnew, hsame⟩ := objNextF_new h ho
  cases hd : decide (r.tm.erase = e) with
  | false => exact Or.inr (of_decide_eq_false hd)
  | true =>
    have he := of_decide_eq_true hd
    refine Or.inl ?_
    cases hx : U'.find? (fun a => !(CaptureSet.elem U a)) with
    | some a =>
      have hp := List.find?_some hx
      have hnu : a ∉ U := fun hm => by
        rw [(CaptureSet.elem_iff U).mpr hm] at hp
        cases hp
      exact ⟨a, List.mem_of_find?_eq_some hx, hnu, hnew a (List.mem_of_find?_eq_some hx) hnu⟩
    | none =>
      have hall : ∀ a ∈ U', a ∈ U := fun a ha => by
        have hn := List.find?_eq_none.mp hx a ha
        cases hm : CaptureSet.elem U a with
        | true => exact (CaptureSet.elem_iff U).mp hm
        | false =>
          rw [hm] at hn
          exact absurd rfl hn
      exact absurd ⟨hsame hall, he⟩ hgo

/-- A pass at a written set goes on only with other definitions. -/
theorem objFix_progress_fixed {S : Shape (s,x)} {e : Defs (s,x)} {U : CaptureSet s}
    {r : DefsElab (Γ.consSelf e S U) S} {t : Tank} {U' : CaptureSet s} {t' : Tank}
    (h : objNextF Γ S true e U r t = (U', t')) (hgo : ¬ (U' = U ∧ r.tm.erase = e)) :
    r.tm.erase ≠ e := by
  have hu : objNextF Γ S true e U r t = (U, t) := rfl
  rw [hu] at h
  cases h
  exact fun he => hgo ⟨rfl, he⟩

end Progress

/-! ## Checks

Each check types a surface program at `defaultFuel` in the kernel, resolved
over the empty platform or over `πc`.  It states the use set and type, or
that there is none, and the tank left.  An unmarked tank says that the fuel
played no part in the verdict.  A rejection with the tank unmarked holds at
every fuel (`synthTop?_stable`). -/

section Checks

open Captures.DotMNF.Examples

/-- The use set a derivation concludes at. -/
def usesOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : CaptureSet s := U

/-- The type a derivation concludes at. -/
def tyOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : Ty s := T

/-- The use set and type of a program over a platform after resolution, from
a full tank of `n` units, with the tank left. -/
def judgAt (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) :
    Option (CaptureSet π.sig × Ty π.sig) × Tank :=
  match resolveTop Λc π e with
  | some a => ((synthTopF n π a).1.map fun r => (r.uses, r.ty), (synthTopF n π a).2)
  | none => (none, ⟨n, true⟩)

/-- The erasure of the elaborated program, from a full tank of `n` units. -/
def elabAt (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Option (Tm π.sig) :=
  (resolveTop Λc π e).bind fun a => (synthTopF n π a).1.map fun r => r.tm.erase

/-- The typer keeps the skeleton of the program. -/
def keepsSkel (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Bool :=
  match resolveTop Λc π e with
  | some a =>
      match (synthTopF n π a).1 with
      | some r => decide (r.tm.skel = a.skel)
      | none => false
  | none => false

/-- `λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)`, E10 at function types. -/
def E10tsrc : STm :=
  cap% λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)

/-- `let i = λ(x : ⊤). x in (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i`. -/
def E11src : STm :=
  cap% let i = λ(x : ⊤). x in
       (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i

/-- C2 with the client ascribed at the calculus's `C2ClientTy`. -/
def C2ascSrc : STm :=
  cap% let c = (λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                  λ(u : ⊤). x.run u
                : ∀(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2})
                    (∀(u : ⊤) ⊤) ^ {k1, k2}) in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

/-- The ascribed C2 erases to the calculus's term. -/
example : (resolveTop Λc πc C2ascSrc).map ATm.erase = some C2tm := by decide

/-- C5 in direct style, `let n = it.next in let r = n un in r`. -/
def C5src : STm := cap% let n = it.next in let r = n un in r

/-- The names of `S2Ctx3`: the platform, then `mk`, `un` and `it`. -/
def C5names : NameEnv ([],c,c,x,x,x) := ((πc.names.cons "mk").cons "un").cons "it"

/-- The platform set at `S2Ctx3`. -/
def C5plat : CaptureSet ([],c,c,x,x,x) :=
  CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken πc.set))

/-- C5 resolves to the term of the calculus's `C5_typed`. -/
example : (resolveIn Λc C5names C5plat C5src).map ATm.erase =
    some (.let (.proj .here lnext) (.let (.app .here (.there (.there .here))) (.path (.var .here)))) := by
  decide

/-- S1 with `withFile` unascribed. -/
def S1bareSrc : STm :=
  cap% let withFile =
        λ(cp : (μ(c. {C^ : {}..{k1}})) ^ {}).
           λ(op : (∀(f : (μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})) ^ {k1}) ⊤) ^ {cp.C}).
             let fl = ν(file : {read : (∀(u : ⊤) ⊤)}. {read = λ(u : ⊤). u}) in op fl in
      let cp = ν(c : {C^ : {k1}..{k1}}. {C^ = {k1}}) in
      let op = λ(f : (μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})) ^ {k1}). λ(u : ⊤). u in
      let g = withFile cp in
      let r = g op in
      r

/-- The unascribed S1 erases to the calculus's term. -/
example : (resolveTop Λc πc S1bareSrc).map ATm.erase = some S1tm := by decide

/-- C7 as a Scala program has it: no box written, and the element called where
it is read, `let e = o.e1 in e u`. -/
def C7scalaSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u

/-- An argument that needs a box: `g` takes a boxed capability and `f1` is not
boxed. -/
def argBoxSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let g = λ(b : □((∀(u : ⊤) ⊤) ^ {k1})). b in g f1

/-- An argument that needs an unboxing: `h` takes the capability and `e` is its
box. -/
def argUnboxSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})}. {e1 = f1}) in
        let e = o.e1 in
        let h = λ(k : (∀(u : ⊤) ⊤) ^ {k1}). k in h e

/-- A receiver that is a box: `e.a` with `e` boxed has no field. -/
def recvSrc : STm :=
  cap% λ(p : {a : ⊤} ^ {k1}).
        let o = ν(z : {e1 : □({a : ⊤} ^ {k1})}. {e1 = p}) in
        let e = o.e1 in e.a

/-- A literal that holds `f` in a field. -/
def impureSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = f})

/-- A literal that holds `f` in a field and its box in another. -/
def impureInsSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : □((∀(u : ⊤) ⊤) ^ {f})} ∧ {b : (∀(u : ⊤) ⊤) ^ {f}}. {a = f} ∧ {b = f})

/-- A literal that uses `f` and `h`, with `h` declared at `{y.C}` and the
member `C` of `y` bounded by `{}`.  The empty set accounts for `h`, so the
literal's set is `{f}`. -/
def accountedSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(y : {C^ : {}..{}}). λ(h : (∀(u : ⊤) ⊤) ^ {y.C}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : (∀(u : ⊤) ⊤) ^ {h}}. {a = f} ∧ {b = h})

/-- The context `κ, x : ⊤ ^ {κ}`. -/
def capVarCtx : Ctx ([],c,x) := .cons (.consC .nil) (Ty.capt [CapAtom.cvar .here] .top)

/-- E1 with the middle written.  A `let` annotation types the whole `let`, so
`let t : T = x in t` ascribes `T` to `x`. -/
def E1ssrc : STm :=
  cap% λ(x : {A : ⊤..⊥}).
         let y : {B : {a : ⊤} .. {a : ⊤}} = (let u : x.A = (let t : ⊤ = x in t) in u) in y

/-- E3 with the middle written, by the same ascription. -/
def E3ssrc : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = (let u : x.A = z in u) in y

/-- A function at an intersection of two function types, applied to an
argument only the second accepts. -/
def P5src : STm :=
  cap% λ(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). λ(y : ⊤). f y

/-- `y : x.A`, the field `a` four steps down `x.A`'s upper bound. -/
def P4src : STm :=
  cap% λ(x : {A : ⊥ .. μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : ⊤}))}). λ(y : x.A). y.a

/-- A projection with two fields, the first through `x.A`'s upper bound.  Only
the second has the member `b`. -/
def R1src : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A projection with two written fields.  Only the second has the member `b`. -/
def R2src : STm :=
  cap% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A written `let` annotation that the bound value does not meet. -/
def A1src : STm :=
  cap% λ(x : ⊤). let y : {a : ⊤} = x in y

/-- A field reached only through a middle the program does not write:
`n : {a : ⊤}` below `x.A`, and `x.A` below `{b : ⊤}`. -/
def B1src : STm :=
  cap% λ(x : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}). n.b

/-- G: the inner `let` has the type `z.A`, which avoidance replaces by the meet
of the upper bounds of `z`'s two members `A`, and the member `b` is found in
the meet. -/
def Gsrc : STm :=
  cap% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})). λ(w : ⊤).
         let r = (let z = f w in z.v) in r.b

/-- A check through `∀` bodies that never ends, `x : p.A` against `q.B`,
through a written `let` type. -/
def LPletSrc : STm :=
  cap% λ(p : μ(s. {A : ⊥ .. ∀(y : ⊤) s.A})). λ(q : μ(s. {B : ∀(y : ⊤) s.B .. ⊤})).
         λ(x : p.A). let r : q.B = x in r

/-- The same check through an ascription. -/
def LPascSrc : STm :=
  cap% λ(p : μ(s. {A : ⊥ .. ∀(y : ⊤) s.A})). λ(q : μ(s. {B : ∀(y : ⊤) s.B .. ⊤})).
         λ(x : p.A). (x : q.B)

/-- The inner `let` of G alone. -/
def Ginsrc : STm :=
  cap% λ(f : ∀(y : ⊤) μ(s. ({A : ⊥ .. {a : ⊤}} ∧ {A : ⊥ .. {b : ⊤}}) ∧ {v : s.A})). λ(w : ⊤).
         let z = f w in z.v

/-- The function type of G. -/
def GFun : Ty [] :=
  (Shape.all (.top ^ []) ((Shape.mu (.and
    (.and (.typ lA .bot (.fld la (.top ^ []))) (.typ lA .bot (.fld lb (.top ^ []))))
    (.fld lv ((Shape.sel (.var .here) lA) ^ [])))) ^ [])) ^ []

/-- `κ₁` at the signature of `C7Ctxe`. -/
private abbrev k1e : BVar ([],c,c,x,x,x,x) .cap := .there (.there (.there (.there (.there .here))))

/-- The ascription `(e : (⊤ → ⊤) ^ {κ₁})` at `C7Ctxe`, where `e` is the box. -/
def C7ascE : ATm ([],c,c,x,x,x,x) := .asc (.path (.var .here)) (capTy k1e)

/-- C7 with the unboxing at the other capability. -/
def rejOtherCapSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k2} ⊸ e

/-- An unboxing of a closure. -/
def rejUnboxClosureSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). {k1} ⊸ f1

/-- C7 with the fields swapped. -/
def rejSwappedSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f2} ∧ {e2 = f1})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- A capability ascribed at the other capability. -/
def rejOtherAscSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). (f1 : (∀(u : ⊤) ⊤) ^ {k2})

/-- An unboxing whose type does not reach the goal. -/
def rejUnboxGoalSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k2})

/-- The Scala form of C7 elaborated, erased:
`λ(f1). λ(f2). λ(u). let o = … in let e = o.e1 in let e' = {k1} ⊸ e in e' u`. -/
def C7scalaTm : Tm ([],c,c) :=
  .val (.lam (capTy k1) (.val (.lam (capTy (.there .here)) (.val (.lam unitTy
    (.let (.val (.obj (C7Defs (.there (.there (.there .here))) (.there (.there .here)))))
      (.let (.proj .here le1)
        (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here))))))]
            .here)
          (.app .here (.there (.there (.there .here))))))))))))

/-- `argBoxSrc` elaborated, erased: `let y = □ f1 in g y`. -/
def argBoxTm : Tm ([],c,c) :=
  .val (.lam (capTy k1)
    (.let (.val (.lam ((Shape.box (capTy (.there (.there .here)))) ^ []) (.path (.var .here))))
      (.let (.val (.box (.there .here))) (.app (.there .here) .here))))

/-- `argUnboxSrc` elaborated, erased: `let y = {k1} ⊸ e in h y`. -/
def argUnboxTm : Tm ([],c,c) :=
  .val (.lam (capTy k1)
    (.let (.val (.obj (.trm le1 (.val (.box (.there .here))))))
      (.let (.proj .here le1)
        (.let (.val (.lam (capTy (.there (.there (.there (.there .here))))) (.path (.var .here))))
          (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]
              (.there .here))
            (.app (.there .here) .here))))))

/-- `recvSrc` elaborated, erased: `let p' = {k1} ⊸ e in p'.a`. -/
def recvTm : Tm ([],c,c) :=
  .val (.lam ((Shape.fld la unitTy) ^ [CapAtom.cvar k1])
    (.let (.val (.obj (.trm le1 (.val (.box (.there .here))))))
      (.let (.proj .here le1)
        (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there .here))))] .here)
          (.proj .here la)))))

/-- `impureInsSrc` elaborated, erased: `□ f` in the first field. -/
def impureInsTm : Tm ([],c,c) :=
  .val (.lam (capTy k1)
    (.val (.obj (.and (.trm la (.val (.box (.there .here))))
      (.trm lb (.path (.var (.there .here))))))))

/-! ### E1 to E11 over the empty platform

E1, E3 and E4 need a middle the program does not write, and the typer
chooses none.  E10 applies a variable at `⊤`. -/

example : judgAt .empty E1src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel
example : judgAt .empty E2src =
    (some ([], (Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ []),
      ⟨defaultFuel - 64, false⟩) := by decide +kernel
example : judgAt .empty E3src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel
example : judgAt .empty E4src = (none, ⟨defaultFuel - 12, false⟩) := by decide +kernel
example : judgAt .empty E5src = (some (usesOfDeriv E5, tyOfDeriv E5), ⟨defaultFuel - 19, false⟩) := by
  decide +kernel
example : judgAt .empty E6src =
    (some ([], (Shape.all E6Int (tyOfDeriv E6)) ^ []), ⟨defaultFuel - 15, false⟩) := by decide +kernel
example : judgAt .empty E7src = (some (usesOfDeriv E7, tyOfDeriv E7), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel
example : judgAt .empty E8src = (some (usesOfDeriv E8, tyOfDeriv E8), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel
example : judgAt .empty E9src =
    (some ([], (Shape.all E8Dom ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 7, false⟩) := by decide +kernel
example : judgAt .empty E10src = (none, ⟨defaultFuel - 2, false⟩) := by decide +kernel
example : judgAt .empty E10tsrc =
    (some ([], (Shape.all (arrowS ^ []) ((Shape.all (arrowS ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 11, false⟩) := by decide +kernel
example : judgAt .empty E11src = (some ([], unitTy), ⟨defaultFuel - 21, false⟩) := by decide +kernel

-- The middles written.
example : judgAt .empty E1ssrc = (some ([], (Shape.all E1Dom E1Res) ^ []), ⟨defaultFuel - 18, false⟩) := by
  decide +kernel
example : judgAt .empty E3ssrc =
    (some ([], (Shape.all E3Dom ((Shape.all E3T2 E3T1) ^ [])) ^ []), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

/-! ### The capture programs over `πc` -/

example : judgAt πc C7src =
    (some (usesOfDeriv C7_typed, tyOfDeriv C7_typed), ⟨defaultFuel - 23, false⟩) := by decide +kernel
example : elabAt πc C7src = some C7tm := by decide +kernel
example : judgAt πc C7nbSrc =
    (some (usesOfDeriv C7_typed, tyOfDeriv C7_typed), ⟨defaultFuel - 51, false⟩) := by decide +kernel
example : elabAt πc C7nbSrc = some C7tm := by decide +kernel
example : judgAt πc C7scalaSrc =
    (some ([], (Shape.all (capTy k1) ((Shape.all (capTy (.there .here))
      ((Shape.all unitTy unitTy) ^ [CapAtom.cvar (.there (.there (.there .here)))])) ^ [])) ^ []),
      ⟨defaultFuel - 54, false⟩) := by decide +kernel
example : elabAt πc C7scalaSrc = some C7scalaTm := by decide +kernel
example : keepsSkel πc C7scalaSrc = true := by decide +kernel
example : judgAt πc S3src =
    (some (usesOfDeriv S3_typed, tyOfDeriv S3_typed), ⟨defaultFuel - 42, false⟩) := by decide +kernel
example : judgAt πc S3nbSrc =
    (some (usesOfDeriv S3_typed, tyOfDeriv S3_typed), ⟨defaultFuel - 79, false⟩) := by decide +kernel
example : elabAt πc S3nbSrc = some S3tm := by decide +kernel
example : judgAt πc C2ascSrc =
    (some (usesOfDeriv C2_typed, tyOfDeriv C2_typed), ⟨defaultFuel - 177, false⟩) := by decide +kernel
example : judgAt πc C2src =
    (some ([CapAtom.cvar k2], arrowS ^ [CapAtom.cvar k2]), ⟨defaultFuel - 175, false⟩) := by
  decide +kernel
example : elabAt πc C2src = some C2tm := by decide +kernel
example : judgAt πc S1src =
    (some (usesOfDeriv S1_typed, tyOfDeriv S1_typed), ⟨defaultFuel - 91, false⟩) := by decide +kernel
example : judgAt πc S1bareSrc = (some ([], unitTy), ⟨defaultFuel - 78, false⟩) := by decide +kernel
example : elabAt πc S1bareSrc = some S1tm := by decide +kernel
example : judgAt πc S2src =
    (some (usesOfDeriv S2_typed, tyOfDeriv S2_typed), ⟨defaultFuel - 116, false⟩) := by decide +kernel

/-- C5 at `S2Ctx3`: the least judgment `{it, it.C}` and `⊤ ^ {it.C}`, and the
calculus's judgment reached from it on the same tank. -/
example : (resolveIn Λc C5names C5plat C5src).map (fun a =>
    ((synthInF S2Ctx3 a defaultFuel).1.map (fun r => (r.uses, r.ty)), (synthInF S2Ctx3 a defaultFuel).2)) =
    some (some ([CapAtom.var .here, CapAtom.sel .here lC], Ty.capt [CapAtom.sel .here lC] .top),
      ⟨defaultFuel - 17, false⟩) := by decide +kernel
example : (resolveIn Λc C5names C5plat C5src).map (fun a =>
    ((checkInF S2Ctx3 a (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) ⟨defaultFuel, false⟩).1.isSome,
      (checkInF S2Ctx3 a (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) ⟨defaultFuel, false⟩).2)) =
    some (true, ⟨defaultFuel - 63, false⟩) := by decide +kernel

/-! ### Box inference at an argument, a receiver and a field -/

example : judgAt πc argBoxSrc =
    (some ([], (Shape.all (capTy k1) ((Shape.box (capTy (.there (.there .here)))) ^ [])) ^ []),
      ⟨defaultFuel - 16, false⟩) := by decide +kernel
example : elabAt πc argBoxSrc = some argBoxTm := by decide +kernel
example : keepsSkel πc argBoxSrc = true := by decide +kernel
example : judgAt πc argUnboxSrc =
    (some ([], (Shape.all (capTy k1) (arrowS ^ [CapAtom.cvar (.there (.there .here))])) ^
      [CapAtom.cvar k1]), ⟨defaultFuel - 39, false⟩) := by decide +kernel
example : elabAt πc argUnboxSrc = some argUnboxTm := by decide +kernel
example : judgAt πc recvSrc =
    (some ([], (Shape.all ((Shape.fld la unitTy) ^ [CapAtom.cvar k1]) unitTy) ^ [CapAtom.cvar k1]),
      ⟨defaultFuel - 28, false⟩) := by decide +kernel
example : elabAt πc recvSrc = some recvTm := by decide +kernel
example : keepsSkel πc recvSrc = true := by decide +kernel
example : judgAt πc impureSrc =
    (some ([], (Shape.all (capTy k1)
      ((Shape.mu (.fld la (arrowS ^ [CapAtom.var (.there .here)]))) ^ [CapAtom.var .here])) ^ []),
      ⟨defaultFuel - 12, false⟩) := by decide +kernel
example : judgAt πc impureInsSrc =
    (some ([], (Shape.all (capTy k1)
      ((Shape.mu (.and (.fld la ((Shape.box (arrowS ^ [CapAtom.var (.there .here)])) ^ []))
        (.fld lb (arrowS ^ [CapAtom.var (.there .here)])))) ^ [CapAtom.var .here])) ^ []),
      ⟨defaultFuel - 21, false⟩) := by decide +kernel
example : elabAt πc impureInsSrc = some impureInsTm := by decide +kernel

/-! ### The atoms the object fixpoint adds

An atom the current set accounts for is not added.  `{x}` is below `{κ}`
when `x` is declared at `{κ}`, and nothing but `{}` is below `{}`. -/

example : newAtomsF capVarCtx [CapAtom.cvar (.there .here)]
    [CapAtom.var .here, CapAtom.cvar (.there .here)] ⟨defaultFuel, false⟩ =
    ([], ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : newAtomsF capVarCtx [] [CapAtom.var .here] ⟨defaultFuel, false⟩ =
    ([CapAtom.var .here], ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : judgAt πc accountedSrc =
    (some ([], (Shape.all (capTy k1) ((Shape.all ((Shape.cap lC [] []) ^ [])
      ((Shape.all (arrowS ^ [CapAtom.sel .here lC])
        ((Shape.mu (.and (.fld la (arrowS ^ [CapAtom.var (.there (.there (.there .here)))]))
          (.fld lb (arrowS ^ [CapAtom.var (.there .here)])))) ^
          [CapAtom.var (.there (.there .here))])) ^ [])) ^ [])) ^ []),
      ⟨defaultFuel - 40, false⟩) := by decide +kernel

/-! ### What box inference rejects

The ascription at `C7Ctxe` elaborates to the calculus's unboxing.  The five
programs that follow ask for an insertion the rules do not license, and each
is rejected with the tank unmarked. -/

example : (synthInF C7Ctxe C7ascE defaultFuel).1.map (fun r => (r.tm.erase, r.uses, r.ty)) =
    some (.unbox [CapAtom.cvar k1e] .here, usesOfDeriv C7unbox, tyOfDeriv C7unbox) := by
  decide +kernel
example : (synthInF C7Ctxe C7ascE defaultFuel).2 = ⟨defaultFuel - 5, false⟩ := by decide +kernel
example : judgAt πc rejOtherCapSrc = (none, ⟨defaultFuel - 19, false⟩) := by decide +kernel
example : judgAt πc rejUnboxClosureSrc = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel
example : judgAt πc rejSwappedSrc = (none, ⟨defaultFuel - 14, false⟩) := by decide +kernel
example : judgAt πc rejOtherAscSrc = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel
example : judgAt πc rejUnboxGoalSrc = (none, ⟨defaultFuel - 48, false⟩) := by decide +kernel

/-! ### Every member a candidate, a written annotation that binds, and avoidance at the meet -/

example : judgAt .empty P4src =
    (some ([], (Shape.all ((Shape.typ lA .bot (.mu (.and (.fld lb unitTy)
      (.and (.fld lv unitTy) (.fld la unitTy))))) ^ [])
      ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 28, false⟩) := by decide +kernel
example : judgAt .empty P5src =
    (some ([], (Shape.all ((Shape.and (.all ((Shape.fld la unitTy) ^ []) unitTy) (.all unitTy unitTy)) ^ [])
      ((Shape.all unitTy unitTy) ^ [])) ^ []), ⟨defaultFuel - 13, false⟩) := by decide +kernel
example : judgAt .empty R1src =
    (some ([], (Shape.all E8Dom ((Shape.all ((Shape.and (.sel (.var .here) lA)
      (.fld la ((Shape.fld lb unitTy) ^ []))) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 17, false⟩) := by decide +kernel
example : judgAt .empty R2src =
    (some ([], (Shape.all ((Shape.and (.fld la unitTy) (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      unitTy) ^ []), ⟨defaultFuel - 10, false⟩) := by decide +kernel
example : judgAt .empty A1src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel
example : judgAt .empty B1src = (none, ⟨defaultFuel - 2, false⟩) := by decide +kernel
example : judgAt .empty Ginsrc =
    (some ([], (Shape.all GFun ((Shape.all unitTy
      ((Shape.and (.fld la unitTy) (.fld lb unitTy)) ^ [])) ^ [])) ^ []),
      ⟨defaultFuel - 44, false⟩) := by decide +kernel
example : judgAt .empty Gsrc =
    (some ([], (Shape.all GFun ((Shape.all unitTy unitTy) ^ [])) ^ []), ⟨defaultFuel - 50, false⟩) := by
  decide +kernel

/-! ### The recursion limit

LP, through a written `let` type and through an ascription, ends with the
tank marked. -/

example : (judgAt .empty LPletSrc).1 = none := by decide +kernel
example : (judgAt .empty LPletSrc).2.out = true := by decide +kernel
example : (judgAt .empty LPascSrc).1 = none := by decide +kernel
example : (judgAt .empty LPascSrc).2.out = true := by decide +kernel

end Checks

end CapturesFrontend
