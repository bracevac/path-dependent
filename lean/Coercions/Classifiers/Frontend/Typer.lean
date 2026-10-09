import Coercions.Classifiers.Frontend.Adapt
import Coercions.Classifiers.Frontend.Alg
import Coercions.Classifiers.Frontend.Resolve
import Coercions.Classifiers.DotToFCdot.Prediction

/-!
# The typer

The typer reads a use set and an answer off an annotated term and returns the
derivation of `HasTy` (`lean/Coercions/Classifiers/DotMNF/Typing.lean`) about
the erasure of the term it typed.  Every result carries its derivation, so
the result type is the soundness statement.

It runs on the tank of `Fuel.lean`.  One tank is threaded through every goal
it asks: each subtyping, subcapturing, kinding, answer and variable goal of
`Sub.lean`, each member lookup of `Look.lean`, and each avoidance of
`Avoid.lean`.  So the fuel counts the work of the whole typing, and a goal
that finds the tank short marks it.  A marked tank is the recursion limit.
It is never a rejection by the rules.

## Least sets

The typer computes the least use set the rules allow.  A variable declared
at the empty set is used at the empty set and keeps its declared type.  Any
other variable is used at `{x}` with its declared shape at `{x}`.  A value is
used at `{}`.  Application, projection and unboxing join the sets of their
premises with `capJoin`.  At the binders the set is a candidate followed by
evidence.

- `λ(x : T). t` drops `{x}` and `{x ↾ φ}` from the body's set, reads `{x.C}`
  and `{x.C ↾ φ}` at the upper bound of `x`'s capture member, found by the
  lookup, and strengthens the result past the arrow's binder and the body's
  root.
- `let x = t in u` approximates the body's set from above (`avoidUses`):
  `{x}` becomes the capture set of `t`'s type (`sc-var`), `{x.C}` the
  member's upper bound, and a restricted atom of `x` the same set restricted,
  so the filter is kept.
- `let ⟨c, x⟩ = t in u` charges the bound of the witness, and the body's set
  without the payload and the witness.
- `ν(z : S. d)` is typed by a least fixpoint on its capture set (`objFixF`).

## Written types

A written type is decided to be in the notation of `Classifiers` and then read
where it is written.  A lambda domain reads `any` as the arrow's own capture
binder (`Value.expand`).  A `let` annotation, an ascription and an object's
self shape read `any` at `Ctx.reading`: the innermost scope root, or the
program's platform set if there is none.  A `fresh` in the result of an arrow
becomes an existential (`Ty.expandFresh`).  The platform set `ps` is an
argument of the typer for that reason.

## Candidates

Synthesis returns a list of candidates, each an elaborated term with its use
set, its answer and its derivation.  The compiler merges two members of one
name (`TypeBounds.&` in `core/Types.scala`).  The calculus has no rule for the
merge, so the typer keeps every choice instead.

- A variable has its first view.
- `x y` tries every function type the lookup finds in `x`, and keeps each one
  whose domain, with the arrow's binder at `y`, `y` meets.  An argument that
  fails is adapted by box adaptation and bound by a `let`.  A function with a
  box and no function type is unboxed and bound by a `let`.
- `x.a` returns every field at `a` the lookup finds.  A receiver with a box
  and no such field is unboxed and bound by a `let`.
- `let x = t in u` without annotation returns every pair of a candidate of
  `t` and a candidate of `u`.  The body's type is approximated by a type free
  of `x` (`avoidLet`), as `TypeOps.avoid` does.  When the candidate of `t` has
  an existential answer, the `let` becomes an unpacking: the body is renamed
  past the witness binder, typed under the witness and the payload, and its
  answer leaves their scope by `avoidEx`.
- `let x : A = t in u` has the answer `A`.  The annotation binds.  The body is
  checked against it and is never approximated.  An existential annotation is
  reached from the plain `let` by the answer goal, which packs it.
- `□ x` is the box of the first view, and `C ⊸ x` unboxes every box the
  lookup finds with the boxed set `C`, read off the first box when none is
  written.
- `(t : T)` checks `t` against `T`.

## Checking

Synthesis and checking are one function, `inferF`, with an optional goal.  It
is structural on an index that starts at the size of the term.  Every
recursive call is at a subterm, or at the body of a `let` renamed past the
witness binder of an unpacking, which has the same size.  Checking a variable
goes through box adaptation (`adaptVarF`), whose plain checking is the `var`
goal.  That goal reaches the rules subsumption does not, `HasTy.andI` and
`HasTy.recI`.  Three forms are checked against the goal's form first: a `λ`
against a function type checks its body against the codomain, a `let` with
no annotation checks its body against the goal, and a box value against a box
goal checks the variable against the boxed type.  Every other candidate is
moved to the goal by the answer goal.

## The object rule

`HasTy.obj` types the definitions of a literal under a class root and a self
binder that holds the same definitions and the same capture set as the
conclusion.  Box adaptation changes the definitions, and the set of a literal
is known only after its definitions are typed.  `objFixF` iterates.  It types
the definitions under a binder at the current definitions and set, and stops
when the elaborated definitions erase to the ones the binder holds and their
use set is below the current set and the self variable.  Otherwise the next
pass takes the elaborated definitions and the current set joined with the
atoms of the set they used that the current set does not account for.  Those
atoms have the self variable dropped, their capture members read at their
upper bounds, and the class root strengthened away.  An atom is accounted for
when the subcapturing goal from it to the current set has an answer.

This is the compiler's class use set, a variable grown until it is solved
(`CheckCaptures.recheckClassDef`, `CaptureSet.tryInclude`).  The comparison is
by subcapturing, not by syntax, so a restricted atom `{a ↾ φ}` that the set
already holds through `{a}`, or through `{a ↾ ψ}` with `φ` a subkind of `ψ`, is
not added again.  Restricting `a ↾ φ` again at `φ` (`CapAtom.projBy`) appends
the exclusion lists of the kind, so the result is a new atom as syntax, and the
set that holds `a ↾ φ` accounts for it.  A pass that goes on adds an atom the
set does not account for, or goes on with other definitions
(`objFix_progress`).  The number of passes is bounded by `objBound`, a size of
the program that counts each base atom once per kind the classifiers in scope
can form.  A pass that reaches the bound marks the tank, so the bound never
causes a rejection.

## Verdicts

`synthTopF` and `synthInF` return the first candidate with the tank left.
`synthIn?` and `synthTop?` read that as a verdict, the form `compile` returns.
A candidate is `ok`.  A marked tank is `unknown`.  A rejection with the tank
unmarked is `rejected` when a reason with its proof is found, and `unknown`
otherwise.  `whyF` looks for the reason: a written type outside the notation
(`anyNotOk`, `freshNotOk`), a body whose answer is an existential outside
every scope (`existentialAtTop`), or a level escape at the goal an annotation
or an ascription reached (`levelEscape`).  The last is found by walking the
synthesized type and the written one as the arrow rule does, and is certified
by `escape_rejected_at`, the contrapositive of `source_lvl_safety`.  It speaks
of the goal the typer reached, not of every derivation of the program.

## The theorems

Every computation here is framed: it keeps a marked tank, never adds fuel,
and does the same with more fuel (`synthF_frame`).  So a typing that ends
unmarked gives the same answer at every larger fuel (`synthTop?_mono`,
`synthTop?_stable`).  A rejection that ends unmarked is a rejection at every
fuel.

The typer has no completeness theorem.  It does not find a derivation through
a middle type the program does not write, as the compiler does not.  It does
not merge two members, so it tries each.  It does not find a judgment whose
search needs more than the fuel.  A lookup through a cyclic member is cut, as
the compiler cuts a cyclic reference.

Every definition is structural, so the kernel evaluates the typer.  The checks
at the end of the module type the example programs at `defaultFuel` by
`decide +kernel`.  A level escape reads the resolution through `capsK`, a
structural twin of the well-founded `Ctx.caps`, so the kernel decides those
verdicts too.
-/

namespace ClassifiersFrontend

open Frontend.Fuel ClassifiersFrontend.Core
open Classifiers.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub
  SubShape Subcap ESub HasTy DefsTy Platform Subst)
open scoped Classifiers.DotMNF

/-- The fuel of a typing.  One field, the size of the tank every entry point
starts from. -/
structure Budget where
  fuel : Nat := defaultFuel

/-! ## Reasons and verdicts -/

/-- Why a program is rejected, with the proof. -/
inductive Reason : Type where
  /-- A written type puts `any` where `Classifiers` reads none. -/
  | anyNotOk {s : Sig} (T : Ty s) (h : T.anyOk = false)
  /-- A written type puts `fresh` where `Classifiers` reads none. -/
  | freshNotOk {s : Sig} (T : Ty s) (h : T.freshOk = false)
  /-- No member-free subcapturing puts `C` below `D` at `Γ`.  The atom `r`
  is the root the certificate confines `D` to. -/
  | levelEscape {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) (r : Classifiers.FCdot.CapAtom s)
      (cert : ¬ ∃ d : Subcap Γ C D, d.MemberFree)
  /-- The answer at `Γ`, a context outside every scope, is an existential,
  and no answer inclusion takes it to a plain type. -/
  | existentialAtTop {s : Sig} (Γ : Ctx s) (E : ETy s)
      (cert : ∀ T : Ty s, ¬ Nonempty (ESub Γ E (.ty T)))

/-- The verdict of the typer. -/
inductive Verdict (α : Type) : Type where
  /-- Typed, with the result. -/
  | ok : α → Verdict α
  /-- Rejected, with a reason that carries its proof. -/
  | rejected : Reason → Verdict α
  /-- No answer, with no reason found, or the recursion limit. -/
  | unknown : Verdict α

namespace Verdict

variable {α β : Type}

/-- Sequencing: a rejection or an `unknown` stops the computation. -/
def bind (v : Verdict α) (f : α → Verdict β) : Verdict β :=
  match v with
  | .ok a => f a
  | .rejected r => .rejected r
  | .unknown => .unknown

/-- The result of a success, transformed. -/
def map (f : α → β) (v : Verdict α) : Verdict β :=
  match v with
  | .ok a => .ok (f a)
  | .rejected r => .rejected r
  | .unknown => .unknown

/-- An optional result read as a verdict: nothing is `unknown`. -/
def ofOption (o : Option α) : Verdict α :=
  match o with
  | some a => .ok a
  | none => .unknown

/-- The result of a success. -/
def toOption (v : Verdict α) : Option α :=
  match v with
  | .ok a => some a
  | _ => none

/-- The verdict is a success. -/
def isOk (v : Verdict α) : Bool :=
  match v with
  | .ok _ => true
  | _ => false

/-- The verdict is a rejection. -/
def isRejected (v : Verdict α) : Bool :=
  match v with
  | .rejected _ => true
  | _ => false

/-- The reason of a rejection. -/
def reason? (v : Verdict α) : Option Reason :=
  match v with
  | .rejected r => some r
  | _ => none

end Verdict

/-- The name of a reason, for messages. -/
def Reason.name : Reason → String
  | .anyNotOk _ _ => "anyNotOk"
  | .freshNotOk _ _ => "freshNotOk"
  | .levelEscape _ _ _ _ _ => "levelEscape"
  | .existentialAtTop _ _ _ => "existentialAtTop"

/-- The rejection of an existential answer outside every scope, where no root
can absorb its witness. -/
def existentialAt {s : Sig} (Γ : Ctx s) (q : XElab Γ) : Reason :=
  .existentialAtTop Γ (∃ᶜ[q.bnd] q.body) (fun _ ⟨e⟩ => by cases e)

/-! ## Written types

A written type is decided to be in the notation of `Classifiers` and then read
at the position it is written at.  A lambda domain and a `let` annotation are
decided as part of an arrow, since the conditions on them are the arrow
clauses of `Shape.anyOk` and `Shape.freshOk`. -/

/-- The arrow with parameter `T` and a pure `⊤` result.  Its `anyOk` is
`T.domAnyOk` and its `freshOk` is `T.noFresh`. -/
def domArrow {s : Sig} (T : Ty (Sig.dom s)) : Ty s := (Shape.all T (.ty (.top ^ []))) ^ []

/-- The arrow with a pure `⊤` parameter and the answer `E` as its result. -/
def ansArrow {s : Sig} (E : ETy s) : Ty s :=
  (Shape.all (.top ^ []) (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E))) ^ []

/-- Why a written type is not in the notation of `Classifiers`, if it is not. -/
def writtenWhy {s : Sig} (T : Ty s) : Option Reason :=
  if h : T.anyOk = false then some (.anyNotOk T h)
  else if h' : T.freshOk = false then some (.freshNotOk T h')
  else none

/-- Why a written answer is not in the notation of `Classifiers`.  An
existential is decided as the result of an arrow. -/
def writtenAnsWhy {s : Sig} (E : ETy s) : Option Reason :=
  match E with
  | .ty T => writtenWhy T
  | .ex _ _ => writtenWhy (ansArrow E)

/-- A written lambda domain read at the arrow's own capture binder
(`Value.expand`). -/
def readDom {s : Sig} (T : Ty (Sig.dom s)) : Dom s := T.expand [CapAtom.cvar .here]

/-- A written answer read at a context, with `ps` the platform set. -/
def readAns {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (E : ETy s) : ETy s :=
  match E with
  | .ty T => .ty (readAt Γ ps T)
  | .ex C T => ETy.expand (.ex C T) (Γ.reading ps)

/-- A written self shape read at a context, as `Classifiers` reads `(μ S) ^ {}`
there. -/
def readSelf {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x)) : Shape (s,x) :=
  S.expand (CaptureSet.weaken (Γ.reading ps))

/-- The platform set under a lambda body's root, arrow binder and parameter. -/
abbrev psBody {s : Sig} (ps : CaptureSet s) : CaptureSet (Sig.body s) :=
  CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) (CaptureSet.weaken (k := .cap) ps))

/-- The platform set under an object's class root and self, and under the
witness and payload of an unpacking. -/
abbrev psObj {s : Sig} (ps : CaptureSet s) : CaptureSet ((s,c),x) :=
  CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) ps)

/-- The platform set under one term binder. -/
abbrev psVar {s : Sig} (ps : CaptureSet s) : CaptureSet (s,x) := CaptureSet.weaken (k := .var) ps

/-! ## Moving a derivation across a decided equality

The label of a member occurs twice in the conclusion of its rule, so these use
`cases` rather than a rewrite. -/

/-- A type member definition against a declaration whose bounds are the
definition's own shape. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {S L U : Shape s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy V Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A capture member definition against a declaration whose bounds are the
definition's own set. -/
def defsCapAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {c c1 c2 : CaptureSet s}
    (hA : A = B) (h1 : c = c1) (h2 : c = c2) : DefsTy V Γ (.cap A c) (.cap B c1 c2) := by
  cases hA; cases h1; cases h2; exact .cap

/-- A term member definition against a field declaration at the same
label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy V Γ t (.ty T)) : DefsTy V Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- `{}-I` for definitions equal to the ones the self binder holds, which the
typer typed under it. -/
def objOf {s : Sig} {Γ : Ctx s} {d e : Defs ((s,c),x)} {S : Shape (s,x)} {U : CaptureSet s}
    (h : e = d)
    (dt : DefsTy (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here]) (Γ.objBody d S U) e
      S.underRoot)
    (hd : Defs.Distinct d) : HasTy [] Γ (.val (.obj e)) (.ty ((Shape.mu S) ^ U)) := by
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

/-- Keep the first candidate of each use set and answer. -/
def dedupE {s : Sig} {Γ : Ctx s} : List (Elab Γ) → List (Elab Γ)
  | [] => []
  | r :: rs => r :: (dedupE rs).filter fun r' => !decide (r'.uses = r.uses ∧ r'.ans = r.ans)

/-- A candidate at exactly the answer asked for. -/
def toChecked {s : Sig} {Γ : Ctx s} (r : Elab Γ) (E : ETy s) : Option (Checked Γ E) :=
  if h : r.ans = E then some ⟨r.tm, r.uses, h ▸ r.deriv⟩ else none

/-- The first candidate at exactly the answer asked for. -/
def firstChecked {s : Sig} {Γ : Ctx s} (rs : List (Elab Γ)) (E : ETy s) : Option (Checked Γ E) :=
  rs.findSome? fun r => toChecked r E

/-- The candidates moved to a goal: all of them when there is none, and each
one the answer goal takes to `E` otherwise. -/
def finishF {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (rs : List (Elab Γ)) :
    Fu (List (Elab Γ)) :=
  match G with
  | none => Fu.ret rs
  | some E => Fu.flatMapL (fun r => mapL (subsumeF Γ r E) Checked.toElab) rs

/-! ## The binders of a set

`All-I` and `{}-I` drop the binder `x` from a set over `(s,x)`, and read each
`{x.C}` at the upper bound of the capture member `C` of `x`.  A restricted
atom `{x ↾ φ}` is dropped as `{x}` is, and `{x.C ↾ φ}` is read as `{x.C}`,
since `unproj` puts it below `{x.C}` (`capDropHere?`). -/

/-- The upper bound of the first capture member of the innermost binder at each
label `{x.C}` or `{x.C ↾ φ}` of `V` names, found by the lookup. -/
def hereBoundsF {s : Sig} (Γ : Ctx (s,x)) (V : CaptureSet (s,x)) :
    Fu (List (Label × CaptureSet (s,x))) :=
  Fu.flatMapL (fun a =>
    match a.base with
    | .sel .here C => Fu.bind (capsAt Γ .here C) fun ds =>
        Fu.ret (listO (ds.head?.map fun d => (C, d.2.1)))
    | _ => Fu.ret []) V

/-- The bound found at a label. -/
def selOf {s : Sig} (bs : List (Label × CaptureSet s)) (C : Label) : Option (CaptureSet s) :=
  (bs.find? fun p => decide (p.1 = C)).map (·.2)

/-- The set of a function: the body's set `V` without the parameter,
strengthened past the arrow binder and the body root, with the evidence
`V <: U↑↑↑ ∪ {x}` that `All-I` asks for.  A body that uses its arrow binder or
its body root has no such set. -/
def lamUsesF {s : Sig} (Γ : Ctx s) (T : Dom s) (V : CaptureSet (Sig.body s)) :
    Fu (Option ((U : CaptureSet s) ×
      Subcap (Γ.body T) V
        (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here]))) :=
  Fu.bind (hereBoundsF (Γ.body T) V) fun bs =>
    match capDropHere? (selOf bs) V with
    | some U2 =>
        match capStrengthen? (k := .cap) U2 with
        | some U1 =>
            match capStrengthen? (k := .cap) U1 with
            | some U =>
                mapO (capF (Γ.body T) V
                  (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here]))
                  fun e => ⟨U, e⟩
            | none => Fu.ret none
        | none => Fu.ret none
    | none => Fu.ret none

/-! ## Assembling a `let` -/

/-- `HasTy.let` at the result type `A`, with the body's use set approximated
from above and both premises widened to the join. -/
def letAtF {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (A : Ty s) (p : PElab Γ)
    (r2 : Checked (Γ.cons p.ty) (.ty A.weaken)) : Fu (Option (Elab Γ)) :=
  if hwf : Ty.Wf A then
    mapO (avoidUses Γ p.ty r2.uses) fun q =>
      ⟨.let ann p.tm r2.tm, capJoin p.uses q.1, .ty A,
        HasTy.let (widenLeft p.deriv q.1)
          (widenUses r2.deriv (q.2.trans (.elem (weaken_subset (capJoin_right p.uses q.1))))) hwf⟩
  else Fu.ret none

/-- `HasTy.let` at the avoided type of its body.  A body with an existential
answer has none, since `HasTy.let` concludes at a plain type. -/
def letFinishF {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    (r2 : Elab (Γ.cons p.ty)) : Fu (Option (Elab Γ)) :=
  match r2.split with
  | .inl q =>
      bindO (avoidLet Γ p.ty q.ty) fun a =>
        letAtF Γ ann a.1 p ⟨q.tm, q.uses, HasTy.sub q.deriv (.ty a.2) .refl⟩
  | .inr _ => Fu.ret none

/-- Every candidate of a body under the binder of `p`, each closed by
`letFinishF`. -/
def letPairsF {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    (body : Fu (List (Elab (Γ.cons p.ty)))) : Fu (List (Elab Γ)) :=
  Fu.bind body fun r2s => Fu.flatMapL (fun r2 => mapL (letFinishF Γ ann p r2) id) r2s

/-! ## Assembling an unpacking

`HasTy.letex` opens the witness binder and the payload binder.  The body's use
set may name the witness.  Everything else it uses is charged to the declared
set, which is above the witness's bound. -/

/-- What an unpacking's body uses beyond the witness, with the payload replaced
by the set it is declared at and its capture members by their upper bounds
(`capUpAt`).  The declared set of the unpacking is the bound `C₀` joined with
it, and the evidence is `V <: U₂↑↑ ∪ {c}` at that set. -/
def letexUsesF {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (C₀ : CaptureSet s)
    (V : CaptureSet ((s,c),x)) :
    Fu (Option ((res : CaptureSet s) ×
      Subcap ((Γ.consC).cons T) V
        (CaptureSet.weaken (CaptureSet.weaken (k := .cap) (capJoin C₀ res)) ∪
          [CapAtom.cvar (.there .here)]))) :=
  Fu.bind (capUpAt ((Γ.consC).cons T) .here V) fun r =>
    match capStrengthen? (k := .var) r.1 with
    | some V1 =>
        match capStrengthen? (k := .cap) (V1.filter fun a => !(decide (a = CapAtom.cvar .here))) with
        | some res =>
            mapO (capF ((Γ.consC).cons T) V
              (CaptureSet.weaken (CaptureSet.weaken (k := .cap) (capJoin C₀ res)) ∪
                [CapAtom.cvar (.there .here)])) fun e => ⟨res, e⟩
        | none => Fu.ret none
    | none => Fu.ret none

/-- `HasTy.letex` at the answer `E`, the use set widened to the join. -/
def letexOfF {s : Sig} (Γ : Ctx s) (q : XElab Γ) (E : ETy s)
    (r2 : Checked ((Γ.consC).cons q.body) (ETy.weaken (ETy.weaken (k := .cap) E))) :
    Fu (Option (Elab Γ)) :=
  mapO (letexUsesF Γ q.body q.bnd r2.uses) fun p =>
    ⟨.letex q.tm r2.tm, capJoin q.uses (capJoin q.bnd p.1), E,
      widenUses
        (HasTy.letex q.deriv (.elem (capJoin_left q.bnd p.1)) (widenUses r2.deriv p.2))
        (Subcap.union (.elem (capJoin_left q.uses (capJoin q.bnd p.1)))
          (.elem (capJoin_right q.uses (capJoin q.bnd p.1))))⟩

/-- An unpacking at the answer of its body moved past the witness and the
payload by `avoidEx`. -/
def letexFinishF {s : Sig} (Γ : Ctx s) (q : XElab Γ) (r2 : Elab ((Γ.consC).cons q.body)) :
    Fu (Option (Elab Γ)) :=
  bindO (avoidEx Γ q.body r2.ans) fun a =>
    letexOfF Γ q a.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv a.2 .refl⟩

/-- Every candidate of an unpacking's body, each closed by `letexFinishF`. -/
def letexPairsF {s : Sig} (Γ : Ctx s) (q : XElab Γ)
    (body : Fu (List (Elab ((Γ.consC).cons q.body)))) : Fu (List (Elab Γ)) :=
  Fu.bind body fun r2s => Fu.flatMapL (fun r2 => mapL (letexFinishF Γ q r2) id) r2s

/-! ## The two kinds of `let`

A `let` whose bound term has a plain answer is `HasTy.let`, and one whose
bound term has an existential answer is an unpacking.  The body is passed as
a function of the binder and of an optional goal, so these pieces need no
typer. -/

/-- The candidates of a body under the binder of a plain bound term. -/
abbrev BodyP {s : Sig} (Γ : Ctx s) : Type :=
  (p : PElab Γ) → Option (ETy (s,x)) → Fu (List (Elab (Γ.cons p.ty)))

/-- The candidates of a body under the witness and the payload of an
existential bound term. -/
abbrev BodyX {s : Sig} (Γ : Ctx s) : Type :=
  (q : XElab Γ) → Option (ETy ((s,c),x)) → Fu (List (Elab ((Γ.consC).cons q.body)))

/-- A `let` without annotation, at one candidate of the bound term: every
candidate of the body, approximated past the binder. -/
def letBoundF {s : Sig} (Γ : Ctx s) (r1 : Elab Γ) (bp : BodyP Γ) (bx : BodyX Γ) :
    Fu (List (Elab Γ)) :=
  match r1.split with
  | .inl p => letPairsF Γ none p (bp p none)
  | .inr q => letexPairsF Γ q (bx q none)

/-- A `let` at the answer `E`, at one candidate of the bound term: the body
checked against `E` under the binder.  A plain bound term with an existential
`E` has no such body.  An annotation `ann` then types the body, avoids it, and
packs the plain `let` into `E`. -/
def letOneF {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (E : ETy s) (r1 : Elab Γ)
    (bp : BodyP Γ) (bx : BodyX Γ) : Fu (Option (Elab Γ)) :=
  match r1.split, E with
  | .inl p, .ty G =>
      if tyWf? G then
        Fu.bind (bp p (some (.ty G.weaken))) fun r2s =>
          match firstChecked r2s (.ty G.weaken) with
          | some r2 => letAtF Γ ann G p r2
          | none => Fu.ret none
      else Fu.ret none
  | .inl p, .ex _ _ =>
      match ann with
      | some _ =>
          Fu.bind (letPairsF Γ ann p (bp p none)) fun rs =>
            Fu.firstSome (fun r => mapO (subsumeF Γ r E) Checked.toElab) rs
      | none => Fu.ret none
  | .inr q, E =>
      Fu.bind (bx q (some (ETy.weaken (ETy.weaken (k := .cap) E)))) fun r2s =>
        match firstChecked r2s (ETy.weaken (ETy.weaken (k := .cap) E)) with
        | some r2 => letexOfF Γ q E r2
        | none => Fu.ret none

/-! ## Application and projection -/

/-- `x y` at each function type found, the argument checked plainly at the
domain with the arrow's binder at `y`. -/
def appWithF {s : Sig} (Γ : Ctx s) {x : BVar s .var} (fs : List (FnView Γ x)) (y : BVar s .var) :
    Fu (List (Elab Γ)) :=
  Fu.flatMapL (fun f => mapL (checkVarF Γ y (Ty.subst f.dom (Subst.singleC (.var y)))) fun r =>
    (⟨.app x y, capJoin f.uses r.uses, ETy.subst f.cod (Subst.arg y),
      HasTy.app (widenLeft f.deriv r.uses) (widenRight f.uses r.deriv)⟩ : Elab Γ)) fs

/-- `x y` at each function type the lookup finds. -/
def appCoreF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) : Fu (List (Elab Γ)) :=
  Fu.bind (fnViewsF Γ x) fun fs => appWithF Γ fs y

/-- `x y` at the function types `fs`.  If no domain takes `y` plainly, `y` is
adapted against each domain by box adaptation and bound by a `let`. -/
def appStepWithF {s : Sig} (Γ : Ctx s) (x y : BVar s .var) (fs : List (FnView Γ x)) :
    Fu (List (Elab Γ)) :=
  orElseL (appWithF Γ fs y)
    (Fu.flatMapL (fun f =>
      Fu.bind (adaptInsertF Γ y (Ty.subst f.dom (Subst.singleC (.var y)))) fun
        | some r => letPairsF Γ none r.toPElab (appCoreF (Γ.cons r.toPElab.ty) (.there x) .here)
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
          | some C => Fu.flatMapL (fun p =>
              letPairsF Γ none p (appStepF (Γ.cons p.ty) .here (.there y))) (unboxAll C bs)
          | none => Fu.ret []
      | _ => appStepWithF Γ x y fs) fun cs =>
      Fu.ret (dedupE cs)

/-- The projection at a field found. -/
def projOf {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} (f : FldView Γ x a) : Elab Γ :=
  ⟨.proj x a, f.uses, .ty f.ty, HasTy.proj f.deriv⟩

/-- A projection: one candidate per field the lookup finds.  A receiver with
no field but a box is unboxed at the set of its first box and bound by a
`let`. -/
def projAllF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) : Fu (List (Elab Γ)) :=
  Fu.bind (fldViewsF Γ x a) fun fs =>
    Fu.bind (match fs with
      | [] => Fu.bind (boxViewsF Γ x) fun bs =>
          match firstBoxSet bs with
          | some C => Fu.flatMapL (fun p =>
              letPairsF Γ none p (Fu.bind (fldViewsF (Γ.cons p.ty) .here a) fun gs =>
                Fu.ret (gs.map projOf))) (unboxAll C bs)
          | none => Fu.ret []
      | fs => Fu.ret (fs.map projOf)) fun cs =>
      Fu.ret (dedupE cs)

/-! ## A function -/

/-- The goal's function type, if it is one. -/
def funGoal? {s : Sig} : Option (ETy s) → Option (CaptureSet s × Dom s × Cod s)
  | some (.ty (.capt C (.all T1 T2))) => some (C, T1, T2)
  | _ => none

/-- The domain of a goal below the written one, in the scope `SubShape.all`
compares domains in.  Equal domains need no goal. -/
def domSubF {s : Sig} (Γ : Ctx s) (T1' T1 : Dom s) :
    Fu (Option (Sub Γ.scope (Dom.underRoot T1') (Dom.underRoot T1))) :=
  if h : T1' = T1 then Fu.ret (some (h ▸ Sub.refl _)) else subF Γ.scope _ _

/-- `λ(x : T). t` from the candidates of its body: the codomain read back past
the body's root, and the function's set from the body's. -/
def lamGenF {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (rs : List (Elab (Γ.body T))) :
    Fu (List (Elab Γ)) :=
  Fu.flatMapL (fun (r : Elab (Γ.body T)) =>
    match codPast? r.ans with
    | some ⟨T2, h⟩ =>
        mapL (lamUsesF Γ T r.uses) fun p =>
          (⟨.lam T r.tm, [], .ty ((Shape.all T T2) ^ p.1), HasTy.lam (h ▸ widenUses r.deriv p.2) hwf⟩ :
            Elab Γ)
    | none => Fu.ret []) rs

/-- `λ(x : T). t` against `(∀(x : T1') T2) ^ C`, from the candidates of its
body checked against `T2`: the body's set below `C↑↑↑ ∪ {x}`, and `T1'` below
`T`. -/
def lamCheckF {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (C : CaptureSet s) (T1' : Dom s)
    (T2 : Cod s) (rs : List (Elab (Γ.body T))) : Fu (List (Elab Γ)) :=
  match firstChecked rs (Cod.underRoot T2) with
  | some r =>
      mapL (bindO (capF (Γ.body T) r.uses
          (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken C)) ∪ [.var .here])) fun e =>
        mapO (domSubF Γ T1' T) fun eD =>
          (⟨.lam T r.tm, [], .ty ((Shape.all T1' T2) ^ C),
            HasTy.sub (HasTy.lam (widenUses r.deriv e) hwf)
              (.ty (.capt (SubShape.all eD (ESub.refl _)) .refl)) .refl⟩ : Elab Γ)) id
  | none => Fu.ret []

/-! ## The object rule -/

/-- The definitions of a literal typed under a binder that holds the
definitions `e` and the set `U`. -/
abbrev DefsCheck {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) : Type :=
  (e : Defs ((s,c),x)) → (U : CaptureSet s) → Fu (Option (DefsElab (Γ.objBody e S U) S.underRoot))

/-- The final pass of the object rule: the elaborated definitions are the ones
the binder holds and their set is below the binder's set and the self
variable. -/
def objDoneF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs ((s,c),x)) (U : CaptureSet s)
    (r : DefsElab (Γ.objBody e S U) S.underRoot) : Fu (Option (Elab Γ)) :=
  if hd : r.tm.erase = e then
    if hdist : Defs.Distinct e then
      mapO (capF (Γ.objBody e S U) r.uses
          (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here])) fun ev =>
        ⟨.obj S r.tm, [], .ty ((Shape.mu S) ^ U), objOf hd (r.deriv _ ev) hdist⟩
    else Fu.ret none
  else Fu.ret none

/-- The atom `a` alone if the set `U` does not account for it, and nothing
otherwise. -/
def newAtomF {s : Sig} (Γ : Ctx s) (U : CaptureSet s) (a : CapAtom s) : Fu (CaptureSet s) :=
  if CaptureSet.elem U a then Fu.ret []
  else Fu.bind (capF Γ [a] U) fun
    | some _ => Fu.ret []
    | none => Fu.ret [a]

/-- The atoms of `D` that the set `U` does not account for.  An atom of `U` is
skipped at no cost.  Any other atom `a` is kept when the subcapturing goal
`{a} <: U` has no answer.  The compiler adds an element to a set variable only
when the set does not account for it (`CaptureSet.tryInclude` and
`CaptureSet.accountsFor`). -/
def newAtomsF {s : Sig} (Γ : Ctx s) (U D : CaptureSet s) : Fu (CaptureSet s) :=
  Fu.flatMapL (newAtomF Γ U) D

/-- The set of the next pass: the current set, joined with the atoms it does
not account for of the set the definitions used, with the self variable
dropped, its capture members read at their upper bounds and the class root
strengthened away. -/
def objNextF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs ((s,c),x)) (U : CaptureSet s)
    (r : DefsElab (Γ.objBody e S U) S.underRoot) : Fu (CaptureSet s) :=
  Fu.bind (hereBoundsF (Γ.objBody e S U) r.uses) fun bs =>
    Fu.bind (newAtomsF Γ U (((capDropHere? (selOf bs) r.uses).bind fun V =>
        capStrengthen? (k := .cap) V).getD [])) fun N =>
      Fu.ret (capJoin U N)

/-- The object rule as a least fixpoint on the literal's set.  `chk` types the
definitions under a binder, and the index counts the passes left.  A pass
that changes neither the set nor the definitions ends with no answer.  The
last pass marks the tank. -/
def objFixF {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (chk : DefsCheck Γ S) :
    Nat → Defs ((s,c),x) → CaptureSet s → Fu (Option (Elab Γ))
  | 0, _, _ => fun t => (none, { t with out := true })
  | k + 1, e, U =>
      bindO (chk e U) fun r =>
        Fu.orElse (objDoneF Γ S e U r) fun _ =>
          Fu.bind (objNextF Γ S e U r) fun U' =>
            if U' = U ∧ r.tm.erase = e then Fu.ret none
            else objFixF Γ S chk k r.tm.erase U'
termination_by structural k _ _ => k

/-! ### The bound of the object fixpoint -/

/-- The labels of the capture members a set selects, restricted or not. -/
def capLabelsC {s : Sig} (C : CaptureSet s) : List Label :=
  C.filterMap fun a =>
    match a.base with
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
  | .capk A _ => [A]
  | .sel _ _ => []
  | .mu B => capLabelsS B
  | .all T U => capLabelsT T ++ capLabelsE U
  | .and S T => capLabelsS S ++ capLabelsS T
  | .box T => capLabelsT T
/-- The labels of the capture members a type declares or selects. -/
def capLabelsT {s : Sig} : Ty s → List Label
  | .capt C S => capLabelsC C ++ capLabelsS S
/-- The labels of the capture members an answer declares or selects. -/
def capLabelsE {s : Sig} : ETy s → List Label
  | .ty T => capLabelsT T
  | .ex C T => capLabelsC C ++ capLabelsT T
end

mutual
/-- The labels of the capture members a term declares or selects. -/
def capLabelsA {s : Sig} : ATm s → List Label
  | .path _ => []
  | .lam T t => capLabelsT T ++ capLabelsA t
  | .obj S d => capLabelsS S ++ capLabelsD d
  | .app _ _ => []
  | .proj _ _ => []
  | .let ann t u => capLabelsE (ann.getD (.ty (.top ^ []))) ++ capLabelsA t ++ capLabelsA u
  | .letex t u => capLabelsA t ++ capLabelsA u
  | .box _ => []
  | .unbox C _ => capLabelsC (C.getD [])
  | .asc t T => capLabelsA t ++ capLabelsT T
/-- The labels of the capture members definitions declare or select. -/
def capLabelsD {s : Sig} : ADefs s → List Label
  | .typ _ S => capLabelsS S
  | .cap A c => A :: capLabelsC c
  | .trm _ t => capLabelsA t
  | .and d e => capLabelsD d ++ capLabelsD e
end

mutual
/-- The variable occurrences of a term: the sites where box adaptation may
insert a box or an unboxing. -/
def occA {s : Sig} : ATm s → Nat
  | .path _ => 1
  | .lam _ t => occA t
  | .obj _ d => occD d
  | .app _ _ => 2
  | .proj _ _ => 1
  | .let _ t u => occA t + occA u
  | .letex t u => occA t + occA u
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
  | .consRoot Γ => capLabelsCtx Γ
  | .consInst Γ C => capLabelsCtx Γ ++ capLabelsC C
  | .consCls Γ _ => capLabelsCtx Γ

/-- The kinds a set restricts its atoms to. -/
def kindsC {s : Sig} (C : CaptureSet s) : List Classifiers.Cls.Kind :=
  C.filterMap fun a =>
    match a with
    | .proj _ φ => some φ
    | _ => none

mutual
/-- The kinds a shape restricts an atom to or bounds a capture member by. -/
def kindsS {s : Sig} : Shape s → List Classifiers.Cls.Kind
  | .top => []
  | .bot => []
  | .typ _ L H => kindsS L ++ kindsS H
  | .fld _ T => kindsT T
  | .cap _ c1 c2 => kindsC c1 ++ kindsC c2
  | .capk _ φ => [φ]
  | .sel _ _ => []
  | .mu B => kindsS B
  | .all T U => kindsT T ++ kindsE U
  | .and S T => kindsS S ++ kindsS T
  | .box T => kindsT T
/-- The kinds a type writes. -/
def kindsT {s : Sig} : Ty s → List Classifiers.Cls.Kind
  | .capt C S => kindsC C ++ kindsS S
/-- The kinds an answer writes. -/
def kindsE {s : Sig} : ETy s → List Classifiers.Cls.Kind
  | .ty T => kindsT T
  | .ex C T => kindsC C ++ kindsT T
end

mutual
/-- The kinds a term writes. -/
def kindsA {s : Sig} : ATm s → List Classifiers.Cls.Kind
  | .path _ => []
  | .lam T t => kindsT T ++ kindsA t
  | .obj S d => kindsS S ++ kindsD d
  | .app _ _ => []
  | .proj _ _ => []
  | .let ann t u => kindsE (ann.getD (.ty (.top ^ []))) ++ kindsA t ++ kindsA u
  | .letex t u => kindsA t ++ kindsA u
  | .box _ => []
  | .unbox C _ => kindsC (C.getD [])
  | .asc t T => kindsA t ++ kindsT T
/-- The kinds definitions write. -/
def kindsD {s : Sig} : ADefs s → List Classifiers.Cls.Kind
  | .typ _ S => kindsS S
  | .cap _ c => kindsC c
  | .trm _ t => kindsA t
  | .and d e => kindsD d ++ kindsD e
end

/-- The kinds a context writes. -/
def kindsCtx {s : Sig} : Ctx s → List Classifiers.Cls.Kind
  | .nil => []
  | .cons Γ T => kindsCtx Γ ++ kindsT T
  | .consSelf Γ _ S U => kindsCtx Γ ++ kindsS S ++ kindsC U
  | .consC Γ => kindsCtx Γ
  | .consRoot Γ => kindsCtx Γ
  | .consInst Γ C => kindsCtx Γ ++ kindsC C
  | .consCls Γ _ => kindsCtx Γ

/-- The classifiers a kind names: the root and the exclusions of each of its
subtrees. -/
def kindCls (φ : Classifiers.Cls.Kind) : List Classifiers.Cls.Classifier :=
  φ.flatMap fun t => t.root :: t.excls

/-- The intersection of two kinds names no classifier that neither kind names.
So the kinds a fixpoint pass forms from the written ones, by restricting a
restricted atom again (`CapAtom.projBy`, `CapAtom.kindOf`), name only
classifiers the program writes. -/
theorem kindCls_interB (φ ψ : Classifiers.Cls.Kind) :
    ∀ c ∈ kindCls (φ.interB ψ), c ∈ kindCls φ ∨ c ∈ kindCls ψ := by
  intro c hc
  simp only [kindCls, Classifiers.Cls.Kind.interB, List.mem_flatMap] at hc ⊢
  obtain ⟨v, hv, hcv⟩ := hc
  obtain ⟨t, ht, u, hu, hvu⟩ := hv
  unfold Classifiers.Cls.Subtree.interB at hvu
  split at hvu
  · simp only [Classifiers.Cls.Kind.node, List.mem_singleton] at hvu
    subst hvu
    simp only [List.mem_cons, List.mem_append] at hcv
    rcases hcv with h | h | h
    · exact Or.inl ⟨t, ht, by simp [h]⟩
    · exact Or.inl ⟨t, ht, by simp [h]⟩
    · exact Or.inr ⟨u, hu, by simp [h]⟩
  · split at hvu
    · simp only [Classifiers.Cls.Kind.node, List.mem_singleton] at hvu
      subst hvu
      simp only [List.mem_cons, List.mem_append] at hcv
      rcases hcv with h | h | h
      · exact Or.inr ⟨u, hu, by simp [h]⟩
      · exact Or.inl ⟨t, ht, by simp [h]⟩
      · exact Or.inr ⟨u, hu, by simp [h]⟩
    · simp [Classifiers.Cls.Kind.empty] at hvu

/-- The classifiers a context declares its capture binders at. -/
def clsCtx {s : Sig} : Ctx s → List Classifiers.Cls.Classifier
  | .nil => []
  | .cons Γ _ => clsCtx Γ
  | .consSelf Γ _ _ _ => clsCtx Γ
  | .consC Γ => clsCtx Γ
  | .consRoot Γ => clsCtx Γ
  | .consInst Γ _ => clsCtx Γ
  | .consCls Γ c => clsCtx Γ ++ [c]

/-- A list of classifiers without repetitions, keeping the last occurrence
of each. -/
def clsDedup : List Classifiers.Cls.Classifier → List Classifiers.Cls.Classifier
  | [] => []
  | c :: cs => if (clsDedup cs).contains c then clsDedup cs else c :: clsDedup cs

/-- The number of kinds the classifiers in scope can form, as sets of
classifiers.  The classifiers in scope are `⊤`, the ones the program's kinds
name and the ones its capture binders are declared at.  Say there are `R`.
The classifiers above any one classifier form a chain, so each classifier
lies in the region of the least classifier in scope above it, and there are
at most `R` regions.  A kind that names only classifiers in scope holds a
whole region or none of it, so such kinds denote at most `2 ^ R` sets.
Intersecting kinds keeps their classifiers (`kindCls_interB`). -/
def kindForms {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (d : ADefs ((s,c),x)) : Nat :=
  2 ^ (clsDedup (.top :: clsCtx Γ ++
    (kindsCtx Γ ++ kindsS S ++ kindsD d).flatMap kindCls)).length

/-- The number of atoms over `s` a literal's capture set can hold, plus the
insertion sites of box adaptation, plus two.  A base atom is a term variable,
a capture binder, or a capture member of a term variable at a label of the
program.  The set is meant to hold each base atom at most once per kind the
classifiers in scope can form (`kindForms`), the bare atom at `⊤`.  An atom
joins the set only when the set does not account for it, and the subcapturing
goal compares two restrictions of one base by subkinding.  Only the direction
from subkinding to inclusion of classifier sets is proved
(`Kind.Subkind.contains`).  So a restriction at a kind that denotes the same
classifiers as one the set holds is not added again, however the kind is
written.  The count is a size of the program, not a fuel, and it is not proved
to bound the passes. -/
def objBound {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (d : ADefs ((s,c),x)) : Nat :=
  let V := (ctxVars Γ).length
  let K := (ctxCaps Γ).length
  let L := (capLabelsCtx Γ ++ capLabelsS S ++ capLabelsD d).length
  (V + K + V * L) * kindForms Γ S d + occD d + 2

/-! ## Synthesis and checking

Two functions, structural on an index that starts at the size of the term.
`inferF` returns the candidates of a term: every candidate with no goal, and
every candidate at the goal with one.  `checkDefsF` matches a definition list
against a declaration shape in lockstep, as `DefsTy` does
(`DotMNF/Typing.lean`).  At index zero both mark the tank. -/

mutual

/-- The candidates of a term, each with its derivation, on the tank.  With a
goal `some E`, every candidate is at `E`.  `ps` is the platform set, the
reading of `any` at a position with no scope root. -/
def inferF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Nat → (a : ATm s) → (G : Option (ETy s)) → Fu (List (Elab Γ))
  | 0, _, _ => fun t => ([], { t with out := true })
  | _ + 1, .path (.var x), G =>
      match G with
      | none => Fu.ret [varSynth Γ x]
      | some (.ty T) => mapL (adaptVarF Γ x T) Checked.toElab
      | some (.ex C T) => finishF Γ (some (.ex C T)) [varSynth Γ x]
  | k + 1, .lam T t, G =>
      if (writtenWhy (domArrow T)).isNone then
        if hwf : Ty.Wf (readDom T) then
          orElseL
            (match funGoal? G with
              | some (C, T1', T2) =>
                  Fu.bind (inferF (Γ.body (readDom T)) (psBody ps) k t (some (Cod.underRoot T2)))
                    (lamCheckF Γ (readDom T) hwf C T1' T2)
              | none => Fu.ret [])
            (Fu.bind (inferF (Γ.body (readDom T)) (psBody ps) k t none) fun rs =>
              Fu.bind (lamGenF Γ (readDom T) hwf rs) (finishF Γ G))
        else Fu.ret []
      else Fu.ret []
  | k + 1, .obj S d, G =>
      if (writtenWhy ((Shape.mu S) ^ [])).isNone then
        Fu.bind (objFixF Γ (readSelf Γ ps S)
            (fun e U => checkDefsF (Γ.objBody e (readSelf Γ ps S) U) (psObj ps) k d
              (readSelf Γ ps S).underRoot)
            (objBound Γ (readSelf Γ ps S) d) d.erase []) fun o =>
          finishF Γ G (listO o)
      else Fu.ret []
  | _ + 1, .app x y, G => Fu.bind (appAllF Γ x y) (finishF Γ G)
  | _ + 1, .proj x a, G => Fu.bind (projAllF Γ x a) (finishF Γ G)
  | k + 1, .let ann t u, G =>
      Fu.bind (inferF Γ ps k t none) fun r1s =>
        match ann with
        | none =>
            orElseL
              (match G with
                | some E => mapL (Fu.firstSome (fun r1 => letOneF Γ none E r1
                    (fun p o => inferF (Γ.cons p.ty) (psVar ps) k u o)
                    (fun q o => inferF ((Γ.consC).cons q.body) (psObj ps) k
                      (u.rename (Rename.succ (k := .cap)).lift) o)) r1s) id
                | none => Fu.ret [])
              (Fu.bind (Fu.flatMapL (fun r1 => letBoundF Γ r1
                  (fun p o => inferF (Γ.cons p.ty) (psVar ps) k u o)
                  (fun q o => inferF ((Γ.consC).cons q.body) (psObj ps) k
                    (u.rename (Rename.succ (k := .cap)).lift) o)) r1s) fun cs =>
                finishF Γ G (dedupE cs))
        | some A =>
            if (writtenAnsWhy A).isNone then
              Fu.bind (mapL (Fu.firstSome (fun r1 => letOneF Γ (some (readAns Γ ps A))
                  (readAns Γ ps A) r1
                  (fun p o => inferF (Γ.cons p.ty) (psVar ps) k u o)
                  (fun q o => inferF ((Γ.consC).cons q.body) (psObj ps) k
                    (u.rename (Rename.succ (k := .cap)).lift) o)) r1s) id) (finishF Γ G)
            else Fu.ret []
  | k + 1, .letex t u, G =>
      Fu.bind (inferF Γ ps k t none) fun r1s =>
        Fu.bind (Fu.flatMapL (fun r1 =>
            match r1.split with
            | .inr q => letexPairsF Γ q (inferF ((Γ.consC).cons q.body) (psObj ps) k u none)
            | .inl _ => Fu.ret []) r1s) fun cs =>
          finishF Γ G (dedupE cs)
  | _ + 1, .box x, G =>
      match G with
      | some (.ty T) =>
          orElseL (mapL (boxCheckF Γ x T) fun d => (⟨.box x, [], .ty T, d⟩ : Elab Γ))
            (finishF Γ G [boxValue Γ x])
      | some (.ex C T) => finishF Γ (some (.ex C T)) [boxValue Γ x]
      | none => finishF Γ none [boxValue Γ x]
  | _ + 1, .unbox C x, G =>
      Fu.bind (boxViewsF Γ x) fun bs =>
        match C.orElse fun _ => firstBoxSet bs with
        | some C' => finishF Γ G ((unboxAll C' bs).map PElab.toElab)
        | none => Fu.ret []
  | k + 1, .asc t T, G =>
      if (writtenWhy T).isNone then
        Fu.bind (inferF Γ ps k t (some (.ty (readAt Γ ps T)))) fun rs =>
          finishF Γ G (listO ((firstChecked rs (.ty (readAt Γ ps T))).map fun r =>
            (⟨.asc r.tm (readAt Γ ps T), r.uses, .ty (readAt Γ ps T), r.deriv⟩ : Elab Γ)))
      else Fu.ret []
termination_by structural k _ _ => k

/-- A definition list against a declaration shape, in lockstep: a type member
against a declaration with its shape on both bounds, a capture member against
one with its set on both bounds, a term member against a field at the same
label, an intersection against an intersection.  The result holds the least
use set and the derivation at every set above it. -/
def checkDefsF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    Nat → (d : ADefs s) → (S : Shape s) → Fu (Option (DefsElab Γ S))
  | 0, _, _ => fun t => (none, { t with out := true })
  | _ + 1, .typ A S0, .typ B L U =>
      Fu.ret (if hA : A = B then
        if hL : S0 = L then
          if hU : S0 = U then some ⟨.typ A S0, [], fun _ _ => defsTypAt hA hL hU⟩ else none
        else none
      else none)
  | _ + 1, .cap A c, .cap B c1 c2 =>
      Fu.ret (if hA : A = B then
        if h1 : c = c1 then
          if h2 : c = c2 then some ⟨.cap A c, [], fun _ _ => defsCapAt hA h1 h2⟩ else none
        else none
      else none)
  | k + 1, .trm a t, .fld c T =>
      if h : a = c then
        Fu.bind (inferF Γ ps k t (some (.ty T))) fun rs =>
          Fu.ret ((firstChecked rs (.ty T)).map fun (r : Checked Γ (.ty T)) =>
            ⟨.trm a r.tm, r.uses, fun _ e => defsTrmAt h (widenUses r.deriv e)⟩)
      else Fu.ret none
  | k + 1, .and d1 d2, .and S1 S2 =>
      bindO (checkDefsF Γ ps k d1 S1) fun r1 =>
        mapO (checkDefsF Γ ps k d2 S2) fun r2 =>
          ⟨.and r1.tm r2.tm, capJoin r1.uses r2.uses, fun U e =>
            DefsTy.and (r1.deriv U (.trans (.elem (capJoin_left r1.uses r2.uses)) e))
              (r2.deriv U (.trans (.elem (capJoin_right r1.uses r2.uses)) e))⟩
  | _ + 1, _, _ => Fu.ret none
termination_by structural k _ _ => k

end

/-- Synthesis on the tank: the candidates of a term with no goal. -/
def synthF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) : Fu (List (Elab Γ)) :=
  inferF Γ ps (sizeATm a) a none

/-- Checking on the tank: the candidates of a term at the goal `E`. -/
def checkF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (E : ETy s) :
    Fu (List (Elab Γ)) :=
  inferF Γ ps (sizeATm a) a (some E)

/-! ## The entry points on the tank -/

/-- The first candidate, and `none` if the tank ended marked. -/
def firstCand {α : Type} : List α × Tank → Option α × Tank
  | (c :: _, t) => if t.out then (none, t) else (some c, t)
  | ([], t) => (none, t)

/-- The first candidate of a term in `Γ`, from a full tank of `n` units, with
the tank left. -/
def synthInF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (n : Nat) :
    Option (Elab Γ) × Tank :=
  firstCand (synthF Γ ps a ⟨n, false⟩)

/-- The first candidate of a closed program over a platform, at the
platform's context, from a full tank of `n` units, with the tank left. -/
def synthTopF (n : Nat) (π : PlatformNames) (a : ATm π.sig) : Option (Elab π.plat.ctx) × Tank :=
  synthInF π.plat.ctx π.set a n

/-- An answer below another, by equality or by the answer goal. -/
def esubEqF {s : Sig} (Γ : Ctx s) (E F : ETy s) : Fu (Option (ESub Γ E F)) :=
  if h : E = F then Fu.ret (some (h ▸ ESub.refl E)) else esubF Γ E F

/-- The first candidate of a term in `Γ`, then the subcapturing and answer
goals to a given use set and answer, on the same tank.  The typer returns
the least sets, and a judgment with larger ones is reached this way. -/
def checkInF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (U : CaptureSet s)
    (E : ETy s) : Fu (Option ((t : ATm s) × HasTy U Γ t.erase E)) :=
  Fu.bind (synthF Γ ps a) fun
    | r :: _ => bindO (capF Γ r.uses U) fun eU =>
        mapO (esubEqF Γ r.ans E) fun eE => ⟨r.tm, HasTy.sub r.deriv eE eU⟩
    | [] => Fu.ret none

/-- `checkInF` from a full tank of the budget's fuel. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (U : CaptureSet s) (E : ETy s) : Option ((t : ATm s) × HasTy U Γ t.erase E) :=
  (checkInF Γ ps a U E ⟨b.fuel, false⟩).1

/-! ## The level escape, decided

When a binding annotation or an ascription is not reached, the typer walks
the synthesized type and the written one in parallel, as the arrow rule
does, and collects every set goal that subcapturing does not find.  For each
it tries a certificate.  The certificate needs three decided facts: the
context is well formed (`ctxWf?`), the target set resolves to itself at every
depth (`selfAtom?`), and at one small depth the source set is not confined to
a root the target set is confined to.  The last fact reads the resolution
`Ctx.caps`, which is well founded.  `capsK` computes it structurally on a
budget of steps, so the kernel decides the certificate too. -/

/-- Well-formedness of a context, decided.  Only an object's self binder asks
something, the conditions `literalShape?` and `distinctLabels?`. -/
def ctxWf? {s : Sig} (Γ : Ctx s) : Bool :=
  match Γ with
  | .nil => true
  | .cons Γ _ => ctxWf? Γ
  | .consSelf Γ _ S _ => ctxWf? Γ && literalShape? S && distinctLabels? S
  | .consC Γ => ctxWf? Γ
  | .consRoot Γ => ctxWf? Γ
  | .consInst Γ _ => ctxWf? Γ
  | .consCls Γ _ => ctxWf? Γ
termination_by structural Γ

theorem ctxWf?_sound : ∀ {s : Sig} (Γ : Ctx s), ctxWf? Γ = true → Γ.Wf
  | _, .nil, _ => .nil
  | _, .cons Γ _, h => .cons (ctxWf?_sound Γ (by simpa [ctxWf?] using h))
  | _, .consSelf Γ _ S _, h => by
      simp only [ctxWf?, Bool.and_eq_true] at h
      exact .consSelf (ctxWf?_sound Γ h.1.1) ((literalShape?_iff S).mp h.1.2)
        ((distinctLabels?_iff S).mp h.2)
  | _, .consC Γ, h => .consC (ctxWf?_sound Γ (by simpa [ctxWf?] using h))
  | _, .consRoot Γ, h => .consRoot (ctxWf?_sound Γ (by simpa [ctxWf?] using h))
  | _, .consInst Γ _, h => .consInst (ctxWf?_sound Γ (by simpa [ctxWf?] using h))
  | _, .consCls Γ _, h => .consCls (ctxWf?_sound Γ (by simpa [ctxWf?] using h))

/-- An atom of the target that resolves to itself at every depth: the universal
root, a scope root, or a rigid capture binder, with or without a declared
classifier.  A restricted atom resolves through its base and is not one. -/
def selfAtom? {s : Sig} (Γ : Classifiers.FCdot.Ctx s) (a : Classifiers.FCdot.CapAtom s) : Bool :=
  match a with
  | .top => true
  | .cvar κ =>
      match Γ.lookupCap κ with
      | .root => true
      | .star => true
      | .cls _ => true
      | _ => false
  | _ => false

theorem capsAtom_self {s : Sig} {Γ : Classifiers.FCdot.Ctx s} {a : Classifiers.FCdot.CapAtom s}
    (h : selfAtom? Γ a = true) (n : Nat) : Γ.capsAtom n a = [a] := by
  cases a with
  | top => exact Classifiers.FCdot.Ctx.capsAtom_top Γ n
  | cvar κ =>
      rw [Classifiers.FCdot.Ctx.capsAtom_cvar]
      simp only [selfAtom?] at h
      revert h
      cases Γ.lookupCap κ <;> intro h <;> first | rfl | simp at h
  | var x => simp [selfAtom?] at h
  | name x ℓ => simp [selfAtom?] at h
  | proj a φ => simp [selfAtom?] at h

theorem caps_self {s : Sig} {Γ : Classifiers.FCdot.Ctx s} :
    ∀ (D : Classifiers.FCdot.CaptureSet s), (∀ a ∈ D, selfAtom? Γ a = true) →
      ∀ n, Γ.caps n D = D
  | [], _, n => Classifiers.FCdot.Ctx.caps_nil Γ n
  | a :: D, h, n => by
      rw [Classifiers.FCdot.Ctx.caps_cons, capsAtom_self (h a (List.mem_cons_self ..)) n,
        caps_self D (fun b hb => h b (List.mem_cons_of_mem _ hb)) n]
      rfl

/-! ### Resolution on a step budget

`FCdot.Ctx.caps` is defined by well-founded recursion, so the kernel does not
reduce it.  `capsK` and `capsAtomK` follow its clauses one by one, with one
more argument, a budget of steps, on which they recurse structurally.  When the
budget runs out they answer `none`.  An answer is the resolution
(`capsK_sound`).  So the certificate below is computed by the kernel too. -/

section Budget

open Classifiers

mutual

/-- `Ctx.caps` on a budget of `k` steps. -/
def capsK {s : Sig} (k : Nat) (Γ : FCdot.Ctx s) (n : Nat) (C : FCdot.CaptureSet s) :
    Option (FCdot.CaptureSet s) :=
  match k, C with
  | 0, _ => none
  | _ + 1, [] => some []
  | k + 1, a :: C =>
      match capsAtomK k Γ n a, capsK k Γ n C with
      | some A, some B => some (A ++ B)
      | _, _ => none
termination_by structural k

/-- `Ctx.capsAtom` on a budget of `k` steps. -/
def capsAtomK {s : Sig} (k : Nat) (Γ : FCdot.Ctx s) (n : Nat) (a : FCdot.CapAtom s) :
    Option (FCdot.CaptureSet s) :=
  match k, Γ, n, a with
  | 0, _, _, _ => none
  | k + 1, .cons Γ b, n, .var .here => (capsK k Γ n b.ty.captureSet).map FCdot.CaptureSet.weaken
  | k + 1, .cons Γ _, n, .var (.there y) => (capsAtomK k Γ n (.var y)).map FCdot.CaptureSet.weaken
  | k + 1, .consC Γ _, n, .var (.there y) =>
      (capsAtomK k Γ n (.var y)).map FCdot.CaptureSet.weaken
  | _ + 1, .consC _ .root, _, .cvar .here => some [.cvar .here]
  | _ + 1, .consC _ .star, _, .cvar .here => some [.cvar .here]
  | _ + 1, .consC _ (.cls _), _, .cvar .here => some [.cvar .here]
  | k + 1, .consC Γ (.upper C), n, .cvar .here => (capsK k Γ n C).map FCdot.CaptureSet.weaken
  | k + 1, .consC Γ (.inst C), n, .cvar .here => (capsK k Γ n C).map FCdot.CaptureSet.weaken
  | k + 1, .cons Γ _, n, .cvar (.there κ) =>
      (capsAtomK k Γ n (.cvar κ)).map FCdot.CaptureSet.weaken
  | k + 1, .consC Γ _, n, .cvar (.there κ) =>
      (capsAtomK k Γ n (.cvar κ)).map FCdot.CaptureSet.weaken
  | _ + 1, _, _, .top => some [.top]
  | _ + 1, _, 0, .name _ _ => some []
  | k + 1, Γ, n + 1, .name x ℓ =>
      match Γ.lookupDefC x ℓ with
      | some C => capsK k Γ n C
      | none => some []
  | k + 1, Γ, n, .proj a φ => (capsAtomK k Γ n a).map (·.map (FCdot.CapAtom.proj · φ))
termination_by structural k

end

/-- One step of `capsK_sound`, on atoms. -/
theorem capsAtomK_succ_sound {k : Nat}
    (ihC : ∀ {s : Sig} (Γ : FCdot.Ctx s) (n : Nat) (C L : FCdot.CaptureSet s),
      capsK k Γ n C = some L → Γ.caps n C = L)
    (ihA : ∀ {s : Sig} (Γ : FCdot.Ctx s) (n : Nat) (a : FCdot.CapAtom s)
      (L : FCdot.CaptureSet s), capsAtomK k Γ n a = some L → Γ.capsAtom n a = L) :
    ∀ {s : Sig} (Γ : FCdot.Ctx s) (n : Nat) (a : FCdot.CapAtom s) (L : FCdot.CaptureSet s),
      capsAtomK (k + 1) Γ n a = some L → Γ.capsAtom n a = L
  | _, .cons Γ b, n, .var .here, L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihC _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .cons Γ b, n, .var (.there y), L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihA _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ b, n, .var (.there y), L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihA _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ .root, n, .cvar .here, L, h => by
      simp only [capsAtomK, Option.some.injEq] at h; subst h; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ .star, n, .cvar .here, L, h => by
      simp only [capsAtomK, Option.some.injEq] at h; subst h; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ (.cls _), n, .cvar .here, L, h => by
      simp only [capsAtomK, Option.some.injEq] at h; subst h; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ (.upper C), n, .cvar .here, L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihC _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ (.inst C), n, .cvar .here, L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihC _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .cons Γ b, n, .cvar (.there κ), L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihA _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, .consC Γ b, n, .cvar (.there κ), L, h => by
      simp only [capsAtomK, Option.map_eq_some_iff] at h
      obtain ⟨A, hA, rfl⟩ := h
      rw [← ihA _ _ _ _ hA]; simp [FCdot.Ctx.capsAtom]
  | _, Γ, n, .top, L, h => by
      cases Γ <;> simp only [capsAtomK, Option.some.injEq] at h <;> subst h <;>
        exact FCdot.Ctx.capsAtom_top _ n
  | _, Γ, 0, .name x ℓ, L, h => by
      cases Γ <;> simp only [capsAtomK, Option.some.injEq] at h <;> subst h <;>
        exact FCdot.Ctx.capsAtom_name_zero _ x ℓ
  | _, Γ, n + 1, .name x ℓ, L, h => by
      rw [FCdot.Ctx.capsAtom_name_succ]
      cases hd : Γ.lookupDefC x ℓ with
      | none =>
          cases Γ <;> simp only [capsAtomK, hd, Option.some.injEq] at h <;> subst h <;> rfl
      | some C =>
          cases Γ <;> simp only [capsAtomK, hd] at h <;> exact ihC _ _ _ _ h
  | _, Γ, n, .proj a φ, L, h => by
      rw [FCdot.Ctx.capsAtom_proj]
      cases Γ <;> simp only [capsAtomK, Option.map_eq_some_iff] at h <;>
        obtain ⟨A, hA, rfl⟩ := h <;> rw [ihA _ _ _ _ hA]

/-- An answer of `capsK` or `capsAtomK` is the resolution, at every budget. -/
theorem capsK_sound : ∀ (k : Nat),
    (∀ {s : Sig} (Γ : FCdot.Ctx s) (n : Nat) (C L : FCdot.CaptureSet s),
      capsK k Γ n C = some L → Γ.caps n C = L) ∧
    (∀ {s : Sig} (Γ : FCdot.Ctx s) (n : Nat) (a : FCdot.CapAtom s) (L : FCdot.CaptureSet s),
      capsAtomK k Γ n a = some L → Γ.capsAtom n a = L)
  | 0 => ⟨fun _ _ _ _ h => by simp [capsK] at h, fun _ _ _ _ h => by simp [capsAtomK] at h⟩
  | k + 1 => by
    obtain ⟨ihC, ihA⟩ := capsK_sound k
    refine ⟨fun Γ n C L h => ?_, fun Γ n a L h => ?_⟩
    · cases C with
      | nil => simp [capsK] at h; simp [h]
      | cons a C =>
        simp only [capsK] at h
        split at h
        · rename_i A B hA hB
          cases h
          rw [FCdot.Ctx.caps_cons, ihA _ _ _ _ hA, ihC _ _ _ _ hB]
        · cases h
    · exact capsAtomK_succ_sound ihC ihA Γ n a L h

end Budget

/-- The budget of steps of `certify?`.  A resolution that needs more gives no
certificate. -/
def certifyBudget : Nat := 1024

/-- A certificate for the goal `C <: D` at `Γ`: the first root `r` (the
universal one, then each atom of `D`) that confines `D`, with the first depth
below four at which `C` is not confined to it.  The resolution of `C` is
computed by `capsK`, so the kernel reduces the whole certificate. -/
def certify? {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Option Reason :=
  if hwf : ctxWf? Γ = true then
    if hself : ∀ a ∈ D.translate, selfAtom? Γ.translate a = true then
      (Classifiers.FCdot.CapAtom.top :: D.translate).findSome? fun r =>
        if hr : Γ.translate.Confined D.translate r then
          (List.range 4).findSome? fun n =>
            match hk : capsK certifyBudget Γ.translate n C.translate with
            | some L =>
                if hn : ¬ Γ.translate.Confined L r then
                  some (.levelEscape Γ C D r
                    (escape_rejected_at (ctxWf?_sound Γ hwf) r
                      (fun m => by rw [caps_self _ hself m]; exact hr) n
                      (by rw [(capsK_sound certifyBudget).1 _ _ _ _ hk]; exact hn)))
                else none
            | none => none
        else none
    else none
  else none

/-- A set goal at a context the arrow rule opens. -/
structure Goal where
  /-- The signature of the context. -/
  sig : Sig
  /-- The context. -/
  ctx : Ctx sig
  /-- The set on the left. -/
  lo : CaptureSet sig
  /-- The set on the right. -/
  hi : CaptureSet sig

/-- The set goals that subcapturing from a full tank of `n` units does not
find, walking `T <: U` as the arrow rule does: the two sets, then fields,
boxes, and the domains and codomains of arrows under the scopes the arrow
rule opens.  Structural on the depth `k`. -/
def escGoals (n : Nat) (k : Nat) {s : Sig} (Γ : Ctx s) (T U : Ty s) : List Goal :=
  match k with
  | 0 => []
  | k + 1 =>
      match T, U with
      | .capt C S, .capt C' S' =>
          (if (cap? Γ C C' n).1.isSome then [] else [⟨_, Γ, C, C'⟩]) ++
          match S, S' with
          | .all T1 U1, .all T2 U2 =>
              escGoals n k Γ.scope (Dom.underRoot T2) (Dom.underRoot T1) ++
              (match Cod.underRoot U1, Cod.underRoot U2 with
                | .ty V1, .ty V2 => escGoals n k (Γ.body T2) V1 V2
                | _, _ => [])
          | .fld a T1, .fld a' T2 => if a = a' then escGoals n k Γ T1 T2 else []
          | .box T1, .box T2 => escGoals n k Γ T1 T2
          | _, _ => []
termination_by structural k

/-- The reason when `T` was not moved to the written `U` at `Γ`: the first
goal with a certificate. -/
def diagnose (n : Nat) {s : Sig} (Γ : Ctx s) (T U : Ty s) : Option Reason :=
  (escGoals n n Γ T U).findSome? fun g => certify? g.ctx g.lo g.hi

/-! ## The reason of a rejection

`whyF` walks a term the typer rejected, along the typer's own first
candidates, to the place where nothing was found.  It returns the first
reason it can prove there.  It types subterms with `inferF` on the tank it is
handed. -/

mutual

/-- The reason a term has no candidate, if one is found.  `n` is the fuel of
the subcapturing goals of `diagnose`. -/
def whyF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (n : Nat) :
    Nat → ATm s → Fu (Option Reason)
  | 0, _ => Fu.ret none
  | k + 1, .lam T t =>
      match writtenWhy (domArrow T) with
      | some r => Fu.ret (some r)
      | none =>
          if Ty.Wf (readDom T) then whyF (Γ.body (readDom T)) (psBody ps) n k t
          else Fu.ret none
  | k + 1, .obj S d =>
      match writtenWhy ((Shape.mu S) ^ []) with
      | some r => Fu.ret (some r)
      | none => whyDefsF (Γ.objBody d.erase (readSelf Γ ps S) []) (psObj ps) n k d
  | k + 1, .let ann t u =>
      Fu.bind (inferF Γ ps k t none) fun r1s =>
        match r1s with
        | [] => whyF Γ ps n k t
        | r1 :: _ =>
            match ann.bind writtenAnsWhy with
            | some r => Fu.ret (some r)
            | none =>
                match r1.split with
                | .inl p =>
                    Fu.bind (inferF (Γ.cons p.ty) (psVar ps) k u none) fun r2s =>
                      match r2s with
                      | [] => whyF (Γ.cons p.ty) (psVar ps) n k u
                      | r2 :: _ =>
                          match ann with
                          | none =>
                              Fu.ret (match r2.split, Γ.root? with
                                | .inr q, none => some (existentialAt (Γ.cons p.ty) q)
                                | _, _ => none)
                          | some A =>
                              match readAns Γ ps A with
                              | .ty G =>
                                  Fu.bind (inferF (Γ.cons p.ty) (psVar ps) k u
                                      (some (.ty G.weaken))) fun cs =>
                                    Fu.ret (match firstChecked cs (.ty G.weaken), r2.split with
                                      | none, .inl q => diagnose n (Γ.cons p.ty) q.ty G.weaken
                                      | _, _ => none)
                              | .ex _ _ => Fu.ret none
                | .inr q =>
                    whyF ((Γ.consC).cons q.body) (psObj ps) n k
                      (u.rename (Rename.succ (k := .cap)).lift)
  | k + 1, .letex t u =>
      Fu.bind (inferF Γ ps k t none) fun r1s =>
        match r1s with
        | [] => whyF Γ ps n k t
        | r1 :: _ =>
            match r1.split with
            | .inr q => whyF ((Γ.consC).cons q.body) (psObj ps) n k u
            | .inl _ => Fu.ret none
  | k + 1, .asc t T =>
      match writtenWhy T with
      | some r => Fu.ret (some r)
      | none =>
          Fu.bind (inferF Γ ps k t (some (.ty (readAt Γ ps T)))) fun cs =>
            match firstChecked cs (.ty (readAt Γ ps T)) with
            | some _ => Fu.ret none
            | none =>
                Fu.bind (inferF Γ ps k t none) fun rs =>
                  match rs with
                  | [] => whyF Γ ps n k t
                  | r :: _ =>
                      Fu.ret (match r.split with
                        | .inl q => diagnose n Γ q.ty (readAt Γ ps T)
                        | .inr _ => none)
  | _ + 1, _ => Fu.ret none
termination_by structural k _ => k

/-- The reason definitions have no typing, if one is found. -/
def whyDefsF {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (n : Nat) :
    Nat → ADefs s → Fu (Option Reason)
  | 0, _ => Fu.ret none
  | k + 1, .trm _ t => whyF Γ ps n k t
  | k + 1, .and d1 d2 =>
      Fu.bind (whyDefsF Γ ps n k d1) fun
        | some r => Fu.ret (some r)
        | none => whyDefsF Γ ps n k d2
  | _ + 1, _ => Fu.ret none
termination_by structural k _ => k

end

/-! ## The entry points as verdicts -/

/-- The typer at a given context, as a verdict.  A candidate is `ok`.  A
marked tank is `unknown`.  Otherwise `whyF` looks for a reason from a full
tank of its own. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) :
    Verdict (Elab Γ) :=
  match synthInF Γ ps a b.fuel with
  | (some r, _) => .ok r
  | (none, t) =>
      if t.out then .unknown
      else
        match (whyF Γ ps b.fuel (sizeATm a) a ⟨b.fuel, false⟩).1 with
        | some r => .rejected r
        | none => .unknown

/-- The typer on a closed program over a platform, at `Platform.ctx`.  A program
whose answer is an existential is rejected, since `Compiled` asks for a plain
type. -/
def synthTop? (b : Budget) (π : PlatformNames) (a : ATm π.sig) : Verdict (Elab π.plat.ctx) :=
  (synthIn? b π.plat.ctx π.set a).bind fun r =>
    match r.split with
    | .inl _ => .ok r
    | .inr q => .rejected (existentialAt π.plat.ctx q)

/-! ## The frame lemmas

Each clause is built from the combinators of `Fuel.lean` and from framed
computations of the other modules: the goals of `Sub.lean`, the lookups, box
adaptation of `Adapt.lean` and avoidance.  So each clause is framed, by
induction on the index. -/

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

theorem finishF_framed {s : Sig} (Γ : Ctx s) (G : Option (ETy s)) (rs : List (Elab Γ)) :
    Framed (finishF Γ G rs) := by
  cases G with
  | none => exact ret_framed _
  | some E => exact flatMapL_framed (fun _ => mapL_framed _ (subsumeF_framed _ _ _)) _

theorem hereBoundsF_framed {s : Sig} (Γ : Ctx (s,x)) (V : CaptureSet (s,x)) :
    Framed (hereBoundsF Γ V) := by
  refine flatMapL_framed (fun a => ?_) V
  dsimp only
  split
  · exact bind_framed (capsAt_framed _ _ _) fun _ => ret_framed _
  · exact ret_framed _

theorem lamUsesF_framed {s : Sig} (Γ : Ctx s) (T : Dom s) (V : CaptureSet (Sig.body s)) :
    Framed (lamUsesF Γ T V) := by
  refine bind_framed (hereBoundsF_framed _ _) fun bs => ?_
  dsimp only
  split
  · split
    · split
      · exact mapO_framed _ (capF_framed _ _ _)
      · exact ret_framed _
    · exact ret_framed _
  · exact ret_framed _

theorem letAtF_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (A : Ty s) (p : PElab Γ)
    (r2 : Checked (Γ.cons p.ty) (.ty A.weaken)) : Framed (letAtF Γ ann A p r2) :=
  dite_framed (fun _ => mapO_framed _ (avoidUses_framed _ _ _)) (fun _ => ret_framed _)

theorem letFinishF_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    (r2 : Elab (Γ.cons p.ty)) : Framed (letFinishF Γ ann p r2) := by
  unfold letFinishF
  split
  · exact bindO_framed (avoidLet_framed _ _ _) fun _ => letAtF_framed _ _ _ _ _
  · exact ret_framed _

theorem letPairsF_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (p : PElab Γ)
    {body : Fu (List (Elab (Γ.cons p.ty)))} (hb : Framed body) :
    Framed (letPairsF Γ ann p body) :=
  bind_framed hb fun _ => flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _ _)) _

theorem letexUsesF_framed {s : Sig} (Γ : Ctx s) (T : Ty (s,c)) (C₀ : CaptureSet s)
    (V : CaptureSet ((s,c),x)) : Framed (letexUsesF Γ T C₀ V) := by
  refine bind_framed (capUpAt_framed _ _ _) fun r => ?_
  dsimp only
  split
  · split
    · exact mapO_framed _ (capF_framed _ _ _)
    · exact ret_framed _
  · exact ret_framed _

theorem letexOfF_framed {s : Sig} (Γ : Ctx s) (q : XElab Γ) (E : ETy s)
    (r2 : Checked ((Γ.consC).cons q.body) (ETy.weaken (ETy.weaken (k := .cap) E))) :
    Framed (letexOfF Γ q E r2) :=
  mapO_framed _ (letexUsesF_framed _ _ _ _)

theorem letexFinishF_framed {s : Sig} (Γ : Ctx s) (q : XElab Γ)
    (r2 : Elab ((Γ.consC).cons q.body)) : Framed (letexFinishF Γ q r2) :=
  bindO_framed (avoidEx_framed _ _ _) fun _ => letexOfF_framed _ _ _ _

theorem letexPairsF_framed {s : Sig} (Γ : Ctx s) (q : XElab Γ)
    {body : Fu (List (Elab ((Γ.consC).cons q.body)))} (hb : Framed body) :
    Framed (letexPairsF Γ q body) :=
  bind_framed hb fun _ => flatMapL_framed (fun _ => mapL_framed _ (letexFinishF_framed _ _ _)) _

theorem letBoundF_framed {s : Sig} (Γ : Ctx s) (r1 : Elab Γ) {bp : BodyP Γ} {bx : BodyX Γ}
    (hp : ∀ p o, Framed (bp p o)) (hx : ∀ q o, Framed (bx q o)) :
    Framed (letBoundF Γ r1 bp bx) := by
  unfold letBoundF
  split
  · exact letPairsF_framed _ _ _ (hp _ _)
  · exact letexPairsF_framed _ _ (hx _ _)

theorem letOneF_framed {s : Sig} (Γ : Ctx s) (ann : Option (ETy s)) (E : ETy s) (r1 : Elab Γ)
    {bp : BodyP Γ} {bx : BodyX Γ} (hp : ∀ p o, Framed (bp p o)) (hx : ∀ q o, Framed (bx q o)) :
    Framed (letOneF Γ ann E r1 bp bx) := by
  unfold letOneF
  split
  · refine ite_framed (bind_framed (hp _ _) fun r2s => ?_) (ret_framed _)
    dsimp only
    split
    · exact letAtF_framed _ _ _ _ _
    · exact ret_framed _
  · split
    · exact bind_framed (letPairsF_framed _ _ _ (hp _ _)) fun _ =>
        firstSome_framed (fun _ => mapO_framed _ (subsumeF_framed _ _ _)) _
    · exact ret_framed _
  · refine bind_framed (hx _ _) fun r2s => ?_
    dsimp only
    split
    · exact letexOfF_framed _ _ _ _
    · exact ret_framed _

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
  | some r => exact letPairsF_framed _ _ _ (appCoreF_framed _ _ _)
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
    · exact flatMapL_framed (fun _ => letPairsF_framed _ _ _ (appStepF_framed _ _ _)) _
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
    · exact flatMapL_framed (fun _ => letPairsF_framed _ _ _
        (bind_framed (fldViewsF_framed _ _ _) fun _ => ret_framed _)) _
    · exact ret_framed _
  | cons f fs => exact ret_framed _

theorem domSubF_framed {s : Sig} (Γ : Ctx s) (T1' T1 : Dom s) : Framed (domSubF Γ T1' T1) :=
  dite_framed (fun _ => ret_framed _) (fun _ => subF_framed _ _ _)

theorem lamGenF_framed {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T)
    (rs : List (Elab (Γ.body T))) : Framed (lamGenF Γ T hwf rs) := by
  refine flatMapL_framed (fun r => ?_) rs
  dsimp only
  split
  · exact mapL_framed _ (lamUsesF_framed _ _ _)
  · exact ret_framed _

theorem lamCheckF_framed {s : Sig} (Γ : Ctx s) (T : Dom s) (hwf : Ty.Wf T) (C : CaptureSet s)
    (T1' : Dom s) (T2 : Cod s) (rs : List (Elab (Γ.body T))) :
    Framed (lamCheckF Γ T hwf C T1' T2 rs) := by
  unfold lamCheckF
  split
  · exact mapL_framed _ (bindO_framed (capF_framed _ _ _) fun _ =>
      mapO_framed _ (domSubF_framed _ _ _))
  · exact ret_framed _

theorem objDoneF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs ((s,c),x))
    (U : CaptureSet s) (r : DefsElab (Γ.objBody e S U) S.underRoot) :
    Framed (objDoneF Γ S e U r) :=
  dite_framed (fun _ => dite_framed (fun _ => mapO_framed _ (capF_framed _ _ _))
    (fun _ => ret_framed _)) (fun _ => ret_framed _)

theorem newAtomF_framed {s : Sig} (Γ : Ctx s) (U : CaptureSet s) (a : CapAtom s) :
    Framed (newAtomF Γ U a) := by
  refine ite_framed (ret_framed _) (bind_framed (capF_framed _ _ _) fun o => ?_)
  cases o with
  | some _ => exact ret_framed _
  | none => exact ret_framed _

theorem newAtomsF_framed {s : Sig} (Γ : Ctx s) (U D : CaptureSet s) :
    Framed (newAtomsF Γ U D) :=
  flatMapL_framed (newAtomF_framed Γ U) D

theorem objNextF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) (e : Defs ((s,c),x))
    (U : CaptureSet s) (r : DefsElab (Γ.objBody e S U) S.underRoot) :
    Framed (objNextF Γ S e U r) :=
  bind_framed (hereBoundsF_framed _ _) fun _ =>
    bind_framed (newAtomsF_framed _ _ _) fun _ => ret_framed _

theorem objFixF_framed {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) {chk : DefsCheck Γ S}
    (hchk : ∀ e U, Framed (chk e U)) :
    ∀ k e U, Framed (objFixF Γ S chk k e U)
  | 0, e, U => by
    rw [objFixF]
    exact zero_framed
  | k + 1, e, U => by
    rw [objFixF]
    exact bindO_framed (hchk _ _) fun r => orElse_framed (objDoneF_framed _ _ _ _ _)
      (bind_framed (objNextF_framed _ _ _ _ _) fun _ =>
        ite_framed (ret_framed _) (objFixF_framed Γ S hchk k _ _))

end Frames

mutual

theorem inferF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    (k : Nat) → (a : ATm s) → (G : Option (ETy s)) → Framed (inferF Γ ps k a G)
  | 0, a, G => by
    rw [inferF.eq_1]
    exact nil_framed _
  | k + 1, .path (.var x), G => by
    rcases G with _ | (T | ⟨C, T⟩)
    · rw [inferF]; exact ret_framed _
    · rw [inferF]; exact mapL_framed _ (adaptVarF_framed _ _ _)
    · rw [inferF]; exact finishF_framed _ _ _
  | k + 1, .lam T t, G => by
    rw [inferF]
    refine ite_framed (dite_framed (fun hwf => orElseL_framed ?_ ?_) (fun _ => ret_framed _))
      (ret_framed _)
    · split
      · exact bind_framed (inferF_framed _ _ k t _) fun _ => lamCheckF_framed _ _ _ _ _ _ _
      · exact ret_framed _
    · exact bind_framed (inferF_framed _ _ k t _) fun _ =>
        bind_framed (lamGenF_framed _ _ _ _) fun _ => finishF_framed _ _ _
  | k + 1, .obj S d, G => by
    rw [inferF]
    exact ite_framed (bind_framed (objFixF_framed _ _
      (fun _ _ => checkDefsF_framed _ _ k d _) _ _ _) fun _ => finishF_framed _ _ _) (ret_framed _)
  | k + 1, .app x y, G => by
    rw [inferF]
    exact bind_framed (appAllF_framed _ _ _) fun _ => finishF_framed _ _ _
  | k + 1, .proj x a, G => by
    rw [inferF]
    exact bind_framed (projAllF_framed _ _ _) fun _ => finishF_framed _ _ _
  | k + 1, .let ann t u, G => by
    rw [inferF]
    refine bind_framed (inferF_framed _ _ k t _) fun r1s => ?_
    have hp : ∀ (p : PElab Γ) o, Framed (inferF (Γ.cons p.ty) (psVar ps) k u o) :=
      fun _ _ => inferF_framed _ _ k u _
    have hx : ∀ (q : XElab Γ) o, Framed (inferF ((Γ.consC).cons q.body) (psObj ps) k
        (u.rename (Rename.succ (k := .cap)).lift) o) :=
      fun _ _ => inferF_framed _ _ k _ _
    cases ann with
    | none =>
      refine orElseL_framed ?_ (bind_framed (flatMapL_framed (fun _ =>
        letBoundF_framed _ _ hp hx) _) fun _ => finishF_framed _ _ _)
      cases G with
      | some E => exact mapL_framed _ (firstSome_framed (fun _ => letOneF_framed _ _ _ _ hp hx) _)
      | none => exact ret_framed _
    | some A =>
      exact ite_framed (bind_framed (mapL_framed _ (firstSome_framed
        (fun _ => letOneF_framed _ _ _ _ hp hx) _)) fun _ => finishF_framed _ _ _) (ret_framed _)
  | k + 1, .letex t u, G => by
    rw [inferF]
    refine bind_framed (inferF_framed _ _ k t _) fun r1s =>
      bind_framed (flatMapL_framed (fun r1 => ?_) _) fun _ => finishF_framed _ _ _
    dsimp only
    split
    · exact letexPairsF_framed _ _ (inferF_framed _ _ k u _)
    · exact ret_framed _
  | k + 1, .box x, G => by
    rcases G with _ | (T | ⟨C, T⟩)
    · rw [inferF]; exact finishF_framed _ _ _
    · rw [inferF]
      exact orElseL_framed (mapL_framed _ (boxCheckF_framed _ _ _)) (finishF_framed _ _ _)
    · rw [inferF]; exact finishF_framed _ _ _
  | k + 1, .unbox C x, G => by
    rw [inferF]
    refine bind_framed (boxViewsF_framed _ _) fun bs => ?_
    dsimp only
    split
    · exact finishF_framed _ _ _
    · exact ret_framed _
  | k + 1, .asc t T, G => by
    rw [inferF]
    exact ite_framed (bind_framed (inferF_framed _ _ k t _) fun _ => finishF_framed _ _ _)
      (ret_framed _)

theorem checkDefsF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) :
    (k : Nat) → (d : ADefs s) → (S : Shape s) → Framed (checkDefsF Γ ps k d S)
  | 0, d, S => by
    rw [checkDefsF.eq_1]
    exact zero_framed
  | k + 1, .typ A S0, S => by
    cases S with
    | typ B L U => rw [checkDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | k + 1, .cap A c, S => by
    cases S with
    | cap B c1 c2 => rw [checkDefsF]; exact ret_framed _
    | _ => exact ret_framed _
  | k + 1, .trm a t, S => by
    cases S with
    | fld c T =>
      rw [checkDefsF]
      exact dite_framed (fun _ => bind_framed (inferF_framed _ _ k t _) fun _ => ret_framed _)
        (fun _ => ret_framed _)
    | _ => exact ret_framed _
  | k + 1, .and d1 d2, S => by
    cases S with
    | and S1 S2 =>
      rw [checkDefsF]
      exact bindO_framed (checkDefsF_framed _ _ k d1 S1) fun _ =>
        mapO_framed _ (checkDefsF_framed _ _ k d2 S2)
    | _ => exact ret_framed _

end

/-- A typing that ends unmarked does the same with more fuel. -/
theorem synthF_frame {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s} {t t' : Tank}
    {r : List (Elab Γ)} (h : synthF Γ ps a t = (r, t')) (ho : t'.out = false) (k : Nat) :
    synthF Γ ps a (t.add k) = (r, t'.add k) :=
  (inferF_framed Γ ps _ a none).shift t r t' h ho k

theorem checkF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (E : ETy s) :
    Framed (checkF Γ ps a E) :=
  inferF_framed Γ ps _ a (some E)

theorem esubEqF_framed {s : Sig} (Γ : Ctx s) (E F : ETy s) : Framed (esubEqF Γ E F) :=
  dite_framed (fun _ => ret_framed _) (fun _ => esubF_framed _ _ _)

theorem checkInF_framed {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (U : CaptureSet s)
    (E : ETy s) : Framed (checkInF Γ ps a U E) := by
  refine bind_framed (inferF_framed Γ ps _ a none) fun rs => ?_
  cases rs with
  | cons r _ =>
    exact bindO_framed (capF_framed _ _ _) fun _ => mapO_framed _ (esubEqF_framed _ _ _)
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

theorem synthInF_stable {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s} {n k : Nat}
    {r : Option (Elab Γ)} (h : synthInF Γ ps a n = (r, ⟨k, false⟩)) (m : Nat) :
    (synthInF Γ ps a (n + m)).1 = r := by
  unfold synthInF at h ⊢
  cases hs : synthF Γ ps a ⟨n, false⟩ with
  | mk l t' =>
    have ht' : t' = ⟨k, false⟩ := by
      have := firstCand_snd (synthF Γ ps a ⟨n, false⟩)
      rw [h, hs] at this
      exact this.symm
    have hf := synthF_frame hs (by rw [ht']) m
    have hn : (⟨n + m, false⟩ : Tank) = (⟨n, false⟩ : Tank).add m := rfl
    rw [hn, hf, firstCand_add]
    rw [hs] at h
    rw [h]

theorem synthInF_mono {s : Sig} {Γ : Ctx s} {ps : CaptureSet s} {a : ATm s} {n m : Nat}
    {c : Elab Γ} (h : (synthInF Γ ps a n).1 = some c) (hnm : n ≤ m) :
    (synthInF Γ ps a m).1 = some c := by
  have ho : (synthInF Γ ps a n).2.out = false := firstCand_some h
  have he : synthInF Γ ps a n = (some c, ⟨(synthInF Γ ps a n).2.left, false⟩) := by
    rw [← h, ← ho]
  have := synthInF_stable he (m - n)
  rw [Nat.add_sub_cancel' hnm] at this
  exact this

/-- More fuel keeps the answer of a closed typing. -/
theorem synthTop?_mono {n m : Nat} {π : PlatformNames} {a : ATm π.sig}
    {c : Elab π.plat.ctx} (h : (synthTopF n π a).1 = some c) (hnm : n ≤ m) :
    (synthTopF m π a).1 = some c :=
  synthInF_mono h hnm

/-- A closed typing that ends unmarked gives the same verdict at every larger
fuel.  So a rejection of the typer's search that ends unmarked stays a
rejection at every larger fuel. -/
theorem synthTop?_stable {n k : Nat} {π : PlatformNames} {a : ATm π.sig}
    {r : Option (Elab π.plat.ctx)} (h : synthTopF n π a = (r, ⟨k, false⟩)) (m : Nat) :
    (synthTopF (n + m) π a).1 = r :=
  synthInF_stable h m

/-! ## Progress of the object fixpoint

A pass of `objFixF` that does not stop goes on with the set `objNextF` gives
and with the definitions it elaborated.  It goes on only when one of the two
changed.  When the set changed, it gained an atom that the current set does
not account for: an atom outside the set whose subcapturing goal `{a} <: U`
ended unmarked with no answer, so that no algorithmic derivation of it exists
(`capF_complete`).

These facts do not bound the number of passes.  A pass elaborates the
literal's definitions afresh under its own self binder, and box adaptation
under one binder need not keep the insertions it made under another.  So the
definitions are not known to grow.  The bound `objBound` is a size of the
program, and the pass that reaches it marks the tank (`objFixF_zero`).  So a
literal that runs out of passes is at the recursion limit, never rejected by
the rules. -/

section Progress

variable {s : Sig} {Γ : Ctx s}

/-- The last pass marks the tank. -/
theorem objFixF_zero (S : Shape (s,x)) (chk : DefsCheck Γ S) (e : Defs ((s,c),x))
    (U : CaptureSet s) (t : Tank) :
    objFixF Γ S chk 0 e U t = (none, { t with out := true }) := rfl

/-- A pass: type the definitions, stop if they are final, else go on at the
next set and the elaborated definitions unless both are unchanged. -/
theorem objFixF_succ (S : Shape (s,x)) (chk : DefsCheck Γ S) (k : Nat) (e : Defs ((s,c),x))
    (U : CaptureSet s) :
    objFixF Γ S chk (k + 1) e U =
      bindO (chk e U) fun r =>
        Fu.orElse (objDoneF Γ S e U r) fun _ =>
          Fu.bind (objNextF Γ S e U r) fun U' =>
            if U' = U ∧ r.tm.erase = e then Fu.ret none
            else objFixF Γ S chk k r.tm.erase U' := by
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
        match capF Γ [b] U t with
        | (some _, t1) => ([], t1)
        | (none, t1) => ([b], t1) := by
      unfold newAtomF
      rw [he, if_neg (by decide)]
      unfold Fu.bind
      rcases capF Γ [b] U t with ⟨_ | _, _⟩ <;> rfl
    rw [hu] at h
    rcases hs : capF Γ [b] U t with ⟨o, t1⟩
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
      · have hc := capF_complete hA t (by rw [hs]; exact ho)
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
theorem objNextF_new {S : Shape (s,x)} {e : Defs ((s,c),x)} {U : CaptureSet s}
    {r : DefsElab (Γ.objBody e S U) S.underRoot} {t : Tank} {U' : CaptureSet s} {t' : Tank}
    (h : objNextF Γ S e U r t = (U', t')) (ho : t'.out = false) :
    CaptureSet.Subset U U' ∧ (∀ a ∈ U', a ∉ U → ¬ Alg ⟨s, Γ, .cap [a] U⟩) ∧
      ((∀ a ∈ U', a ∈ U) → U' = U) := by
  have hu : objNextF Γ S e U r t =
      match hereBoundsF (Γ.objBody e S U) r.uses t with
      | (bs, t1) => match newAtomsF Γ U (((capDropHere? (selOf bs) r.uses).bind fun V =>
            capStrengthen? (k := .cap) V).getD []) t1 with
        | (N, t2) => (capJoin U N, t2) := rfl
  rw [hu] at h
  rcases hh : hereBoundsF (Γ.objBody e S U) r.uses t with ⟨bs, t1⟩
  rw [hh] at h
  dsimp only at h
  rcases hn : newAtomsF Γ U (((capDropHere? (selOf bs) r.uses).bind fun V =>
      capStrengthen? (k := .cap) V).getD []) t1 with ⟨N, t2⟩
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
theorem objFix_progress {S : Shape (s,x)} {e : Defs ((s,c),x)} {U : CaptureSet s}
    {r : DefsElab (Γ.objBody e S U) S.underRoot} {t : Tank} {U' : CaptureSet s} {t' : Tank}
    (h : objNextF Γ S e U r t = (U', t')) (ho : t'.out = false)
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

end Progress

/-! ## Checks

Each program is resolved with the labels and platforms of
`lean/Coercions/Classifiers/DotMNF/Examples.lean` and typed at the context of
its platform, or at the context of the example where the example is typed
open.  Each check runs from a full tank of `defaultFuel` units in the kernel.
It states the use set and answer, or that there is none, and the tank left.
An unmarked tank says that the fuel played no part in the verdict.  A
rejection with the tank unmarked holds at every fuel (`synthTop?_stable`).
A rejection by a level escape reads the resolution through `capsK`, so the
kernel checks those verdicts too. -/

section Checks

open Classifiers.DotMNF.Examples

/-- The use set and answer of a closed program over a platform after
resolution, from a full tank of `n` units, with the tank left. -/
def judgAt (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) :
    Option (CaptureSet π.sig × ETy π.sig) × Tank :=
  match resolveTop Λc [] π e with
  | some a => ((synthTopF n π a).1.map fun r => (r.uses, r.ans), (synthTopF n π a).2)
  | none => (none, ⟨n, true⟩)

/-- The use set and answer of a term in `Γ`, from a full tank of `n` units,
with the tank left. -/
def judgIn {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) (n : Nat := defaultFuel) :
    Option (CaptureSet s × ETy s) × Tank :=
  ((synthInF Γ ps a n).1.map fun r => (r.uses, r.ans), (synthInF Γ ps a n).2)

/-- The erasure of the elaborated program, from a full tank of `n` units. -/
def elabAt (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Option (Tm π.sig) :=
  (resolveTop Λc [] π e).bind fun a => (synthTopF n π a).1.map fun r => r.tm.erase

/-- The typer keeps the skeleton of the program. -/
def keepsSkel (π : PlatformNames) (e : STm) (n : Nat := defaultFuel) : Bool :=
  match resolveTop Λc [] π e with
  | some a =>
      match (synthTopF n π a).1 with
      | some r => decide (r.tm.skel = a.skel)
      | none => false
  | none => false

/-- The use set and the answer of a success. -/
def judgmentOf {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Option (CaptureSet s × ETy s) :=
  v.toOption.map fun r => (r.uses, r.ans)

/-- The erasure of the elaborated term of a success. -/
def erasedOf {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Option (Tm s) :=
  v.toOption.map fun r => r.tm.erase

/-- A typing moved to a given use set and answer by `checkIn?`. -/
def reachesAt {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (U : CaptureSet s) (E : ETy s) : Bool :=
  (checkIn? b Γ ps a U E).isSome

/-- A closed program moved to a given use set and answer by `checkIn?`. -/
def topReaches (b : Budget) (π : PlatformNames) (a : Option (ATm π.sig)) (U : CaptureSet π.sig)
    (E : ETy π.sig) : Bool :=
  match a with
  | some a => reachesAt b π.plat.ctx π.set a U E
  | none => false

/-- The name of the reason a closed program is rejected for. -/
def topRejected (b : Budget) (π : PlatformNames) (e : STm) : Option String :=
  (resolveTop Λc [] π e).bind fun a => (synthTop? b π a).reason?.map Reason.name

/-- The depth of the context a level escape was decided at, and whether the
root of its certificate is the universal one. -/
def escapeShape? {α : Type} (v : Verdict α) : Option (Nat × Bool) :=
  match v with
  | .rejected (.levelEscape (s := s) _ _ _ r _) => some (s.length, decide (r = .top))
  | _ => none

/-- The platform set at the example contexts with two term binders over
the platform `fs, k2`. -/
def ps2z : CaptureSet ([],c,c,x,x) := CaptureSet.weaken (CaptureSet.weaken πz.set)

/-- The same over the platform `k1, k2`. -/
def ps2c : CaptureSet ([],c,c,x,x) := CaptureSet.weaken (CaptureSet.weaken πc.set)

/-! ### The programs -/

/-- `process`, written with its parameter at `any`. -/
def W2defSrc : STm := cls% λ(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). u

/-- `freshCell` bound by a `let` whose answer is written with `fresh`. -/
def Z1defSrc : STm :=
  cls% let fc : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs} =
        λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
      in fc

/-- An existential `let` annotation: the plain `let` is typed and packed into
the annotation, with the payload's own set `{f}` as witness. -/
def cov2Src : STm :=
  cls% λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {k1}).
        let r : ∃[c ⊑ {f}] μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c} = f in r

/-- A written existential whose binder sits below a field: the payload's
own set is empty and is no witness, and the written bound `{k1}` is. -/
def cov4Src : STm := cls% λ(p : {a : ⊤ ^ {k1}}). let r : ∃[c ⊑ {k1}] {a : ⊤ ^ {c}} = p in r

/-- A closure that projects its parameter. -/
def cov3Src : STm := cls% λ(o : {a : ⊤ ^ {k1}} ^ {k1}). o.a

/-- C7 with no term-level box: the typer inserts `□ f₁`, `□ f₂` and
`{κ₁} ⊸ e`. -/
def C7src : STm :=
  cls% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- A literal that uses `f` and `h`, with `h` declared at `{y.C}` and the
member `C` of `y` bounded by `{}`.  The empty set accounts for `h`, so the
literal's set is `{f}`. -/
def accountedSrc : STm :=
  cls% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(y : {C^ : {}..{}}). λ(h : (∀(u : ⊤) ⊤) ^ {y.C}).
        ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}} ∧ {b : (∀(u : ⊤) ⊤) ^ {h}}. {a = f} ∧ {b = h})

/-- The context `κ, x : ⊤ ^ {κ}`. -/
def capVarCtx : Ctx ([],c,x) := .cons (.consC .nil) (Ty.capt [CapAtom.cvar .here] .top)

/-- The variable `x` of `capVarCtx` restricted to the kind `φ`. -/
def xAt (φ : Classifiers.Cls.Kind) : CapAtom ([],c,x) := .proj (.var .here) φ

/-- The capture set of the codomain of a function type. -/
def codSet {s : Sig} : ETy s → Option (CaptureSet (Sig.cod s))
  | .ty (.capt _ (.all _ (.ty (.capt C _)))) => some C
  | _ => none

/-- A literal whose definitions use `{g ↾ except[ThreadLocal]}`, through the
avoided `let` of `h`, and `{g}`.  Its set holds both: the first pass starts
from `{}`, and each atom is compared with the set the pass starts from. -/
def restrictedObjSrc : STm :=
  cls% λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.except[ThreadLocal]).
    ν(z : {a : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {g.except[ThreadLocal]}} ∧ {b : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {g}}.
      {a = let h = (g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {g.except[ThreadLocal]}) in h} ∧ {b = g})

/-- A literal whose definition uses `{g ↾ only[Control]}` with `g` declared at
`{}`.  The empty set accounts for that atom, so the literal's set is `{}`. -/
def accountedKindSrc : STm :=
  cls% λ(g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {}).
    ν(z : {a : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {g.only[Control]}}.
      {a = let h = (g : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {g.only[Control]}) in h})

/-- `any` deeper in a domain than its outer set: `W2_deep_rejected`. -/
def deepSrc : STm := cls% λ(x : {read : ⊤ ^ {any}}). x

/-- A call of `freshCell` as the body of a `let` outside every scope: its answer
is an existential and no root absorbs the witness. -/
def exTopSrc : STm :=
  cls% let fc = ((λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
      let un = λ(v : ⊤). v in fc un

/-- The escape at the top of a program.  The result `any` reads as the
platform set, which holds no source root, so the certificate's root is the
universal one. -/
def TopEscSrc : STm :=
  cls% let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                  (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
        = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
      in cb

/-- An ascription is binding too: the escape written as an ascription is
rejected at the callback's body. -/
def AscEscSrc : STm :=
  cls% λ(g : ⊤).
        ((λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f) :
          (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
            (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {})

/-- The same callback, annotated with its result at its own parameter, is
accepted: what it captures stays inside its own scope. -/
def EscOkSrc : STm :=
  cls% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {f}) ^ {f}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb

/-- E1 with the middle written.  A `let` annotation types the whole `let`, so
`let t : T = x in t` ascribes `T` to `x`. -/
def E1ssrc : STm :=
  cls% λ(x : {A : ⊤..⊥}).
         let y : {B : {a : ⊤} .. {a : ⊤}} = (let u : x.A = (let t : ⊤ = x in t) in u) in y

/-- E3 with the middle written, by the same ascription. -/
def E3ssrc : STm :=
  cls% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = (let u : x.A = z in u) in y

/-- A function at a member selected through a recursive shape, ascribed at
the member's upper bound. -/
def PA1src : STm :=
  cls% λ(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) y.A).
        (f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) {a : ⊤})

/-- `y : x.A`, the field `a` four steps down `x.A`'s upper bound. -/
def P4src : STm := cls% λ(x : {A : ⊥ .. μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : ⊤}))}). λ(y : x.A). y.a

/-- A function at an intersection of two function types, applied to an
argument only the second accepts. -/
def P5src : STm := cls% λ(f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : ⊤) ⊤)). λ(y : ⊤). f y

/-- A projection with two fields, the first through `x.A`'s upper bound.  Only
the second has the member `b`. -/
def R1src : STm := cls% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- A projection with two written fields.  Only the second has the member `b`. -/
def R2src : STm := cls% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let z = y.a in z.b

/-- The field reached second, at an ascription. -/
def R3src : STm := cls% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). (y.a : {b : ⊤})

/-- The same choice under a written `let` type. -/
def R4src : STm := cls% λ(y : {a : ⊤} ∧ {a : {b : ⊤}}). let z : ⊤ = y.a in z.b

/-- A field reached only through a middle the program does not write:
`n : {a : ⊤}` below `x.A`, and `x.A` below `{b : ⊤}`. -/
def B1src : STm := cls% λ(x : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}). n.b

/-- A written `let` annotation that the bound value does not meet. -/
def A1src : STm := cls% λ(x : ⊤). let y : {a : ⊤} = x in y

/-- A check through `∀` bodies that never ends, `x : p.A` against `q.B`. -/
def LPsrc : STm :=
  cls% λ(p : μ(s. {A : ⊥ .. ∀(y : ⊤) s.A})). λ(q : μ(s. {B : ∀(y : ⊤) s.B .. ⊤})). λ(x : p.A).
        (x : q.B)

/-- Pierce's divergence of F<:.  The goal comes back under a new binder that
it names, so no cut ends it, and the tank does. -/
def PFsrc : STm :=
  cls% λ(x0 : {A : ⊥ .. ∀(x : {A : ⊥ .. ⊤}) ∀(z : {A : ⊥ .. ∀(y : {A : ⊥ .. x.A})
          ∀(w : {A : ⊥ .. y.A}) w.A}) z.A}).
        λ(v : x0.A). (v : ∀(x1 : {A : ⊥ .. x0.A}) ∀(z : {A : ⊥ .. x1.A}) z.A)

/-- An avoided type with a box, at an argument whose domain is another box.
The inner `let` gives `y` the type `□((∀(u : ⊤) ⊤) ^ {f}) ^ {}`.  Both statuses
are boxed, so `y` is unboxed first, which fails, and then boxed. -/
def BX2src : STm :=
  cls% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). λ(h : (∀(v : □(⊤ ^ {})) ⊤) ^ {}).
        let y = (let g = f in □ g) in h y

/-- The same at an ascription. -/
def BXsrc : STm :=
  cls% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). let y = (let g = f in □ g) in (y : □(⊤ ^ {}))

/-- The last `j` lets `wᵢ = zᵢ.b` of `RK k`, then `wₖ`. -/
def rkWs (k : Nat) : Nat → STm
  | 0 => .var ("w" ++ toString k)
  | j + 1 =>
      .let ("w" ++ toString (k - j)) none (.proj (.var ("z" ++ toString (k - j))) "b") (rkWs k j)
termination_by structural j => j

/-- The last `j` lets `zᵢ = y.a` of `RK k`, then the lets of `rkWs`. -/
def rkZs (k : Nat) : Nat → STm
  | 0 => rkWs k k
  | j + 1 => .let ("z" ++ toString (k - j)) none (.proj (.var "y") "a") (rkZs k j)
termination_by structural j => j

/-- `y : {a : ⊤} ∧ {a : {b : ⊤}}`, then `k` lets `zᵢ = y.a`, then `k` lets
`wᵢ = zᵢ.b`.  The typer tries both fields at every `zᵢ` and learns which one
fails only at the `wᵢ`. -/
def RK (k : Nat) : STm :=
  match R2src with
  | .lam κ y T _ => .lam κ y T (rkZs k k)
  | e => e

/-- CE1's body, the types of `b` and `f` ascribed.  The call returns the
object at `{b ↾ only[Control]}`, which the `let` binding `b` avoids with the
filter kept. -/
def CE1BodySrc : STm :=
  cls% let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) ^ {}) in
    let r = f b in
    r

/-- The platform set of CE1. -/
def psE1 : CaptureSet ([],c,c) := [CapAtom.cvar E1ctl, CapAtom.cvar E1io]

/-! ### W2, Z1, the existential annotations and a projection -/

/-- `process` elaborates to `W2Tm`, its parameter's `any` read as the arrow's
own binder.  Its least answer has the inner closure at its own type, and `W2Ty`
is reached by one `sub`. -/
example : elabAt πc W2defSrc = some W2Tm := by decide +kernel
example : (judgAt πc W2defSrc).2 = ⟨defaultFuel - 2, false⟩ := by decide +kernel
example : topReaches {} πc (resolveTop Λc [] πc W2defSrc) [] (.ty W2Ty) = true := by decide +kernel

/-- The annotation of `freshCell` reads `fresh` as `Z1Ty`, the existential
bounded by `{fs, u}`, and the closure reaches it by the arrow rule, which
packs the cell. -/
example : judgAt πz Z1defSrc = (some ([], .ty (Z1Ty k1)), ⟨defaultFuel - 31, false⟩) := by
  decide +kernel

/-- An existential `let` annotation, packed at the payload's own set `{f}`. -/
example : judgAt πc cov2Src =
    (some ([], .ty ((Shape.all (fileS ^ [CapAtom.cvar (.there k1)])
      (∃ᶜ[[CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))) ^ [])),
      ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- An existential annotation packed at its written bound `{k1}`. -/
example : judgAt πc cov4Src =
    (some ([], .ty ((Shape.all ((Shape.fld la (Shape.top ^ [CapAtom.cvar (.there k1)])) ^ [])
      (∃ᶜ[[CapAtom.cvar (.there (.there k1))]]
        ((Shape.fld la (Shape.top ^ [CapAtom.cvar .here])) ^ []))) ^ [])),
      ⟨defaultFuel - 32, false⟩) := by decide +kernel

/-- A projection is charged its receiver, which leaves with the parameter, so
the closure is pure. -/
example : judgAt πc cov3Src =
    (some ([], .ty ((Shape.all ((Shape.fld la (Shape.top ^ [CapAtom.cvar (.there k1)])) ^
        [CapAtom.cvar (.there k1)])
      (.ty (Shape.top ^ [CapAtom.cvar (.there (.there k1))]))) ^ [])),
      ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-! ### C7: boxes, an unboxing and an object under its class root -/

/-- C7 elaborates to `C7tm`, with the judgment `C7Ty`, and keeps the skeleton
of the program.  The first pass of the object rule inserts the boxes, and the
second runs under a binder that holds them. -/
example : elabAt πc C7src = some C7tm := by decide +kernel
example : judgAt πc C7src = (some ([], .ty C7Ty), ⟨defaultFuel - 80, false⟩) := by decide +kernel
example : keepsSkel πc C7src = true := by decide +kernel

/-! ### The atoms the object fixpoint adds

An atom the current set accounts for is not added.  `{x}` is below `{κ}`
when `x` is declared at `{κ}`, and nothing but `{}` is below `{}`.  The
literal of `accountedSrc` uses `{f, h}`, and its set is `{f}`. -/

example : newAtomsF capVarCtx [CapAtom.cvar (.there .here)]
    [CapAtom.var .here, CapAtom.cvar (.there .here)] ⟨defaultFuel, false⟩ =
    ([], ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : newAtomsF capVarCtx [] [CapAtom.var .here] ⟨defaultFuel, false⟩ =
    ([CapAtom.var .here], ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : judgAt πc accountedSrc =
    (some ([], .ty ((Shape.all (capTy (.there k1))
      (.ty ((Shape.all ((Shape.cap lC [] []) ^ [])
        (.ty ((Shape.all (arrowS ^ [CapAtom.sel (.there .here) lC])
          (.ty ((Shape.mu (.and
              (.fld la (arrowS ^ [CapAtom.var (.there (.there (.there (.there (.there .here)))))]))
              (.fld lb (arrowS ^ [CapAtom.var (.there .here)])))) ^
            [CapAtom.var (.there (.there (.there (.there .here))))]))) ^ []))) ^ []))) ^ [])),
      ⟨defaultFuel - 36, false⟩) := by decide +kernel

/-! ### Restricted atoms in the object fixpoint

Two restrictions of one base compare by subkinding.  `{x ↾ only[Control]}` is
below `{x ↾ only[ThreadLocal]}`, since `Control` extends `ThreadLocal`, and
not the other way.  `{x}` accounts for every restriction of `x`, and a
restriction of `x` does not account for `x`.  Restricting twice at
`except[ThreadLocal]` appends the exclusion lists, so the atom is new as
syntax, and the set at the single restriction accounts for it. -/

example : newAtomsF capVarCtx [xAt (Classifiers.Cls.only Classifiers.Cls.ThreadLocal)]
    [xAt (Classifiers.Cls.only Classifiers.Cls.Control)] ⟨defaultFuel, false⟩ =
    ([], ⟨defaultFuel - 29, false⟩) := by decide +kernel
example : newAtomsF capVarCtx [xAt (Classifiers.Cls.only Classifiers.Cls.Control)]
    [xAt (Classifiers.Cls.only Classifiers.Cls.ThreadLocal)] ⟨defaultFuel, false⟩ =
    ([xAt (Classifiers.Cls.only Classifiers.Cls.ThreadLocal)], ⟨defaultFuel - 59, false⟩) := by
  decide +kernel
example : newAtomsF capVarCtx [CapAtom.var .here]
    [xAt (Classifiers.Cls.only Classifiers.Cls.Control)] ⟨defaultFuel, false⟩ =
    ([], ⟨defaultFuel - 3, false⟩) := by decide +kernel
example : newAtomsF capVarCtx [xAt (Classifiers.Cls.only Classifiers.Cls.Control)]
    [CapAtom.var .here] ⟨defaultFuel, false⟩ =
    ([CapAtom.var .here], ⟨defaultFuel - 15, false⟩) := by decide +kernel
example : (xAt (Classifiers.Cls.except Classifiers.Cls.ThreadLocal)).projBy
    (Classifiers.Cls.except Classifiers.Cls.ThreadLocal) ≠
    xAt (Classifiers.Cls.except Classifiers.Cls.ThreadLocal) := by decide +kernel
example : newAtomsF capVarCtx [xAt (Classifiers.Cls.except Classifiers.Cls.ThreadLocal)]
    [(xAt (Classifiers.Cls.except Classifiers.Cls.ThreadLocal)).projBy
      (Classifiers.Cls.except Classifiers.Cls.ThreadLocal)] ⟨defaultFuel, false⟩ =
    ([], ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-- `restrictedObjSrc` and `accountedKindSrc` at CE1's platform: the use set,
the codomain's set, which is the literal's, and the tank left. -/
example : (resolveIn Λk exCls E1Names restrictedObjSrc).map (fun a =>
      let r := judgIn E1PlatCtx psE1 a
      (r.1.map fun p => (p.1, codSet p.2), r.2)) =
    some (some ([], some [CapAtom.var .here,
      .proj (.var .here) (Classifiers.Cls.except Classifiers.Cls.ThreadLocal)]),
      ⟨defaultFuel - 153, false⟩) := by decide +kernel
example : (resolveIn Λk exCls E1Names accountedKindSrc).map (fun a =>
      let r := judgIn E1PlatCtx psE1 a
      (r.1.map fun p => (p.1, codSet p.2), r.2)) =
    some (some ([], some []), ⟨defaultFuel - 37, false⟩) := by decide +kernel

/-! ### The open programs

At the version's contexts.  `Z1callerAnn` becomes an unpacking, and the
version's `Z1Use ∪ Z1Use` is reached from the least set by one `sub`. -/

/-- The call `p f` at `W2CallCtx`, at the use set `{f}` and the answer `⊤`. -/
example : judgIn W2CallCtx ps2c (.app (.there .here) .here) =
    (some ([CapAtom.var .here], .ty unitTy), ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- The caller of `freshCell`: the call charged `{fc}`, the unpacking its
bound `{fs, un}`, and the closure it hands back at its own type. -/
example : judgIn Z1Ctx ps2z Z1callerAnn =
    (some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here], .ty (arrowS ^ [])),
      ⟨defaultFuel - 8, false⟩) := by decide +kernel
example : (synthInF Z1Ctx ps2z Z1callerAnn defaultFuel).1.map (·.tm.erase) =
    some (.letex (.app (.there .here) .here) (.let (.path (.var .here)) unitTm)) := by
  decide +kernel
example : reachesAt {} Z1Ctx ps2z Z1callerAnn (Z1Use ∪ Z1Use) (.ty unitTy) = true := by
  decide +kernel

/-- An unpacking whose answer is the second call's existential, moved past the
witness and the payload of the first. -/
example : judgIn Z1Ctx ps2z Z1TailAnn =
    (some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here],
      ∃ᶜ[Z1Use] (fileS ^ [CapAtom.cvar .here])), ⟨defaultFuel - 5, false⟩) := by decide +kernel

/-- `λ(h : (∀(u : ⊤) ⊤) ^ {any}). let z = unit in h z`: a pure closure whose
domain reads `any` as the arrow's own binder. -/
example : judgIn (platCtx.cons unitTy) (CaptureSet.weaken πc.set) P1ann =
    (some ([], .ty ((Shape.all (arrowS ^ [CapAtom.cvar .here]) (.ty unitTy)) ^ [])),
      ⟨defaultFuel - 4, false⟩) := by decide +kernel

/-- Inside a scope the payload's type leaves an unpacking by the level rule:
`let x = fc un in x` under a lambda is a file captured by that body's root,
the compiler's local root absorbing a `fresh`. -/
example : (resolveIn Λc [] (((z1Names.consC "%").consC "%").cons "v") (cls% let x = fc un in x)).map
    (fun a => judgIn (Z1Ctx.body unitTy) (psBody ps2z) a) =
    some (some ([CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.cvar (up fs2),
        CapAtom.var (.there (.there (.there .here)))],
      .ty (fileS ^ [CapAtom.cvar (.there (.there .here))])), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-! ### Rejections by a written type and by an existential answer -/

/-- `any` deeper in a domain than its outer set, `W2_deep_rejected`, with the
tank unmarked. -/
example : judgAt πc deepSrc = (none, ⟨defaultFuel, false⟩) := by decide +kernel
example : topRejected {} πc deepSrc = some "anyNotOk" := by decide +kernel

/-- `fresh` in a domain. -/
example : (synthIn? {} platCtx πc.set
    (.lam (.capt [CapAtom.fresh] .top) (.path (.var .here)))).reason?.map Reason.name =
    some "freshNotOk" := by decide +kernel

/-- The call of `freshCell` outside every scope: its answer is an existential
and no root absorbs the witness. -/
example : judgAt πz exTopSrc = (none, ⟨defaultFuel - 19, false⟩) := by decide +kernel
example : topRejected {} πz exTopSrc = some "existentialAtTop" := by decide +kernel

/-! ### Rejections by a level escape

The kernel checks each verdict, the depth of the context reached and the kind
of root.  The rejections themselves leave the tank unmarked. -/

example : judgAt πc EscSrc = (none, ⟨defaultFuel - 31, false⟩) := by decide +kernel
example : judgAt πc TopEscSrc = (none, ⟨defaultFuel - 31, false⟩) := by decide +kernel
example : judgAt πc AscEscSrc = (none, ⟨defaultFuel - 88, false⟩) := by decide +kernel

/- The escape: the callback's result `any` is the root of `λ(g : ⊤)`'s body,
and the callback returns its parameter.  The goal reached is `{f} <: {κ_g}` in
the callback's body, in the context that also binds `cb`, nine binders deep.
The certificate's root is `κ_g`. -/
example : (resolveTop Λc [] πc EscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) =
    some (9, false) := by
  decide +kernel

/- At the top the result `any` reads as the platform set, so the
certificate's root is the universal one. -/
example : (resolveTop Λc [] πc TopEscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) =
    some (6, true) := by
  decide +kernel

/- The escape written as an ascription is rejected at the callback's body. -/
example : (resolveTop Λc [] πc AscEscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) =
    some (8, false) := by
  decide +kernel

/-- The same callback at its own parameter is accepted. -/
example : (judgAt πc EscOkSrc).1.map (·.1) = some [] := by decide +kernel
example : (judgAt πc EscOkSrc).2 = ⟨defaultFuel - 4, false⟩ := by decide +kernel

/-! ### Middles written, every member a candidate, and annotations that bind -/

/-- E1 and E3 with their middle written. -/
example : judgAt .empty E1ssrc =
    (some ([], .ty ((Shape.all E1Dom (.ty E1Res)) ^ [])), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel
example : judgAt .empty E3ssrc =
    (some ([], .ty ((Shape.all E3Dom (.ty ((Shape.all E3T2 (.ty E3T1)) ^ []))) ^ [])),
      ⟨defaultFuel - 18, false⟩) := by decide +kernel

/-- PA1, P4, P5: a member through a recursive shape, a field four steps down,
the second of two function types. -/
example : (judgAt πc PA1src).1.map (·.1) = some [] := by decide +kernel
example : (judgAt πc PA1src).2 = ⟨defaultFuel - 45, false⟩ := by decide +kernel
example : (judgAt πc P4src).1.map (·.1) = some [] := by decide +kernel
example : (judgAt πc P4src).2 = ⟨defaultFuel - 28, false⟩ := by decide +kernel
example : judgAt πc P5src =
    (some ([], .ty ((Shape.all ((Shape.and (.all ((Shape.fld la unitTy) ^ []) (.ty unitTy))
      (.all unitTy (.ty unitTy))) ^ []) (.ty ((Shape.all unitTy (.ty unitTy)) ^ []))) ^ [])),
      ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- R1 to R4: the field that lets the rest of the program type. -/
example : (judgAt πc R1src).1.map (·.1) = some [] := by decide +kernel
example : (judgAt πc R1src).2 = ⟨defaultFuel - 17, false⟩ := by decide +kernel
example : judgAt πc R2src =
    (some ([], .ty ((Shape.all ((Shape.and (.fld la unitTy) (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      (.ty unitTy)) ^ [])), ⟨defaultFuel - 10, false⟩) := by decide +kernel
example : judgAt πc R3src =
    (some ([], .ty ((Shape.all ((Shape.and (.fld la unitTy) (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      (.ty ((Shape.fld lb unitTy) ^ []))) ^ [])), ⟨defaultFuel - 11, false⟩) := by decide +kernel
example : judgAt πc R4src =
    (some ([], .ty ((Shape.all ((Shape.and (.fld la unitTy) (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      (.ty unitTy)) ^ [])), ⟨defaultFuel - 9, false⟩) := by decide +kernel

/-- B1 needs a middle the program does not write, and A1's annotation binds.
Both are rejected with the tank unmarked. -/
example : judgAt πc B1src = (none, ⟨defaultFuel - 2, false⟩) := by decide +kernel
example : judgAt πc A1src = (none, ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-! ### Box adaptation by the box status -/

/-- BX2 and BX: `y` has the avoided type `□((∀(u : ⊤) ⊤) ^ {f}) ^ {}`, and
the goal is a box too.  Unboxing `y` fails and boxing it succeeds. -/
example : (judgAt πc BX2src).1.map (·.1) = some [] := by decide +kernel
example : (judgAt πc BX2src).2 = ⟨defaultFuel - 34, false⟩ := by decide +kernel
example : judgAt πc BXsrc =
    (some ([], .ty ((Shape.all (capTy (.there k1)) (.ty ((Shape.box (Shape.top ^ [])) ^ []))) ^ [])),
      ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-! ### Every field at every `let`, and the recursion limit

RK at ten lets tries both fields at each and pays for it in the tank.  LP and
PF end with the tank marked. -/

example : (judgAt πc (RK 10)).1.isSome = true := by decide +kernel
example : (judgAt πc (RK 10)).2 = ⟨defaultFuel - 8205, false⟩ := by decide +kernel
example : (judgAt πc LPsrc).1 = none := by decide +kernel
example : (judgAt πc LPsrc).2.out = true := by decide +kernel
example : (judgAt πc PFsrc).1 = none := by decide +kernel
example : (judgAt πc PFsrc).2.out = true := by decide +kernel


/-! ### Avoiding a restricted binder

CE1 binds `b` at the filtered platform set and calls `Try.apply` on it.  The
call returns the object at `{b ↾ only[Control]}`, which the `let` binding `b`
avoids.  Avoidance replaces the restricted atom by the set `b` is declared
at, restricted to the same kind, so the filter is kept and the use set is the
filtered platform set. -/

/-- CE1's body erases to the version's `E1tm`, at the judgment `E1_typed`:
the filtered platform set and the object at it. -/
example : (resolveIn Λk exCls E1Names CE1BodySrc).map (fun a => judgIn E1PlatCtx psE1 a) =
    some (some (E1Filt, .ty E1Ty), ⟨defaultFuel - 45, false⟩) := by decide +kernel
example : (resolveIn Λk exCls E1Names CE1BodySrc).bind
    (fun a => (synthInF E1PlatCtx psE1 a defaultFuel).1.map (·.tm.erase)) = some E1tm := by
  decide +kernel

/-- Inside the scope of `b` the call's answer is `{b ↾ only[Control]}`, the
version's `E1AppTy`, at the use set `{b}`. -/
example : judgIn E1Ctx2 (CaptureSet.weaken (CaptureSet.weaken psE1)) (.app .here (.there .here)) =
    (some ([CapAtom.var (.there .here)], .ty E1AppTy), ⟨defaultFuel - 27, false⟩) := by
  decide +kernel

end Checks

end ClassifiersFrontend
