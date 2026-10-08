import Coercions.CapturesCC.Frontend.Adapt
import Coercions.CapturesCC.Frontend.Resolve
import Coercions.CapturesCC.DotToFCdot.Prediction

/-!
# The derivation producing typer

The typer reads a use set and an answer off an annotated term and returns the
derivation of `HasTy` (`lean/Coercions/CapturesCC/DotMNF/Typing.lean`) about
the erasure of the term it typed.  Every success carries its derivation, so
soundness is the result type.  The typer is fuel bounded and incomplete,
since subcapturing goes through subtyping and DOT subtyping is undecidable.

## Verdicts

A run ends in `ok` with the elaborated term and its derivation, `rejected` with
a `Reason` that carries a proof of what it claims, or `unknown` when the search
found nothing within its budget.  There are four reasons.

- `anyNotOk` and `freshNotOk`: a written type puts `any` or `fresh` where the
  `CapturesCC` gives it no reading (`Ty.anyOk`, `Ty.freshOk`).
- `levelEscape`: no member-free subcapturing puts `C` below `D` at the context
  the typer reached.  The proof is `escape_rejected_at` of `Search.lean`, the
  contrapositive of `source_lvl_safety`.  It speaks of the goal the typer
  reached, not of every derivation of the program.
- `existentialAtTop`: the answer outside every scope is an existential where
  the program or a `let` asks for a plain type.

## Use sets and written types

The typer computes the least use set the rules allow.  A variable declared at
the empty set is used at the empty set, any other variable at `{x}`.  A call is
charged `{x, y}` and a projection `{x}`.  A `let` charges its binder to the set
the binder is declared at, by `sc-var`.

A written type is read where it is written, after deciding that it is in the
notation of `CapturesCC`.  A lambda domain reads `any` as the arrow's own capture
binder (`Value.expand`).  A `let` annotation, an ascription and an object's
self shape read `any` at `Ctx.reading`: the innermost scope root, or the
program's platform set if there is none.  A `fresh` in the result of an arrow
becomes an existential (`Ty.expandFresh`).

## Scopes

The typer opens scopes only through `Ctx.body` and `Ctx.objBody`, so binder
levels are those of `CapturesCC`.  A lambda body sits under its body root, its arrow
binder and its parameter.  An object's definitions sit under its class root
and its self.

## The avoidance ladder

`HasTy.let` asks for a plain result type `T'` with the body typed at `T'↑`.  A
written annotation on a `let` or an ascription is binding: only it is tried,
and when it fails the typer looks for a rejection at the goal it reached.  An
existential annotation is reached from the plain `let` by answer inclusion,
which packs it.  Without an annotation three rungs are tried.

1. The body's type, with the shape strengthened past the binder and the set
   with the binder replaced by the binder's declared set.
2. `⊤` at that set.
3. If the bound term's answer is an existential, the `let` becomes an
   unpacking `letex`.  The body is renamed past the new witness binder and
   typed under the witness and the payload.  Its answer leaves their scope by
   strengthening, or by the level rule into the innermost root, which is the
   compiler's local `any` absorbing a `fresh`.

The first rung that succeeds wins.  Otherwise the first rejection is the
verdict, and if there is none the verdict is `unknown`.

## Checking

`check?` adds clauses to synthesis followed by answer inclusion.  A `λ` against
a function type checks its body against the codomain.  A `let` with no
annotation checks its body against the goal.  A box value against a box goal
checks the variable against the boxed type.  A variable checked against a goal
goes through box inference (`adaptVar?` of `Adapt.lean`).

## Fuel

`synth?`, `check?` and `checkDefs?` are one block, structural on the fuel, and
every call inside is at one unit less.  `synth?` ends each fuel level with a
retry at the previous level, which changes no answer and makes `synth?_le` an
induction on the fuel.  The search runs at its own counters, `Budget.cap` for
sets and `Budget.sub` for shapes.  Typing reduces in the kernel, except that a
`levelEscape` rejection reads the well-founded `Ctx.caps`, so it is computed by
compiled code.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label PartialRename witness?)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Tm Value Defs Ctx Sub
  SubShape Subcap ESub HasTy DefsTy Platform Subst)
open scoped CapturesCC.DotMNF

/-! ## Reasons and verdicts -/

/-- Why a program is rejected, with the proof. -/
inductive Reason : Type where
  /-- A written type puts `any` where `CapturesCC` reads none. -/
  | anyNotOk {s : Sig} (T : Ty s) (h : T.anyOk = false)
  /-- A written type puts `fresh` where `CapturesCC` reads none. -/
  | freshNotOk {s : Sig} (T : Ty s) (h : T.freshOk = false)
  /-- No member-free subcapturing puts `C` below `D` at `Γ`.  The atom `r`
  is the root the certificate confines `D` to. -/
  | levelEscape {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) (r : CapturesCC.FCdot.CapAtom s)
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
  /-- Not found within the budget. -/
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

/-- The ladder rule.  A success wins.  Otherwise the second alternative is
tried, and a failure keeps the first rejection, if any. -/
def orElse (v : Verdict α) (w : Unit → Verdict α) : Verdict α :=
  match v with
  | .ok a => .ok a
  | .rejected r =>
      match w () with
      | .ok b => .ok b
      | _ => .rejected r
  | .unknown => w ()

/-- A second look when nothing was decided: only `unknown` runs `w`. -/
def whenUnknown (v : Verdict α) (w : Unit → Verdict α) : Verdict α :=
  match v with
  | .unknown => w ()
  | v => v

/-- A search result read as a verdict: nothing found is `unknown`. -/
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

/-- A success of the second alternative is kept by the ladder rule. -/
theorem isOk_orElse_right {v : Verdict α} {w : Unit → Verdict α} (h : (w ()).isOk = true) :
    (v.orElse w).isOk = true := by
  cases v with
  | ok a => rfl
  | rejected r =>
      simp only [orElse]
      cases hw : w () with
      | ok b => rfl
      | rejected r' => rw [hw] at h; simp [isOk] at h
      | unknown => rw [hw] at h; simp [isOk] at h
  | unknown => simpa [orElse] using h

end Verdict

/-- The name of a reason, for messages. -/
def Reason.name : Reason → String
  | .anyNotOk _ _ => "anyNotOk"
  | .freshNotOk _ _ => "freshNotOk"
  | .levelEscape _ _ _ _ _ => "levelEscape"
  | .existentialAtTop _ _ _ => "existentialAtTop"

/-! ## Typings at a plain and at an existential answer -/

/-- A typing at a plain answer. -/
structure PElab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase (.ty ty)

/-- A typing at an existential answer `∃ᶜ[bnd] body`. -/
structure XElab {s : Sig} (Γ : Ctx s) where
  /-- The elaborated term. -/
  tm : ATm s
  /-- The use set. -/
  uses : CaptureSet s
  /-- The bound of the witness. -/
  bnd : CaptureSet s
  /-- The type under the witness binder. -/
  body : Ty (s,c)
  /-- The derivation. -/
  deriv : HasTy uses Γ tm.erase (∃ᶜ[bnd] body)

/-- A synthesized typing split by the form of its answer. -/
def Elab.split {s : Sig} {Γ : Ctx s} (r : Elab Γ) : PElab Γ ⊕ XElab Γ :=
  match r with
  | ⟨tm, uses, .ty T, d⟩ => .inl ⟨tm, uses, T, d⟩
  | ⟨tm, uses, .ex C T, d⟩ => .inr ⟨tm, uses, C, T, d⟩

/-- A typing at a plain answer read as a synthesized one. -/
def PElab.toElab {s : Sig} {Γ : Ctx s} (r : PElab Γ) : Elab Γ := ⟨r.tm, r.uses, .ty r.ty, r.deriv⟩

/-! ## Written types

A written type is decided to be in the notation of `CapturesCC` and then read at
the position it is written at.  A lambda domain and a `let` annotation are
decided as part of an arrow, since the conditions on them are the arrow
clauses of `Shape.anyOk` and `Shape.freshOk`. -/

/-- The arrow with parameter `T` and a pure `⊤` result.  Its `anyOk` is
`T.domAnyOk` and its `freshOk` is `T.noFresh`. -/
def domArrow {s : Sig} (T : Ty (Sig.dom s)) : Ty s := (Shape.all T (.ty (.top ^ []))) ^ []

/-- The arrow with a pure `⊤` parameter and the answer `E` as its result. -/
def ansArrow {s : Sig} (E : ETy s) : Ty s :=
  (Shape.all (.top ^ []) (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E))) ^ []

/-- A written type is in the notation of `CapturesCC`: every `any` and `fresh`
sits where `CapturesCC` reads it. -/
def written {s : Sig} (T : Ty s) : Verdict Unit :=
  if h : T.anyOk = false then .rejected (.anyNotOk T h)
  else if h' : T.freshOk = false then .rejected (.freshNotOk T h')
  else .ok ()

/-- A written answer is in the notation of `CapturesCC`.  An existential is decided
as the result of an arrow. -/
def writtenAns {s : Sig} (E : ETy s) : Verdict Unit :=
  match E with
  | .ty T => written T
  | .ex _ _ => written (ansArrow E)

/-- A written lambda domain read at the arrow's own capture binder
(`Value.expand`). -/
def readDom {s : Sig} (T : Ty (Sig.dom s)) : Dom s := T.expand [CapAtom.cvar .here]

/-- A written answer read at a context, with `ps` the platform set. -/
def readAns {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (E : ETy s) : ETy s :=
  match E with
  | .ty T => .ty (readAt Γ ps T)
  | .ex C T => ETy.expand (.ex C T) (Γ.reading ps)

/-- A written self shape read at a context, as `CapturesCC` reads `(μ S) ^ {}`
there. -/
def readSelf {s : Sig} (Γ : Ctx s) (ps : CaptureSet s) (S : Shape (s,x)) : Shape (s,x) :=
  S.expand (CaptureSet.weaken (Γ.reading ps))

/-- The platform set under a lambda body's root, arrow binder and parameter. -/
abbrev psBody {s : Sig} (ps : CaptureSet s) : CaptureSet (Sig.body s) :=
  CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) (CaptureSet.weaken (k := .cap) ps))

/-- The platform set under an object's class root and self. -/
abbrev psObj {s : Sig} (ps : CaptureSet s) : CaptureSet ((s,c),x) :=
  CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) ps)

/-- The platform set under one term binder. -/
abbrev psVar {s : Sig} (ps : CaptureSet s) : CaptureSet (s,x) := CaptureSet.weaken (k := .var) ps

/-! ## Moving a derivation across a decided equality

The label of a member occurs twice in the conclusion of its rule, so these use
`cases` rather than a rewrite. -/

/-- A field view read at the label the projection asks for. -/
def hasFldAt {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var} {a c : Label}
    {T : Ty s} {C : CaptureSet s} (h : c = a)
    (d : HasTy U Γ (.path (.var x)) (.ty ((Shape.fld c T) ^ C))) :
    HasTy U Γ (.path (.var x)) (.ty ((Shape.fld a T) ^ C)) := by
  cases h; exact d

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

/-- A shape below itself, across a decided equality. -/
def subShapeOfEq {s : Sig} {Γ : Ctx s} {S T : Shape s} (h : S = T) : SubShape Γ S T := by
  cases h; exact .refl

/-- `{}-I` for definitions that are the literal's own up to a decided equality:
the self binder holds the definitions the program wrote, which the typer typed
under it. -/
def objOf {s : Sig} {Γ : Ctx s} {d e : Defs ((s,c),x)} {S : Shape (s,x)} {U : CaptureSet s}
    (h : e = d)
    (dt : DefsTy (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here]) (Γ.objBody d S U) e
      S.underRoot)
    (hd : Defs.Distinct d) : HasTy [] Γ (.val (.obj e)) (.ty ((Shape.mu S) ^ U)) := by
  cases h; exact .obj dt hd

/-- The codomain of a lambda: the body's answer with the body root removed
(`Cod.underRoot`). -/
def codOf? {s : Sig} (E : ETy (Sig.body s)) : Option { T : Cod s // E = Cod.underRoot T } :=
  match witness? (eTyRename? E PartialRename.unshift.lift.lift) with
  | some ⟨T, h⟩ =>
      some ⟨T, eTyRename?_sound E T _ _
        (PartialRename.Inverts.lift (PartialRename.Inverts.lift PartialRename.unshift_inverts)) h⟩
  | none => none

/-! ## Reading a view

The typer consults the views of the search in four ways.  None recurses. -/

/-- A function type a variable has, with the derivation. -/
structure AllView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The domain, under the arrow's capture binder. -/
  dom : Dom s
  /-- The codomain, under the arrow's capture binder and the parameter. -/
  cod : Cod s
  /-- The capture set of the function. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.all dom cod) ^ cs))

/-- A field a variable has at a given label, with the derivation. -/
structure FldView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type of the field. -/
  ty : Ty s
  /-- The capture set of the object. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ((Shape.fld a ty) ^ cs))

/-- The first view that is a function type.  Only the first is tried. -/
def allView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (vs : List (View Γ x)) :
    Option (AllView Γ x) :=
  firstSome (fun v =>
    match hv : v.ty with
    | .capt C (.all T1 T2) => some ⟨v.uses, T1, T2, C, hv ▸ v.deriv⟩
    | _ => none) vs

/-- The first view that is a field declaration at the label asked for. -/
def fldView {s : Sig} {Γ : Ctx s} {x : BVar s .var} (a : Label) (vs : List (View Γ x)) :
    Option (FldView Γ x a) :=
  firstSome (fun v =>
    match hv : v.ty with
    | .capt C (.fld c T) =>
        if h : c = a then some ⟨v.uses, T, C, hasFldAt h (hv ▸ v.deriv)⟩ else none
    | _ => none) vs

/-- The first view at exactly the type asked for. -/
def viewAt {s : Sig} {Γ : Ctx s} {x : BVar s .var} (T : Ty s) (vs : List (View Γ x)) :
    Option (VarChecked Γ x T) :=
  firstSome (fun v => if h : v.ty = T then some ⟨v.uses, h ▸ v.deriv⟩ else none) vs

/-- The first view the subtyping search takes to the type asked for. -/
def viewSub {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (c n : Nat) (T : Ty s)
    (vs : List (View Γ x)) : Option (VarChecked Γ x T) :=
  firstSome (fun v => (sub? D c n v.ty T).map fun e =>
    ⟨v.uses, HasTy.sub v.deriv (.ty e) .refl⟩) vs

/-! ## Checking a variable -/

/-- Checking a variable.  Three rules, in order.

1. A goal `(S₁ ∧ S₂) ^ C` splits by `HasTy.andI` at the join of the two use
   sets.
2. A goal `(μ S) ^ C` whose body is declaration shaped folds by `HasTy.recI`.
   `SubShape` has no rule for `μ`, so such a goal is otherwise unreachable from
   an opened view.
3. Otherwise a view at exactly the goal, and then a view the subtyping search
   takes there. -/
def checkVar? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat)
    (x : BVar s .var) (T : Ty s) : Option (VarChecked Γ x T) :=
  match n with
  | 0 => none
  | n + 1 =>
      ((match T with
        | .capt C (.and S1 S2) =>
            (checkVar? D b n x (S1 ^ C)).bind fun r1 =>
              (checkVar? D b n x (S2 ^ C)).map fun r2 =>
                ⟨capJoin r1.uses r2.uses,
                  HasTy.andI (widenLeft r1.deriv r2.uses) (widenRight r1.uses r2.deriv)⟩
        | _ => none) : Option (VarChecked Γ x T)).orElse fun _ =>
      ((match T with
        | .capt C (.mu S) =>
            if hd : Shape.Decl S then
              (checkVar? D b n x ((S.substVar x) ^ C)).map fun r => ⟨r.uses, HasTy.recI r.deriv hd⟩
            else none
        | _ => none) : Option (VarChecked Γ x T)).orElse fun _ =>
      (viewAt T (views D b x)).orElse fun _ => viewSub D b.cap b.sub T (views D b x)
termination_by structural n

/-! ## Candidates with their evidence -/

/-- The upper bound of the capture member `C` of the innermost binder, as the
table under that binder records it.  An atom `{x.C}` is replaced by it when `x`
goes out of scope. -/
def hereSel {s : Sig} {Γ : Ctx (s,x)} (D : DeclTable Γ) : Label → Option (CaptureSet (s,x)) :=
  fun ℓ => firstSome (fun d => if d.vr = .here ∧ d.lbl = ℓ then some d.hi else none) D.caps

/-- The set of a function: the body's set `V` without the parameter,
strengthened past the arrow binder and the body root, with the evidence
`V <: U↑↑↑ ∪ {x}` that `All-I` asks for.  A body that uses its arrow binder or
its body root has no such set. -/
def lamUses? {s : Sig} {Γ : Ctx s} {T : Dom s} (D : DeclTable (Γ.body T)) (c : Nat)
    (V : CaptureSet (Sig.body s)) :
    Option ((U : CaptureSet s) ×
      Subcap (Γ.body T) V
        (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here])) := do
  let U2 ← capDropHere? (hereSel D) V
  let U1 ← capStrengthen? (k := .cap) U2
  let U ← capStrengthen? (k := .cap) U1
  let e ← subcap? D c V (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken U)) ∪ [.var .here])
  some ⟨U, e⟩

/-- `All-I` from a synthesized body. -/
def lamOf? {s : Sig} {Γ : Ctx s} {T : Dom s} (D : DeclTable (Γ.body T)) (c : Nat)
    (hwf : Ty.Wf T) (r : Elab (Γ.body T)) : Option (Elab Γ) :=
  match codOf? r.ans with
  | some ⟨T2, h⟩ =>
      match lamUses? D c r.uses with
      | some ⟨U, e⟩ =>
          some ⟨.lam T r.tm, [], .ty ((Shape.all T T2) ^ U), HasTy.lam (h ▸ widenUses r.deriv e) hwf⟩
      | none => none
  | none => none

/-- The set a `let` adds to its bound term's `U₁`: the body's set `V` with `{x}`
replaced by the capture set of `x`'s type, with evidence that `V` is below the
join of the two. -/
def letUses? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (c : Nat)
    (U1 : CaptureSet s) (V : CaptureSet (s,x)) :
    Option ((U2 : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken (capJoin U1 U2))) := do
  let U2 ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) V
  let e ← subcap? D c V (CaptureSet.weaken (capJoin U1 U2))
  some ⟨U2, e⟩

/-- The first rung of the ladder: the body's shape strengthened and its set
avoided. -/
def avoidStrengthen? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (c : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW SW => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let w ← shapeStrengthenW? SW
      let e ← subcap? D c CW (CaptureSet.weaken C')
      some ⟨w.val ^ C', Sub.capt (subShapeOfEq w.property) e⟩

/-- The second rung of the ladder: `⊤` at the avoided set. -/
def avoidTop? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (c : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW _ => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let e ← subcap? D c CW (CaptureSet.weaken C')
      some ⟨.top ^ C', Sub.capt SubShape.top e⟩

/-! ## Assembling a `let` -/

/-- `HasTy.let` at the result type `T'`, with the use set joined and both
premises widened to it. -/
def letOf? {s : Sig} {Γ : Ctx s} (r1 : PElab Γ) (D : DeclTable (Γ.cons r1.ty)) (c : Nat)
    (ann : Option (ETy s)) (T' : Ty s) (r2 : Checked (Γ.cons r1.ty) (.ty (Ty.weaken T'))) :
    Option (Checked Γ (.ty T')) :=
  if hwf : Ty.Wf T' then
    (letUses? D c r1.uses r2.uses).map fun p =>
      ⟨.let ann r1.tm r2.tm, capJoin r1.uses p.1,
        HasTy.let (widenLeft r1.deriv p.1) (widenUses r2.deriv p.2) hwf⟩
  else none

/-- The first two rungs of the ladder for a body already synthesized.  A body
with an existential answer has neither, since `HasTy.let` concludes at a plain
type. -/
def letAvoid? {s : Sig} {Γ : Ctx s} (r1 : PElab Γ) (D : DeclTable (Γ.cons r1.ty)) (c : Nat)
    (ann : Option (ETy s)) (r2 : Elab (Γ.cons r1.ty)) : Option (Elab Γ) :=
  match r2.split with
  | .inl q =>
      ((avoidStrengthen? D c q.ty).bind fun p =>
        (letOf? r1 D c ann p.1 ⟨q.tm, q.uses, HasTy.sub q.deriv (.ty p.2) .refl⟩).map
          Checked.toElab).orElse fun _ =>
      (avoidTop? D c q.ty).bind fun p =>
        (letOf? r1 D c ann p.1 ⟨q.tm, q.uses, HasTy.sub q.deriv (.ty p.2) .refl⟩).map
          Checked.toElab
  | .inr _ => none

/-! ## Assembling an unpacking

`HasTy.letex` opens the witness binder and the payload binder.  The body's use
set may name the witness.  Everything else it uses is charged to the declared
set `U₂`, which is above the witness's bound. -/

/-- What an unpacking's body uses beyond the witness, with the payload replaced
by the set it is declared at.  The declared set of the unpacking is the bound
`C₀` joined with it, and the evidence is `V <: U₂↑↑ ∪ {c}` at that set. -/
def letexUses? {s : Sig} {Γ : Ctx s} {T : Ty (s,c)} (D : DeclTable ((Γ.consC).cons T))
    (c : Nat) (C₀ : CaptureSet s) (V : CaptureSet ((s,c),x)) :
    Option ((res : CaptureSet s) ×
      Subcap ((Γ.consC).cons T) V
        (CaptureSet.weaken (CaptureSet.weaken (k := .cap) (capJoin C₀ res)) ∪
          [CapAtom.cvar (.there .here)])) := do
  let V1 ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) V
  let res ← capStrengthen? (k := .cap) (V1.filter (fun a => !(decide (a = CapAtom.cvar .here))))
  let e ← subcap? D c V
    (CaptureSet.weaken (CaptureSet.weaken (k := .cap) (capJoin C₀ res)) ∪
      [CapAtom.cvar (.there .here)])
  some ⟨res, e⟩

/-- `HasTy.letex` at the answer `E`, the use set widened to the join. -/
def letexOf? {s : Sig} {Γ : Ctx s} (r1 : XElab Γ) (D : DeclTable ((Γ.consC).cons r1.body))
    (c : Nat) (E : ETy s)
    (r2 : Checked ((Γ.consC).cons r1.body) (ETy.weaken (ETy.weaken (k := .cap) E))) :
    Option (Checked Γ E) :=
  match letexUses? D c r1.bnd r2.uses with
  | some ⟨res, e⟩ =>
      some ⟨.letex r1.tm r2.tm, capJoin r1.uses (capJoin r1.bnd res),
        widenUses
          (HasTy.letex r1.deriv (.elem (capJoin_left r1.bnd res)) (widenUses r2.deriv e))
          (Subcap.union (.elem (capJoin_left r1.uses (capJoin r1.bnd res)))
            (.elem (capJoin_right r1.uses (capJoin r1.bnd res))))⟩
  | none => none

/-- An atom of the witness or the payload of an unpacking, replaced by the root
`ρ`. -/
def absorbAtom {s : Sig} (ρ : CapAtom ((s,c),x)) (a : CapAtom ((s,c),x)) : CapAtom ((s,c),x) :=
  match a with
  | .var .here => ρ
  | .sel .here _ => ρ
  | .cvar (.there .here) => ρ
  | a => a

/-- The answer of an unpacking's body moved out of the scope of the witness and
the payload.  First by strengthening.  Then, for a plain answer, by the level
rule: their atoms go to the innermost root of the context, whose level they are
at.  A context with no root absorbs nothing. -/
def exAvoid? {s : Sig} {Γ : Ctx s} {T : Ty (s,c)} (D : DeclTable ((Γ.consC).cons T)) (c : Nat)
    (E : ETy ((s,c),x)) :
    Option ((E' : ETy s) × ESub ((Γ.consC).cons T) E (ETy.weaken (ETy.weaken (k := .cap) E'))) :=
  (match eTyStrengthenW? (k := .var) E with
    | some ⟨F, hF⟩ =>
        match eTyStrengthenW? (k := .cap) F with
        | some ⟨E', hE'⟩ => some ⟨E', by rw [hF, hE']; exact ESub.refl _⟩
        | none => none
    | none => none :
      Option ((E' : ETy s) × ESub ((Γ.consC).cons T) E (ETy.weaken (ETy.weaken (k := .cap) E')))).orElse
    fun _ =>
  match E, Γ.root? with
  | .ty (.capt C S), some ρ => do
      let w1 ← shapeStrengthenW? (k := .var) S
      let w2 ← shapeStrengthenW? (k := .cap) w1.val
      let C1 := C.map (absorbAtom (CapAtom.cvar (.there (.there ρ))))
      let C2 ← capStrengthen? (k := .var) C1
      let C' ← capStrengthen? (k := .cap) C2
      let e ← subcap? D c C (CaptureSet.weaken (CaptureSet.weaken (k := .cap) C'))
      some ⟨.ty (w2.val ^ C'),
        ESub.ty (Sub.capt (subShapeOfEq
          (w1.property.trans (congrArg (fun X => Shape.weaken X) w2.property))) e)⟩
  | _, _ => none

/-- The way out at an existential bound term, for a body already synthesized:
its answer avoided, then `HasTy.letex`. -/
def letexAvoid? {s : Sig} {Γ : Ctx s} (r1 : XElab Γ) (D : DeclTable ((Γ.consC).cons r1.body))
    (c : Nat) (r2 : Elab ((Γ.consC).cons r1.body)) : Option (Elab Γ) :=
  (exAvoid? D c r2.ans).bind fun p =>
    (letexOf? r1 D c p.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv p.2 .refl⟩).map Checked.toElab

/-! ## The object rule, in passes

`HasTy.obj` types the definitions of a literal under a class root and a self
binder that holds the same definitions and the same capture set as the
conclusion.  Box inference changes the definitions, and the capture set is only
known once they are typed.  So the literal is typed in passes.  A pass types
the definitions it is given under a self binder that holds them and the current
set.  It is final when the elaborated definitions erase to the ones the binder
holds and their use set is below the current set and the self variable.
Otherwise the next pass takes the elaborated definitions, with their boxes, and
the set they used, with the self variable dropped, its capture members read at
their upper bounds, and the class root strengthened away.  The first pass runs
at the empty set.  `Budget.obj` bounds the passes. -/

/-- One typing of the definitions of a literal under its scope, at the
definitions and the set the self binder holds. -/
abbrev DefsCheck {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) : Type :=
  (d : ADefs ((s,c),x)) → (U : CaptureSet s) →
    Verdict (DefsElab (Γ.objBody d.erase S U) S.underRoot)

/-- The passes of the object rule.  `chk` types the definitions and `k` counts
the passes left. -/
def objPasses? {s : Sig} {Γ : Ctx s} (b : Budget) (S : Shape (s,x)) (chk : DefsCheck Γ S)
    (k : Nat) (d : ADefs ((s,c),x)) (U : CaptureSet s) : Verdict (Elab Γ) :=
  match k with
  | 0 => .unknown
  | k + 1 =>
      (chk d U).bind fun r =>
        let D := decls b (Γ.objBody d.erase S U)
        (Verdict.ofOption
          (if hd : r.tm.erase = d.erase then
            if hdist : Defs.Distinct d.erase then
              (subcap? D b.cap r.uses (CaptureSet.weaken (CaptureSet.weaken U) ∪ [.var .here])).map
                fun e => ⟨.obj S r.tm, [], .ty ((Shape.mu S) ^ U), objOf hd (r.deriv _ e) hdist⟩
            else none
          else none)).orElse fun _ =>
        let U' := ((capDropHere? (hereSel D) r.uses).bind fun V => capStrengthen? (k := .cap) V).getD U
        objPasses? b S chk k r.tm U'
termination_by structural k

/-! ## The level escape, decided

When a binding annotation is not reached, the typer walks the synthesized type
and the annotation in parallel, as the arrow rule of the search does, and
collects every set goal the search does not find.  For each it tries a
certificate.  The certificate needs three decided facts: the context is well
formed (`ctxWf?`), the target set resolves to itself at every depth
(`selfAtom?`), and at one small depth the source set is not confined to a root
the target set is confined to.  The last fact reads the well-founded
`Ctx.caps`, so compiled code computes it, not the kernel. -/

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

/-- An atom of the target that resolves to itself at every depth: the universal
root, a scope root, or a rigid capture binder. -/
def selfAtom? {s : Sig} (Γ : CapturesCC.FCdot.Ctx s) (a : CapturesCC.FCdot.CapAtom s) : Bool :=
  match a with
  | .top => true
  | .cvar κ =>
      match Γ.lookupCap κ with
      | .root => true
      | .star => true
      | _ => false
  | _ => false

theorem capsAtom_self {s : Sig} {Γ : CapturesCC.FCdot.Ctx s} {a : CapturesCC.FCdot.CapAtom s}
    (h : selfAtom? Γ a = true) (n : Nat) : Γ.capsAtom n a = [a] := by
  cases a with
  | top => exact CapturesCC.FCdot.Ctx.capsAtom_top Γ n
  | cvar κ =>
      rw [CapturesCC.FCdot.Ctx.capsAtom_cvar]
      simp only [selfAtom?] at h
      revert h
      cases Γ.lookupCap κ <;> intro h <;> first | rfl | simp at h
  | var x => simp [selfAtom?] at h
  | name x ℓ => simp [selfAtom?] at h

theorem caps_self {s : Sig} {Γ : CapturesCC.FCdot.Ctx s} :
    ∀ (D : CapturesCC.FCdot.CaptureSet s), (∀ a ∈ D, selfAtom? Γ a = true) →
      ∀ n, Γ.caps n D = D
  | [], _, n => CapturesCC.FCdot.Ctx.caps_nil Γ n
  | a :: D, h, n => by
      rw [CapturesCC.FCdot.Ctx.caps_cons, capsAtom_self (h a (List.mem_cons_self ..)) n,
        caps_self D (fun b hb => h b (List.mem_cons_of_mem _ hb)) n]
      rfl

/-- A certificate for the goal `C <: D` at `Γ`: the first root `r` (the
universal one, then each atom of `D`) that confines `D`, with the first depth
below four at which `C` is not confined to it. -/
def certify? {s : Sig} (Γ : Ctx s) (C D : CaptureSet s) : Option Reason :=
  if hwf : ctxWf? Γ = true then
    if hself : ∀ a ∈ D.translate, selfAtom? Γ.translate a = true then
      firstSome (fun r =>
        if hr : Γ.translate.Confined D.translate r then
          firstSome (fun n =>
            if hn : ¬ Γ.translate.Confined (Γ.translate.caps n C.translate) r then
              some (.levelEscape Γ C D r
                (escape_rejected_at (ctxWf?_sound Γ hwf) r
                  (fun m => by rw [caps_self _ hself m]; exact hr) n hn))
            else none) (List.range 4)
        else none) (CapturesCC.FCdot.CapAtom.top :: D.translate)
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

/-- The set goals the search does not find, walking `T <: U` as the search does:
the two sets, then fields, boxes, and the domains and codomains of arrows under
the scopes the arrow rule opens.  Structural on the depth `k`. -/
def escGoals (b : Budget) (k : Nat) {s : Sig} (Γ : Ctx s) (T U : Ty s) : List Goal :=
  match k with
  | 0 => []
  | k + 1 =>
      match T, U with
      | .capt C S, .capt C' S' =>
          (if (subcap? (baseDecls allBudget Γ) b.cap C C').isSome then [] else [⟨_, Γ, C, C'⟩]) ++
          match S, S' with
          | .all T1 U1, .all T2 U2 =>
              escGoals b k Γ.scope (Dom.underRoot T2) (Dom.underRoot T1) ++
              (match Cod.underRoot U1, Cod.underRoot U2 with
                | .ty V1, .ty V2 => escGoals b k (Γ.body T2) V1 V2
                | _, _ => [])
          | .fld a T1, .fld a' T2 => if a = a' then escGoals b k Γ T1 T2 else []
          | .box T1, .box T2 => escGoals b k Γ T1 T2
          | _, _ => []
termination_by structural k

/-- The verdict when `T` was not moved to the annotation `U` at `Γ`: a
rejection at the first goal with a certificate, `unknown` otherwise. -/
def diagnose {α : Type} (b : Budget) {s : Sig} (Γ : Ctx s) (T U : Ty s) : Verdict α :=
  match firstSome (fun g => certify? g.ctx g.lo g.hi) (escGoals b b.sub Γ T U) with
  | some r => .rejected r
  | none => .unknown

/-- The rejection of an existential answer outside every scope, where no root
can absorb its witness. -/
def topExistential {α : Type} {s : Sig} (Γ : Ctx s) (q : XElab Γ) : Verdict α :=
  .rejected (.existentialAtTop Γ (∃ᶜ[q.bnd] q.body) (fun _ ⟨e⟩ => by cases e))

/-! ## The typer -/

mutual

/-- Synthesis, clause by clause.  `ps` is the platform set, the reading of
`any` at a position with no scope root.

- a variable is its first view, `varSynth`
- `λ(x : T). t` decides and reads the domain, synthesizes the body under
  `Γ.body T` against a table rebuilt there, and takes the codomain and the
  function's set from the body by `lamOf?`
- `ν(z : S. d)` decides and reads the self shape and runs the passes of the
  object rule, `objPasses?`
- `x y` reads the first function view of `x` and checks `y` against its domain
  with the arrow's binder at `y`, at the join of the two sets.  An argument that
  fails is adapted and bound by a `let`.  A function with no function view and a
  box view is unboxed and bound by a `let`
- `x.a` reads the first field view of `x` at `a`.  A receiver with no such view
  and a box view is unboxed and bound by a `let`
- `let x (: E)? = t in u` climbs the ladder, or is bound by its annotation.  A
  body whose answer is an existential is rejected outside every scope, by
  `topExistential`
- `let ⟨c, x⟩ = t in u` unpacks the existential answer of `t`
- `□ x` boxes the first view of `x`, at the empty use set
- `C ⊸ x` unboxes the first box view of `x` at the set `C`, read off the box
  type when none is written
- `(t : T)` decides and reads `T` and checks `t` against it. -/
def synth? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (ps : CaptureSet s) (n : Nat)
    (a : ATm s) : Verdict (Elab Γ) :=
  match n with
  | 0 => .unknown
  | n + 1 =>
      ((match a with
        | .path (.var x) => .ok (varSynth Γ x)
        | .lam T t =>
            (written (domArrow T)).bind fun _ =>
              let T1 := readDom T
              if hwf : Ty.Wf T1 then
                (synth? (decls b (Γ.body T1)) b (psBody ps) n t).bind fun r =>
                  .ofOption (lamOf? (decls b (Γ.body T1)) b.cap hwf r)
              else .unknown
        | .obj S d =>
            (written ((Shape.mu S) ^ [])).bind fun _ =>
              let S' := readSelf Γ ps S
              objPasses? b S'
                (fun d' U' => checkDefs? (decls b (Γ.objBody d'.erase S' U')) b (psObj ps) n d'
                  S'.underRoot)
                b.obj d []
        | .app x y =>
            match allView (views D b x) with
            | some v =>
                let A := Ty.subst v.dom (Subst.singleC (.var y))
                (Verdict.ofOption ((checkVar? D b n y A).map fun r =>
                  (⟨.app x y, capJoin v.uses r.uses, ETy.subst v.cod (Subst.arg y),
                    HasTy.app (widenLeft v.deriv r.uses) (widenRight v.uses r.deriv)⟩ : Elab Γ))).orElse
                  fun _ =>
                -- rules two and three at the argument, bound by a `let`
                (Verdict.ofOption (adaptInsert? D b.cap b.sub (fun T => checkVar? D b n y T)
                    (views D b y) A)).bind fun r =>
                  let p : PElab Γ := ⟨r.tm, r.uses, A, r.deriv⟩
                  (synth? (decls b (Γ.cons A)) b (psVar ps) n (.app (.there x) .here)).bind fun r2 =>
                    .ofOption (letAvoid? p (decls b (Γ.cons A)) b.cap none r2)
            | none =>
                -- rule four at the function, bound by a `let`
                (Verdict.ofOption (unboxFirst? (views D b x))).bind fun r1 =>
                  match r1.split with
                  | .inl p =>
                      (synth? (decls b (Γ.cons p.ty)) b (psVar ps) n (.app .here (.there y))).bind
                        fun r2 => .ofOption (letAvoid? p (decls b (Γ.cons p.ty)) b.cap none r2)
                  | .inr _ => .unknown
        | .proj x l =>
            match fldView l (views D b x) with
            | some v => .ok ⟨.proj x l, v.uses, .ty v.ty, HasTy.proj v.deriv⟩
            | none =>
                -- rule four at the receiver, bound by a `let`
                (Verdict.ofOption (unboxFirst? (views D b x))).bind fun r1 =>
                  match r1.split with
                  | .inl p =>
                      (synth? (decls b (Γ.cons p.ty)) b (psVar ps) n (.proj .here l)).bind fun r2 =>
                        .ofOption (letAvoid? p (decls b (Γ.cons p.ty)) b.cap none r2)
                  | .inr _ => .unknown
        | .let ann t u =>
            (synth? D b ps n t).bind fun r1 =>
              match ann with
              | none =>
                  match r1.split with
                  | .inl p =>
                      (synth? (decls b (Γ.cons p.ty)) b (psVar ps) n u).bind fun r2 =>
                        match r2.split, Γ.root? with
                        | .inr q, none => topExistential (Γ.cons p.ty) q
                        | _, _ => .ofOption (letAvoid? p (decls b (Γ.cons p.ty)) b.cap none r2)
                  | .inr q =>
                      (synth? (decls b ((Γ.consC).cons q.body)) b (psObj ps) n
                          (u.rename (Rename.succ (k := .cap)).lift)).bind fun r2 =>
                        .ofOption (letexAvoid? q (decls b ((Γ.consC).cons q.body)) b.cap r2)
              | some A =>
                  (writtenAns A).bind fun _ =>
                    let A' := readAns Γ ps A
                    (match r1.split, A' with
                      | .inl p, .ty G =>
                          (check? (decls b (Γ.cons p.ty)) b (psVar ps) n u (.ty (Ty.weaken G))).bind
                            fun r2 =>
                              .ofOption ((letOf? p (decls b (Γ.cons p.ty)) b.cap (some A') G r2).map
                                Checked.toElab)
                      | .inl p, .ex _ _ =>
                          (synth? (decls b (Γ.cons p.ty)) b (psVar ps) n u).bind fun r2 =>
                            .ofOption ((letAvoid? p (decls b (Γ.cons p.ty)) b.cap (some A') r2).bind
                              fun r => (subsume? D b.cap b.sub r A').map Checked.toElab)
                      | .inr q, E =>
                          (check? (decls b ((Γ.consC).cons q.body)) b (psObj ps) n
                              (u.rename (Rename.succ (k := .cap)).lift)
                              (ETy.weaken (ETy.weaken (k := .cap) E))).bind fun r2 =>
                            .ofOption ((letexOf? q (decls b ((Γ.consC).cons q.body)) b.cap E r2).map
                              Checked.toElab)).whenUnknown fun _ =>
                    -- the annotation is binding: look for a rejection at the goal reached
                    match r1.split, A' with
                    | .inl p, .ty G =>
                        (synth? (decls b (Γ.cons p.ty)) b (psVar ps) n u).bind fun r2 =>
                          match r2.split with
                          | .inl q => diagnose b (Γ.cons p.ty) q.ty (Ty.weaken G)
                          | .inr _ => .unknown
                    | _, _ => .unknown
        | .letex t u =>
            (synth? D b ps n t).bind fun r1 =>
              match r1.split with
              | .inr q =>
                  (synth? (decls b ((Γ.consC).cons q.body)) b (psObj ps) n u).bind fun r2 =>
                    .ofOption (letexAvoid? q (decls b ((Γ.consC).cons q.body)) b.cap r2)
              | .inl _ => .unknown
        | .box x =>
            let v := varView Γ x
            .ok ⟨.box x, [], .ty ((Shape.box v.ty) ^ []), HasTy.box v.deriv⟩
        | .unbox C x =>
            .ofOption (match C with
              | some C => unboxSynth? C (views D b x)
              | none => unboxFirst? (views D b x))
        | .asc t T =>
            (written T).bind fun _ =>
              let T' := readAt Γ ps T
              ((check? D b ps n t (.ty T')).map fun r =>
                (⟨.asc r.tm T', r.uses, .ty T', r.deriv⟩ : Elab Γ)).whenUnknown fun _ =>
              -- the ascription is binding: look for a rejection at the goal reached
              (synth? D b ps n t).bind fun r =>
                match r.split with
                | .inl q => diagnose b Γ q.ty T'
                | .inr _ => .unknown)
        : Verdict (Elab Γ)).orElse fun _ => synth? D b ps n a
termination_by structural n

/-- Checking against an answer.  A variable against a plain goal goes to box
inference, `adaptVar?`, with `checkVar?` as plain checker.  Three clauses check
a term against the goal's own form and fall back to synthesis: a `λ` against a
function type, an unannotated `let` against any goal, a box value against a
box.  Everything else is synthesized and moved to the goal by a decided
equality or by the answer search, which packs a plain answer into an
existential goal. -/
def check? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (ps : CaptureSet s) (n : Nat)
    (a : ATm s) (E : ETy s) : Verdict (Checked Γ E) :=
  match n with
  | 0 => .unknown
  | n + 1 =>
      let bySynth : Unit → Verdict (Checked Γ E) := fun _ =>
        (synth? D b ps n a).bind fun r => .ofOption (subsume? D b.cap b.sub r E)
      match a with
      | .path (.var x) =>
          ((match E with
            | .ty G =>
                .ofOption (adaptVar? D b.cap b.sub (fun T' => checkVar? D b n x T') (views D b x) G)
            | .ex _ _ => .unknown) : Verdict (Checked Γ E)).orElse bySynth
      | .lam T1 t =>
          ((match E with
            | .ty (.capt C (.all T1' T2)) =>
                (written (domArrow T1)).bind fun _ =>
                  let T1r := readDom T1
                  if hwf : Ty.Wf T1r then
                    (check? (decls b (Γ.body T1r)) b (psBody ps) n t (Cod.underRoot T2)).bind fun r =>
                      .ofOption ((subcap? (decls b (Γ.body T1r)) b.cap r.uses
                          (CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken C)) ∪
                            [.var .here])).bind fun e =>
                        (if h : T1' = T1r then some (h ▸ Sub.refl (Dom.underRoot T1'))
                          else sub? (baseDecls allBudget Γ.scope) b.cap b.sub
                            (Dom.underRoot T1') (Dom.underRoot T1r)).map fun eD =>
                          ⟨.lam T1r r.tm, [],
                            HasTy.sub (HasTy.lam (widenUses r.deriv e) hwf)
                              (.ty (.capt (SubShape.all eD (ESub.refl _)) .refl)) .refl⟩)
                  else .unknown
            | _ => .unknown) : Verdict (Checked Γ E)).orElse bySynth
      | .let none t u =>
          ((synth? D b ps n t).bind fun r1 =>
            (match r1.split, E with
              | .inl p, .ty G =>
                  (check? (decls b (Γ.cons p.ty)) b (psVar ps) n u (.ty (Ty.weaken G))).bind fun r2 =>
                    .ofOption (letOf? p (decls b (Γ.cons p.ty)) b.cap none G r2)
              | .inr q, E =>
                  (check? (decls b ((Γ.consC).cons q.body)) b (psObj ps) n
                      (u.rename (Rename.succ (k := .cap)).lift)
                      (ETy.weaken (ETy.weaken (k := .cap) E))).bind fun r2 =>
                    .ofOption (letexOf? q (decls b ((Γ.consC).cons q.body)) b.cap E r2)
              | .inl _, .ex _ _ => .unknown) : Verdict (Checked Γ E)).orElse bySynth
      | .box x =>
          ((match E with
            | .ty G =>
                .ofOption ((boxCheck? (fun T' => checkVar? D b n x T') G).map fun d =>
                  (⟨.box x, [], d⟩ : Checked Γ (.ty G)))
            | .ex _ _ => .unknown) : Verdict (Checked Γ E)).orElse bySynth
      | _ => bySynth ()
termination_by structural n

/-- Checking a definition list.  `DefsTy` is syntax directed on both the
definitions and the shape, so they are matched in lockstep: a type member
against a declaration with its own shape on both bounds, a capture member
against a declaration with its own set on both bounds, a term member against a
field at the same label, an intersection against an intersection.  The result
holds the least use set and the derivation at every set above it. -/
def checkDefs? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (ps : CaptureSet s)
    (n : Nat) (d : ADefs s) (S : Shape s) : Verdict (DefsElab Γ S) :=
  match n with
  | 0 => .unknown
  | n + 1 =>
      match d, S with
      | .typ A S0, .typ B L U =>
          if hA : A = B then
            if hL : S0 = L then
              if hU : S0 = U then .ok ⟨.typ A S0, [], fun _ _ => defsTypAt hA hL hU⟩
              else .unknown
            else .unknown
          else .unknown
      | .cap A c, .cap B c1 c2 =>
          if hA : A = B then
            if h1 : c = c1 then
              if h2 : c = c2 then .ok ⟨.cap A c, [], fun _ _ => defsCapAt hA h1 h2⟩ else .unknown
            else .unknown
          else .unknown
      | .trm l t, .fld l' T =>
          if h : l = l' then
            (check? D b ps n t (.ty T)).map fun (r : Checked Γ (.ty T)) =>
              ⟨.trm l r.tm, r.uses, fun _ e => defsTrmAt h (widenUses r.deriv e)⟩
          else .unknown
      | .and d1 d2, .and S1 S2 =>
          (checkDefs? D b ps n d1 S1).bind fun (r1 : DefsElab Γ S1) =>
            (checkDefs? D b ps n d2 S2).map fun (r2 : DefsElab Γ S2) =>
              ⟨.and r1.tm r2.tm, capJoin r1.uses r2.uses, fun U e =>
                DefsTy.and (r1.deriv U (.trans (.elem (capJoin_left r1.uses r2.uses)) e))
                  (r2.deriv U (.trans (.elem (capJoin_right r1.uses r2.uses)) e))⟩
      | _, _ => .unknown
termination_by structural n

end

/-! ## The entry points -/

/-- The typer at a given context.  It builds the declaration table once and runs
at `Budget.typer`.  `ps` is the platform set at the context.  This is the entry
point for a term under a context, as the open examples of `DotMNF/Examples.lean`
are. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s) :
    Verdict (Elab Γ) :=
  synth? (decls b Γ) b ps b.typer a

/-- The typer on a closed program over a platform, at `Platform.ctx`.  A program
whose answer is an existential is rejected, since `Compiled` asks for a plain
type. -/
def synthTop? (b : Budget) (π : PlatformNames) (a : ATm π.sig) : Verdict (Elab π.plat.ctx) :=
  (synthIn? b π.plat.ctx π.set a).bind fun r =>
    match r.split with
    | .inl _ => .ok r
    | .inr q => topExistential π.plat.ctx q

/-- The typer at a given context, followed by one `sub` to a given use set and
answer, both found by the search.  The typer returns the least sets, and a
judgment written with larger ones is reached this way. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (U : CaptureSet s) (E : ETy s) : Verdict ((t : ATm s) × HasTy U Γ t.erase E) :=
  (synthIn? b Γ ps a).bind fun r =>
    .ofOption ((subcap? (decls b Γ) b.cap r.uses U).bind fun eU =>
      (if h : r.ans = E then some (h ▸ ESub.refl r.ans)
        else esub? (decls b Γ) b.cap b.sub r.ans E).map fun eE =>
          ⟨r.tm, HasTy.sub r.deriv eE eU⟩)

/-! ## Fuel monotonicity

The statement is about successes, not derivations: more fuel may find another
derivation of the same judgment, and `HasTy` is `Type`-valued without decidable
equality.  The retry at the end of `synth?`'s fuel level makes it an induction
on the fuel.  A rejection is not monotone. -/

/-- One more unit of fuel never loses a success. -/
theorem synth?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {ps : CaptureSet s}
    {n : Nat} {a : ATm s} (h : (synth? D b ps n a).isOk = true) :
    (synth? D b ps (n + 1) a).isOk = true := by
  rw [synth?.eq_def]
  exact Verdict.isOk_orElse_right h

/-- More fuel never loses a success. -/
theorem synth?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {ps : CaptureSet s}
    {n n' : Nat} (h : n ≤ n') (a : ATm s) :
    (synth? D b ps n a).isOk = true → (synth? D b ps n' a).isOk = true := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun x => synth?_succ (ih x)

/-! ## Checks

Each program is resolved with the labels and platform of the examples in
`lean/Coercions/CapturesCC/DotMNF/Examples.lean` and typed at the program
context of its platform, or at the context of the example where the example
is typed open.  A check compares the elaborated term, use set and answer with
those of the example.  The use set is compared up to `subcap?` both ways where
the least set is not the one the example wrote.

Each success runs at a budget at which it is found.  A larger typer fuel finds
the same (`synth?_le`).  A check one unit short shows what a counter measures.

Successes and rejections by a written type or an existential are
`decide +kernel` facts.  A `levelEscape` rejection reads `Ctx.caps`, which the
kernel does not reduce, so those verdicts are `#eval expect` tests. -/

section Checks

open CapturesCC.DotMNF.Examples

/-- The use set and the answer of a success. -/
def judgmentOf {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Option (CaptureSet s × ETy s) :=
  v.toOption.map fun r => (r.uses, r.ans)

/-- The erasure of the elaborated term of a success. -/
def erasedOf {s : Sig} {Γ : Ctx s} (v : Verdict (Elab Γ)) : Option (Tm s) :=
  v.toOption.map fun r => r.tm.erase

/-- A success whose elaborated term has the skeleton of the program. -/
def keepsSkel {s : Sig} {Γ : Ctx s} (a : ATm s) (v : Verdict (Elab Γ)) : Bool :=
  match v with
  | .ok r => decide (r.tm.skel = a.skel)
  | _ => false

/-- A success moved to a given use set and answer by one `sub`, through
`checkIn?`. -/
def reachesAt {s : Sig} (b : Budget) (Γ : Ctx s) (ps : CaptureSet s) (a : ATm s)
    (U : CaptureSet s) (E : ETy s) : Bool :=
  (checkIn? b Γ ps a U E).isOk

/-- Two use sets, each below the other by the subcapturing search. -/
def subcapBoth {s : Sig} (b : Budget) (Γ : Ctx s) (U V : CaptureSet s) : Bool :=
  (subcap? (decls b Γ) b.cap U V).isSome && (subcap? (decls b Γ) b.cap V U).isSome

/-- The judgment of a closed program over its platform. -/
def topJudgment (b : Budget) (π : PlatformNames) (a : Option (ATm π.sig)) :
    Option (CaptureSet π.sig × ETy π.sig) :=
  a.bind fun a => judgmentOf (synthTop? b π a)

/-- The erased elaboration of a closed program over its platform. -/
def topErased (b : Budget) (π : PlatformNames) (a : Option (ATm π.sig)) : Option (Tm π.sig) :=
  a.bind fun a => erasedOf (synthTop? b π a)

/-- A closed program moved to a given use set and answer by one `sub`. -/
def topReaches (b : Budget) (π : PlatformNames) (a : Option (ATm π.sig)) (U : CaptureSet π.sig)
    (E : ETy π.sig) : Bool :=
  match a with
  | some a => reachesAt b π.plat.ctx π.set a U E
  | none => false

/-- The name of the reason a closed program is rejected for. -/
def topRejected (b : Budget) (π : PlatformNames) (a : Option (ATm π.sig)) : Option String :=
  a.bind fun a => (synthTop? b π a).reason?.map Reason.name

/-- The depth of the context a level escape was decided at, and whether the root
of its certificate is the universal one. -/
def escapeShape? {α : Type} (v : Verdict α) : Option (Nat × Bool) :=
  match v with
  | .rejected (.levelEscape (s := s) _ _ _ r _) => some (s.length, decide (r = .top))
  | _ => none

/-- The platform set at the example contexts with two term binders over
the platform `fs, k2`. -/
def ps2z : CaptureSet ([],c,c,x,x) := CaptureSet.weaken (CaptureSet.weaken πz.set)

/-- The same over the platform `k1, k2`. -/
def ps2c : CaptureSet ([],c,c,x,x) := CaptureSet.weaken (CaptureSet.weaken πc.set)

/-! ### W2: the call of a capture-parameter arrow -/

/-- `W2_call`: `p f` at `W2CallCtx` has the use set `{f}` and answer `⊤`.  The
argument is checked at `File ^ {f}`, the domain with the arrow's binder at the
argument. -/
example : judgmentOf (synthIn? { decls := 0, views := 0, sub := 0, cap := 0, typer := 2, obj := 0 }
    W2CallCtx ps2c (.app (.there .here) .here)) = some ([CapAtom.var .here], .ty unitTy) := by
  decide +kernel

/-- One unit of typer fuel short. -/
example : judgmentOf (synthIn? { decls := 0, views := 0, sub := 0, cap := 0, typer := 1, obj := 0 }
    W2CallCtx ps2c (.app (.there .here) .here)) = none := by
  decide +kernel

/-- `process` itself, written with its parameter at `any`. -/
def W2defSrc : STm := cc% λ(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). u

/-- It elaborates to `W2Tm`, its parameter's `any` read as the arrow's own
binder.  Its least answer has the inner closure at its own type, and `W2Ty` is
reached by one `sub`. -/
example : topErased {} πc (resolveTop Λc πc W2defSrc) = some W2Tm := by decide +kernel

example : topReaches {} πc (resolveTop Λc πc W2defSrc) [] (.ty W2Ty) = true := by decide +kernel

/-! ### Z1: the caller of `freshCell`, at `Z1Ctx` -/

/-- The budget of the caller. -/
def bZ1 : Budget := { decls := 0, views := 0, sub := 0, cap := 2, typer := 4, obj := 0 }

/-- The `let` becomes a `letex`, and the elaborated term erases to the term of
`Z1_caller`. -/
example : erasedOf (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) =
    some (.letex (.app (.there .here) .here) (.let (.path (.var .here)) unitTm)) := by
  decide +kernel

/-- The elaboration keeps the skeleton of the program. -/
example : keepsSkel Z1callerAnn (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) = true := by decide +kernel

/-- The least judgment: the call charged `{fc}`, the unpacking its bound
`{fs, un}`, and the closure it hands back at its own type. -/
example : judgmentOf (synthIn? bZ1 Z1Ctx ps2z Z1callerAnn) =
    some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here], .ty (arrowS ^ [])) := by
  decide +kernel

/-- The judgment of `Z1_caller`, `Z1Use ∪ Z1Use` and `⊤`, is reached by one
`sub`. -/
example : reachesAt { bZ1 with cap := 4, sub := 1 } Z1Ctx ps2z Z1callerAnn (Z1Use ∪ Z1Use)
    (.ty unitTy) = true := by
  decide +kernel

/-- The two use sets are below each other: `{fc}` is below `{fs}` by
`sc-var`. -/
example : subcapBoth { bZ1 with cap := 4 } Z1Ctx
    [CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here] (Z1Use ∪ Z1Use) = true := by
  decide +kernel

/-- One unit of the set search short: the payload is not charged to its
witness. -/
example : (synthIn? { bZ1 with cap := 1 } Z1Ctx ps2z Z1callerAnn).isOk = false := by
  decide +kernel

/-! ### An unpacking whose answer is existential -/

/-- The budget of `Z1_tail`. -/
def bTail : Budget := { decls := 0, views := 0, sub := 0, cap := 1, typer := 3, obj := 0 }

/-- `let c1 = fc un in fc un` unpacks the first call, and its answer is the
second call's existential, strengthened past the witness and the payload.  It
erases to the term of `Z1_tail`. -/
example : erasedOf (synthIn? bTail Z1Ctx ps2z Z1TailAnn) =
    some (.letex (.app (.there .here) .here)
      (.app (.there (.there (.there .here))) (.there (.there .here)))) := by
  decide +kernel

example : judgmentOf (synthIn? bTail Z1Ctx ps2z Z1TailAnn) =
    some ([CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here],
      ∃ᶜ[Z1Use] (fileS ^ [CapAtom.cvar .here])) := by
  decide +kernel

example : subcapBoth { bTail with cap := 4 } Z1Ctx
    [CapAtom.var (.there .here), CapAtom.cvar fs2, CapAtom.var .here] (Z1Use ∪ Z1Use) = true := by
  decide +kernel

/-- Inside a scope the payload's type leaves by the level rule: the witness and
the payload are at the level of the innermost root, so `let x = fc un in x`
under a lambda is a file captured by that body's root.  This is the compiler's
local `any` absorbing a `fresh`. -/
example : (resolveIn Λc (((z1Names.consC "%").consC "%").cons "v") (cc% let x = fc un in x)).bind
    (fun a => judgmentOf (synthIn? {} (Z1Ctx.body unitTy) (psBody ps2z) a)) =
    some ([CapAtom.var (.there (.there (.there (.there .here)))), CapAtom.cvar (up fs2),
        CapAtom.var (.there (.there (.there .here)))],
      .ty (fileS ^ [CapAtom.cvar (.there (.there .here))])) := by
  decide +kernel

/-! ### A capture parameter that is called -/

/-- `λ(h : (∀(u : ⊤) ⊤) ^ {any}). let z = unit in h z`, with `unit : ⊤` bound
outside, is a pure closure whose domain reads `any` as the arrow's own binder.
The call is charged `{h, z}`, `z` is pure, and `h` leaves with the parameter. -/
example : judgmentOf (synthIn? { decls := 0, views := 0, sub := 0, cap := 1, typer := 4, obj := 0 }
    (platCtx.cons unitTy) (CaptureSet.weaken πc.set) P1ann) =
    some ([], .ty ((Shape.all (arrowS ^ [CapAtom.cvar .here]) (.ty unitTy)) ^ [])) := by
  decide +kernel

/-- One unit of typer fuel short. -/
example : (synthIn? { decls := 0, views := 0, sub := 0, cap := 1, typer := 3, obj := 0 }
    (platCtx.cons unitTy) (CaptureSet.weaken πc.set) P1ann).isOk = false := by
  decide +kernel

/-! ### `fresh` in a written result, and existential annotations -/

/-- `freshCell` bound by a `let` whose answer is written with `fresh`. -/
def Z1defSrc : STm :=
  cc% let fc : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs} =
        λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r
      in fc

/-- The annotation reads `fresh` as `Z1Ty`, the existential bounded by
`{fs, u}`, and the closure reaches it by the arrow rule, which packs the
cell. -/
example : topJudgment { decls := 0, views := 0, sub := 2, cap := 1, typer := 8, obj := 1 } πz
    (resolveTop Λc πz Z1defSrc) = some ([], .ty (Z1Ty k1)) := by
  decide +kernel

/-- An existential `let` annotation: the plain `let` is typed and packed into
the annotation, with the payload's own set `{f}` as witness. -/
def cov2Src : STm :=
  cc% λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {k1}).
        let r : ∃[c ⊑ {f}] μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {c} = f in r

example : topJudgment { decls := 0, views := 0, sub := 1, cap := 2, typer := 3, obj := 0 } πc
    (resolveTop Λc πc cov2Src) =
    some ([], .ty ((Shape.all (fileS ^ [CapAtom.cvar (.there k1)])
      (∃ᶜ[[CapAtom.var .here]] (fileS ^ [CapAtom.cvar .here]))) ^ [])) := by
  decide +kernel

/-- A written existential whose binder sits below a field: the payload's
own set is empty and is no witness, and the written bound `{k1}` is. -/
def cov4Src : STm := cc% λ(p : {a : ⊤ ^ {k1}}). let r : ∃[c ⊑ {k1}] {a : ⊤ ^ {c}} = p in r

example : topJudgment { decls := 0, views := 0, sub := 2, cap := 2, typer := 3, obj := 0 } πc
    (resolveTop Λc πc cov4Src) =
    some ([], .ty ((Shape.all ((Shape.fld la (Shape.top ^ [CapAtom.cvar (.there k1)])) ^ [])
      (∃ᶜ[[CapAtom.cvar (.there (.there k1))]]
        ((Shape.fld la (Shape.top ^ [CapAtom.cvar .here])) ^ []))) ^ [])) := by
  decide +kernel

/-! ### A projection is charged its receiver -/

/-- A closure that projects its parameter. -/
def cov3Src : STm := cc% λ(o : {a : ⊤ ^ {k1}} ^ {k1}). o.a

/-- It is pure: the body is charged `{o}`, which leaves with the parameter. -/
example : topJudgment { decls := 0, views := 0, sub := 0, cap := 1, typer := 2, obj := 0 } πc
    (resolveTop Λc πc cov3Src) =
    some ([], .ty ((Shape.all ((Shape.fld la (Shape.top ^ [CapAtom.cvar (.there k1)])) ^
        [CapAtom.cvar (.there k1)])
      (.ty (Shape.top ^ [CapAtom.cvar (.there (.there k1))]))) ^ [])) := by
  decide +kernel

/-- The body itself, at its scope: `o.a` is charged `{o}`. -/
example : judgmentOf (synthIn? { decls := 0, views := 0, sub := 0, cap := 1, typer := 1, obj := 0 }
    (platCtx.body ((Shape.fld la (Shape.top ^ [CapAtom.cvar (.there k1)])) ^
      [CapAtom.cvar (.there k1)]))
    (psBody πc.set) (.proj .here la)) =
    some ([CapAtom.var .here], .ty (Shape.top ^ [CapAtom.cvar (up k1)])) := by
  decide +kernel

/-! ### C7: boxes, an unboxing and an object under its class root -/

/-- C7 with no term-level box: the typer inserts `□ f₁`, `□ f₂` and
`{κ₁} ⊸ e`. -/
def C7src : STm :=
  cc% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- The budget of C7. -/
def bC7 : Budget := { decls := 0, views := 2, sub := 1, cap := 2, typer := 8, obj := 2 }

/-- It elaborates to `C7tm`, with the judgment `C7Ty`, and keeps the skeleton of
the program. -/
example : topErased bC7 πc (resolveTop Λc πc C7src) = some C7tm := by decide +kernel

example : topJudgment bC7 πc (resolveTop Λc πc C7src) = some ([], .ty C7Ty) := by decide +kernel

example : (match resolveTop Λc πc C7src with
    | some a => keepsSkel a (synthTop? bC7 πc a)
    | none => false) = true := by
  decide +kernel

/-- One pass of the object rule is not enough: the first pass inserts the boxes,
and the self binder it ran under holds the definitions without them. -/
example : topJudgment { bC7 with obj := 1 } πc (resolveTop Λc πc C7src) = none := by
  decide +kernel

/-! ### Rejections by a written type and by an existential answer -/

/-- `any` deeper in a domain than its outer set: `W2_deep_rejected`. -/
def deepSrc : STm := cc% λ(x : {read : ⊤ ^ {any}}). x

example : topRejected {} πc (resolveTop Λc πc deepSrc) = some "anyNotOk" := by decide +kernel

#eval expect (topRejected {} πc (resolveTop Λc πc deepSrc) == some "anyNotOk") "deep any"

/-- `fresh` in a domain, which the resolver refuses, is refused by the typer
too. -/
example : (synthIn? {} platCtx πc.set (.lam (.capt [CapAtom.fresh] .top) (.path (.var .here)))).reason?.map
    Reason.name = some "freshNotOk" := by
  decide +kernel

/-- A call of `freshCell` as the body of a `let` outside every scope: its answer
is an existential and no root absorbs the witness. -/
def exTopSrc : STm :=
  cc% let fc = ((λ(u : ⊤). let r = ν(f : {read : (∀(v : ⊤) ⊤) ^ {f}}. {read = λ(v : ⊤). v}) in r)
                  : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}) in
      let un = λ(v : ⊤). v in fc un

example : topRejected { typer := 12 } πz (resolveTop Λc πz exTopSrc) = some "existentialAtTop" := by
  decide +kernel

#eval expect (topRejected { typer := 12 } πz (resolveTop Λc πz exTopSrc) == some "existentialAtTop")
  "existential at the top"

/-! ### Rejections by a level escape

Compiled code computes each verdict, since its certificate reads `Ctx.caps`.
The depth of the context reached and the kind of root are checked too. -/

/- The escape: the callback's result `any` is the root of `λ(g : ⊤)`'s body,
and the callback returns its parameter.  The goal reached is `{f} <: {κ_g}` in
the callback's body, in the context that also binds `cb`, nine binders deep.
The certificate's root is `κ_g`. -/
#eval expect ((resolveTop Λc πc EscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) ==
  some (9, false)) "the escape"

/-- The same escape at the top of a program.  The result `any` reads as the
platform set, which holds no source root, so the certificate's root is the
universal one. -/
def TopEscSrc : STm :=
  cc% let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                  (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
        = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
      in cb

#eval expect ((resolveTop Λc πc TopEscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) ==
  some (6, true)) "the escape at the top"

/-- An ascription is binding too: the escape written as an ascription is
rejected at the callback's body. -/
def AscEscSrc : STm :=
  cc% λ(g : ⊤).
        ((λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f) :
          (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
            (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {})

#eval expect ((resolveTop Λc πc AscEscSrc).bind (fun a => escapeShape? (synthTop? {} πc a)) ==
  some (8, false)) "the escape by an ascription"

/-- The same callback, annotated with its result at its own parameter, is
accepted: what it captures stays inside its own scope. -/
def EscOkSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {f}) ^ {f}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb

example : (resolveTop Λc πc EscOkSrc).bind (fun a => (synthTop? {} πc a).toOption.map (·.uses)) =
    some [] := by
  decide +kernel

end Checks

end CapturesCCFrontend
