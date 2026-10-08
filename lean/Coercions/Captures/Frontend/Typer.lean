import Coercions.Captures.Frontend.Adapt
import Coercions.Captures.Frontend.Resolve

/-!
# The typer

The typer reads a type and a use set off an annotated term and returns the
calculus's derivation (`DotMNF/Typing.lean`) about the erasure of the term.  It
is fuel bounded and `Option` valued.  Every result carries its `HasTy`
derivation, so the result type is the soundness statement.  It is incomplete,
since subcapturing goes through subtyping and DOT subtyping is undecidable.

## Least sets

The typer computes the least use set and capture set the rules allow.  A
variable declared at the empty set is used at the empty set and keeps its
declared type.  Any other variable is used at `{x}` with its declared shape at
`{x}`.  A value is used at `{}`.  Application, projection and unboxing join
the sets of their premises with `capJoin`.  At the three binders the set is a
candidate followed by evidence.

- `λ(x : T). t` drops `{x}` from the body's set, reads `{x.C}` at the upper
  bound of `x`'s capture member, and strengthens the rest.  The subcapturing
  search finds the inclusion the rule asks for.
- `let x = t in u` replaces `{x}` in the body's set by the capture set of
  `t`'s type (`sc-var`), reads `{x.C}` the same way, and strengthens.  Both
  premises are widened to the join of the two sets.
- `ν(z : S. d)` types the definitions under the self binder at the written
  set, or `{}`.  Their set has to be below that set and `{z}`.  If it is not
  and no set is written, the definitions are typed again at the set they used,
  with `{z}` dropped (`objPasses?`).

## Result type of a `let`

`HasTy.let` asks for a result type `T'` with the body typed at `T'↑`.  Three
choices are tried in order: the annotation of the `let`, the body's type with
its shape strengthened and its set avoided, and `⊤` at the avoided set.  A set
cannot be dropped, since `Sub` asks for a subcapturing on it, so the third
fails when the set does not avoid.

## Checking

`check?` adds three clauses to synthesis followed by subsumption.  A `λ`
against a function type checks its body against the codomain, which lets an
ascribed signature reach the inside of a function.  A `let` with no annotation
checks its body against the goal.  A box value against a box goal checks the
variable against the boxed type.  Each clause falls back to synthesis.

A variable checked against a goal goes through box inference (`adaptVar?` of
`Adapt.lean`): plain checking, then `□ x` when no view of `x` is a box, then
`C ⊸ x` at the set of its first box view.  These are rules 1 to 3 of
`Adapt.lean`.  Rule 4 is `unboxFirst?`, used below.

`checkVar?` checks a variable.  It is separate because `And-I` and `Rec-I`
conclude about a variable and are not reached by subsumption.  `checkDefs?`
matches a definition list against a declaration shape in lockstep, as
`DefsTy` does.

## Insertions bound by a `let`

An argument, a function and a receiver must be variables, so an inserted box
or unboxing is bound by a `let`.  An argument that fails plain checking
against the domain is adapted, and `x y` becomes `let y' = □ y in x y'` or
`let y' = C ⊸ y in x y'`.  A function or receiver with a box view and no
function or field view is unboxed at the set of its first box view, so `x y`
becomes `let x' = C ⊸ x in x' y` and `x.a` becomes `let x' = C ⊸ x in x'.a`.
The body is synthesized under the new binder, and the `let` takes the second
and third choices above.  The skeleton inlines a `let` of a variable, so the
elaborated term keeps the program's skeleton.

## Fuel

The four functions form one block, structural on the fuel.  Every call inside
is at one unit less.  `synth?` ends each fuel level with a retry at the
previous level, which makes `synth?_le` an induction on the fuel.  The search
runs at `Budget.sub`, its own counter.  The checks at the end are
`decide +kernel`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Ctx Sub SubShape Subcap
  HasTy DefsTy Platform)
open scoped Captures.DotMNF

/-! ## Moving a derivation across a decided equality

The label of a member occurs twice in the conclusion, so these use `cases`
and not a rewrite. -/

/-- A field view read at the label the projection asks for. -/
def hasFldAt {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var} {a c : Label}
    {T : Ty s} {C : CaptureSet s} (h : c = a)
    (d : HasTy U Γ (.path (.var x)) ((Shape.fld c T) ^ C)) :
    HasTy U Γ (.path (.var x)) ((Shape.fld a T) ^ C) := by
  cases h; exact d

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

/-- A shape below itself, across a decided equality. -/
def subShapeOfEq {s : Sig} {Γ : Ctx s} {S T : Shape s} (h : S = T) : SubShape Γ S T := by
  cases h; exact .refl

/-- `{}-I` for definitions equal to the ones the self binder holds. -/
def objOf {s : Sig} {Γ : Ctx s} {d e : Defs (s,x)} {S : Shape (s,x)} {U : CaptureSet s}
    (h : e = d) (dt : DefsTy (CaptureSet.weaken U ∪ [.var .here]) (Γ.consSelf d S U) e S)
    (hd : Defs.Distinct d) : HasTy [] Γ (.val (.obj e)) ((Shape.mu S) ^ U) := by
  cases h; exact .obj dt hd

/-! ## Reading a view

None of these recurses. -/

/-- A function type a variable has, with the derivation. -/
structure AllView {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The domain. -/
  dom : Ty s
  /-- The codomain, under the domain's binder. -/
  cod : Ty (s,x)
  /-- The capture set of the function. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ((Shape.all dom cod) ^ cs)

/-- A field a variable has at a given label, with the derivation. -/
structure FldView {s : Sig} (Γ : Ctx s) (x : BVar s .var) (a : Label) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type of the field. -/
  ty : Ty s
  /-- The capture set of the object. -/
  cs : CaptureSet s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ((Shape.fld a ty) ^ cs)

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
def viewSub {s : Sig} {Γ : Ctx s} {x : BVar s .var} (D : DeclTable Γ) (n : Nat) (T : Ty s)
    (vs : List (View Γ x)) : Option (VarChecked Γ x T) :=
  firstSome (fun v => (sub? D n v.ty T).map fun e => ⟨v.uses, HasTy.sub v.deriv e .refl⟩) vs

/-! ## Candidates with their evidence -/

/-- The upper bound of the capture member `C` of the innermost binder, per the
table.  It replaces `{x.C}` when `x` goes out of scope. -/
def hereSel {s : Sig} {Γ : Ctx (s,x)} (D : DeclTable Γ) : Label → Option (CaptureSet (s,x)) :=
  fun ℓ => firstSome (fun d => if d.vr = .here ∧ d.lbl = ℓ then some d.hi else none) D.caps

/-- The set of a function: the body's set `V` without the parameter, with the
evidence `V <: U↑ ∪ {x}` that `All-I` asks for. -/
def lamUses? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat)
    (V : CaptureSet (s,x)) :
    Option ((U : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken U ∪ [.var .here])) := do
  let U ← capDropHere? (hereSel D) V
  let e ← subcap? D n V (CaptureSet.weaken U ∪ [.var .here])
  some ⟨U, e⟩

/-- The set a `let` adds to its bound term's `U₁`: the body's set `V` with
`{x}` replaced by the capture set of `x`'s type, with the evidence that `V` is
below the join. -/
def letUses? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat)
    (U1 : CaptureSet s) (V : CaptureSet (s,x)) :
    Option ((U2 : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken (capJoin U1 U2))) := do
  let U2 ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) V
  let e ← subcap? D n V (CaptureSet.weaken (capJoin U1 U2))
  some ⟨U2, e⟩

/-- The body's type with the shape strengthened and the set avoided. -/
def avoidStrengthen? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW SW => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let w ← shapeStrengthenW? SW
      let e ← subcap? D n CW (CaptureSet.weaken C')
      some ⟨w.val ^ C', Sub.capt (subShapeOfEq w.property) e⟩

/-- `⊤` at the avoided set. -/
def avoidTop? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW _ => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let e ← subcap? D n CW (CaptureSet.weaken C')
      some ⟨.top ^ C', Sub.capt SubShape.top e⟩

/-! ## Assembling a `let` -/

/-- `HasTy.let` at the result type `T'`, with both premises widened to the
joined use set. -/
def letOf? {s : Sig} {Γ : Ctx s} (r1 : Elab Γ) (D : DeclTable (Γ.cons r1.ty)) (n : Nat)
    (ann : Option (Ty s)) (T' : Ty s) (r2 : Checked (Γ.cons r1.ty) T'.weaken) :
    Option (Checked Γ T') :=
  if hwf : Ty.Wf T' then
    (letUses? D n r1.uses r2.uses).map fun p =>
      ⟨.let ann r1.tm r2.tm, capJoin r1.uses p.1,
        HasTy.let (widenLeft r1.deriv p.1) (widenUses r2.deriv p.2) hwf⟩
  else none

/-- A checked typing read as a synthesized one. -/
def Checked.toElab {s : Sig} {Γ : Ctx s} {T : Ty s} (r : Checked Γ T) : Elab Γ :=
  ⟨r.tm, r.uses, T, r.deriv⟩

/-- The second and third choices for a body already synthesized: its type with
the shape strengthened and the set avoided, else `⊤` at the avoided set. -/
def letAvoid? {s : Sig} {Γ : Ctx s} (r1 : Elab Γ) (D : DeclTable (Γ.cons r1.ty)) (n : Nat)
    (ann : Option (Ty s)) (r2 : Elab (Γ.cons r1.ty)) : Option (Elab Γ) :=
  ((avoidStrengthen? D n r2.ty).bind fun p =>
    (letOf? r1 D n ann p.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv p.2 .refl⟩).map Checked.toElab).orElse
    fun _ =>
  (avoidTop? D n r2.ty).bind fun p =>
    (letOf? r1 D n ann p.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv p.2 .refl⟩).map Checked.toElab

/-! ## The object rule

`HasTy.obj` types the definitions of a literal under a self binder that holds
the same definitions and capture set as the conclusion.  Box inference changes
the definitions, and the set of a literal with no written set is known only
after its definitions are typed.  So the literal is typed in passes.

A pass types the definitions under a self binder that holds them and the
current set.  It is final when the elaborated definitions erase to the ones
the binder holds and their use set is below the current set and the self
variable.  Otherwise the next pass takes the elaborated definitions, which
hold their boxes, and the set they used, with the self variable dropped and
its capture members read at their upper bounds.  A written set never changes.
`Budget.obj` bounds the passes. -/

/-- One typing of the definitions of a literal under its self binder. -/
abbrev DefsCheck {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) : Type :=
  (d : ADefs (s,x)) → (U : CaptureSet s) → Option (DefsElab (Γ.consSelf d.erase S U) S)

/-- The passes of the object rule.  `chk` types the definitions, `fix` says
whether the set was written and `k` counts the passes left. -/
def objPasses? {s : Sig} {Γ : Ctx s} (b : Budget) (S : Shape (s,x)) (fix : Bool)
    (chk : DefsCheck Γ S) (k : Nat) (d : ADefs (s,x)) (U : CaptureSet s) : Option (Elab Γ) :=
  match k with
  | 0 => none
  | k + 1 =>
      (chk d U).bind fun r =>
        let D := decls b (Γ.consSelf d.erase S U)
        ((if hd : r.tm.erase = d.erase then
            if hdist : Defs.Distinct d.erase then
              (subcap? D b.sub r.uses (CaptureSet.weaken U ∪ [.var .here])).map fun e =>
                ⟨.obj S (some U) r.tm, [], (Shape.mu S) ^ U, objOf hd (r.deriv _ e) hdist⟩
            else none
          else none) : Option (Elab Γ)).orElse fun _ =>
        let U' := if fix then U else (capDropHere? (hereSel D) r.uses).getD U
        objPasses? b S fix chk k r.tm U'
termination_by structural k


/-! ## The typer -/

mutual

/-- Synthesis, clause by clause.

- a variable is its first view, `varSynth`
- `λ(x : T). t` decides `Ty.Wf T`, synthesizes the body under `Γ.cons T`
  against a table rebuilt there, and takes the function's set from the body's
  by `lamUses?`
- `ν(z : S (^ U)?. d)` runs `objPasses?`
- `x y` reads the first function view of `x` and checks `y` against its
  domain at the join of the two sets.  An argument that fails is adapted and
  bound by a `let`.  A function with a box view and no function view is
  unboxed and bound by a `let`
- `x.a` reads the first field view of `x` at `a`.  A receiver with a box view
  and no such view is unboxed and bound by a `let`
- `let x (: A)? = t in u` takes the annotation, else the second and third
  choices for the result type
- `□ x` boxes the first view of `x`, at the empty use set
- `C ⊸ x` unboxes the first box view of `x` at the set `C`
- `(t : T)` checks `t` against `T`. -/
def synth? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat) (a : ATm s) :
    Option (Elab Γ) :=
  match n with
  | 0 => none
  | n + 1 =>
      ((match a with
        | .path (.var x) => some (varSynth Γ x)
        | .lam T t =>
            if hwf : Ty.Wf T then
              (synth? (decls b (Γ.cons T)) b n t).bind fun r =>
                match lamUses? (decls b (Γ.cons T)) b.sub r.uses with
                | some ⟨U, e⟩ =>
                    some ⟨.lam T r.tm, [], (Shape.all T r.ty) ^ U, HasTy.lam (widenUses r.deriv e) hwf⟩
                | none => none
            else none
        | .obj S U d =>
            objPasses? b S U.isSome
              (fun d' U' => checkDefs? (decls b (Γ.consSelf d'.erase S U')) b n d' S)
              b.obj d (U.getD [])
        | .app x y =>
            (match allView (views D b x) with
            | some v =>
                ((checkVar? D b n y v.dom).map fun r =>
                  (⟨.app x y, capJoin v.uses r.uses, v.cod.substVar y,
                    HasTy.app (widenLeft v.deriv r.uses) (widenRight v.uses r.deriv)⟩ : Elab Γ)).orElse
                  fun _ =>
                -- rules 2 and 3 of box inference at the argument, bound by a `let`
                (adaptInsert? D b.sub (fun T => checkVar? D b n y T) (views D b y) v.dom).bind
                  fun r =>
                    let r1 := r.toElab
                    (synth? (decls b (Γ.cons r1.ty)) b n (.app (.there x) .here)).bind fun r2 =>
                      letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2
            | none =>
                -- rule 4 at the function, bound by a `let`
                (unboxFirst? (views D b x)).bind fun r1 =>
                  (synth? (decls b (Γ.cons r1.ty)) b n (.app .here (.there y))).bind fun r2 =>
                    letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2)
        | .proj x a =>
            (match fldView a (views D b x) with
            | some v => some ⟨.proj x a, v.uses, v.ty, HasTy.proj v.deriv⟩
            | none =>
                -- rule 4 at the receiver, bound by a `let`
                (unboxFirst? (views D b x)).bind fun r1 =>
                  (synth? (decls b (Γ.cons r1.ty)) b n (.proj .here a)).bind fun r2 =>
                    letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2)
        | .let ann t u =>
            (synth? D b n t).bind fun r1 =>
              -- the annotation
              ((match ann with
                | some A =>
                    (check? (decls b (Γ.cons r1.ty)) b n u A.weaken).bind fun r2 =>
                      (letOf? r1 (decls b (Γ.cons r1.ty)) b.sub ann A r2).map Checked.toElab
                | none => none) : Option (Elab Γ)).orElse fun _ =>
              -- the second and third choices
              (synth? (decls b (Γ.cons r1.ty)) b n u).bind fun r2 =>
                letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub ann r2
        | .box x =>
            let v := varView Γ x
            some ⟨.box x, [], (Shape.box v.ty) ^ [], HasTy.box v.deriv⟩
        | .unbox C x => unboxSynth? C (views D b x)
        | .asc t T => (check? D b n t T).map fun r => ⟨.asc r.tm T, r.uses, T, r.deriv⟩)
        : Option (Elab Γ)).orElse fun _ => synth? D b n a
termination_by structural n

/-- Checking.  A variable goes to box inference, `adaptVar?`, with `checkVar?`
as its plain checker.  Three clauses check a term against the goal's form and
fall back to synthesis: a `λ` against a function type, an unannotated `let`
against any goal, and a box value against a box.  Everything else is
synthesized and moved to the goal by a decided equality or the subtyping
search. -/
def check? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat) (a : ATm s)
    (T : Ty s) : Option (Checked Γ T) :=
  match n with
  | 0 => none
  | n + 1 =>
      let bySynth : Unit → Option (Checked Γ T) := fun _ =>
        (synth? D b n a).bind fun r => subsume? D b.sub r T
      match a with
      | .path (.var x) => adaptVar? D b.sub (fun T' => checkVar? D b n x T') (views D b x) T
      | .lam T1 t =>
          ((match T with
            | .capt C (.all T1' T2) =>
                if hwf : Ty.Wf T1 then
                  (check? (decls b (Γ.cons T1)) b n t T2).bind fun r =>
                    (subcap? (decls b (Γ.cons T1)) b.sub r.uses
                        (CaptureSet.weaken C ∪ [.var .here])).bind fun e =>
                      (sub? D b.sub T1' T1).map fun eD =>
                        ⟨.lam T1 r.tm, [],
                          HasTy.sub (HasTy.lam (widenUses r.deriv e) hwf)
                            (Sub.capt (SubShape.all eD (Sub.refl T2)) .refl) .refl⟩
                else none
            | _ => none) : Option (Checked Γ T)).orElse bySynth
      | .let none t u =>
          ((if tyWf? T then
              (synth? D b n t).bind fun r1 =>
                (check? (decls b (Γ.cons r1.ty)) b n u T.weaken).bind fun r2 =>
                  letOf? r1 (decls b (Γ.cons r1.ty)) b.sub none T r2
            else none) : Option (Checked Γ T)).orElse bySynth
      | .box x =>
          ((boxCheck? (fun T' => checkVar? D b n x T') T).map fun d => ⟨.box x, [], d⟩).orElse
            bySynth
      | _ => bySynth ()
termination_by structural n

/-- Checking a variable, by three rules in order.

1. A goal `(S₁ ∧ S₂) ^ C` splits by `HasTy.andI` at the join of the two use
   sets.
2. A goal `(μ S) ^ C` whose body is a declaration folds by `HasTy.recI`.
   `SubShape` has no rule for `μ`, so no opened view reaches such a goal.
3. Otherwise the views are consulted, first for a view at exactly the goal and
   then for a view the subtyping search takes there. -/
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
      (viewAt T (views D b x)).orElse fun _ => viewSub D b.sub T (views D b x)
termination_by structural n

/-- Checking a definition list.  `DefsTy` is syntax directed on definitions
and shape, so they are matched in lockstep: a type member against a
declaration with its shape on both bounds, a capture member against one with
its set on both bounds, a term member against a field at the same label, and
an intersection against an intersection.  The result holds the least use set
and the derivation at every set above it. -/
def checkDefs? {s : Sig} {Γ : Ctx s} (D : DeclTable Γ) (b : Budget) (n : Nat) (d : ADefs s)
    (S : Shape s) : Option (DefsElab Γ S) :=
  match n with
  | 0 => none
  | n + 1 =>
      match d, S with
      | .typ A S0, .typ B L U =>
          if hA : A = B then
            if hL : S0 = L then
              if hU : S0 = U then some ⟨.typ A S0, [], fun _ _ => defsTypAt hA hL hU⟩ else none
            else none
          else none
      | .cap A c, .cap B c1 c2 =>
          if hA : A = B then
            if h1 : c = c1 then
              if h2 : c = c2 then some ⟨.cap A c, [], fun _ _ => defsCapAt hA h1 h2⟩ else none
            else none
          else none
      | .trm a t, .fld c T =>
          if h : a = c then
            (check? D b n t T).map fun (r : Checked Γ T) =>
              ⟨.trm a r.tm, r.uses, fun _ e => defsTrmAt h (widenUses r.deriv e)⟩
          else none
      | .and d1 d2, .and S1 S2 =>
          (checkDefs? D b n d1 S1).bind fun (r1 : DefsElab Γ S1) =>
            (checkDefs? D b n d2 S2).map fun (r2 : DefsElab Γ S2) =>
              ⟨.and r1.tm r2.tm, capJoin r1.uses r2.uses, fun U e =>
                DefsTy.and (r1.deriv U (.trans (.elem (capJoin_left r1.uses r2.uses)) e))
                  (r2.deriv U (.trans (.elem (capJoin_right r1.uses r2.uses)) e))⟩
      | _, _ => none
termination_by structural n

end

/-! ## The entry points -/

/-- The typer at a context.  It builds the declaration table once and runs at
`Budget.typer`. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Elab Γ) :=
  synth? (decls b Γ) b b.typer a

/-- The context of a platform: one capture binder per capability.  It
mirrors `Platform.ctx`. -/
def platformCtx {s : Sig} (P : Platform s) : Ctx s :=
  match P with
  | .nil => .nil
  | .cons P => .consC (platformCtx P)
termination_by structural P

/-- The typer on a closed program over a platform. -/
def synthTop? (b : Budget) (π : PlatformNames) (a : ATm π.sig) : Option (Elab (platformCtx π.plat)) :=
  synthIn? b (platformCtx π.plat) a

/-- The typer at a context, then the search to a given use set and type.  The
typer returns the least sets, and a judgment with larger ones is reached this
way. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (U : CaptureSet s) (T : Ty s) :
    Option ((t : ATm s) × HasTy U Γ t.erase T) :=
  (synthIn? b Γ a).bind fun r =>
    (subcap? (decls b Γ) b.sub r.uses U).bind fun eU =>
      (sub? (decls b Γ) b.sub r.ty T).map fun eT => ⟨r.tm, HasTy.sub r.deriv eT eU⟩

/-! ## Fuel monotonicity

The statement speaks of `isSome`, because more fuel may find another
derivation of the same judgment.  The retry at the end of each fuel level
makes it an induction on the fuel. -/

/-- One more unit of fuel never loses an answer. -/
theorem synth?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {n : Nat}
    {a : ATm s} (h : (synth? D b n a).isSome) : (synth? D b (n + 1) a).isSome := by
  rw [synth?.eq_def]
  exact isSome_orElse_right h

/-- More fuel never loses an answer. -/
theorem synth?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {n n' : Nat}
    (h : n ≤ n') (a : ATm s) : (synth? D b n a).isSome → (synth? D b n' a).isSome :=
  isSome_of_le (fun n => synth? D b n a) (fun _ => synth?_succ) h

/-! ## Examples with their boxes written

Each program is resolved over its platform with the labels of the calculus's
examples and typed at the empty context or the platform's.  Its use set and
type are compared with the ones the hand written derivation of
`DotMNF/Examples.lean` concludes.  Every comparison is a `decide +kernel`.
Each budget is one at which the program types, and a larger typer fuel also
works (`synth?_le`).  Checks one unit short of a budget fail. -/

section Checks

open Captures.DotMNF.Examples

/-- The use set a derivation concludes at. -/
def usesOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : CaptureSet s := U

/-- The type a derivation concludes at. -/
def tyOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : Ty s := T

/-- A resolved term types at the context with the given use set and type. -/
def synthsAt {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) (U : CaptureSet s)
    (T : Ty s) : Bool :=
  match a with
  | none => false
  | some a =>
      match synthIn? b Γ a with
      | some r => decide (r.uses = U ∧ r.ty = T)
      | none => false

/-- A resolved term types at the context and `checkIn?` moves it to the given
use set and type. -/
def reachesAt {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) (U : CaptureSet s)
    (T : Ty s) : Bool :=
  match a with
  | none => false
  | some a => (checkIn? b Γ a U T).isSome

/-! ### E1 to E8, at pure sets -/

/-- E1, the annotated `let` retyped by the bad bounds chain. -/
example : synthsAt { decls := 1, views := 0, sub := 2, typer := 4 } Ctx.nil
    (resolveTop Λc .empty E1src) (usesOfDeriv E1) (tyOfDeriv E1) = true := by decide +kernel

/-- E1 with one unit less search fuel. -/
example : synthsAt { decls := 1, views := 0, sub := 1, typer := 4 } Ctx.nil
    (resolveTop Λc .empty E1src) (usesOfDeriv E1) (tyOfDeriv E1) = false := by decide +kernel

/-- E2, the recursive literal: the outer `let` takes the third choice, `⊤`. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } Ctx.nil
    (resolveTop Λc .empty E2src) (usesOfDeriv E2) (tyOfDeriv E2) = true := by decide +kernel

/-- E3, the intersection with a shared member. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 5 } Ctx.nil
    (resolveTop Λc .empty E3src) (usesOfDeriv E3) (tyOfDeriv E3) = true := by decide +kernel

/-- E4, typing with no realizer: two rounds of the table. -/
example : synthsAt { decls := 2, views := 1, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E4src) (usesOfDeriv E4) (tyOfDeriv E4) = true := by decide +kernel

/-- E4 with one round of the table less: `w` never reaches `{A : Int..⊤}`. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E4src) (usesOfDeriv E4) (tyOfDeriv E4) = false := by decide +kernel

/-- E5, an object returned from a function. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 7 } Ctx.nil
    (resolveTop Λc .empty E5src) (usesOfDeriv E5) (tyOfDeriv E5) = true := by decide +kernel

/-- E6, a field typed at its own literal's member, under the `λ` that binds
the `n` the calculus's context holds. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E6src) [] ((Shape.all E6Int ((Shape.mu E6Self) ^ [])) ^ []) = true := by
  decide +kernel

/-- E7, the alias cycle: two type members and nothing searched. -/
example : synthsAt { decls := 0, views := 0, sub := 1, typer := 3 } Ctx.nil
    (resolveTop Λc .empty E7src) (usesOfDeriv E7) (tyOfDeriv E7) = true := by decide +kernel

/-- E8, refining an abstract type. -/
example : synthsAt { decls := 0, views := 1, sub := 1, typer := 3 } Ctx.nil
    (resolveTop Λc .empty E8src) (usesOfDeriv E8) (tyOfDeriv E8) = true := by decide +kernel

/-! ### Capture examples, with boxes and ascriptions written -/

/-- C7, a pure container of two boxed capabilities.  The fields check by the
`Box` rule in checking mode, the client unboxes at `{κ₁}`. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7src) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = true := by
  decide +kernel

/-- C7 with one unit less typer fuel. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc C7src) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = false := by
  decide +kernel

/-- S3, a type member at a boxed capturing type.  The client's unboxing
reaches the box through the upper bound of the member. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3src) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = true := by
  decide +kernel

/-- S3 with no round of the table: the member that holds the box is not found,
so the unboxing has no box view. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3src) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = false := by
  decide +kernel

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

/-- C2 at the calculus's judgment, `{κ₁,κ₂}` and `(⊤ → ⊤) ^ {κ₁,κ₂}`.  The
client checks against its ascription, so its call is charged to the upper
bound of the abstract member. -/
example : synthsAt { decls := 0, views := 2, sub := 4, typer := 9 } platCtx
    (resolveTop Λc πc C2ascSrc) (usesOfDeriv C2_typed) (tyOfDeriv C2_typed) = true := by
  decide +kernel

/-- C2 with one unit less search fuel. -/
example : synthsAt { decls := 0, views := 2, sub := 3, typer := 9 } platCtx
    (resolveTop Λc πc C2ascSrc) (usesOfDeriv C2_typed) (tyOfDeriv C2_typed) = false := by
  decide +kernel

/-- S1, `withFile` bound by an ascription at its `any` signature, at the
calculus's judgment `{fs}` and `⊤ ^ {fs}`. -/
example : synthsAt { decls := 0, views := 1, sub := 5, typer := 10 } platCtx
    (resolveTop Λc πc S1src) (usesOfDeriv S1_typed) (tyOfDeriv S1_typed) = true := by
  decide +kernel

/-- S1 with one unit less search fuel. -/
example : synthsAt { decls := 0, views := 1, sub := 4, typer := 10 } platCtx
    (resolveTop Λc πc S1src) (usesOfDeriv S1_typed) (tyOfDeriv S1_typed) = false := by
  decide +kernel

/-- S2, `mk` bound by an ascription at its `any` signature, at the calculus's
judgment `{fs}` and `⊤ ^ {fs}`.  The literal packs by `Rec-I` against the
checked `let`, and the caller's `{it.C}` leaves scope at the member's upper
bound `{fs}`. -/
example : synthsAt { decls := 1, views := 2, sub := 4, typer := 10 } platCtx
    (resolveTop Λc πc S2src) (usesOfDeriv S2_typed) (tyOfDeriv S2_typed) = true := by
  decide +kernel

/-- S2 with one unit less typer fuel. -/
example : synthsAt { decls := 1, views := 2, sub := 4, typer := 9 } platCtx
    (resolveTop Λc πc S2src) (usesOfDeriv S2_typed) (tyOfDeriv S2_typed) = false := by
  decide +kernel

/-! ### C5, at the calculus's context

C5 is the caller of `mk` in S2, typed in `DotMNF/Examples.lean` at `S2Ctx3`, where `it`
is bound.  The typer finds the least judgment, `{it, it.C}` and `⊤ ^ {it.C}`.
The calculus's `{fs}` and `⊤ ^ {fs}` are above it, and the search reaches them. -/

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

/-- The least judgment of C5 at `S2Ctx3`. -/
example : synthsAt { decls := 0, views := 2, sub := 3, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src)
    [CapAtom.var .here, CapAtom.sel .here lC] (.top ^ [CapAtom.sel .here lC]) = true := by
  decide +kernel

/-- The calculus's judgment of C5, reached from the least one: `{it}` by
`sc-var` to `{fs, un}`, `un` by `sc-var` to `{}`, and `{it.C}` by the upper
bound of the member. -/
example : reachesAt { decls := 1, views := 2, sub := 5, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src) (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) = true := by
  decide +kernel

/-- With one unit less search fuel the chain from `{it}` is not found. -/
example : reachesAt { decls := 1, views := 2, sub := 4, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src) (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) = false := by
  decide +kernel

/-! ### Least judgments without ascriptions

Without the ascriptions the typer finds judgments more precise than the
calculus's.  S1 types at `{}` and `⊤`, since its operation never calls the
file.  C2 types at `{κ₂}` and `(⊤ → ⊤) ^ {κ₂}`, since its answer is the client
at `b`, whose member is `{κ₂}`. -/

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

/-- The least judgment of S1: `{}` and `⊤`. -/
example : synthsAt { decls := 0, views := 1, sub := 2, typer := 9 } platCtx
    (resolveTop Λc πc S1bareSrc) [] (.top ^ []) = true := by
  decide +kernel

/-- The least judgment of C2: `{κ₂}` and `(⊤ → ⊤) ^ {κ₂}`. -/
example : synthsAt { decls := 1, views := 2, sub := 3, typer := 9 } platCtx
    (resolveTop Λc πc C2src) [CapAtom.cvar k2] (arrowS ^ [CapAtom.cvar k2]) = true := by
  decide +kernel

/-! ### Box inference

These programs write no box and no unboxing in terms.  The typer inserts
them.  Each check compares the erasure of the elaborated term with the
calculus's term or a term written out here, and the elaborated skeleton with
the program's.  A literal whose definitions take a box needs a second pass of
the object rule, so `obj := 1` is too little for it. -/

/-- The erasure of the elaborated term, when the typer succeeds. -/
def elabTm {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) : Option (Tm s) :=
  a.bind fun a => (synthIn? b Γ a).map fun r => r.tm.erase

/-- The typer succeeds and keeps the skeleton of the program. -/
def keepsSkel {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) : Bool :=
  match a with
  | none => false
  | some a =>
      match synthIn? b Γ a with
      | some r => decide (r.tm.skel = a.skel)
      | none => false

/-- C7 with no box in terms elaborates to the calculus's term: `□ f₁` and
`□ f₂` at the fields by rule 2 of `Adapt.lean`, and `{κ₁} ⊸ e` at the
ascription by rule 3. -/
example : elabTm { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7nbSrc) = some C7tm := by decide +kernel

/-- Its judgment is the calculus's. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7nbSrc) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = true := by
  decide +kernel

/-- One pass is not enough: the first pass inserts the boxes, and its binder
holds the definitions without them. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8, obj := 1 } platCtx
    (resolveTop Λc πc C7nbSrc) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = false := by
  decide +kernel

/-- S3 with no box in terms elaborates to the calculus's term.  The field
`elem = f` is declared at `z.A`, which is not a box, and `□ f` reaches it
through the lower bound of `A`.  The client's ascription unboxes `e` through
the upper bound of `o.A`. -/
example : elabTm { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) = some S3tm := by decide +kernel

/-- Its judgment is the calculus's. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = true := by
  decide +kernel

/-- With no round of the table the member `A` is not found. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = false := by
  decide +kernel

/-- C7 as a Scala program has it: no box written, and the element called where
it is read, `let e = o.e1 in e u`.  `e` has a box view and no function view,
so rule 4 binds `{κ₁} ⊸ e` before the call. -/
def C7scalaSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u

/-- The Scala form elaborates to `let e = o.e1 in let e' = {κ₁} ⊸ e in e' u`. -/
example : elabTm { decls := 0, views := 2, sub := 2, typer := 9 } platCtx
    (resolveTop Λc πc C7scalaSrc) =
      some (.val (.lam (capTy k1) (.val (.lam (capTy (.there .here)) (.val (.lam unitTy
        (.let (.val (.obj (C7Defs (.there (.there (.there .here))) (.there (.there .here)))))
          (.let (.proj .here le1)
            (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here))))))]
                .here)
              (.app .here (.there (.there (.there .here))))))))))))) := by
  decide +kernel

/-- The Scala form keeps the skeleton of the program. -/
example : keepsSkel { decls := 0, views := 2, sub := 2, typer := 9 } platCtx
    (resolveTop Λc πc C7scalaSrc) = true := by decide +kernel

/-- Its judgment charges `{κ₁}` to the innermost function and nothing to
the two outer ones. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 9 } platCtx
    (resolveTop Λc πc C7scalaSrc) []
    ((Shape.all (capTy k1) ((Shape.all (capTy (.there .here))
      ((Shape.all unitTy unitTy) ^ [CapAtom.cvar (.there (.there (.there .here)))])) ^ [])) ^ []) =
      true := by decide +kernel

/-- An argument that needs a box: `g` takes a boxed capability and `f1` is not
boxed.  The box is bound by `let y = □ f1 in g y`. -/
def argBoxSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let g = λ(b : □((∀(u : ⊤) ⊤) ^ {k1})). b in g f1

example : elabTm { decls := 0, views := 0, sub := 2, typer := 5 } platCtx
    (resolveTop Λc πc argBoxSrc) =
      some (.val (.lam (capTy k1)
        (.let (.val (.lam ((Shape.box (capTy (.there (.there .here)))) ^ []) (.path (.var .here))))
          (.let (.val (.box (.there .here))) (.app (.there .here) .here))))) := by
  decide +kernel

example : keepsSkel { decls := 0, views := 0, sub := 2, typer := 5 } platCtx
    (resolveTop Λc πc argBoxSrc) = true := by decide +kernel

/-- An argument that needs an unboxing: `h` takes the capability and `e` is its
box.  The unboxing is bound by `let y = {κ₁} ⊸ e in h y`. -/
def argUnboxSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})}. {e1 = f1}) in
        let e = o.e1 in
        let h = λ(k : (∀(u : ⊤) ⊤) ^ {k1}). k in h e

example : elabTm { decls := 0, views := 1, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc argUnboxSrc) =
      some (.val (.lam (capTy k1)
        (.let (.val (.obj (.trm le1 (.val (.box (.there .here))))))
          (.let (.proj .here le1)
            (.let (.val (.lam (capTy (.there (.there (.there (.there .here))))) (.path (.var .here))))
              (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there .here)))))]
                  (.there .here))
                (.app (.there .here) .here))))))) := by
  decide +kernel

/-- The function's set is the unboxing's, `{κ₁}`. -/
example : synthsAt { decls := 0, views := 1, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc argUnboxSrc) []
    ((Shape.all (capTy k1) (arrowS ^ [CapAtom.cvar (.there (.there .here))])) ^
      [CapAtom.cvar k1]) = true := by
  decide +kernel

/-- A receiver that is a box: `e.a` with `e` boxed has no field view, so
rule 4 binds `let p' = {κ₁} ⊸ e in p'.a`. -/
def recvSrc : STm :=
  cap% λ(p : {a : ⊤} ^ {k1}).
        let o = ν(z : {e1 : □({a : ⊤} ^ {k1})}. {e1 = p}) in
        let e = o.e1 in e.a

example : elabTm { decls := 0, views := 1, sub := 2, typer := 6 } platCtx
    (resolveTop Λc πc recvSrc) =
      some (.val (.lam ((Shape.fld la unitTy) ^ [CapAtom.cvar k1])
        (.let (.val (.obj (.trm le1 (.val (.box (.there .here))))))
          (.let (.proj .here le1)
            (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there .here))))] .here)
              (.proj .here la)))))) := by
  decide +kernel

example : keepsSkel { decls := 0, views := 1, sub := 2, typer := 6 } platCtx
    (resolveTop Λc πc recvSrc) = true := by decide +kernel

/-! ### The capture set of a literal

A literal with no written set and a field that uses a capability is typed in
two passes.  The first runs under the empty set, whose inclusion fails.  The
second runs under the set the first found.  If a box is inserted as well, the
second pass does both. -/

/-- A literal that holds `f` in a field. -/
def impureSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}). ν(z : {a : (∀(u : ⊤) ⊤) ^ {f}}. {a = f})

/-- It is typed at `{f}`. -/
example : synthsAt { decls := 0, views := 0, sub := 1, typer := 5 } platCtx
    (resolveTop Λc πc impureSrc) []
    ((Shape.all (capTy k1)
      ((Shape.mu (.fld la (arrowS ^ [CapAtom.var (.there .here)]))) ^ [CapAtom.var .here])) ^ []) =
      true := by
  decide +kernel

/-- One pass is not enough. -/
example : (elabTm { decls := 0, views := 0, sub := 1, typer := 5, obj := 1 } platCtx
    (resolveTop Λc πc impureSrc)).isSome = false := by
  decide +kernel

/-- A literal that holds `f` in a field and its box in another. -/
def impureInsSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        ν(z : {a : □((∀(u : ⊤) ⊤) ^ {f})} ∧ {b : (∀(u : ⊤) ⊤) ^ {f}}. {a = f} ∧ {b = f})

/-- It is typed at `{f}`, with `□ f` in the first field. -/
example : elabTm { decls := 0, views := 0, sub := 1, typer := 6 } platCtx
    (resolveTop Λc πc impureInsSrc) =
      some (.val (.lam (capTy k1)
        (.val (.obj (.and (.trm la (.val (.box (.there .here))))
          (.trm lb (.path (.var (.there .here))))))))) := by
  decide +kernel

example : synthsAt { decls := 0, views := 0, sub := 1, typer := 6 } platCtx
    (resolveTop Λc πc impureInsSrc) []
    ((Shape.all (capTy k1)
      ((Shape.mu (.and (.fld la ((Shape.box (arrowS ^ [CapAtom.var (.there .here)])) ^ []))
        (.fld lb (arrowS ^ [CapAtom.var (.there .here)])))) ^ [CapAtom.var .here])) ^ []) = true := by
  decide +kernel

/-! ### What box inference rejects

An insertion the rules do not license is rejected.  These are the rejections
of `Adapt.lean`, made by the typer on whole terms. -/

/-- `κ₁` at the signature of `C7Ctxe`. -/
private abbrev k1e : BVar ([],c,c,x,x,x,x) .cap := .there (.there (.there (.there (.there .here))))

/-- The ascription `(e : (⊤ → ⊤) ^ {κ₁})` at `C7Ctxe`, where `e` is the box. -/
def C7ascE : ATm ([],c,c,x,x,x,x) := .asc (.path (.var .here)) (capTy k1e)

/-- It elaborates to the calculus's unboxing `{κ₁} ⊸ e`. -/
example : (synthIn? { decls := 0, views := 1, sub := 1, typer := 2 } C7Ctxe C7ascE).map
    (fun r => r.tm.erase) = some (.unbox [CapAtom.cvar k1e] .here) := by decide +kernel

/-- The unboxing charges `{κ₁}`, the use set of the calculus's `C7unbox`. -/
example : reachesAt { decls := 0, views := 1, sub := 1, typer := 2 } C7Ctxe (some C7ascE)
    (usesOfDeriv C7unbox) (tyOfDeriv C7unbox) = true := by decide +kernel

/-- It is not typed at the empty use set: no rule puts `{κ₁}` below `{}`. -/
example : reachesAt { decls := 3, views := 3, sub := 6, typer := 8 } C7Ctxe (some C7ascE)
    [] (tyOfDeriv C7unbox) = false := by decide +kernel

/-- C7 with the unboxing at the other capability is rejected: the box's set is
`{κ₁}`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k2} ⊸ e))).isSome = false := by decide +kernel

/-- An unboxing of a closure is rejected: `f1` has no box view. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). {k1} ⊸ f1))).isSome = false := by
  decide +kernel

/-- C7 with the fields swapped is rejected: `□ f₂` is not a box of a capability
below `{κ₁}`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f2} ∧ {e2 = f1})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})))).isSome = false := by decide +kernel

/-- A capability ascribed at the other capability is rejected: plain checking
fails, and a box is not a function. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). (f1 : (∀(u : ⊤) ⊤) ^ {k2})))).isSome =
      false := by decide +kernel

/-- An unboxing whose type does not reach the goal is rejected: `{κ₁} ⊸ e` is
a capability of `κ₁`, not `κ₂`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k2})))).isSome = false := by decide +kernel

/-- A program with its boxes written is unchanged by box inference. -/
example : elabTm { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7src) = some C7tm := by decide +kernel

end Checks

end CapturesFrontend
