import Coercions.Captures.Frontend.Adapt
import Coercions.Captures.Frontend.Resolve

/-!
# The derivation producing typer

The typer reads a type and a use set off an annotated term and returns the
version's derivation (`lean/Coercions/Captures/DotMNF/Typing.lean`) about the
erasure of the term it typed.  It is fuel bounded, `Option` valued, and
sound by construction: every result carries its `HasTy` derivation, so
soundness is the result type and there is no soundness theorem to prove.

It is incomplete by necessity, since subcapturing goes through subtyping and
DOT subtyping is undecidable.  No completeness theorem is claimed.

## Least sets

The typer computes the least use set and the least capture set the rules
allow.  A variable declared at the empty set is used at the empty set and
keeps its declared type, any other variable is used at `{x}` with its
declared shape at `{x}`.  A value is used at `{}`.  An application, a
projection and an unboxing join the sets of their premises with `capJoin`.
At the three binders the set is a candidate followed by evidence.

- `λ(x : T). t` drops `{x}` from the body's set, reads an atom `{x.C}` at the
  upper bound of `x`'s capture member, and strengthens the rest.  The
  inclusion the rule asks for is found by the subcapturing search.
- `let x = t in u` replaces `{x}` in the body's set by the capture set of
  `t`'s type, which is what `sc-var` reads at the binder, reads `{x.C}` the
  same way, and strengthens.  Both premises are widened to the join of the
  two sets.
- `ν(z : S. d)` types the definitions under the self binder at the set the
  literal is written with, or `{}` when none is written.  The definitions'
  set has to be below that set and `{z}`.  When it is not and no set is
  written, the definitions are typed again at the set they used, with `{z}`
  dropped (`objPasses?`).

## The avoidance ladder

`HasTy.let` asks for a result type `T'` with the body typed at `T'↑`.
Three rungs are tried in order: the annotation of the `let`, the body's
type with its shape strengthened and its set avoided as above, and `⊤` at
the avoided set.  A set cannot be dropped, since `Sub` asks for a
subcapturing on it, so the third rung fails when the set does not avoid.

## Checking

`check?` adds three clauses to synthesis followed by subsumption.  A `λ`
against a function type checks its body against the codomain, which is how
an ascribed signature reaches the inside of a function.  A `let` with no
annotation checks its body against the goal.  A box value against a box
goal checks the variable against the boxed type.  Each clause falls back to
synthesis when it fails, so it only adds derivations.

A variable checked against a goal goes through box inference
(`adaptVar?` of `Adapt.lean`): plain checking first, then `□ x` when no view
of `x` is a box, then `C ⊸ x` at the set of its first box view.  The result
holds the inserted term in place of `x`.

`checkVar?` checks a variable.  It is a separate function because two rules
of the calculus conclude about a variable and are not reached by
subsumption: `And-I` and `Rec-I`.  `checkDefs?` matches a definition list
against a declaration shape in lockstep, as `DefsTy` does, and returns the
derivation at every use set above the definitions' least one.

## Insertions bound by a `let`

An argument, a function and a receiver must be variables, so a box or an
unboxing inserted there is bound by a `let`.  An argument that fails plain
checking against the domain is adapted as above, and `x y` becomes
`let y' = □ y in x y'` or `let y' = C ⊸ y in x y'`.  A function or a
receiver with no function or field view and a box view is unboxed at the set
of its first box view, and `x y` becomes `let x' = C ⊸ x in x' y`, `x.a`
becomes `let x' = C ⊸ x in x'.a`.  The body is synthesized under the new
binder and the `let` takes the second and third rungs of the ladder.  The
skeleton inlines a `let` of a variable, so the elaborated term has the
skeleton of the program.

## Fuel

The four functions are one block, structural on the fuel: every call inside
the block is at one unit less.  `synth?` ends its fuel level with a retry at
the previous level, which changes no answer the clauses give and makes
`synth?_le` an induction on the fuel.  The search is always called at
`Budget.sub`, its own counter.  Everything here reduces in the kernel, and
the checks at the end are `decide +kernel`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Ctx Sub SubShape Subcap
  HasTy DefsTy Platform)
open scoped Captures.DotMNF

/-! ## Moving a derivation across a decided equality

The label of a member occurs twice in the conclusion of the rule that
carries it, so these are written with `cases` rather than with a rewrite. -/

/-- A field view read at the label the projection asks for. -/
def hasFldAt {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {x : BVar s .var} {a c : Label}
    {T : Ty s} {C : CaptureSet s} (h : c = a)
    (d : HasTy U Γ (.path (.var x)) ((Shape.fld c T) ^ C)) :
    HasTy U Γ (.path (.var x)) ((Shape.fld a T) ^ C) := by
  cases h; exact d

/-- A type member definition against a declaration whose two bounds are the
definition's own shape. -/
def defsTypAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {S L U : Shape s}
    (hA : A = B) (hL : S = L) (hU : S = U) : DefsTy V Γ (.typ A S) (.typ B L U) := by
  cases hA; cases hL; cases hU; exact .typ

/-- A capture member definition against a declaration whose two bounds are
the definition's own set. -/
def defsCapAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {A B : Label} {c c1 c2 : CaptureSet s}
    (hA : A = B) (h1 : c = c1) (h2 : c = c2) : DefsTy V Γ (.cap A c) (.cap B c1 c2) := by
  cases hA; cases h1; cases h2; exact .cap

/-- A term member definition against a field declaration at the same
label. -/
def defsTrmAt {s : Sig} {Γ : Ctx s} {V : CaptureSet s} {a c : Label} {t : Tm s} {T : Ty s}
    (h : a = c) (ht : HasTy V Γ t T) : DefsTy V Γ (.trm a t) (.fld c T) := by
  cases h; exact .trm ht

/-- A shape below itself, across a decided equality. -/
def subShapeOfEq {s : Sig} {Γ : Ctx s} {S T : Shape s} (h : S = T) : SubShape Γ S T := by
  cases h; exact .refl

/-- `{}-I` for definitions that are the literal's own up to a decided
equality: the self binder holds the definitions the program wrote, and the
typer typed them under it. -/
def objOf {s : Sig} {Γ : Ctx s} {d e : Defs (s,x)} {S : Shape (s,x)} {U : CaptureSet s}
    (h : e = d) (dt : DefsTy (CaptureSet.weaken U ∪ [.var .here]) (Γ.consSelf d S U) e S)
    (hd : Defs.Distinct d) : HasTy [] Γ (.val (.obj e)) ((Shape.mu S) ^ U) := by
  cases h; exact .obj dt hd

/-! ## Reading a view

The typer consults the views of the search in four ways.  None of them
recurses, and none is part of the block. -/

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

/-- The upper bound of the capture member `C` of the innermost binder, as the
table under that binder records it.  It is what an atom `{x.C}` is replaced
by when `x` goes out of scope. -/
def hereSel {s : Sig} {Γ : Ctx (s,x)} (D : DeclTable Γ) : Label → Option (CaptureSet (s,x)) :=
  fun ℓ => firstSome (fun d => if d.vr = .here ∧ d.lbl = ℓ then some d.hi else none) D.caps

/-- The set of a function: the body's set `V` without the parameter, with
the evidence `V <: U↑ ∪ {x}` that `All-I` asks for. -/
def lamUses? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat)
    (V : CaptureSet (s,x)) :
    Option ((U : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken U ∪ [.var .here])) := do
  let U ← capDropHere? (hereSel D) V
  let e ← subcap? D n V (CaptureSet.weaken U ∪ [.var .here])
  some ⟨U, e⟩

/-- The set a `let` adds to its bound term's `U₁`: the body's set `V` with
`{x}` replaced by the capture set of `x`'s type, with the evidence that `V`
is below the join of the two sets. -/
def letUses? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat)
    (U1 : CaptureSet s) (V : CaptureSet (s,x)) :
    Option ((U2 : CaptureSet s) × Subcap (Γ.cons T) V (CaptureSet.weaken (capJoin U1 U2))) := do
  let U2 ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) V
  let e ← subcap? D n V (CaptureSet.weaken (capJoin U1 U2))
  some ⟨U2, e⟩

/-- The second rung of the ladder: the body's shape strengthened and its
set avoided. -/
def avoidStrengthen? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW SW => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let w ← shapeStrengthenW? SW
      let e ← subcap? D n CW (CaptureSet.weaken C')
      some ⟨w.val ^ C', Sub.capt (subShapeOfEq w.property) e⟩

/-- The third rung of the ladder: `⊤` at the avoided set. -/
def avoidTop? {s : Sig} {Γ : Ctx s} {T : Ty s} (D : DeclTable (Γ.cons T)) (n : Nat) :
    (W : Ty (s,x)) → Option ((T' : Ty s) × Sub (Γ.cons T) W T'.weaken)
  | .capt CW _ => do
      let C' ← capAvoid? (CaptureSet.weaken T.captureSet) (hereSel D) CW
      let e ← subcap? D n CW (CaptureSet.weaken C')
      some ⟨.top ^ C', Sub.capt SubShape.top e⟩

/-! ## Assembling a `let` -/

/-- `HasTy.let` at the result type `T'`, with the use set joined and both
premises widened to it. -/
def letOf? {s : Sig} {Γ : Ctx s} (r1 : Elab Γ) (D : DeclTable (Γ.cons r1.ty)) (n : Nat)
    (ann : Option (Ty s)) (T' : Ty s) (r2 : Checked (Γ.cons r1.ty) T'.weaken) :
    Option (Checked Γ T') :=
  if hwf : Ty.Wf T' then
    (letUses? D n r1.uses r2.uses).map fun p =>
      ⟨.let ann r1.tm r2.tm, capJoin r1.uses p.1,
        HasTy.let (widenLeft r1.deriv p.1) (widenUses r2.deriv p.2) hwf⟩
  else none

/-- A typing at a given type read as a synthesized one. -/
def Checked.toElab {s : Sig} {Γ : Ctx s} {T : Ty s} (r : Checked Γ T) : Elab Γ :=
  ⟨r.tm, r.uses, T, r.deriv⟩

/-- The second and third rungs of the ladder, for a body already
synthesized: its type with the shape strengthened and the set avoided, and
otherwise `⊤` at the avoided set. -/
def letAvoid? {s : Sig} {Γ : Ctx s} (r1 : Elab Γ) (D : DeclTable (Γ.cons r1.ty)) (n : Nat)
    (ann : Option (Ty s)) (r2 : Elab (Γ.cons r1.ty)) : Option (Elab Γ) :=
  ((avoidStrengthen? D n r2.ty).bind fun p =>
    (letOf? r1 D n ann p.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv p.2 .refl⟩).map Checked.toElab).orElse
    fun _ =>
  (avoidTop? D n r2.ty).bind fun p =>
    (letOf? r1 D n ann p.1 ⟨r2.tm, r2.uses, HasTy.sub r2.deriv p.2 .refl⟩).map Checked.toElab

/-! ## The object rule, in passes

`HasTy.obj` types the definitions of a literal under a self binder that
holds the same definitions and the same capture set the conclusion has.
Box inference changes the definitions, and the capture set of a literal
with no written set is only known once its definitions are typed.  So the
literal is typed in passes.  A pass types the definitions it is given under
a self binder that holds them and the current set.  It is final when the
elaborated definitions erase to the ones the binder holds and their use set
is below the current set and the self variable.  Otherwise the next pass
takes the elaborated definitions, which hold their boxes, so the next pass
inserts nothing, and the set the definitions used, with the self variable
dropped and its capture members read at their upper bounds.  A written set
is never changed.  The number of passes is `Budget.obj`. -/

/-- One typing of the definitions of a literal under its self binder, at the
definitions and the set the binder holds. -/
abbrev DefsCheck {s : Sig} (Γ : Ctx s) (S : Shape (s,x)) : Type :=
  (d : ADefs (s,x)) → (U : CaptureSet s) → Option (DefsElab (Γ.consSelf d.erase S U) S)

/-- The passes of the object rule.  `chk` types the definitions, `fix` says
whether the set was written, `k` counts the passes left.  The elaborated
literal records the set it was typed at. -/
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
  against a table rebuilt there, and takes the function's set from the
  body's by `lamUses?`
- `ν(z : S (^ U)?. d)` runs the passes of the object rule, `objPasses?`
- `x y` reads the first function view of `x` and checks `y` against its
  domain, at the join of the two sets.  An argument that fails is adapted
  and bound by a `let`.  A function with no function view and a box view is
  unboxed and bound by a `let`
- `x.a` reads the first field view of `x` at `a`.  A receiver with no such
  view and a box view is unboxed and bound by a `let`
- `let x (: A)? = t in u` climbs the avoidance ladder
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
                -- rules two and three at the argument, bound by a `let`
                (adaptInsert? D b.sub (fun T => checkVar? D b n y T) (views D b y) v.dom).bind
                  fun r =>
                    let r1 := r.toElab
                    (synth? (decls b (Γ.cons r1.ty)) b n (.app (.there x) .here)).bind fun r2 =>
                      letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2
            | none =>
                -- rule four at the function, bound by a `let`
                (unboxFirst? (views D b x)).bind fun r1 =>
                  (synth? (decls b (Γ.cons r1.ty)) b n (.app .here (.there y))).bind fun r2 =>
                    letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2)
        | .proj x a =>
            (match fldView a (views D b x) with
            | some v => some ⟨.proj x a, v.uses, v.ty, HasTy.proj v.deriv⟩
            | none =>
                -- rule four at the receiver, bound by a `let`
                (unboxFirst? (views D b x)).bind fun r1 =>
                  (synth? (decls b (Γ.cons r1.ty)) b n (.proj .here a)).bind fun r2 =>
                    letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub none r2)
        | .let ann t u =>
            (synth? D b n t).bind fun r1 =>
              -- rung one: the annotation
              ((match ann with
                | some A =>
                    (check? (decls b (Γ.cons r1.ty)) b n u A.weaken).bind fun r2 =>
                      (letOf? r1 (decls b (Γ.cons r1.ty)) b.sub ann A r2).map Checked.toElab
                | none => none) : Option (Elab Γ)).orElse fun _ =>
              -- rungs two and three
              (synth? (decls b (Γ.cons r1.ty)) b n u).bind fun r2 =>
                letAvoid? r1 (decls b (Γ.cons r1.ty)) b.sub ann r2
        | .box x =>
            let v := varView Γ x
            some ⟨.box x, [], (Shape.box v.ty) ^ [], HasTy.box v.deriv⟩
        | .unbox C x => unboxSynth? C (views D b x)
        | .asc t T => (check? D b n t T).map fun r => ⟨.asc r.tm T, r.uses, T, r.deriv⟩)
        : Option (Elab Γ)).orElse fun _ => synth? D b n a
termination_by structural n

/-- Checking.  A variable goes to box inference, `adaptVar?`, with
`checkVar?` as its plain checker.  Three clauses check a term
against the goal's own form, each falling back to synthesis: a `λ` against
a function type, an unannotated `let` against any goal, a box value against
a box.  Everything else is synthesized and moved to the goal by a decided
equality or by the subtyping search. -/
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

/-- Checking a variable.  Three rules, in order.

1. A goal `(S₁ ∧ S₂) ^ C` splits by `HasTy.andI` at the join of the two
   use sets.
2. A goal `(μ S) ^ C` whose body is declaration shaped folds by
   `HasTy.recI`.  `SubShape` has no rule for `μ`, so such a goal is
   otherwise unreachable from an opened view.
3. Otherwise the views are consulted, first for a view at exactly the goal
   and then for a view the subtyping search takes there. -/
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

/-- Checking a definition list.  `DefsTy` is syntax directed on both the
definitions and the shape, so the two are matched in lockstep: a type
member against a declaration with its own shape on both bounds, a capture
member against a declaration with its own set on both bounds, a term member
against a field at the same label, and an intersection against an
intersection.  The result holds the least use set of the definitions and the
derivation at every set above it. -/
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

/-- The typer at a given context.  It builds the declaration table of the
context once and runs at `Budget.typer`.  This is the entry point for a term
that sits under a context, as the version's open examples do. -/
def synthIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) : Option (Elab Γ) :=
  synth? (decls b Γ) b b.typer a

/-- The context of a platform: one capture binder per capability, with no
bound.  It is the version's `Platform.ctx`, clause for clause. -/
def platformCtx {s : Sig} (P : Platform s) : Ctx s :=
  match P with
  | .nil => .nil
  | .cons P => .consC (platformCtx P)
termination_by structural P

/-- The typer on a closed program over a platform. -/
def synthTop? (b : Budget) (π : PlatformNames) (a : ATm π.sig) : Option (Elab (platformCtx π.plat)) :=
  synthIn? b (platformCtx π.plat) a

/-- The typer at a given context, followed by one `sub` to a given use set
and type, both found by the search.  The typer returns the least sets, and a
judgment written with larger ones is reached this way. -/
def checkIn? {s : Sig} (b : Budget) (Γ : Ctx s) (a : ATm s) (U : CaptureSet s) (T : Ty s) :
    Option ((t : ATm s) × HasTy U Γ t.erase T) :=
  (synthIn? b Γ a).bind fun r =>
    (subcap? (decls b Γ) b.sub r.uses U).bind fun eU =>
      (sub? (decls b Γ) b.sub r.ty T).map fun eT => ⟨r.tm, HasTy.sub r.deriv eT eU⟩

/-! ## Fuel monotonicity

The statement is about `isSome` and not about derivations: more fuel may
find another derivation of the same judgment, and `HasTy` is `Type` valued
with no decidable equality.  The retry at the end of `synth?`'s fuel level
makes it an induction on the fuel alone. -/

/-- One more unit of fuel never loses an answer. -/
theorem synth?_succ {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {n : Nat}
    {a : ATm s} (h : (synth? D b n a).isSome) : (synth? D b (n + 1) a).isSome := by
  rw [synth?.eq_def]
  exact isSome_orElse_right h

/-- More fuel never loses an answer. -/
theorem synth?_le {s : Sig} {Γ : Ctx s} {D : DeclTable Γ} {b : Budget} {n n' : Nat}
    (h : n ≤ n') (a : ATm s) : (synth? D b n a).isSome → (synth? D b n' a).isSome :=
  isSome_of_le (fun n => synth? D b n a) (fun _ => synth?_succ) h

/-! ## The programs with their boxes written

Every program is resolved over its platform with the labels of the
version's examples, typed at the empty context or at the platform's, and its
use set and type are compared with the ones the version's hand written
derivation concludes (`lean/Coercions/Captures/DotMNF/Examples.lean`).  The
typer returns the derivation, so a success is a `HasTy` and not an answer.
The typer is structural, so every comparison is a `decide +kernel`.

The budget of each is one at which it is found.  The four counters were
lowered one at a time from `(decls 3, views 3, sub 6)` at the least typer
fuel that succeeds there, so the budget is found, not proved least, and a
larger typer fuel finds it too (`synth?_le`).  A few checks one unit short
show that the budget measures the search. -/

section Checks

open Captures.DotMNF.Examples

/-- The use set a derivation concludes at. -/
def usesOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : CaptureSet s := U

/-- The type a derivation concludes at. -/
def tyOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : Ty s := T

/-- The check: a resolved term is typed at the context and its use set and
type are the given ones.  `CaptureSet` and `Ty` have decidable equality, so
the comparison is a decision on the sets and the type, not on the
derivation. -/
def synthsAt {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) (U : CaptureSet s)
    (T : Ty s) : Bool :=
  match a with
  | none => false
  | some a =>
      match synthIn? b Γ a with
      | some r => decide (r.uses = U ∧ r.ty = T)
      | none => false

/-- The check through `checkIn?`: a resolved term is typed at the context
and moved to the given use set and type by the search. -/
def reachesAt {s : Sig} (b : Budget) (Γ : Ctx s) (a : Option (ATm s)) (U : CaptureSet s)
    (T : Ty s) : Bool :=
  match a with
  | none => false
  | some a => (checkIn? b Γ a U T).isSome

/-! ### E1 to E8, at pure sets -/

/-- E1, the annotated `let` retyped by the bad bounds chain. -/
example : synthsAt { decls := 1, views := 0, sub := 2, typer := 4 } Ctx.nil
    (resolveTop Λc .empty E1src) (usesOfDeriv E1) (tyOfDeriv E1) = true := by decide +kernel

/-- E1 one unit of the search short: the chain is not found. -/
example : synthsAt { decls := 1, views := 0, sub := 1, typer := 4 } Ctx.nil
    (resolveTop Λc .empty E1src) (usesOfDeriv E1) (tyOfDeriv E1) = false := by decide +kernel

/-- E2, the recursive literal: the outer `let` takes the third rung, `⊤`. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } Ctx.nil
    (resolveTop Λc .empty E2src) (usesOfDeriv E2) (tyOfDeriv E2) = true := by decide +kernel

/-- E3, the intersection with a shared member. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 5 } Ctx.nil
    (resolveTop Λc .empty E3src) (usesOfDeriv E3) (tyOfDeriv E3) = true := by decide +kernel

/-- E4, typing with no realizer: two rounds of the table. -/
example : synthsAt { decls := 2, views := 1, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E4src) (usesOfDeriv E4) (tyOfDeriv E4) = true := by decide +kernel

/-- E4 one round of the table short: `w` never reaches `{A : Int..⊤}`. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E4src) (usesOfDeriv E4) (tyOfDeriv E4) = false := by decide +kernel

/-- E5, an object returned from a function. -/
example : synthsAt { decls := 1, views := 1, sub := 2, typer := 7 } Ctx.nil
    (resolveTop Λc .empty E5src) (usesOfDeriv E5) (tyOfDeriv E5) = true := by decide +kernel

/-- E6, a field typed at its own literal's member, under the `λ` that binds
the `n` the version's context holds. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 6 } Ctx.nil
    (resolveTop Λc .empty E6src) [] ((Shape.all E6Int ((Shape.mu E6Self) ^ [])) ^ []) = true := by
  decide +kernel

/-- E7, the alias cycle: two type members and nothing searched. -/
example : synthsAt { decls := 0, views := 0, sub := 1, typer := 3 } Ctx.nil
    (resolveTop Λc .empty E7src) (usesOfDeriv E7) (tyOfDeriv E7) = true := by decide +kernel

/-- E8, refining an abstract type. -/
example : synthsAt { decls := 0, views := 1, sub := 1, typer := 3 } Ctx.nil
    (resolveTop Λc .empty E8src) (usesOfDeriv E8) (tyOfDeriv E8) = true := by decide +kernel

/-! ### The capture examples, with their boxes and ascriptions written -/

/-- C7, a pure container of two boxed capabilities.  The fields check by the
`Box` rule in checking mode, the client unboxes at `{κ₁}`. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7src) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = true := by
  decide +kernel

/-- C7 one unit of typer fuel short. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc C7src) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = false := by
  decide +kernel

/-- S3, a type member at a boxed capturing type.  The client's unboxing
reaches the box through the upper bound of the member. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3src) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = true := by
  decide +kernel

/-- S3 with no round of the table: the member that holds the box is not
found, so the unboxing has no box view. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3src) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = false := by
  decide +kernel

/-- C2 with the client ascribed at the version's `C2ClientTy`.  The version
annotates the client by hand, and the program text names that type by an
ascription. -/
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

/-- The ascribed C2 erases to the version's term. -/
example : (resolveTop Λc πc C2ascSrc).map ATm.erase = some C2tm := by decide

/-- C2 at the version's judgment, `{κ₁,κ₂}` and `(⊤ → ⊤) ^ {κ₁,κ₂}`: the
client checks against its ascription, so its call is charged to the upper
bound of the abstract member. -/
example : synthsAt { decls := 0, views := 2, sub := 4, typer := 9 } platCtx
    (resolveTop Λc πc C2ascSrc) (usesOfDeriv C2_typed) (tyOfDeriv C2_typed) = true := by
  decide +kernel

/-- C2 one unit of the search short. -/
example : synthsAt { decls := 0, views := 2, sub := 3, typer := 9 } platCtx
    (resolveTop Λc πc C2ascSrc) (usesOfDeriv C2_typed) (tyOfDeriv C2_typed) = false := by
  decide +kernel

/-- S1, `withFile` bound by an ascription at its `any` signature, at the
version's judgment `{fs}` and `⊤ ^ {fs}`. -/
example : synthsAt { decls := 0, views := 1, sub := 5, typer := 10 } platCtx
    (resolveTop Λc πc S1src) (usesOfDeriv S1_typed) (tyOfDeriv S1_typed) = true := by
  decide +kernel

/-- S1 one unit of the search short. -/
example : synthsAt { decls := 0, views := 1, sub := 4, typer := 10 } platCtx
    (resolveTop Λc πc S1src) (usesOfDeriv S1_typed) (tyOfDeriv S1_typed) = false := by
  decide +kernel

/-- S2, `mk` bound by an ascription at its `any` signature, at the version's
judgment `{fs}` and `⊤ ^ {fs}`.  The literal packs by `Rec-I` against the
checked `let`, and the caller's `{it.C}` leaves scope at the member's upper
bound `{fs}`. -/
example : synthsAt { decls := 1, views := 2, sub := 4, typer := 10 } platCtx
    (resolveTop Λc πc S2src) (usesOfDeriv S2_typed) (tyOfDeriv S2_typed) = true := by
  decide +kernel

/-- S2 one unit of typer fuel short. -/
example : synthsAt { decls := 1, views := 2, sub := 4, typer := 9 } platCtx
    (resolveTop Λc πc S2src) (usesOfDeriv S2_typed) (tyOfDeriv S2_typed) = false := by
  decide +kernel

/-! ### C5, at the version's own context

C5 is the caller of `mk` in S2, typed by the version at `S2Ctx3`, where `it`
is bound.  The typer finds the least judgment, `{it, it.C}` and
`⊤ ^ {it.C}`, which the version's `{fs}` and `⊤ ^ {fs}` are above.  One
`sub`, found by the search, reaches the version's judgment. -/

/-- C5 in direct style, `let n = it.next in let r = n un in r`. -/
def C5src : STm := cap% let n = it.next in let r = n un in r

/-- The names of `S2Ctx3`: the platform, then `mk`, `un` and `it`. -/
def C5names : NameEnv ([],c,c,x,x,x) := ((πc.names.cons "mk").cons "un").cons "it"

/-- The platform set at `S2Ctx3`. -/
def C5plat : CaptureSet ([],c,c,x,x,x) :=
  CaptureSet.weaken (CaptureSet.weaken (CaptureSet.weaken πc.set))

/-- C5 resolves to the term of the version's `C5_typed`. -/
example : (resolveIn Λc C5names C5plat C5src).map ATm.erase =
    some (.let (.proj .here lnext) (.let (.app .here (.there (.there .here))) (.path (.var .here)))) := by
  decide

/-- The least judgment of C5 at `S2Ctx3`. -/
example : synthsAt { decls := 0, views := 2, sub := 3, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src)
    [CapAtom.var .here, CapAtom.sel .here lC] (.top ^ [CapAtom.sel .here lC]) = true := by
  decide +kernel

/-- The version's judgment of C5, reached from the least one by the
search: `{it}` by `sc-var` to `{fs, un}` and `un` by `sc-var` to `{}`, and
`{it.C}` by the upper bound of the member. -/
example : reachesAt { decls := 1, views := 2, sub := 5, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src) (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) = true := by
  decide +kernel

/-- One unit of the search short, the chain from `{it}` is not found. -/
example : reachesAt { decls := 1, views := 2, sub := 4, typer := 4 } S2Ctx3
    (resolveIn Λc C5names C5plat C5src) (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) = false := by
  decide +kernel

/-! ### The least judgments without ascriptions

Without the ascriptions that name the version's types the typer finds
judgments more precise than the version's.  S1 types at `{}` and `⊤`, since
its operation never calls the file.  C2 types at `{κ₂}` and
`(⊤ → ⊤) ^ {κ₂}`, since its answer is the client at `b`, whose member is
`{κ₂}`. -/

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

/-- The unascribed S1 erases to the version's term. -/
example : (resolveTop Λc πc S1bareSrc).map ATm.erase = some S1tm := by decide

/-- The least judgment of S1: `{}` and `⊤`. -/
example : synthsAt { decls := 0, views := 1, sub := 2, typer := 9 } platCtx
    (resolveTop Λc πc S1bareSrc) [] (.top ^ []) = true := by
  decide +kernel

/-- The least judgment of C2, as `Notation.lean` writes it: `{κ₂}` and
`(⊤ → ⊤) ^ {κ₂}`. -/
example : synthsAt { decls := 1, views := 2, sub := 3, typer := 9 } platCtx
    (resolveTop Λc πc C2src) [CapAtom.cvar k2] (arrowS ^ [CapAtom.cvar k2]) = true := by
  decide +kernel

/-! ### Box inference

The programs below write no term level box and no unboxing.  The typer
inserts them, and each check compares the erasure of the elaborated term
with the version's term or with the term written out here, and the
elaborated skeleton with the program's.  A literal whose definitions take a
box needs a second pass of the object rule, so `obj := 1` is one unit
short for it. -/

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

/-- C7 with no term level box elaborates to the version's term: `□ f₁` and
`□ f₂` at the fields, by the second rule, and `{κ₁} ⊸ e` at the ascription,
by the third. -/
example : elabTm { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7nbSrc) = some C7tm := by decide +kernel

/-- Its judgment is the version's. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7nbSrc) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = true := by
  decide +kernel

/-- One pass of the object rule is not enough: the first pass inserts the
boxes, and the binder it ran under holds the definitions without them. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 8, obj := 1 } platCtx
    (resolveTop Λc πc C7nbSrc) (usesOfDeriv C7_typed) (tyOfDeriv C7_typed) = false := by
  decide +kernel

/-- S3 with no term level box elaborates to the version's term.  The field
`elem = f` is declared at `z.A`, which is not a box: the box `□ f` reaches it
through the lower bound of `A`.  The client's ascription unboxes `e` through
the upper bound of `o.A`. -/
example : elabTm { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) = some S3tm := by decide +kernel

/-- Its judgment is the version's. -/
example : synthsAt { decls := 1, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = true := by
  decide +kernel

/-- With no round of the table the member `A` is not found, so neither
bound reaches the box. -/
example : synthsAt { decls := 0, views := 2, sub := 2, typer := 7 } platCtx
    (resolveTop Λc πc S3nbSrc) (usesOfDeriv S3_typed) (tyOfDeriv S3_typed) = false := by
  decide +kernel

/-- C7 in the form a Scala program has: no box written, and the element
called where it is read, `let e = o.e1 in e u`.  `e` has a box view and no
function view, so the fourth rule binds `{κ₁} ⊸ e` before the call. -/
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

/-- An argument that needs a box: `g` takes a boxed capability and `f1` is
not boxed.  The box is bound by a `let`, `let y = □ f1 in g y`. -/
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

/-- An argument that needs an unboxing: `h` takes the capability and `e` is
its box.  The unboxing is bound by a `let`, `let y = {κ₁} ⊸ e in h y`. -/
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
the fourth rule binds `let p' = {κ₁} ⊸ e in p'.a`. -/
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

/-! ### The capture set of a literal, in passes

A literal with no written set and a field that uses a capability is typed
in two passes.  The first runs under the empty set, whose inclusion fails.
The second runs under the set the first one found.  With a box inserted as
well, the second pass does both jobs. -/

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

Every result carries its derivation, so an insertion the rules do not
license is a rejection.  These are the rejections of the cases of
`Adapt.lean`, made by the typer on whole terms. -/

/-- `κ₁` at the signature of `C7Ctxe`. -/
private abbrev k1e : BVar ([],c,c,x,x,x,x) .cap := .there (.there (.there (.there (.there .here))))

/-- The ascription `(e : (⊤ → ⊤) ^ {κ₁})` at the version's `C7Ctxe`, where
`e` is the box. -/
def C7ascE : ATm ([],c,c,x,x,x,x) := .asc (.path (.var .here)) (capTy k1e)

/-- It elaborates to the version's unboxing `{κ₁} ⊸ e`. -/
example : (synthIn? { decls := 0, views := 1, sub := 1, typer := 2 } C7Ctxe C7ascE).map
    (fun r => r.tm.erase) = some (.unbox [CapAtom.cvar k1e] .here) := by decide +kernel

/-- The unboxing charges `{κ₁}`, the use set of the version's `C7unbox`. -/
example : reachesAt { decls := 0, views := 1, sub := 1, typer := 2 } C7Ctxe (some C7ascE)
    (usesOfDeriv C7unbox) (tyOfDeriv C7unbox) = true := by decide +kernel

/-- It is not typed at the empty use set: no rule puts `{κ₁}` below `{}`. -/
example : reachesAt { decls := 3, views := 3, sub := 6, typer := 8 } C7Ctxe (some C7ascE)
    [] (tyOfDeriv C7unbox) = false := by decide +kernel

/-- C7 with the unboxing written at the other capability is rejected: the
box's set is `{κ₁}`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k2} ⊸ e))).isSome = false := by decide +kernel

/-- An unboxing of a closure is rejected: `f1` has no box view. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). {k1} ⊸ f1))).isSome = false := by
  decide +kernel

/-- C7 with the fields swapped is rejected: `□ f₂` is not a box of a
capability below `{κ₁}`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f2} ∧ {e2 = f1})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})))).isSome = false := by decide +kernel

/-- A capability ascribed at the other capability is rejected: plain
checking fails, and a box is not a function. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). (f1 : (∀(u : ⊤) ⊤) ^ {k2})))).isSome =
      false := by decide +kernel

/-- An unboxing whose type does not reach the goal is rejected: `{κ₁} ⊸ e`
is a capability of `κ₁`, not of `κ₂`. -/
example : (elabTm { decls := 3, views := 3, sub := 6, typer := 10 } platCtx
    (resolveTop Λc πc (cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k2})))).isSome = false := by decide +kernel

/-- A program with its boxes written is not changed by box inference: C7
elaborates to the version's term. -/
example : elabTm { decls := 0, views := 2, sub := 2, typer := 8 } platCtx
    (resolveTop Λc πc C7src) = some C7tm := by decide +kernel

end Checks

end CapturesFrontend
