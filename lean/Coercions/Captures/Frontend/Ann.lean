import Coercions.Captures.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms

`ATm` is `DotMNF.Tm` plus the annotations a front end needs and the calculus
does not keep.

- The self shape of an object literal, and its capture set when the program
  writes one.  `HasTy.obj` takes both from the context entry, so neither can
  be synthesized from the definitions.  A literal with no written set leaves
  the set to the typer.
- The optional result type of a `let`.
- The ascription `(t : T)`, a checking point for box inference.

Boxing, unboxing, application and projection are as in the calculus and take
bare variables, so monadic normal form holds by construction.  `ATm.erase`
lands in `DotMNF.Tm` and drops the annotations.

`ATm.skel` is the skeleton of a term, the part a program and its elaboration
must agree on.  It forgets types, capture sets, boxes, unboxing sets and
ascriptions, and it inlines a `let` of a variable, so `let y' = □ y in x y'`
has the skeleton of `x y`.  `Skel` has decidable equality.

A partial term, `PTm`, is an `ATm` whose slots may be empty: a lambda's domain,
the self shape of a literal, and the type written on a term member.  The
resolver produces it and the elaborator fills the empty slots.  `ATm` stays the
elaborated term, since the typer and every theorem about it read every slot.
`PTm.full?` and `ATm.toI` translate between the two, `PTm.fills` says that an
elaborated term agrees with the slots the programmer wrote, and `PTm.skel`
gives a partial term the skeleton of each of its fillings.  `PTm.deps` reads
off a field's right-hand side the fields it projects off the self, so that the
fields of a literal without a self shape are typed in order.

Nothing here is part of the metatheory.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs)

/-! ## Syntax -/

mutual
/-- Terms of DOT-MNF with capture sets and the front end's annotations. -/
inductive ATm : Sig → Type where
  /-- A path, which in this calculus is a variable. -/
  | path : Path s → ATm s
  /-- `λ(x : T). t`. -/
  | lam : Ty s → ATm (s,x) → ATm s
  /-- `ν(x : S (^ U)?. d)`: the self shape under the self binder, and the
  object's own capture set outside it, if written. -/
  | obj : Shape (s,x) → Option (CaptureSet s) → ADefs (s,x) → ATm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → ATm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → ATm s
  /-- `let x (: U)? = t in u`. -/
  | «let» : Option (Ty s) → ATm s → ATm (s,x) → ATm s
  /-- `□ x`, a box value. -/
  | box : BVar s .var → ATm s
  /-- `C ⊸ x`, an unboxing. -/
  | unbox : CaptureSet s → BVar s .var → ATm s
  /-- `(t : T)`, a checking point.  Erased. -/
  | asc : ATm s → Ty s → ATm s
/-- Definitions of an annotated object literal. -/
inductive ADefs : Sig → Type where
  /-- `{type A = S}`. -/
  | typ : Label → Shape s → ADefs s
  /-- `{C = c}`, a capture member definition. -/
  | cap : Label → CaptureSet s → ADefs s
  /-- `{a = t}`. -/
  | trm : Label → ATm s → ADefs s
  /-- `d ∧ e`. -/
  | and : ADefs s → ADefs s → ADefs s
end

deriving instance DecidableEq for ATm, ADefs

/-! ## Erasure

The only bridge from `ATm` to `DotMNF.Tm`. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase {s : Sig} (t : ATm s) : Tm s :=
  match t with
  | .path p => .path p
  | .lam T t => .val (.lam T t.erase)
  | .obj _ _ d => .val (.obj d.erase)
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let _ t u => .let t.erase u.erase
  | .box x => .val (.box x)
  | .unbox C x => .unbox C x
  | .asc t _ => t.erase
termination_by structural t
/-- Drop the annotations of a definition list. -/
def ADefs.erase {s : Sig} (d : ADefs s) : Defs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a t => .trm a t.erase
  | .and d e => .and d.erase e.erase
termination_by structural d
end

/-! ## Renaming

As in `DotMNF`.  The self shape of a literal lives under the self binder and
gets the lifted renaming.  The object's own set and the type of a `let` live
outside it. -/

mutual
/-- Rename the free variables of an annotated term. -/
def ATm.rename {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2) : ATm s2 :=
  match t with
  | .path p => .path (p.rename ρ)
  | .lam T t => .lam (T.rename ρ) (t.rename ρ.lift)
  | .obj S U d => .obj (S.rename ρ.lift) (U.map (fun C => CaptureSet.rename C ρ)) (d.rename ρ.lift)
  | .app x y => .app (ρ.var x) (ρ.var y)
  | .proj x a => .proj (ρ.var x) a
  | .let ann t u => .let (ann.map (fun U => U.rename ρ)) (t.rename ρ) (u.rename ρ.lift)
  | .box x => .box (ρ.var x)
  | .unbox C x => .unbox (CaptureSet.rename C ρ) (ρ.var x)
  | .asc t T => .asc (t.rename ρ) (T.rename ρ)
termination_by structural t
/-- Rename the free variables of an annotated definition list. -/
def ADefs.rename {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2) : ADefs s2 :=
  match d with
  | .typ A S => .typ A (S.rename ρ)
  | .cap C c => .cap C (CaptureSet.rename c ρ)
  | .trm a t => .trm a (t.rename ρ)
  | .and d e => .and (d.rename ρ) (e.rename ρ)
termination_by structural d
end

/-- Weakening of an annotated term, under one new term binder. -/
def ATm.weaken (t : ATm s) : ATm (s,x) := t.rename Rename.succ

/-! ## Erasure commutes with renaming -/

mutual
/-- Erasure commutes with renaming. -/
theorem ATm.erase_rename : ∀ {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2),
    (t.rename ρ).erase = t.erase.rename ρ
  | _, _, .path _, _ => rfl
  | _, _, .lam T t, ρ => by
      show Tm.val (.lam (T.rename ρ) (t.rename ρ.lift).erase) = _
      rw [ATm.erase_rename t ρ.lift]; rfl
  | _, _, .obj _ _ d, ρ => by
      show Tm.val (.obj (d.rename ρ.lift).erase) = _
      rw [ADefs.erase_rename d ρ.lift]; rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .proj _ _, _ => rfl
  | _, _, .let _ t u, ρ => by
      show Tm.let (t.rename ρ).erase (u.rename ρ.lift).erase = _
      rw [ATm.erase_rename t ρ, ATm.erase_rename u ρ.lift]; rfl
  | _, _, .box _, _ => rfl
  | _, _, .unbox _ _, _ => rfl
  | _, _, .asc t _, ρ => by
      show (t.rename ρ).erase = _
      rw [ATm.erase_rename t ρ]; rfl
/-- Erasure commutes with renaming, on definitions. -/
theorem ADefs.erase_rename : ∀ {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2),
    (d.rename ρ).erase = d.erase.rename ρ
  | _, _, .typ _ _, _ => rfl
  | _, _, .cap _ _, _ => rfl
  | _, _, .trm a t, ρ => by
      show Defs.trm a (t.rename ρ).erase = _
      rw [ATm.erase_rename t ρ]; rfl
  | _, _, .and d e, ρ => by
      show Defs.and (d.rename ρ).erase (e.rename ρ).erase = _
      rw [ADefs.erase_rename d ρ, ADefs.erase_rename e ρ]; rfl
end

/-! ## Size

The node count of a term.  Types and capture sets do not count. -/

mutual
/-- The node count of an annotated term. -/
def sizeATm {s : Sig} (t : ATm s) : Nat :=
  match t with
  | .path _ => 1
  | .lam _ t => sizeATm t + 1
  | .obj _ _ d => sizeADefs d + 1
  | .app _ _ => 1
  | .proj _ _ => 1
  | .let _ t u => sizeATm t + sizeATm u + 1
  | .box _ => 1
  | .unbox _ _ => 1
  | .asc t _ => sizeATm t + 1
termination_by structural t
/-- The node count of an annotated definition list. -/
def sizeADefs {s : Sig} (d : ADefs s) : Nat :=
  match d with
  | .typ _ _ => 1
  | .cap _ _ => 1
  | .trm _ t => sizeATm t + 1
  | .and d e => sizeADefs d + sizeADefs e + 1
termination_by structural d
end

/-- Every term has at least one node. -/
theorem sizeATm_pos {s : Sig} (t : ATm s) : 0 < sizeATm t := by
  cases t <;> simp [sizeATm]

/-- Every definition list has at least one node. -/
theorem sizeADefs_pos {s : Sig} (d : ADefs s) : 0 < sizeADefs d := by
  cases d <;> simp [sizeADefs]

/-! ## Skeletons

A skeleton keeps the binding structure, de Bruijn positions and labels. -/

mutual
/-- The skeleton of a term. -/
inductive Skel : Type where
  /-- A variable, by position. -/
  | var (i : Nat)
  /-- A function, one binder. -/
  | lam (t : Skel)
  /-- An object literal, one self binder. -/
  | obj (d : SkelDefs)
  /-- An application. -/
  | app (i j : Nat)
  /-- A projection. -/
  | proj (i : Nat) (ℓ : Label)
  /-- A `let`, one binder over the body. -/
  | «let» (t u : Skel)
/-- The skeleton of a definition list.  A capture member definition has the
skeleton of a type definition. -/
inductive SkelDefs : Type where
  /-- A type or capture member definition. -/
  | typ (ℓ : Label)
  /-- A term member definition. -/
  | trm (ℓ : Label) (t : Skel)
  /-- `d ∧ e`. -/
  | and (d e : SkelDefs)
end

deriving instance DecidableEq, Repr for Skel, SkelDefs

/-- The position of a bound variable, counting binders of both kinds. -/
def bvarPos {s : Sig} {k : Kind} (x : BVar s k) : Nat :=
  match x with
  | .here => 0
  | .there y => bvarPos y + 1
termination_by structural x

/-- The position of `i` after replacing position `k` by the outer position
`j`.  Inner positions stay, `k` becomes `j` shifted past the `k` inner
binders, and outer positions lose the removed binder. -/
def Skel.instPos (k j i : Nat) : Nat :=
  if i < k then i else if i = k then j + k else i - 1

mutual
/-- Replace the variable at position `k` by the outer position `j`, and
remove its binder. -/
def Skel.inst (k j : Nat) (t : Skel) : Skel :=
  match t with
  | .var i => .var (Skel.instPos k j i)
  | .lam t => .lam (Skel.inst (k + 1) j t)
  | .obj d => .obj (SkelDefs.inst (k + 1) j d)
  | .app i i' => .app (Skel.instPos k j i) (Skel.instPos k j i')
  | .proj i ℓ => .proj (Skel.instPos k j i) ℓ
  | .let t u => .let (Skel.inst k j t) (Skel.inst (k + 1) j u)
termination_by structural t
/-- `Skel.inst` on a definition list. -/
def SkelDefs.inst (k j : Nat) (d : SkelDefs) : SkelDefs :=
  match d with
  | .typ ℓ => .typ ℓ
  | .trm ℓ t => .trm ℓ (Skel.inst k j t)
  | .and d e => .and (SkelDefs.inst k j d) (SkelDefs.inst k j e)
termination_by structural d
end

/-- A `let` skeleton, inlined when the bound skeleton is a variable. -/
def Skel.mkLet (t u : Skel) : Skel :=
  match t with
  | .var j => Skel.inst 0 j u
  | t => .let t u

mutual
/-- The skeleton of a term. -/
def ATm.skel {s : Sig} (t : ATm s) : Skel :=
  match t with
  | .path (.var x) => .var (bvarPos x)
  | .lam _ t => .lam t.skel
  | .obj _ _ d => .obj d.skel
  | .app x y => .app (bvarPos x) (bvarPos y)
  | .proj x a => .proj (bvarPos x) a
  | .let _ t u => Skel.mkLet t.skel u.skel
  | .box x => .var (bvarPos x)
  | .unbox _ x => .var (bvarPos x)
  | .asc t _ => t.skel
termination_by structural t
/-- The skeleton of a definition list. -/
def ADefs.skel {s : Sig} (d : ADefs s) : SkelDefs :=
  match d with
  | .typ A _ => .typ A
  | .cap C _ => .typ C
  | .trm a t => .trm a t.skel
  | .and d e => .and d.skel e.skel
termination_by structural d
end

/-! ## No `any`

`NoAnyAnn` says that no annotation, capture set or type definition holds the
atom `any`.  The resolver emits only such terms (`resolve_noAny`). -/

mutual
/-- No `any` in any annotation, set or type definition of the term. -/
def ATm.NoAnyAnn {s : Sig} (t : ATm s) : Bool :=
  match t with
  | .path _ => true
  | .lam T t => T.noAny && t.NoAnyAnn
  | .obj S U d =>
      S.noAny && (match U with | none => true | some C => CaptureSet.noAny C) && d.NoAnyAnn
  | .app _ _ => true
  | .proj _ _ => true
  | .let ann t u =>
      (match ann with | none => true | some U => U.noAny) && t.NoAnyAnn && u.NoAnyAnn
  | .box _ => true
  | .unbox C _ => CaptureSet.noAny C
  | .asc t T => t.NoAnyAnn && T.noAny
termination_by structural t
/-- No `any` in any annotation, set or type definition of the definitions. -/
def ADefs.NoAnyAnn {s : Sig} (d : ADefs s) : Bool :=
  match d with
  | .typ _ S => S.noAny
  | .cap _ c => CaptureSet.noAny c
  | .trm _ t => t.NoAnyAnn
  | .and d e => d.NoAnyAnn && e.NoAnyAnn
termination_by structural d
end

/-! ## Examples

A binding inserted for a box does not change the skeleton:
`λ(x). λ(y). let y' = □ y in x y'` against `λ(x). λ(y). x y`. -/

example :
    (ATm.lam (.capt [] .top) (.lam (.capt [] .top)
      (.let none (.box .here) (.app (.there (.there .here)) .here))) : ATm []).skel =
    (ATm.lam (.capt [] .top) (.lam (.capt [] .top)
      (.app (.there .here) .here)) : ATm []).skel := by decide

/-- A `let` of a non-variable stays. -/
example :
    (ATm.lam (.capt [] .top) (.let none (.app .here .here) (.path (.var .here))) : ATm []).skel =
      .lam (.let (.app 0 0) (.var 0)) := by decide

/-- Ascriptions and unboxings are forgotten. -/
example :
    (ATm.lam (.capt [] .top) (.asc (.unbox [] .here) (.capt [] .top)) : ATm []).skel =
      .lam (.var 0) := by decide

/-! ## Partial terms

`PTm` is `ATm` with `Option` at every slot inference may fill: a lambda's
domain, a literal's self shape, and a written field type.  `none` is an empty
slot.  A domain is one slot, its shape and set together, so a written domain
`S` keeps meaning `S ^ {}`.  The object's own set stays the `Option` it is in
`ATm`, written or left to the typer, and is no slot of its own.  The resolver
returns a `PTm`, the elaborator fills it, and the elaborated term is an `ATm`,
the input of the typer.  Each `let` also records where it comes from, since the
elaborator treats a call argument apart from other bindings. -/

/-- Where a `let` of a partial term comes from.  `written` is a `let` of the
source.  `arg` is the binding `atomize` inserts at the operand of an
application, the one place a call argument sits.  `recv` is the binding at an
operator, at the receiver of a projection, or at the operand of a box or an
unboxing.  An ascription has its own constructor, so it needs no tag. -/
inductive LetTag where
  | written
  | arg
  | recv
deriving DecidableEq, Repr

mutual
/-- An annotated term whose slots may be empty. -/
inductive PTm : Sig → Type where
  /-- A path, which in this calculus is a variable. -/
  | path : Path s → PTm s
  /-- `λ(x : T). t`, or `λx. t` with the domain empty. -/
  | lam : Option (Ty s) → PTm (s,x) → PTm s
  /-- `ν(x : S (^ U)?. d)`, or `ν(x. d)` with the self shape empty.  The set
  sits outside the self binder, as in `ATm.obj`. -/
  | obj : Option (Shape (s,x)) → Option (CaptureSet s) → PDefs (s,x) → PTm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → PTm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → PTm s
  /-- `let x (: U)? = t in u`, with the origin of the binding. -/
  | «let» : LetTag → Option (Ty s) → PTm s → PTm (s,x) → PTm s
  /-- `□ x`, a box value. -/
  | box : BVar s .var → PTm s
  /-- `C ⊸ x`, an unboxing. -/
  | unbox : CaptureSet s → BVar s .var → PTm s
  /-- `(t : T)`, a checking point. -/
  | asc : PTm s → Ty s → PTm s
/-- Definitions whose term members may carry a written type. -/
inductive PDefs : Sig → Type where
  /-- `{type A = S}`. -/
  | typ : Label → Shape s → PDefs s
  /-- `{C = c}`, a capture member definition. -/
  | cap : Label → CaptureSet s → PDefs s
  /-- `{a = t}`, or `{a : T = t}` with a written type. -/
  | trm : Label → Option (Ty s) → PTm s → PDefs s
  /-- `d ∧ e`. -/
  | and : PDefs s → PDefs s → PDefs s
end

deriving instance DecidableEq for PTm, PDefs

/-! ## The bridges to `ATm` -/

mutual
/-- The `ATm` a partial term stands for, when no slot is empty.  A written
field type has no place in `ATm`, so it makes the term partial.  The tag is
dropped. -/
def PTm.full? : {s : Sig} → PTm s → Option (ATm s)
  | _, .path p => some (.path p)
  | _, .lam (some T) t => t.full?.map (.lam T)
  | _, .lam none _ => none
  | _, .obj (some S) U d => d.full?.map (.obj S U)
  | _, .obj none _ _ => none
  | _, .app x y => some (.app x y)
  | _, .proj x a => some (.proj x a)
  | _, .let _ ann t u =>
      match t.full?, u.full? with
      | some a, some b => some (.let ann a b)
      | _, _ => none
  | _, .box x => some (.box x)
  | _, .unbox C x => some (.unbox C x)
  | _, .asc t T => t.full?.map fun a => .asc a T
/-- The `ADefs` that a block of partial terms stands for, when no slot is
empty and no field type is written. -/
def PDefs.full? : {s : Sig} → PDefs s → Option (ADefs s)
  | _, .typ A S => some (.typ A S)
  | _, .cap C c => some (.cap C c)
  | _, .trm a none t => t.full?.map (.trm a)
  | _, .trm _ (some _) _ => none
  | _, .and d e =>
      match d.full?, e.full? with
      | some a, some b => some (.and a b)
      | _, _ => none
end

mutual
/-- Every slot written.  Every `let` is tagged `written`. -/
def ATm.toI : {s : Sig} → ATm s → PTm s
  | _, .path p => .path p
  | _, .lam T t => .lam (some T) t.toI
  | _, .obj S U d => .obj (some S) U d.toI
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let ann t u => .let .written ann t.toI u.toI
  | _, .box x => .box x
  | _, .unbox C x => .unbox C x
  | _, .asc t T => .asc t.toI T
/-- Every slot written, and no field type. -/
def ADefs.toI : {s : Sig} → ADefs s → PDefs s
  | _, .typ A S => .typ A S
  | _, .cap C c => .cap C c
  | _, .trm a t => .trm a none t.toI
  | _, .and d e => .and d.toI e.toI
end

/-! ## Agreement with the written slots -/

/-- The left part of an intersection shape.  Any other shape gives `⊤`, which
has no field, so a written field type checked against it does not agree. -/
def shapeLeft {s : Sig} : Shape s → Shape s
  | .and S _ => S
  | _ => .top

/-- The right part of an intersection shape, and `⊤` for any other shape. -/
def shapeRight {s : Sig} : Shape s → Shape s
  | .and _ S => S
  | _ => .top

mutual
/-- The elaborated term agrees with every written slot.  An empty slot agrees
with anything.  The object's set is no slot, so it must be equal.  The tag is
ignored. -/
def PTm.fills : {s : Sig} → PTm s → ATm s → Bool
  | _, .path p, .path q => decide (p = q)
  | _, .lam o t, .lam T a =>
      (match o with | some T' => decide (T' = T) | none => true) && t.fills a
  | _, .obj o U d, .obj S U' d' =>
      (match o with | some S' => decide (S' = S) | none => true) && decide (U = U') &&
        d.fills S d'
  | _, .app x y, .app x' y' => decide (x = x') && decide (y = y')
  | _, .proj x a, .proj x' a' => decide (x = x') && decide (a = a')
  | _, .let _ o t u, .let o' a b => decide (o = o') && t.fills a && u.fills b
  | _, .box x, .box x' => decide (x = x')
  | _, .unbox C x, .unbox C' x' => decide (C = C') && decide (x = x')
  | _, .asc t T, .asc a T' => decide (T = T') && t.fills a
  | _, _, _ => false
/-- Definitions against the self shape they were typed at, in lockstep.  A
written field type equals the shape's field at that label.  An intersection of
definitions splits the shape with `shapeLeft` and `shapeRight`, so a shape out
of step with the definitions leaves no field for a written type to agree
with. -/
def PDefs.fills : {s : Sig} → PDefs s → Shape s → ADefs s → Bool
  | _, .typ A S, _, .typ A' S' => decide (A = A') && decide (S = S')
  | _, .cap C c, _, .cap C' c' => decide (C = C') && decide (c = c')
  | _, .trm a o t, U, .trm a' b =>
      decide (a = a') &&
      (match o, U with
       | some V, .fld _ W => decide (V = W)
       | some _, _ => false
       | none, _ => true) && t.fills b
  | _, .and d e, U, .and d' e' => d.fills (shapeLeft U) d' && e.fills (shapeRight U) e'
  | _, _, _, _ => false
end

/-! ## Skeletons of partial terms

The skeleton forgets every slot and every tag, so a partial term and each of
its fillings have the same one (`PTm.skel_of_fills`). -/

mutual
/-- The skeleton of a partial term. -/
def PTm.skel : {s : Sig} → PTm s → Skel
  | _, .path (.var x) => .var (bvarPos x)
  | _, .lam _ t => .lam t.skel
  | _, .obj _ _ d => .obj d.skel
  | _, .app x y => .app (bvarPos x) (bvarPos y)
  | _, .proj x a => .proj (bvarPos x) a
  | _, .let _ _ t u => Skel.mkLet t.skel u.skel
  | _, .box x => .var (bvarPos x)
  | _, .unbox _ x => .var (bvarPos x)
  | _, .asc t _ => t.skel
/-- The skeleton of the definitions of a partial term. -/
def PDefs.skel : {s : Sig} → PDefs s → SkelDefs
  | _, .typ A _ => .typ A
  | _, .cap C _ => .typ C
  | _, .trm a _ t => .trm a t.skel
  | _, .and d e => .and d.skel e.skel
end

/-! ## No `any` in a partial term

As `ATm.NoAnyAnn`, with an empty slot holding no `any`. -/

mutual
/-- No `any` in any written annotation, set or type definition of the
term. -/
def PTm.NoAnyAnn : {s : Sig} → PTm s → Bool
  | _, .path _ => true
  | _, .lam o t => (match o with | none => true | some T => T.noAny) && t.NoAnyAnn
  | _, .obj o U d =>
      (match o with | none => true | some S => S.noAny) &&
        (match U with | none => true | some C => CaptureSet.noAny C) && d.NoAnyAnn
  | _, .app _ _ => true
  | _, .proj _ _ => true
  | _, .let _ ann t u =>
      (match ann with | none => true | some U => U.noAny) && t.NoAnyAnn && u.NoAnyAnn
  | _, .box _ => true
  | _, .unbox C _ => CaptureSet.noAny C
  | _, .asc t T => t.NoAnyAnn && T.noAny
/-- No `any` in any written annotation, set or type definition of the
definitions. -/
def PDefs.NoAnyAnn : {s : Sig} → PDefs s → Bool
  | _, .typ _ S => S.noAny
  | _, .cap _ c => CaptureSet.noAny c
  | _, .trm _ o t => (match o with | none => true | some T => T.noAny) && t.NoAnyAnn
  | _, .and d e => d.NoAnyAnn && e.NoAnyAnn
end

/-! ## The size measure of partial terms

The same node count as `sizeATm` and `sizeADefs`.  Types, sets and tags do not
count. -/

mutual
/-- The node count of a partial term. -/
def sizePTm : {s : Sig} → PTm s → Nat
  | _, .path _ => 1
  | _, .lam _ t => sizePTm t + 1
  | _, .obj _ _ d => sizePDefs d + 1
  | _, .app _ _ => 1
  | _, .proj _ _ => 1
  | _, .let _ _ t u => sizePTm t + sizePTm u + 1
  | _, .box _ => 1
  | _, .unbox _ _ => 1
  | _, .asc t _ => sizePTm t + 1
/-- The node count of the definitions of a partial term. -/
def sizePDefs : {s : Sig} → PDefs s → Nat
  | _, .typ _ _ => 1
  | _, .cap _ _ => 1
  | _, .trm _ _ t => sizePTm t + 1
  | _, .and d e => sizePDefs d + sizePDefs e + 1
end

/-! ## Erasures

Each erasure maps a partial term to a partial term with some written slots
emptied.  They state that a program written with fewer annotations resolves to
the written program with those annotations erased.  `eraseDoms` empties every
lambda domain, `eraseSelf` every self shape, `eraseArgs` the domain of every
lambda in argument position, and `eraseAsc` the domain of every lambda directly
under an ascription.  `eraseG` combines the last three: the program a Scala
programmer writes where an expected type reaches. -/

/-- Erase a lambda's domain, at the head only. -/
def PTm.dropDom : {s : Sig} → PTm s → PTm s
  | _, .lam _ t => .lam none t
  | _, t => t

mutual
/-- Every lambda domain erased. -/
def PTm.eraseDoms : {s : Sig} → PTm s → PTm s
  | _, .path p => .path p
  | _, .lam _ t => .lam none t.eraseDoms
  | _, .obj S U d => .obj S U d.eraseDoms
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u => .let g ann t.eraseDoms u.eraseDoms
  | _, .box x => .box x
  | _, .unbox C x => .unbox C x
  | _, .asc t T => .asc t.eraseDoms T
/-- Every lambda domain erased, in definitions. -/
def PDefs.eraseDoms : {s : Sig} → PDefs s → PDefs s
  | _, .typ A S => .typ A S
  | _, .cap C c => .cap C c
  | _, .trm a o t => .trm a o t.eraseDoms
  | _, .and d e => .and d.eraseDoms e.eraseDoms
end

mutual
/-- Every self shape erased, with the object's set.  A literal without a self
shape has no syntax for its set, so the set goes with the shape. -/
def PTm.eraseSelf : {s : Sig} → PTm s → PTm s
  | _, .path p => .path p
  | _, .lam T t => .lam T t.eraseSelf
  | _, .obj _ _ d => .obj none none d.eraseSelf
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u => .let g ann t.eraseSelf u.eraseSelf
  | _, .box x => .box x
  | _, .unbox C x => .unbox C x
  | _, .asc t T => .asc t.eraseSelf T
/-- Every self shape erased, in definitions. -/
def PDefs.eraseSelf : {s : Sig} → PDefs s → PDefs s
  | _, .typ A S => .typ A S
  | _, .cap C c => .cap C c
  | _, .trm a o t => .trm a o t.eraseSelf
  | _, .and d e => .and d.eraseSelf e.eraseSelf
end

mutual
/-- The domain of every lambda bound by an `arg` binding erased. -/
def PTm.eraseArgs : {s : Sig} → PTm s → PTm s
  | _, .path p => .path p
  | _, .lam T t => .lam T t.eraseArgs
  | _, .obj S U d => .obj S U d.eraseArgs
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u =>
      .let g ann (if g = .arg then t.eraseArgs.dropDom else t.eraseArgs) u.eraseArgs
  | _, .box x => .box x
  | _, .unbox C x => .unbox C x
  | _, .asc t T => .asc t.eraseArgs T
/-- The domain of every lambda bound by an `arg` binding erased, in
definitions. -/
def PDefs.eraseArgs : {s : Sig} → PDefs s → PDefs s
  | _, .typ A S => .typ A S
  | _, .cap C c => .cap C c
  | _, .trm a o t => .trm a o t.eraseArgs
  | _, .and d e => .and d.eraseArgs e.eraseArgs
end

mutual
/-- The domain of every lambda directly under an ascription erased. -/
def PTm.eraseAsc : {s : Sig} → PTm s → PTm s
  | _, .path p => .path p
  | _, .lam T t => .lam T t.eraseAsc
  | _, .obj S U d => .obj S U d.eraseAsc
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let g ann t u => .let g ann t.eraseAsc u.eraseAsc
  | _, .box x => .box x
  | _, .unbox C x => .unbox C x
  | _, .asc t T => .asc t.eraseAsc.dropDom T
/-- The domain of every lambda directly under an ascription erased, in
definitions. -/
def PDefs.eraseAsc : {s : Sig} → PDefs s → PDefs s
  | _, .typ A S => .typ A S
  | _, .cap C c => .cap C c
  | _, .trm a o t => .trm a o t.eraseAsc
  | _, .and d e => .and d.eraseAsc e.eraseAsc
end

/-- Every self shape, every domain in argument position and every domain
directly under an ascription erased. -/
def PTm.eraseG {s : Sig} (p : PTm s) : PTm s := p.eraseAsc.eraseArgs.eraseSelf

/-! ## The bridges agree -/

mutual
/-- A term with every slot written is full, and `full?` gives it back. -/
theorem ATm.full?_toI : ∀ {s : Sig} (a : ATm s), a.toI.full? = some a
  | _, .path _ => rfl
  | _, .lam T t => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, Option.map_some]
  | _, .obj S U d => by simp only [ATm.toI, PTm.full?, ADefs.full?_toI d, Option.map_some]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let ann t u => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, ATm.full?_toI u]
  | _, .box _ => rfl
  | _, .unbox _ _ => rfl
  | _, .asc t T => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, Option.map_some]
/-- Definitions with every slot written are full, and `full?` gives them
back. -/
theorem ADefs.full?_toI : ∀ {s : Sig} (d : ADefs s), d.toI.full? = some d
  | _, .typ _ _ => rfl
  | _, .cap _ _ => rfl
  | _, .trm a t => by simp only [ADefs.toI, PDefs.full?, ATm.full?_toI t, Option.map_some]
  | _, .and d e => by simp only [ADefs.toI, PDefs.full?, ADefs.full?_toI d, ADefs.full?_toI e]
end

mutual
/-- A term with every slot written has its own skeleton. -/
theorem ATm.skel_toI : ∀ {s : Sig} (a : ATm s), a.toI.skel = a.skel
  | _, .path (.var _) => rfl
  | _, .lam _ t => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t]
  | _, .obj _ _ d => by simp only [ATm.toI, PTm.skel, ATm.skel, ADefs.skel_toI d]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let _ t u => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t, ATm.skel_toI u]
  | _, .box _ => rfl
  | _, .unbox _ _ => rfl
  | _, .asc t _ => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t]
/-- Definitions with every slot written have their own skeleton. -/
theorem ADefs.skel_toI : ∀ {s : Sig} (d : ADefs s), d.toI.skel = d.skel
  | _, .typ _ _ => rfl
  | _, .cap _ _ => rfl
  | _, .trm _ t => by simp only [ADefs.toI, PDefs.skel, ADefs.skel, ATm.skel_toI t]
  | _, .and d e => by
      simp only [ADefs.toI, PDefs.skel, ADefs.skel, ADefs.skel_toI d, ADefs.skel_toI e]
end

mutual
/-- A term with every slot written agrees with itself. -/
theorem ATm.fills_toI : ∀ {s : Sig} (a : ATm s), a.toI.fills a = true
  | _, .path _ => by simp only [ATm.toI, PTm.fills, decide_true]
  | _, .lam _ t => by simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ATm.fills_toI t]
  | _, .obj S _ d => by
      simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ADefs.fills_toI d S]
  | _, .app _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .let _ t u => by
      simp only [ATm.toI, PTm.fills, decide_true, ATm.fills_toI t, ATm.fills_toI u,
        Bool.and_self]
  | _, .box _ => by simp only [ATm.toI, PTm.fills, decide_true]
  | _, .unbox _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .asc t _ => by
      simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ATm.fills_toI t]
/-- Definitions with every slot written agree with themselves, against any
self shape, since they carry no written field type. -/
theorem ADefs.fills_toI : ∀ {s : Sig} (d : ADefs s) (S : Shape s), d.toI.fills S d = true
  | _, .typ _ _, _ => by simp only [ADefs.toI, PDefs.fills, decide_true, Bool.and_self]
  | _, .cap _ _, _ => by simp only [ADefs.toI, PDefs.fills, decide_true, Bool.and_self]
  | _, .trm _ t, _ => by
      simp only [ADefs.toI, PDefs.fills, decide_true, ATm.fills_toI t, Bool.and_self]
  | _, .and d e, S => by
      simp only [ADefs.toI, PDefs.fills, ADefs.fills_toI d (shapeLeft S),
        ADefs.fills_toI e (shapeRight S), Bool.and_self]
end

mutual
/-- A full partial term agrees with the term it gives. -/
theorem PTm.fills_of_full? : ∀ {s : Sig} {p : PTm s} {a : ATm s},
    p.full? = some a → p.fills a = true
  | _, .path _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true]
  | _, .lam (some _) t, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PTm.fills_of_full? ht]
  | _, .lam none _, _, h => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .obj (some S) _ d, _, h => by
      simp only [PTm.full?] at h
      cases hd : d.full? with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some e =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PDefs.fills_of_full? S hd]
  | _, .obj none _ _, _, h => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .app _ _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true, Bool.and_self]
  | _, .proj _ _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true, Bool.and_self]
  | _, .let _ _ t u, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, reduceCtorEq] at h
      | some b =>
          cases hu : u.full? with
          | none => simp only [ht, hu, reduceCtorEq] at h
          | some c =>
              simp only [ht, hu, Option.some.injEq] at h
              subst h
              simp only [PTm.fills, decide_true, PTm.fills_of_full? ht, PTm.fills_of_full? hu,
                Bool.and_self]
  | _, .box _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true]
  | _, .unbox _ _, _, h => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simp only [PTm.fills, decide_true, Bool.and_self]
  | _, .asc t _, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PTm.fills_of_full? ht]
/-- Full `PDefs` agree with the definitions they give, against any self
shape. -/
theorem PDefs.fills_of_full? : ∀ {s : Sig} {d : PDefs s} {e : ADefs s} (S : Shape s),
    d.full? = some e → d.fills S e = true
  | _, .typ _ _, _, _, h => by
      simp only [PDefs.full?, Option.some.injEq] at h
      subst h
      simp only [PDefs.fills, decide_true, Bool.and_self]
  | _, .cap _ _, _, _, h => by
      simp only [PDefs.full?, Option.some.injEq] at h
      subst h
      simp only [PDefs.fills, decide_true, Bool.and_self]
  | _, .trm _ none t, _, _, h => by
      simp only [PDefs.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PDefs.fills, decide_true, Bool.true_and, PTm.fills_of_full? ht]
  | _, .trm _ (some _) _, _, _, h => by simp only [PDefs.full?, reduceCtorEq] at h
  | _, .and d1 d2, _, S, h => by
      simp only [PDefs.full?] at h
      cases h1 : d1.full? with
      | none => simp only [h1, reduceCtorEq] at h
      | some b =>
          cases h2 : d2.full? with
          | none => simp only [h1, h2, reduceCtorEq] at h
          | some c =>
              simp only [h1, h2, Option.some.injEq] at h
              subst h
              simp only [PDefs.fills, PDefs.fills_of_full? (shapeLeft S) h1,
                PDefs.fills_of_full? (shapeRight S) h2, Bool.and_self]
end

mutual
/-- A filling has the skeleton of the partial term it fills. -/
theorem PTm.skel_of_fills : ∀ {s : Sig} {p : PTm s} {a : ATm s},
    p.fills a = true → p.skel = a.skel
  | _, .path (.var _), .path (.var _), h => by
      simp only [PTm.fills, decide_eq_true_eq] at h
      rw [h]; rfl
  | _, .lam _ t, .lam _ b, h => by
      simp only [PTm.fills, Bool.and_eq_true] at h
      simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.2]
  | _, .obj _ _ d, .obj S _ e, h => by
      simp only [PTm.fills, Bool.and_eq_true] at h
      simp only [PTm.skel, ATm.skel, PDefs.skel_of_fills S h.2]
  | _, .app _ _, .app _ _, h => by
      simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, h.2]; rfl
  | _, .proj _ _, .proj _ _, h => by
      simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, h.2]; rfl
  | _, .let _ _ t u, .let _ b c, h => by
      simp only [PTm.fills, Bool.and_eq_true] at h
      simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.1.2, PTm.skel_of_fills h.2]
  | _, .box _, .box _, h => by
      simp only [PTm.fills, decide_eq_true_eq] at h
      rw [h]; rfl
  | _, .unbox _ _, .unbox _ _, h => by
      simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.2]; rfl
  | _, .asc t _, .asc b _, h => by
      simp only [PTm.fills, Bool.and_eq_true] at h
      simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.2]
  | _, .path _, .lam _ _, h | _, .path _, .obj _ _ _, h | _, .path _, .app _ _, h
  | _, .path _, .proj _ _, h | _, .path _, .let _ _ _, h | _, .path _, .box _, h
  | _, .path _, .unbox _ _, h | _, .path _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .lam _ _, .path _, h | _, .lam _ _, .obj _ _ _, h | _, .lam _ _, .app _ _, h
  | _, .lam _ _, .proj _ _, h | _, .lam _ _, .let _ _ _, h | _, .lam _ _, .box _, h
  | _, .lam _ _, .unbox _ _, h | _, .lam _ _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .obj _ _ _, .path _, h | _, .obj _ _ _, .lam _ _, h | _, .obj _ _ _, .app _ _, h
  | _, .obj _ _ _, .proj _ _, h | _, .obj _ _ _, .let _ _ _, h | _, .obj _ _ _, .box _, h
  | _, .obj _ _ _, .unbox _ _, h | _, .obj _ _ _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .app _ _, .path _, h | _, .app _ _, .lam _ _, h | _, .app _ _, .obj _ _ _, h
  | _, .app _ _, .proj _ _, h | _, .app _ _, .let _ _ _, h | _, .app _ _, .box _, h
  | _, .app _ _, .unbox _ _, h | _, .app _ _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .proj _ _, .path _, h | _, .proj _ _, .lam _ _, h | _, .proj _ _, .obj _ _ _, h
  | _, .proj _ _, .app _ _, h | _, .proj _ _, .let _ _ _, h | _, .proj _ _, .box _, h
  | _, .proj _ _, .unbox _ _, h | _, .proj _ _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .let _ _ _ _, .path _, h | _, .let _ _ _ _, .lam _ _, h
  | _, .let _ _ _ _, .obj _ _ _, h | _, .let _ _ _ _, .app _ _, h
  | _, .let _ _ _ _, .proj _ _, h | _, .let _ _ _ _, .box _, h
  | _, .let _ _ _ _, .unbox _ _, h | _, .let _ _ _ _, .asc _ _, h => by
      simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .box _, .path _, h | _, .box _, .lam _ _, h | _, .box _, .obj _ _ _, h
  | _, .box _, .app _ _, h | _, .box _, .proj _ _, h | _, .box _, .let _ _ _, h
  | _, .box _, .unbox _ _, h | _, .box _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .unbox _ _, .path _, h | _, .unbox _ _, .lam _ _, h | _, .unbox _ _, .obj _ _ _, h
  | _, .unbox _ _, .app _ _, h | _, .unbox _ _, .proj _ _, h | _, .unbox _ _, .let _ _ _, h
  | _, .unbox _ _, .box _, h | _, .unbox _ _, .asc _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .asc _ _, .path _, h | _, .asc _ _, .lam _ _, h | _, .asc _ _, .obj _ _ _, h
  | _, .asc _ _, .app _ _, h | _, .asc _ _, .proj _ _, h | _, .asc _ _, .let _ _ _, h
  | _, .asc _ _, .box _, h | _, .asc _ _, .unbox _ _, h => by simp only [PTm.fills, Bool.false_eq_true] at h
/-- Filled definitions have the skeleton of the `PDefs` they fill, against
any self shape. -/
theorem PDefs.skel_of_fills : ∀ {s : Sig} {d : PDefs s} {e : ADefs s} (S : Shape s),
    d.fills S e = true → d.skel = e.skel
  | _, .typ _ _, .typ _ _, _, h => by
      simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1]; rfl
  | _, .cap _ _, .cap _ _, _, h => by
      simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1]; rfl
  | _, .trm _ _ t, .trm _ b, _, h => by
      simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [PDefs.skel, ADefs.skel, h.1.1, PTm.skel_of_fills h.2]
  | _, .and d1 d2, .and e1 e2, S, h => by
      simp only [PDefs.fills, Bool.and_eq_true] at h
      simp only [PDefs.skel, ADefs.skel, PDefs.skel_of_fills (shapeLeft S) h.1,
        PDefs.skel_of_fills (shapeRight S) h.2]
  | _, .typ _ _, .cap _ _, _, h | _, .typ _ _, .trm _ _, _, h | _, .typ _ _, .and _ _, _, h
  | _, .cap _ _, .typ _ _, _, h | _, .cap _ _, .trm _ _, _, h | _, .cap _ _, .and _ _, _, h
  | _, .trm _ _ _, .typ _ _, _, h | _, .trm _ _ _, .cap _ _, _, h
  | _, .trm _ _ _, .and _ _, _, h | _, .and _ _, .typ _ _, _, h
  | _, .and _ _, .cap _ _, _, h | _, .and _ _, .trm _ _, _, h => by
      simp only [PDefs.fills, Bool.false_eq_true] at h
end

/-- A full partial term has the skeleton of the term it gives. -/
theorem PTm.skel_of_full? {s : Sig} {p : PTm s} {a : ATm s} (h : p.full? = some a) :
    p.skel = a.skel :=
  PTm.skel_of_fills (PTm.fills_of_full? h)

mutual
/-- Writing every slot keeps the absence of `any`. -/
theorem ATm.NoAnyAnn_toI : ∀ {s : Sig} (a : ATm s), a.toI.NoAnyAnn = a.NoAnyAnn
  | _, .path _ => rfl
  | _, .lam _ t => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t]
  | _, .obj _ _ d => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ADefs.NoAnyAnn_toI d]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let _ t u => by
      simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t, ATm.NoAnyAnn_toI u]
  | _, .box _ => rfl
  | _, .unbox _ _ => rfl
  | _, .asc t _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t]
/-- Writing every slot keeps the absence of `any`, in definitions. -/
theorem ADefs.NoAnyAnn_toI : ∀ {s : Sig} (d : ADefs s), d.toI.NoAnyAnn = d.NoAnyAnn
  | _, .typ _ _ => rfl
  | _, .cap _ _ => rfl
  | _, .trm _ t => by
      simp only [ADefs.toI, PDefs.NoAnyAnn, ADefs.NoAnyAnn, ATm.NoAnyAnn_toI t, Bool.true_and]
  | _, .and d e => by
      simp only [ADefs.toI, PDefs.NoAnyAnn, ADefs.NoAnyAnn, ADefs.NoAnyAnn_toI d,
        ADefs.NoAnyAnn_toI e]
end

mutual
/-- A full partial term with no `any` gives a term with no `any`. -/
theorem PTm.NoAnyAnn_of_full? : ∀ {s : Sig} {p : PTm s} {a : ATm s},
    p.full? = some a → p.NoAnyAnn = true → a.NoAnyAnn = true
  | _, .path _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; rfl
  | _, .lam (some _) t, _, h, hn => by
      simp only [PTm.full?] at h
      simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hn
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [ATm.NoAnyAnn, hn.1, PTm.NoAnyAnn_of_full? ht hn.2, Bool.and_self]
  | _, .lam none _, _, h, _ => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .obj (some _) _ d, _, h, hn => by
      simp only [PTm.full?] at h
      simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hn
      cases hd : d.full? with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some e =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [ATm.NoAnyAnn, hn.1.1, hn.1.2, PDefs.NoAnyAnn_of_full? hd hn.2,
            Bool.and_self]
  | _, .obj none _ _, _, h, _ => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .app _ _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; rfl
  | _, .proj _ _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; rfl
  | _, .let _ _ t u, _, h, hn => by
      simp only [PTm.full?] at h
      simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hn
      cases ht : t.full? with
      | none => simp only [ht, reduceCtorEq] at h
      | some b =>
          cases hu : u.full? with
          | none => simp only [ht, hu, reduceCtorEq] at h
          | some c =>
              simp only [ht, hu, Option.some.injEq] at h
              subst h
              simp only [ATm.NoAnyAnn, hn.1.1, PTm.NoAnyAnn_of_full? ht hn.1.2,
                PTm.NoAnyAnn_of_full? hu hn.2, Bool.and_self]
  | _, .box _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; rfl
  | _, .unbox _ _, _, h, hn => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h
      simpa only [PTm.NoAnyAnn, ATm.NoAnyAnn] using hn
  | _, .asc t _, _, h, hn => by
      simp only [PTm.full?] at h
      simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hn
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [ATm.NoAnyAnn, hn.2, PTm.NoAnyAnn_of_full? ht hn.1, Bool.and_self]
/-- Full `PDefs` with no `any` give definitions with no `any`. -/
theorem PDefs.NoAnyAnn_of_full? : ∀ {s : Sig} {d : PDefs s} {e : ADefs s},
    d.full? = some e → d.NoAnyAnn = true → e.NoAnyAnn = true
  | _, .typ _ _, _, h, hn => by
      simp only [PDefs.full?, Option.some.injEq] at h
      subst h
      simpa only [PDefs.NoAnyAnn, ADefs.NoAnyAnn] using hn
  | _, .cap _ _, _, h, hn => by
      simp only [PDefs.full?, Option.some.injEq] at h
      subst h
      simpa only [PDefs.NoAnyAnn, ADefs.NoAnyAnn] using hn
  | _, .trm _ none t, _, h, hn => by
      simp only [PDefs.full?] at h
      simp only [PDefs.NoAnyAnn, Bool.true_and] at hn
      cases ht : t.full? with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some b =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [ADefs.NoAnyAnn, PTm.NoAnyAnn_of_full? ht hn]
  | _, .trm _ (some _) _, _, h, _ => by simp only [PDefs.full?, reduceCtorEq] at h
  | _, .and d1 d2, _, h, hn => by
      simp only [PDefs.full?] at h
      simp only [PDefs.NoAnyAnn, Bool.and_eq_true] at hn
      cases h1 : d1.full? with
      | none => simp only [h1, reduceCtorEq] at h
      | some b =>
          cases h2 : d2.full? with
          | none => simp only [h1, h2, reduceCtorEq] at h
          | some c =>
              simp only [h1, h2, Option.some.injEq] at h
              subst h
              simp only [ADefs.NoAnyAnn, PDefs.NoAnyAnn_of_full? h1 hn.1,
                PDefs.NoAnyAnn_of_full? h2 hn.2, Bool.and_self]
end

mutual
/-- `toI` keeps the node count. -/
theorem sizePTm_toI : ∀ {s : Sig} (a : ATm s), sizePTm a.toI = sizeATm a
  | _, .path _ => rfl
  | _, .lam _ t => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t]
  | _, .obj _ _ d => by simp only [ATm.toI, sizePTm, sizeATm, sizePDefs_toI d]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let _ t u => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t, sizePTm_toI u]
  | _, .box _ => rfl
  | _, .unbox _ _ => rfl
  | _, .asc t _ => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t]
/-- `toI` keeps the node count of definitions. -/
theorem sizePDefs_toI : ∀ {s : Sig} (d : ADefs s), sizePDefs d.toI = sizeADefs d
  | _, .typ _ _ => rfl
  | _, .cap _ _ => rfl
  | _, .trm _ t => by simp only [ADefs.toI, sizePDefs, sizeADefs, sizePTm_toI t]
  | _, .and d e => by simp only [ADefs.toI, sizePDefs, sizeADefs, sizePDefs_toI d, sizePDefs_toI e]
end

/-! ## Dependencies on the self

A field of a literal without a self shape is typed once the fields it reads
off the self are.  `PTm.deps` reads them off a right-hand side.  `vs` are the
variables that stand for the self: the self itself, and every variable a `let`
without a type binds to one of them.  A projection `w.a` with `w` among them
depends on `a`.  Any other use of one of them, as a value, a function, an
argument, a box, an unboxing or a term bound at a written type, sets the flag,
since it needs the whole self shape.  A type `x.A` or a set `{x.C}` in an
annotation is no dependency, since type and capture members are known at
once. -/

/-- The bound term of a `let` makes its variable stand for the self: no
written type, and a variable of `vs`. -/
def PTm.isAlias {s : Sig} (vs : List (BVar s .var)) : Option (Ty s) → PTm s → Bool
  | none, .path (.var y) => vs.contains y
  | _, _ => false

mutual
/-- The labels a term projects off the self, in term order, and whether it
uses the self any other way. -/
def PTm.deps : {s : Sig} → PTm s → List (BVar s .var) → List Label × Bool
  | _, .path (.var y), vs => ([], vs.contains y)
  | _, .lam _ t, vs => t.deps (vs.map .there)
  | _, .obj _ _ d, vs => d.deps (vs.map .there)
  | _, .app x y, vs => ([], vs.contains x || vs.contains y)
  | _, .proj x a, vs => (if vs.contains x then [a] else [], false)
  | _, .let _ ann t u, vs =>
      if PTm.isAlias vs ann t then u.deps (.here :: vs.map .there)
      else
        match t.deps vs, u.deps (vs.map .there) with
        | (l1, b1), (l2, b2) => (l1 ++ l2, b1 || b2)
  | _, .box x, vs => ([], vs.contains x)
  | _, .unbox _ x, vs => ([], vs.contains x)
  | _, .asc t _, vs => t.deps vs
/-- The labels a definition list projects off the self, and the flag. -/
def PDefs.deps : {s : Sig} → PDefs s → List (BVar s .var) → List Label × Bool
  | _, .typ _ _, _ => ([], false)
  | _, .cap _ _, _ => ([], false)
  | _, .trm _ _ t, vs => t.deps vs
  | _, .and d e, vs =>
      match d.deps vs, e.deps vs with
      | (l1, b1), (l2, b2) => (l1 ++ l2, b1 || b2)
end

end CapturesFrontend
