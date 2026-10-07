import Coercions.Captures.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms with capture sets

`ATm` is the version's `DotMNF.Tm` (`lean/Coercions/Captures/DotMNF/Syntax.lean`)
with the annotations a front end needs and the calculus does not keep.

- The self shape of an object literal, and the object's own capture set when
  the program writes one.  `HasTy.obj` types the definitions of a literal
  against a context entry that already holds both
  (`lean/Coercions/Captures/DotMNF/Typing.lean`), so neither can be
  synthesized from the definitions.  A literal with no written set leaves
  the set to the typer.
- The optional result type of a `let`.
- The ascription `(t : T)`, a checking point for box inference.  The
  calculus has no such term and erasure drops it.

The box value `□ x` and the unboxing `C ⊸ x` are the calculus's own and are
kept as they are.  `ATm.erase` lands in `DotMNF.Tm`.  Application,
projection, boxing and unboxing take bare variables, so monadic normal form
holds by construction.

`ATm.skel` is the skeleton of a term, the part a program and its
elaboration must agree on.  It forgets type annotations, capture sets, the
box former, the set of an unboxing and ascriptions.  It inlines a `let`
whose bound term has a variable as its skeleton, so that a binding inserted
for a box, `let y' = □ y in x y'`, has the skeleton of `x y`.  `Skel` has
decidable equality, so two skeletons are compared by `decide`.

Nothing of this module is part of the metatheory and no definition here lives
in a namespace of the version.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs)

/-! ## The syntax -/

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

/-! ## Erasure to the frozen syntax

The annotations and the ascriptions are dropped and nothing else changes.
This is the only bridge from the front end's term syntax to `DotMNF.Tm`. -/

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

The clauses mirror `DotMNF.Tm.rename` and `DotMNF.Defs.rename`, with the
annotations renamed at the signature they live in.  The self shape of a
literal lives under the self binder, so it is renamed with the lifted
renaming.  The object's own set and the type of a `let` live outside the
binder, so they are renamed with the renaming itself. -/

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

/-! ## The size measure

The node count of a term, which a typer recursing on the syntax can use.
Types and capture sets do not count.  Both functions are at least one
everywhere. -/

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

A skeleton keeps the binding structure, the variables as de Bruijn
positions across both kinds of binder, the labels of projections and
definitions, and nothing else. -/

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
/-- The skeleton of a definition list.  A capture member definition sits at
a type label and its value is a set, so its skeleton is that of a type
definition. -/
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

/-- The position after replacing the variable at position `k` by the
outer position `j`.  Positions below `k` are bound inside and stay, `k`
itself becomes `j` shifted past the `k` inner binders, and positions above
`k` lose the binder that was removed. -/
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
/-- The skeleton of a term: annotations, capture sets, boxes, the set of an
unboxing and ascriptions forgotten, and a `let` of a variable inlined. -/
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

/-! ## No `any` in an annotation

`NoAnyAnn` says that no annotation, capture set or type definition of an
annotated term holds the atom `any`.  The resolver emits only such terms
(`resolve_noAny` of `Resolve.lean`), so the typer never sees `any`. -/

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

/-! ## Sanity

A binding inserted for a box has the skeleton of the plain application:
`λ(x). λ(y). let y' = □ y in x y'` against `λ(x). λ(y). x y`. -/

example :
    (ATm.lam (.capt [] .top) (.lam (.capt [] .top)
      (.let none (.box .here) (.app (.there (.there .here)) .here))) : ATm []).skel =
    (ATm.lam (.capt [] .top) (.lam (.capt [] .top)
      (.app (.there .here) .here)) : ATm []).skel := by decide

/-- A `let` of a term that is not a variable stays. -/
example :
    (ATm.lam (.capt [] .top) (.let none (.app .here .here) (.path (.var .here))) : ATm []).skel =
      .lam (.let (.app 0 0) (.var 0)) := by decide

/-- An ascription and an unboxing are forgotten. -/
example :
    (ATm.lam (.capt [] .top) (.asc (.unbox [] .here) (.capt [] .top)) : ATm []).skel =
      .lam (.var 0) := by decide

end CapturesFrontend
