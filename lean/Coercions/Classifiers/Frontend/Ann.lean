import Coercions.Classifiers.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms with scopes and existential answers

`ATm` is the version's `DotMNF.Tm` (`lean/Coercions/Classifiers/DotMNF/Syntax.lean`)
with the annotations a front end needs and the calculus does not keep.

- The self shape of an object literal.  `HasTy.obj` types the definitions
  against a context entry that already holds it
  (`lean/Coercions/Classifiers/DotMNF/Typing.lean`), so it cannot be
  synthesized from the definitions.  The object's capture set is not
  written.  The typer synthesizes it.
- The optional result answer of a `let`.  It may be existential.
- The set of an unboxing, optional.  An unboxing with no set leaves the set
  to the typer, which reads it off the box type.
- The ascription `(t : T)`, a checking point.  The calculus has no such
  term and erasure drops it.

Every binder the calculus has and the program does not write is in the
signature.  A lambda's domain lives under the arrow's own capture binder, at
`Sig.dom s`.  Its body lives under the body root, the arrow binder and the
parameter, at `Sig.body s`.  The definitions of an object live under the
class root and the self.  The self shape lives under the self alone, as
`HasTy.obj` reads it.  An unpacking `letex` opens a capture binder for the
witness and a term binder for the payload.  A `let` stays a `let`.  Whether
it unpacks is the typer's choice, made from the answer of the bound term.

`ATm.erase` lands in `DotMNF.Tm`.  Application, projection, boxing and
unboxing take bare variables, so monadic normal form holds by construction.

`ATm.skel` is the skeleton of a term, the part a program and its
elaboration must agree on.  It forgets type annotations, capture sets,
capture binders, the box former, the set of an unboxing and ascriptions.  It
numbers a term variable among the term binders only.  It does not tell a
`let` from a `letex`, and it inlines either when the bound skeleton is a
variable.  So the `letex` the typer makes of a `let`, with its body renamed
past the new witness binder, has the skeleton of the `let`
(`ATm.skel_rename_succLift`).  `Skel` has decidable equality, so two
skeletons are compared by `decide`.

Nothing of this module is part of the metatheory and no definition here lives
in a namespace of the version.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs)

/-! ## The syntax -/

mutual
/-- Terms of DOT-MNF with scopes and the front end's annotations. -/
inductive ATm : Sig → Type where
  /-- A path, which in this calculus is a variable. -/
  | path : Path s → ATm s
  /-- `λ(x : T). t`: the domain under the arrow's own capture binder, the
  body under the body root, the arrow binder and the parameter. -/
  | lam : Ty (Sig.dom s) → ATm (Sig.body s) → ATm s
  /-- `ν(x : S. d)`: the self shape under the self binder, the definitions
  under the class root and the self. -/
  | obj : Shape (s,x) → ADefs ((s,c),x) → ATm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → ATm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → ATm s
  /-- `let x (: E)? = t in u`, the result answer optional. -/
  | «let» : Option (ETy s) → ATm s → ATm (s,x) → ATm s
  /-- `let ⟨c, x⟩ = t in u`, a written unpacking: the witness binder, then
  the payload. -/
  | letex : ATm s → ATm ((s,c),x) → ATm s
  /-- `□ x`, a box value. -/
  | box : BVar s .var → ATm s
  /-- `C ⊸ x`, an unboxing.  With no set the typer reads it off the box
  type. -/
  | unbox : Option (CaptureSet s) → BVar s .var → ATm s
  /-- `(t : T)`, a checking point.  Erased. -/
  | asc : ATm s → Ty s → ATm s
/-- Definitions of an annotated object literal. -/
inductive ADefs : Sig → Type where
  /-- `{type A = S}`. -/
  | typ : Label → Shape s → ADefs s
  /-- `{C^ = c}`, a capture member definition. -/
  | cap : Label → CaptureSet s → ADefs s
  /-- `{a = t}`. -/
  | trm : Label → ATm s → ADefs s
  /-- `d ∧ e`. -/
  | and : ADefs s → ADefs s → ADefs s
end

deriving instance DecidableEq for ATm, ADefs

/-! ## Erasure to the frozen syntax

The annotations and the ascriptions are dropped.  An unboxing with no set
erases with the empty set.  A `let` erases to a `let`.  This is a function
for comparisons with the version's terms, not the bridge to a derivation:
the typer returns the term it typed. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase {s : Sig} (t : ATm s) : Tm s :=
  match t with
  | .path p => .path p
  | .lam T t => .val (.lam T t.erase)
  | .obj _ d => .val (.obj d.erase)
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let _ t u => .let t.erase u.erase
  | .letex t u => .letex t.erase u.erase
  | .box x => .val (.box x)
  | .unbox C x => .unbox (C.getD []) x
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

The clauses mirror `DotMNF.Tm.rename`, `DotMNF.Value.rename` and
`DotMNF.Defs.rename`, with the annotations renamed at the signature they
live in.  A domain lives under one capture binder and is renamed with the
renaming lifted once.  A self shape lives under the self and is renamed with
the renaming lifted once.  The answer of a `let` and the set of an unboxing
live outside every binder of the term. -/

mutual
/-- Rename the free variables of an annotated term. -/
def ATm.rename {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2) : ATm s2 :=
  match t with
  | .path p => .path (p.rename ρ)
  | .lam T t => .lam (T.rename ρ.lift) (t.rename ρ.lift.lift.lift)
  | .obj S d => .obj (S.rename ρ.lift) (d.rename ρ.lift.lift)
  | .app x y => .app (ρ.var x) (ρ.var y)
  | .proj x a => .proj (ρ.var x) a
  | .let ann t u => .let (ann.map (fun E => E.rename ρ)) (t.rename ρ) (u.rename ρ.lift)
  | .letex t u => .letex (t.rename ρ) (u.rename ρ.lift.lift)
  | .box x => .box (ρ.var x)
  | .unbox C x => .unbox (C.map (fun C => CaptureSet.rename C ρ)) (ρ.var x)
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
      show Tm.val (.lam (T.rename ρ.lift) (t.rename ρ.lift.lift.lift).erase) = _
      rw [ATm.erase_rename t ρ.lift.lift.lift]; rfl
  | _, _, .obj _ d, ρ => by
      show Tm.val (.obj (d.rename ρ.lift.lift).erase) = _
      rw [ADefs.erase_rename d ρ.lift.lift]; rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .proj _ _, _ => rfl
  | _, _, .let _ t u, ρ => by
      show Tm.let (t.rename ρ).erase (u.rename ρ.lift).erase = _
      rw [ATm.erase_rename t ρ, ATm.erase_rename u ρ.lift]; rfl
  | _, _, .letex t u, ρ => by
      show Tm.letex (t.rename ρ).erase (u.rename ρ.lift.lift).erase = _
      rw [ATm.erase_rename t ρ, ATm.erase_rename u ρ.lift.lift]; rfl
  | _, _, .box _, _ => rfl
  | _, _, .unbox C _, _ => by cases C <;> rfl
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
  | .obj _ d => sizeADefs d + 1
  | .app _ _ => 1
  | .proj _ _ => 1
  | .let _ t u => sizeATm t + sizeATm u + 1
  | .letex t u => sizeATm t + sizeATm u + 1
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

A skeleton keeps the binding structure of the term binders, the term
variables as positions among those binders, the labels of projections and
definitions, and nothing else.  Capture binders are not in a skeleton. -/

mutual
/-- The skeleton of a term. -/
inductive Skel : Type where
  /-- A term variable, by position among the term binders. -/
  | var (i : Nat)
  /-- A function, one term binder, the parameter. -/
  | lam (t : Skel)
  /-- An object literal, one term binder, the self. -/
  | obj (d : SkelDefs)
  /-- An application. -/
  | app (i j : Nat)
  /-- A projection. -/
  | proj (i : Nat) (ℓ : Label)
  /-- A `let` or an unpacking, one term binder over the body. -/
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

/-- One for a term binder, zero for a capture binder. -/
def Kind.termCount : Kind → Nat
  | .var => 1
  | .cap => 0

/-- The position of a bound variable among the term binders.  A capture
binder between the variable and its own binder does not count. -/
def varPos {s : Sig} {k : Kind} (x : BVar s k) : Nat :=
  match x with
  | .here => 0
  | @BVar.there _ _ k0 y => varPos y + Kind.termCount k0
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
/-- The skeleton of a term: annotations, capture sets, capture binders,
boxes, the set of an unboxing and ascriptions forgotten, a `letex` read as a
`let`, and a `let` of a variable inlined. -/
def ATm.skel {s : Sig} (t : ATm s) : Skel :=
  match t with
  | .path (.var x) => .var (varPos x)
  | .lam _ t => .lam t.skel
  | .obj _ d => .obj d.skel
  | .app x y => .app (varPos x) (varPos y)
  | .proj x a => .proj (varPos x) a
  | .let _ t u => Skel.mkLet t.skel u.skel
  | .letex t u => Skel.mkLet t.skel u.skel
  | .box x => .var (varPos x)
  | .unbox _ x => .var (varPos x)
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

/-! ## Skeletons do not see capture binders

A renaming that keeps the position of every term variable among the term
binders keeps the skeleton.  Weakening past a capture binder is such a
renaming, and so is every lift of one.  The instance `letex` insertion needs
is the body of a `let`, renamed past the new witness binder under the
payload binder. -/

/-- The renaming keeps the position of every term variable among the term
binders. -/
def KeepsVarPos {s1 s2 : Sig} (ρ : Rename s1 s2) : Prop :=
  ∀ x : BVar s1 .var, varPos (ρ.var x) = varPos x

/-- A lift of a renaming that keeps positions keeps them, at either kind of
binder. -/
theorem KeepsVarPos.lift {s1 s2 : Sig} {ρ : Rename s1 s2} (h : KeepsVarPos ρ) {k : Kind} :
    KeepsVarPos (ρ.lift (k := k)) := by
  intro x
  cases x with
  | here => rfl
  | there y =>
      show varPos (ρ.var y) + Kind.termCount k = varPos y + Kind.termCount k
      rw [h y]

/-- Weakening past a capture binder keeps positions. -/
theorem KeepsVarPos.succCap {s : Sig} : KeepsVarPos (Rename.succ (s := s) (k := .cap)) :=
  fun _ => rfl

mutual
/-- A renaming that keeps positions keeps the skeleton of a term. -/
theorem ATm.skel_rename : ∀ {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2),
    KeepsVarPos ρ → (t.rename ρ).skel = t.skel
  | _, _, .path (.var x), _, h => by
      show Skel.var (varPos _) = Skel.var (varPos x)
      rw [h x]
  | _, _, .lam _ t, ρ, h => by
      show Skel.lam (t.rename ρ.lift.lift.lift).skel = Skel.lam t.skel
      rw [ATm.skel_rename t _ h.lift.lift.lift]
  | _, _, .obj _ d, ρ, h => by
      show Skel.obj (d.rename ρ.lift.lift).skel = Skel.obj d.skel
      rw [ADefs.skel_rename d _ h.lift.lift]
  | _, _, .app x y, _, h => by
      show Skel.app (varPos _) (varPos _) = Skel.app (varPos x) (varPos y)
      rw [h x, h y]
  | _, _, .proj x a, _, h => by
      show Skel.proj (varPos _) a = Skel.proj (varPos x) a
      rw [h x]
  | _, _, .let _ t u, ρ, h => by
      show Skel.mkLet (t.rename ρ).skel (u.rename ρ.lift).skel = Skel.mkLet t.skel u.skel
      rw [ATm.skel_rename t ρ h, ATm.skel_rename u _ h.lift]
  | _, _, .letex t u, ρ, h => by
      show Skel.mkLet (t.rename ρ).skel (u.rename ρ.lift.lift).skel = Skel.mkLet t.skel u.skel
      rw [ATm.skel_rename t ρ h, ATm.skel_rename u _ h.lift.lift]
  | _, _, .box x, _, h => by
      show Skel.var (varPos _) = Skel.var (varPos x)
      rw [h x]
  | _, _, .unbox _ x, _, h => by
      show Skel.var (varPos _) = Skel.var (varPos x)
      rw [h x]
  | _, _, .asc t _, ρ, h => by
      show (t.rename ρ).skel = t.skel
      rw [ATm.skel_rename t ρ h]
/-- A renaming that keeps positions keeps the skeleton of definitions. -/
theorem ADefs.skel_rename : ∀ {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2),
    KeepsVarPos ρ → (d.rename ρ).skel = d.skel
  | _, _, .typ _ _, _, _ => rfl
  | _, _, .cap _ _, _, _ => rfl
  | _, _, .trm a t, ρ, h => by
      show SkelDefs.trm a (t.rename ρ).skel = SkelDefs.trm a t.skel
      rw [ATm.skel_rename t ρ h]
  | _, _, .and d e, ρ, h => by
      show SkelDefs.and (d.rename ρ).skel (e.rename ρ).skel = SkelDefs.and d.skel e.skel
      rw [ADefs.skel_rename d ρ h, ADefs.skel_rename e ρ h]
end

/-- The body of a `let`, renamed past a new capture binder under its own
term binder, keeps its skeleton.  This is the renaming that turns
`let x = t in u` into `let ⟨c, x⟩ = t in u`. -/
theorem ATm.skel_rename_succLift {s : Sig} (t : ATm (s,x)) :
    ATm.skel (t.rename (Rename.succ (k := .cap)).lift) = ATm.skel t :=
  ATm.skel_rename t _ KeepsVarPos.succCap.lift

/-- So the unpacking made of a `let` has the skeleton of the `let`. -/
theorem ATm.skel_letex_of_let {s : Sig} (ann : Option (ETy s)) (t : ATm s) (u : ATm (s,x)) :
    ATm.skel (.letex t (u.rename (Rename.succ (k := .cap)).lift)) = ATm.skel (.let ann t u) := by
  show Skel.mkLet t.skel (u.rename _).skel = Skel.mkLet t.skel u.skel
  rw [ATm.skel_rename_succLift u]

/-! ## No `any` in an annotation

`NoAnyAnn` says that no annotation, capture set or type definition of an
annotated term holds the atom `any`.  The resolver keeps every `any` the
program writes, for the typer to read at the context it builds, and adds
none of its own (`resolve_noAny` of `Resolve.lean`). -/

mutual
/-- No `any` in any annotation, set or type definition of the term. -/
def ATm.NoAnyAnn {s : Sig} (t : ATm s) : Bool :=
  match t with
  | .path _ => true
  | .lam T t => T.noAny && t.NoAnyAnn
  | .obj S d => S.noAny && d.NoAnyAnn
  | .app _ _ => true
  | .proj _ _ => true
  | .let ann t u =>
      (match ann with | none => true | some E => E.noAny) && t.NoAnyAnn && u.NoAnyAnn
  | .letex t u => t.NoAnyAnn && u.NoAnyAnn
  | .box _ => true
  | .unbox C _ => (match C with | none => true | some C => CaptureSet.noAny C)
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

/-! ## Sanity -/

/-- `⊤` as a pure type. -/
private abbrev pTop {s : Sig} : Ty s := .capt [] .top

/-- A lambda's parameter is position zero in its body.  The body root and
the arrow binder are not counted. -/
example : (ATm.lam pTop (.path (.var .here)) : ATm []).skel = .lam (.var 0) := by decide

/-- A binding inserted for a box has the skeleton of the plain application:
`λ(x). λ(y). let y' = □ y in x y'` against `λ(x). λ(y). x y`.  Between `x`
and `y` sit the body root and the arrow binder of the inner lambda, and
the skeleton does not count them. -/
example :
    (ATm.lam pTop (.lam pTop
      (.let none (.box .here) (.app (.there (.there (.there (.there .here)))) .here))) :
        ATm []).skel =
    (ATm.lam pTop (.lam pTop
      (.app (.there (.there (.there .here))) .here)) : ATm []).skel := by decide

/-- An object's self is position zero in its definitions.  The class root
is not counted. -/
example :
    (ATm.obj .top (.trm (.trm 0) (.path (.var .here))) : ATm []).skel =
      .obj (.trm (.trm 0) (.var 0)) := by decide

/-- A `let` of a term that is not a variable stays, and so does a `letex`. -/
example :
    (ATm.lam pTop (.let none (.app .here .here) (.path (.var .here))) : ATm []).skel =
      .lam (.let (.app 0 0) (.var 0)) := by decide

example :
    (ATm.lam pTop (.letex (.app .here .here) (.path (.var .here))) : ATm []).skel =
      .lam (.let (.app 0 0) (.var 0)) := by decide

/-- An ascription and an unboxing are forgotten, with or without a set. -/
example :
    (ATm.lam pTop (.asc (.unbox none .here) pTop) : ATm []).skel = .lam (.var 0) := by decide

example :
    (ATm.lam pTop (.unbox (some []) .here) : ATm []).skel = .lam (.var 0) := by decide

/-- An unboxing with no set erases with the empty set. -/
example : (ATm.unbox none .here : ATm [.var]).erase = .unbox [] .here := by decide

end ClassifiersFrontend
