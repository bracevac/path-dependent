import Coercions.Classifiers.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms

`ATm` is the version's `DotMNF.Tm` (`lean/Coercions/Classifiers/DotMNF/Syntax.lean`)
with the annotations a front end needs and the calculus does not keep.

- The self shape of an object literal.  `HasTy.obj` types the definitions
  against a context entry that already holds it, so it cannot be synthesized
  from the definitions.  The object's capture set is not written.  The typer
  synthesizes it.
- The optional result answer of a `let`, which may be existential.
- The optional set of an unboxing.  Without it the typer reads the set off
  the box type.
- The ascription `(t : T)`, a checking point.  Erasure drops it.

Every binder the calculus has and the program does not write is in the
signature.  A lambda's domain lives at `Sig.dom s`, under the arrow's own
capture binder.  Its body lives at `Sig.body s`, under the body root, the
arrow binder and the parameter.  The definitions of an object live under the
class root and the self.  The self shape lives under the self alone.  An
unpacking `letex` opens a capture binder for the witness and a term binder
for the payload.  A `let` stays a `let`, and the typer decides from the
bound term's answer whether it unpacks.

`ATm.erase` lands in `DotMNF.Tm`.  Application, projection, boxing and
unboxing take bare variables, so monadic normal form holds by construction.

`ATm.skel` is the part of a term that a program and its elaboration must
agree on.  It forgets type annotations, capture sets, capture binders, the
box former, the set of an unboxing and ascriptions.  It numbers a term
variable among the term binders only.  It does not tell a `let` from a
`letex`, and it inlines either when the bound skeleton is a variable.  So the
`letex` the typer makes of a `let` has the skeleton of the `let`
(`ATm.skel_rename_succLift`).  `Skel` has decidable equality.

A partial term, `PTm`, is an `ATm` whose slots may be empty: a lambda's domain,
the self shape of a literal, and the type written on a term member.  The
resolver produces it and the elaborator fills the empty slots.  `ATm` stays the
elaborated term, since the typer and every theorem about it read every slot.
`PTm.full?` and `ATm.toI` translate between the two, `PTm.fills` says that an
elaborated term agrees with the slots the programmer wrote, and `PTm.skel`
gives a partial term the skeleton of each of its fillings.

Nothing here belongs to the metatheory.
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
  /-- `λ(x : T). t`. -/
  | lam : Ty (Sig.dom s) → ATm (Sig.body s) → ATm s
  /-- `ν(x : S. d)`. -/
  | obj : Shape (s,x) → ADefs ((s,c),x) → ATm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → ATm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → ATm s
  /-- `let x (: E)? = t in u`, the result answer optional. -/
  | «let» : Option (ETy s) → ATm s → ATm (s,x) → ATm s
  /-- `let ⟨c, x⟩ = t in u`, a written unpacking. -/
  | letex : ATm s → ATm ((s,c),x) → ATm s
  /-- `□ x`, a box value. -/
  | box : BVar s .var → ATm s
  /-- `C ⊸ x`, an unboxing.  Without a set the typer reads it off the box type. -/
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

/-! ## Erasure

Erasure drops annotations and ascriptions.  An unboxing without a set erases
with the empty set. -/

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

The clauses mirror `DotMNF.Tm.rename`.  Annotations are renamed at the
signature they live in.  A domain and a self shape each sit under one binder,
so they take the lifted renaming.  The answer of a `let` and the set of an
unboxing sit outside every binder of the term. -/

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

The node count of a term.  Types and capture sets do not count. -/

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

A skeleton keeps the term binders, the term variables as positions among
them, and the labels of projections and definitions.  Nothing else. -/

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

/-- The position after replacing the variable at position `k` by the outer
position `j`.  Positions below `k` stay, `k` becomes `j + k`, and positions
above `k` lose the removed binder. -/
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
/-- The skeleton of a term.  A `letex` reads as a `let`, and a `let` of a
variable is inlined. -/
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
renaming, and so is every lift of one. -/

/-- The renaming keeps the position of every term variable among the term
binders. -/
def KeepsVarPos {s1 s2 : Sig} (ρ : Rename s1 s2) : Prop :=
  ∀ x : BVar s1 .var, varPos (ρ.var x) = varPos x

/-- A lift of a position-keeping renaming keeps positions. -/
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

/-- The body of a `let`, renamed past a new capture binder, keeps its
skeleton.  This is the renaming that turns `let x = t in u` into
`let ⟨c, x⟩ = t in u`. -/
theorem ATm.skel_rename_succLift {s : Sig} (t : ATm (s,x)) :
    ATm.skel (t.rename (Rename.succ (k := .cap)).lift) = ATm.skel t :=
  ATm.skel_rename t _ KeepsVarPos.succCap.lift

/-- So the unpacking made of a `let` has the skeleton of the `let`. -/
theorem ATm.skel_letex_of_let {s : Sig} (ann : Option (ETy s)) (t : ATm s) (u : ATm (s,x)) :
    ATm.skel (.letex t (u.rename (Rename.succ (k := .cap)).lift)) = ATm.skel (.let ann t u) := by
  show Skel.mkLet t.skel (u.rename _).skel = Skel.mkLet t.skel u.skel
  rw [ATm.skel_rename_succLift u]

/-! ## No `any` in an annotation

`NoAnyAnn` says that no annotation, capture set or type definition of a term
holds the atom `any`.  The resolver keeps the `any` a program writes and adds
none (`resolve_noAny` in `Resolve.lean`). -/

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

/-- A lambda's parameter is position zero in its body. -/
example : (ATm.lam pTop (.path (.var .here)) : ATm []).skel = .lam (.var 0) := by decide

/-- A binding inserted for a box has the skeleton of the plain application:
`λ(x). λ(y). let y' = □ y in x y'` against `λ(x). λ(y). x y`.  The body roots and
arrow binders between `x` and `y` are not counted. -/
example :
    (ATm.lam pTop (.lam pTop
      (.let none (.box .here) (.app (.there (.there (.there (.there .here)))) .here))) :
        ATm []).skel =
    (ATm.lam pTop (.lam pTop
      (.app (.there (.there (.there .here))) .here)) : ATm []).skel := by decide

/-- An object's self is position zero in its definitions. -/
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

/-! ## Partial terms

`PTm` is `ATm` with `Option` at every slot inference may fill: a lambda's
domain, a literal's self shape, and a written field type.  `none` is an empty
slot.  A domain is one slot, its shape and set together, so a written domain
`S` keeps meaning `S ^ {}`.  Each slot lives where its written form lives.  A
domain lives under the arrow's own capture binder, a self shape under the self
alone, and a written field type in the signature of the definitions, under the
class root and the self.  The answer of a `let` and the set of an unboxing are
optional in `ATm` and are no slots.  The resolver returns a `PTm`, the
elaborator fills it, and the elaborated term is an `ATm`, the input of the
typer.  Each `let` also records where it comes from, since the elaborator
treats a call argument apart from other bindings.  A `letex` is always written,
so it carries no tag. -/

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
  | lam : Option (Ty (Sig.dom s)) → PTm (Sig.body s) → PTm s
  /-- `ν(x : S. d)`, or `ν(x. d)` with the self shape empty. -/
  | obj : Option (Shape (s,x)) → PDefs ((s,c),x) → PTm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → PTm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → PTm s
  /-- `let x (: E)? = t in u`, with the origin of the binding. -/
  | «let» : LetTag → Option (ETy s) → PTm s → PTm (s,x) → PTm s
  /-- `let ⟨c, x⟩ = t in u`, a written unpacking. -/
  | letex : PTm s → PTm ((s,c),x) → PTm s
  /-- `□ x`, a box value. -/
  | box : BVar s .var → PTm s
  /-- `C ⊸ x`, an unboxing. -/
  | unbox : Option (CaptureSet s) → BVar s .var → PTm s
  /-- `(t : T)`, a checking point. -/
  | asc : PTm s → Ty s → PTm s
/-- Definitions whose term members may carry a written type. -/
inductive PDefs : Sig → Type where
  /-- `{type A = S}`. -/
  | typ : Label → Shape s → PDefs s
  /-- `{C^ = c}`, a capture member definition. -/
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
def PTm.full? {s : Sig} (p : PTm s) : Option (ATm s) :=
  match p with
  | .path q => some (.path q)
  | .lam (some T) t => t.full?.map (.lam T)
  | .lam none _ => none
  | .obj (some S) d => d.full?.map (.obj S)
  | .obj none _ => none
  | .app x y => some (.app x y)
  | .proj x a => some (.proj x a)
  | .let _ ann t u =>
      match t.full?, u.full? with
      | some a, some b => some (.let ann a b)
      | _, _ => none
  | .letex t u =>
      match t.full?, u.full? with
      | some a, some b => some (.letex a b)
      | _, _ => none
  | .box x => some (.box x)
  | .unbox C x => some (.unbox C x)
  | .asc t T => t.full?.map fun a => .asc a T
termination_by structural p
/-- The `ADefs` that a block of partial terms stands for, when no slot is
empty and no field type is written. -/
def PDefs.full? {s : Sig} (d : PDefs s) : Option (ADefs s) :=
  match d with
  | .typ A S => some (.typ A S)
  | .cap C c => some (.cap C c)
  | .trm a none t => t.full?.map (.trm a)
  | .trm _ (some _) _ => none
  | .and d e =>
      match d.full?, e.full? with
      | some a, some b => some (.and a b)
      | _, _ => none
termination_by structural d
end

mutual
/-- Every slot written.  Every `let` is tagged `written`. -/
def ATm.toI {s : Sig} (a : ATm s) : PTm s :=
  match a with
  | .path q => .path q
  | .lam T t => .lam (some T) t.toI
  | .obj S d => .obj (some S) d.toI
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let ann t u => .let .written ann t.toI u.toI
  | .letex t u => .letex t.toI u.toI
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc t.toI T
termination_by structural a
/-- Every slot written, and no field type. -/
def ADefs.toI {s : Sig} (d : ADefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a t => .trm a none t.toI
  | .and d e => .and d.toI e.toI
termination_by structural d
end

/-! ## Agreement with the written slots

The definitions of a literal are typed against its self shape read under the
class root, `S.rename Rename.succ.lift`, which the typing rules call
`Shape.underRoot`.  So a written field type, which lives in the signature of
the definitions, is compared with the field of that shape. -/

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
with anything.  The answer of a `let` and the set of an unboxing are no slots,
so they must be equal.  The tag is ignored. -/
def PTm.fills {s : Sig} (p : PTm s) (a : ATm s) : Bool :=
  match p, a with
  | .path q, .path q' => decide (q = q')
  | .lam o t, .lam T b =>
      (match o with | some T' => decide (T' = T) | none => true) && t.fills b
  | .obj o d, .obj S e =>
      (match o with | some S' => decide (S' = S) | none => true) &&
        d.fills (S.rename (Rename.succ (k := .cap)).lift) e
  | .app x y, .app x' y' => decide (x = x') && decide (y = y')
  | .proj x l, .proj x' l' => decide (x = x') && decide (l = l')
  | .let _ o t u, .let o' b c => decide (o = o') && t.fills b && u.fills c
  | .letex t u, .letex b c => t.fills b && u.fills c
  | .box x, .box x' => decide (x = x')
  | .unbox C x, .unbox C' x' => decide (C = C') && decide (x = x')
  | .asc t T, .asc b T' => decide (T = T') && t.fills b
  | _, _ => false
termination_by structural p
/-- Definitions against the self shape they were typed at, read under the
class root, in lockstep.  A written field type equals the shape's field at
that label.  An intersection of definitions splits the shape with `shapeLeft`
and `shapeRight`, so a shape out of step with the definitions leaves no field
for a written type to agree with. -/
def PDefs.fills {s : Sig} (d : PDefs s) (U : Shape s) (e : ADefs s) : Bool :=
  match d, e with
  | .typ A S, .typ A' S' => decide (A = A') && decide (S = S')
  | .cap C c, .cap C' c' => decide (C = C') && decide (c = c')
  | .trm l o t, .trm l' b =>
      decide (l = l') &&
      (match o, U with
       | some V, .fld _ W => decide (V = W)
       | some _, _ => false
       | none, _ => true) && t.fills b
  | .and d1 d2, .and e1 e2 => d1.fills (shapeLeft U) e1 && d2.fills (shapeRight U) e2
  | _, _ => false
termination_by structural d
end

/-! ## Skeletons of partial terms

The skeleton forgets every slot and every tag, so a partial term and each of
its fillings have the same one (`PTm.skel_of_fills`). -/

mutual
/-- The skeleton of a partial term, with the clauses of `ATm.skel`. -/
def PTm.skel {s : Sig} (p : PTm s) : Skel :=
  match p with
  | .path (.var x) => .var (varPos x)
  | .lam _ t => .lam t.skel
  | .obj _ d => .obj d.skel
  | .app x y => .app (varPos x) (varPos y)
  | .proj x a => .proj (varPos x) a
  | .let _ _ t u => Skel.mkLet t.skel u.skel
  | .letex t u => Skel.mkLet t.skel u.skel
  | .box x => .var (varPos x)
  | .unbox _ x => .var (varPos x)
  | .asc t _ => t.skel
termination_by structural p
/-- The skeleton of the definitions of a partial term. -/
def PDefs.skel {s : Sig} (d : PDefs s) : SkelDefs :=
  match d with
  | .typ A _ => .typ A
  | .cap C _ => .typ C
  | .trm a _ t => .trm a t.skel
  | .and d e => .and d.skel e.skel
termination_by structural d
end

/-! ## No `any` in a partial term

As `ATm.NoAnyAnn`, with an empty slot holding no `any` and a written field
type read. -/

mutual
/-- No `any` in any written annotation, set or type definition of the
term. -/
def PTm.NoAnyAnn {s : Sig} (p : PTm s) : Bool :=
  match p with
  | .path _ => true
  | .lam o t => (match o with | none => true | some T => T.noAny) && t.NoAnyAnn
  | .obj o d => (match o with | none => true | some S => S.noAny) && d.NoAnyAnn
  | .app _ _ => true
  | .proj _ _ => true
  | .let _ ann t u =>
      (match ann with | none => true | some E => E.noAny) && t.NoAnyAnn && u.NoAnyAnn
  | .letex t u => t.NoAnyAnn && u.NoAnyAnn
  | .box _ => true
  | .unbox C _ => (match C with | none => true | some C => CaptureSet.noAny C)
  | .asc t T => t.NoAnyAnn && T.noAny
termination_by structural p
/-- No `any` in any written annotation, set or type definition of the
definitions. -/
def PDefs.NoAnyAnn {s : Sig} (d : PDefs s) : Bool :=
  match d with
  | .typ _ S => S.noAny
  | .cap _ c => CaptureSet.noAny c
  | .trm _ o t => (match o with | none => true | some T => T.noAny) && t.NoAnyAnn
  | .and d e => d.NoAnyAnn && e.NoAnyAnn
termination_by structural d
end

/-! ## The size measure of partial terms

The same node count as `sizeATm` and `sizeADefs`.  Types, sets and tags do not
count. -/

mutual
/-- The node count of a partial term. -/
def sizePTm {s : Sig} (p : PTm s) : Nat :=
  match p with
  | .path _ => 1
  | .lam _ t => sizePTm t + 1
  | .obj _ d => sizePDefs d + 1
  | .app _ _ => 1
  | .proj _ _ => 1
  | .let _ _ t u => sizePTm t + sizePTm u + 1
  | .letex t u => sizePTm t + sizePTm u + 1
  | .box _ => 1
  | .unbox _ _ => 1
  | .asc t _ => sizePTm t + 1
termination_by structural p
/-- The node count of the definitions of a partial term. -/
def sizePDefs {s : Sig} (d : PDefs s) : Nat :=
  match d with
  | .typ _ _ => 1
  | .cap _ _ => 1
  | .trm _ _ t => sizePTm t + 1
  | .and d e => sizePDefs d + sizePDefs e + 1
termination_by structural d
end

/-! ## Erasures

Each erasure maps a partial term to a partial term with some written slots
emptied.  They state that a program written with fewer annotations resolves to
the written program with those annotations erased.  `eraseDoms` empties every
lambda domain, `eraseSelf` every self shape, `eraseArgs` the domain of every
lambda in argument position, and `eraseAsc` the domain of every lambda directly
under an ascription.  `eraseChecked` empties the domain of every lambda in a
checked position, and `eraseG` is it with every self shape erased too: the
program a Scala programmer writes where an expected type reaches. -/

/-- Erase a lambda's domain, at the head only. -/
def PTm.dropDom {s : Sig} (p : PTm s) : PTm s :=
  match p with
  | .lam _ t => .lam none t
  | t => t

mutual
/-- Every lambda domain erased. -/
def PTm.eraseDoms {s : Sig} (p : PTm s) : PTm s :=
  match p with
  | .path q => .path q
  | .lam _ t => .lam none t.eraseDoms
  | .obj S d => .obj S d.eraseDoms
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let g ann t u => .let g ann t.eraseDoms u.eraseDoms
  | .letex t u => .letex t.eraseDoms u.eraseDoms
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc t.eraseDoms T
termination_by structural p
/-- Every lambda domain erased, in definitions. -/
def PDefs.eraseDoms {s : Sig} (d : PDefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a o t => .trm a o t.eraseDoms
  | .and d e => .and d.eraseDoms e.eraseDoms
termination_by structural d
end

mutual
/-- Every self shape erased. -/
def PTm.eraseSelf {s : Sig} (p : PTm s) : PTm s :=
  match p with
  | .path q => .path q
  | .lam T t => .lam T t.eraseSelf
  | .obj _ d => .obj none d.eraseSelf
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let g ann t u => .let g ann t.eraseSelf u.eraseSelf
  | .letex t u => .letex t.eraseSelf u.eraseSelf
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc t.eraseSelf T
termination_by structural p
/-- Every self shape erased, in definitions. -/
def PDefs.eraseSelf {s : Sig} (d : PDefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a o t => .trm a o t.eraseSelf
  | .and d e => .and d.eraseSelf e.eraseSelf
termination_by structural d
end

mutual
/-- The domain of every lambda bound by an `arg` binding erased. -/
def PTm.eraseArgs {s : Sig} (p : PTm s) : PTm s :=
  match p with
  | .path q => .path q
  | .lam T t => .lam T t.eraseArgs
  | .obj S d => .obj S d.eraseArgs
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let g ann t u =>
      .let g ann (if g = .arg then t.eraseArgs.dropDom else t.eraseArgs) u.eraseArgs
  | .letex t u => .letex t.eraseArgs u.eraseArgs
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc t.eraseArgs T
termination_by structural p
/-- The domain of every lambda bound by an `arg` binding erased, in
definitions. -/
def PDefs.eraseArgs {s : Sig} (d : PDefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a o t => .trm a o t.eraseArgs
  | .and d e => .and d.eraseArgs e.eraseArgs
termination_by structural d
end

mutual
/-- The domain of every lambda directly under an ascription erased. -/
def PTm.eraseAsc {s : Sig} (p : PTm s) : PTm s :=
  match p with
  | .path q => .path q
  | .lam T t => .lam T t.eraseAsc
  | .obj S d => .obj S d.eraseAsc
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let g ann t u => .let g ann t.eraseAsc u.eraseAsc
  | .letex t u => .letex t.eraseAsc u.eraseAsc
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc t.eraseAsc.dropDom T
termination_by structural p
/-- The domain of every lambda directly under an ascription erased, in
definitions. -/
def PDefs.eraseAsc {s : Sig} (d : PDefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a o t => .trm a o t.eraseAsc
  | .and d e => .and d.eraseAsc e.eraseAsc
termination_by structural d
end

/-- The body of a `let` is its own binder, as in `let x : A = t in x`. -/
def PTm.isHere {s : Sig} : PTm (s,x) → Bool
  | .path (.var .here) => true
  | _ => false

mutual
/-- The domain of every lambda in a checked position erased.  A position is
checked when the typer passes it a goal: directly under an ascription, the
bound term of a call argument, the bound term of `let x : A = t in x`, the body
of a `let` with a written answer, a field of a literal whose self shape is
written, and the body of a lambda or a block in a checked position.  `chk`
says whether the term itself sits in one.  With `fS` the self shapes are
erased too, and the fields of such a literal sit in no checked position. -/
def PTm.eraseChecked {s : Sig} (fS chk : Bool) (p : PTm s) : PTm s :=
  match p with
  | .path q => .path q
  | .lam T t => .lam (if chk then none else T) (t.eraseChecked fS chk)
  | .obj S d =>
      .obj (if fS then none else S) (d.eraseChecked fS (!fS && S.isSome))
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let g ann t u =>
      .let g ann (t.eraseChecked fS (decide (g = .arg) || (ann.isSome && u.isHere)))
        (u.eraseChecked fS (chk || ann.isSome))
  | .letex t u => .letex (t.eraseChecked fS false) (u.eraseChecked fS chk)
  | .box x => .box x
  | .unbox C x => .unbox C x
  | .asc t T => .asc (t.eraseChecked fS true) T
termination_by structural p
/-- The domain of every lambda in a checked position erased, in
definitions. -/
def PDefs.eraseChecked {s : Sig} (fS chk : Bool) (d : PDefs s) : PDefs s :=
  match d with
  | .typ A S => .typ A S
  | .cap C c => .cap C c
  | .trm a o t => .trm a o (t.eraseChecked fS chk)
  | .and d e => .and (d.eraseChecked fS chk) (e.eraseChecked fS chk)
termination_by structural d
end

/-- Every self shape and the domain of every lambda in a checked position
erased. -/
def PTm.eraseG {s : Sig} (p : PTm s) : PTm s := p.eraseChecked true false

/-! ## The bridges agree -/

mutual
/-- A term with every slot written is full, and `full?` gives it back. -/
theorem ATm.full?_toI : ∀ {s : Sig} (a : ATm s), a.toI.full? = some a
  | _, .path _ => by simp only [ATm.toI, PTm.full?]
  | _, .lam T t => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, Option.map_some]
  | _, .obj S d => by simp only [ATm.toI, PTm.full?, ADefs.full?_toI d, Option.map_some]
  | _, .app _ _ => by simp only [ATm.toI, PTm.full?]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.full?]
  | _, .let ann t u => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, ATm.full?_toI u]
  | _, .letex t u => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, ATm.full?_toI u]
  | _, .box _ => by simp only [ATm.toI, PTm.full?]
  | _, .unbox _ _ => by simp only [ATm.toI, PTm.full?]
  | _, .asc t T => by simp only [ATm.toI, PTm.full?, ATm.full?_toI t, Option.map_some]
/-- Definitions with every slot written are full, and `full?` gives them
back. -/
theorem ADefs.full?_toI : ∀ {s : Sig} (d : ADefs s), d.toI.full? = some d
  | _, .typ _ _ => by simp only [ADefs.toI, PDefs.full?]
  | _, .cap _ _ => by simp only [ADefs.toI, PDefs.full?]
  | _, .trm a t => by simp only [ADefs.toI, PDefs.full?, ATm.full?_toI t, Option.map_some]
  | _, .and d e => by simp only [ADefs.toI, PDefs.full?, ADefs.full?_toI d, ADefs.full?_toI e]
end

mutual
/-- A term with every slot written has its own skeleton. -/
theorem ATm.skel_toI : ∀ {s : Sig} (a : ATm s), a.toI.skel = a.skel
  | _, .path (.var _) => by simp only [ATm.toI, PTm.skel, ATm.skel]
  | _, .lam _ t => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t]
  | _, .obj _ d => by simp only [ATm.toI, PTm.skel, ATm.skel, ADefs.skel_toI d]
  | _, .app _ _ => by simp only [ATm.toI, PTm.skel, ATm.skel]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.skel, ATm.skel]
  | _, .let _ t u => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t, ATm.skel_toI u]
  | _, .letex t u => by
      simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t, ATm.skel_toI u]
  | _, .box _ => by simp only [ATm.toI, PTm.skel, ATm.skel]
  | _, .unbox _ _ => by simp only [ATm.toI, PTm.skel, ATm.skel]
  | _, .asc t _ => by simp only [ATm.toI, PTm.skel, ATm.skel, ATm.skel_toI t]
/-- Definitions with every slot written have their own skeleton. -/
theorem ADefs.skel_toI : ∀ {s : Sig} (d : ADefs s), d.toI.skel = d.skel
  | _, .typ _ _ => by simp only [ADefs.toI, PDefs.skel, ADefs.skel]
  | _, .cap _ _ => by simp only [ADefs.toI, PDefs.skel, ADefs.skel]
  | _, .trm _ t => by simp only [ADefs.toI, PDefs.skel, ADefs.skel, ATm.skel_toI t]
  | _, .and d e => by
      simp only [ADefs.toI, PDefs.skel, ADefs.skel, ADefs.skel_toI d, ADefs.skel_toI e]
end

/-- The skeleton of a term with every slot written, read on the partial term. -/
theorem PTm.skel_toI {s : Sig} (a : ATm s) : a.toI.skel = a.skel := ATm.skel_toI a

mutual
/-- A term with every slot written agrees with itself. -/
theorem ATm.fills_toI : ∀ {s : Sig} (a : ATm s), a.toI.fills a = true
  | _, .path _ => by simp only [ATm.toI, PTm.fills, decide_true]
  | _, .lam _ t => by simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ATm.fills_toI t]
  | _, .obj _ d => by
      simp only [ATm.toI, PTm.fills, decide_true, Bool.true_and, ADefs.fills_toI d]
  | _, .app _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.fills, decide_true, Bool.and_self]
  | _, .let _ t u => by
      simp only [ATm.toI, PTm.fills, decide_true, ATm.fills_toI t, ATm.fills_toI u,
        Bool.and_self]
  | _, .letex t u => by
      simp only [ATm.toI, PTm.fills, ATm.fills_toI t, ATm.fills_toI u, Bool.and_self]
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
  | _, .obj (some _) d, _, h => by
      simp only [PTm.full?] at h
      cases hd : d.full? with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some e =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [PTm.fills, decide_true, Bool.true_and, PDefs.fills_of_full? _ hd]
  | _, .obj none _, _, h => by simp only [PTm.full?, reduceCtorEq] at h
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
  | _, .letex t u, _, h => by
      simp only [PTm.full?] at h
      cases ht : t.full? with
      | none => simp only [ht, reduceCtorEq] at h
      | some b =>
          cases hu : u.full? with
          | none => simp only [ht, hu, reduceCtorEq] at h
          | some c =>
              simp only [ht, hu, Option.some.injEq] at h
              subst h
              simp only [PTm.fills, PTm.fills_of_full? ht, PTm.fills_of_full? hu, Bool.and_self]
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
  | _, .path (.var _), a, h => by
      cases a with
      | path q =>
          cases q with
          | var y =>
              simp only [PTm.fills, decide_eq_true_eq] at h
              rw [h]; simp only [PTm.skel, ATm.skel]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .lam _ t, a, h => by
      cases a with
      | lam _ b =>
          simp only [PTm.fills, Bool.and_eq_true] at h
          simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.2]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .obj _ d, a, h => by
      cases a with
      | obj S e =>
          simp only [PTm.fills, Bool.and_eq_true] at h
          simp only [PTm.skel, ATm.skel, PDefs.skel_of_fills _ h.2]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .app _ _, a, h => by
      cases a with
      | app _ _ =>
          simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          rw [h.1, h.2]; simp only [PTm.skel, ATm.skel]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .proj _ _, a, h => by
      cases a with
      | proj _ _ =>
          simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          rw [h.1, h.2]; simp only [PTm.skel, ATm.skel]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .let _ _ t u, a, h => by
      cases a with
      | «let» _ b c =>
          simp only [PTm.fills, Bool.and_eq_true] at h
          simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.1.2, PTm.skel_of_fills h.2]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .letex t u, a, h => by
      cases a with
      | letex b c =>
          simp only [PTm.fills, Bool.and_eq_true] at h
          simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.1, PTm.skel_of_fills h.2]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .box _, a, h => by
      cases a with
      | box _ =>
          simp only [PTm.fills, decide_eq_true_eq] at h
          rw [h]; simp only [PTm.skel, ATm.skel]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .unbox _ _, a, h => by
      cases a with
      | unbox _ _ =>
          simp only [PTm.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          rw [h.2]; simp only [PTm.skel, ATm.skel]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
  | _, .asc t _, a, h => by
      cases a with
      | asc b _ =>
          simp only [PTm.fills, Bool.and_eq_true] at h
          simp only [PTm.skel, ATm.skel, PTm.skel_of_fills h.2]
      | _ => simp only [PTm.fills, Bool.false_eq_true] at h
/-- Filled definitions have the skeleton of the `PDefs` they fill, against
any self shape. -/
theorem PDefs.skel_of_fills : ∀ {s : Sig} {d : PDefs s} {e : ADefs s} (S : Shape s),
    d.fills S e = true → d.skel = e.skel
  | _, .typ _ _, e, _, h => by
      cases e with
      | typ _ _ =>
          simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          rw [h.1]; simp only [PDefs.skel, ADefs.skel]
      | _ => simp only [PDefs.fills, Bool.false_eq_true] at h
  | _, .cap _ _, e, _, h => by
      cases e with
      | cap _ _ =>
          simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          rw [h.1]; simp only [PDefs.skel, ADefs.skel]
      | _ => simp only [PDefs.fills, Bool.false_eq_true] at h
  | _, .trm _ _ t, e, _, h => by
      cases e with
      | trm _ b =>
          simp only [PDefs.fills, Bool.and_eq_true, decide_eq_true_eq] at h
          simp only [PDefs.skel, ADefs.skel, h.1.1, PTm.skel_of_fills h.2]
      | _ => simp only [PDefs.fills, Bool.false_eq_true] at h
  | _, .and d1 d2, e, S, h => by
      cases e with
      | and e1 e2 =>
          simp only [PDefs.fills, Bool.and_eq_true] at h
          simp only [PDefs.skel, ADefs.skel, PDefs.skel_of_fills (shapeLeft S) h.1,
            PDefs.skel_of_fills (shapeRight S) h.2]
      | _ => simp only [PDefs.fills, Bool.false_eq_true] at h
end

/-- A full partial term has the skeleton of the term it gives. -/
theorem PTm.skel_of_full? {s : Sig} {p : PTm s} {a : ATm s} (h : p.full? = some a) :
    p.skel = a.skel :=
  PTm.skel_of_fills (PTm.fills_of_full? h)

mutual
/-- Writing every slot keeps the absence of `any`. -/
theorem ATm.NoAnyAnn_toI : ∀ {s : Sig} (a : ATm s), a.toI.NoAnyAnn = a.NoAnyAnn
  | _, .path _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn]
  | _, .lam _ t => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t]
  | _, .obj _ d => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ADefs.NoAnyAnn_toI d]
  | _, .app _ _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn]
  | _, .proj _ _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn]
  | _, .let _ t u => by
      simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t, ATm.NoAnyAnn_toI u]
  | _, .letex t u => by
      simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t, ATm.NoAnyAnn_toI u]
  | _, .box _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn]
  | _, .unbox _ _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn]
  | _, .asc t _ => by simp only [ATm.toI, PTm.NoAnyAnn, ATm.NoAnyAnn, ATm.NoAnyAnn_toI t]
/-- Writing every slot keeps the absence of `any`, in definitions. -/
theorem ADefs.NoAnyAnn_toI : ∀ {s : Sig} (d : ADefs s), d.toI.NoAnyAnn = d.NoAnyAnn
  | _, .typ _ _ => by simp only [ADefs.toI, PDefs.NoAnyAnn, ADefs.NoAnyAnn]
  | _, .cap _ _ => by simp only [ADefs.toI, PDefs.NoAnyAnn, ADefs.NoAnyAnn]
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
      subst h; simp only [ATm.NoAnyAnn]
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
  | _, .obj (some _) d, _, h, hn => by
      simp only [PTm.full?] at h
      simp only [PTm.NoAnyAnn, Bool.and_eq_true] at hn
      cases hd : d.full? with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some e =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [ATm.NoAnyAnn, hn.1, PDefs.NoAnyAnn_of_full? hd hn.2, Bool.and_self]
  | _, .obj none _, _, h, _ => by simp only [PTm.full?, reduceCtorEq] at h
  | _, .app _ _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; simp only [ATm.NoAnyAnn]
  | _, .proj _ _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; simp only [ATm.NoAnyAnn]
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
  | _, .letex t u, _, h, hn => by
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
              simp only [ATm.NoAnyAnn, PTm.NoAnyAnn_of_full? ht hn.1,
                PTm.NoAnyAnn_of_full? hu hn.2, Bool.and_self]
  | _, .box _, _, h, _ => by
      simp only [PTm.full?, Option.some.injEq] at h
      subst h; simp only [ATm.NoAnyAnn]
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
  | _, .path _ => by simp only [ATm.toI, sizePTm, sizeATm]
  | _, .lam _ t => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t]
  | _, .obj _ d => by simp only [ATm.toI, sizePTm, sizeATm, sizePDefs_toI d]
  | _, .app _ _ => by simp only [ATm.toI, sizePTm, sizeATm]
  | _, .proj _ _ => by simp only [ATm.toI, sizePTm, sizeATm]
  | _, .let _ t u => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t, sizePTm_toI u]
  | _, .letex t u => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t, sizePTm_toI u]
  | _, .box _ => by simp only [ATm.toI, sizePTm, sizeATm]
  | _, .unbox _ _ => by simp only [ATm.toI, sizePTm, sizeATm]
  | _, .asc t _ => by simp only [ATm.toI, sizePTm, sizeATm, sizePTm_toI t]
/-- `toI` keeps the node count of definitions. -/
theorem sizePDefs_toI : ∀ {s : Sig} (d : ADefs s), sizePDefs d.toI = sizeADefs d
  | _, .typ _ _ => by simp only [ADefs.toI, sizePDefs, sizeADefs]
  | _, .cap _ _ => by simp only [ADefs.toI, sizePDefs, sizeADefs]
  | _, .trm _ t => by simp only [ADefs.toI, sizePDefs, sizeADefs, sizePTm_toI t]
  | _, .and d e => by simp only [ADefs.toI, sizePDefs, sizeADefs, sizePDefs_toI d, sizePDefs_toI e]
end

/-! ## Sanity of partial terms -/

/-- A lambda with its domain empty is partial, filled by any domain, and has
the skeleton of every filling. -/
example : (PTm.lam none (.path (.var .here)) : PTm []).full? = none := by decide

example : (PTm.lam none (.path (.var .here)) : PTm []).fills
    (.lam pTop (.path (.var .here))) = true := by decide

example : (PTm.lam none (.path (.var .here)) : PTm []).skel = .lam (.var 0) := by decide

/-- A written field type makes a literal partial and must equal the field of
the self shape. -/
example : (PTm.obj none (.trm (.trm 0) (some pTop) (.path (.var .here))) : PTm []).full? =
    none := by decide

example : (PTm.obj none (.trm (.trm 0) (some pTop) (.path (.var .here))) : PTm []).fills
    (.obj (.fld (.trm 0) pTop) (.trm (.trm 0) (.path (.var .here)))) = true := by decide

example : (PTm.obj none (.trm (.trm 0) (some pTop) (.path (.var .here))) : PTm []).fills
    (.obj (.fld (.trm 0) (.capt [] .bot)) (.trm (.trm 0) (.path (.var .here)))) = false := by
  decide

/-- A call argument loses its domain under `eraseArgs` and `eraseG`, and so
does a lambda in its body, which sits in a checked position too. -/
example : (PTm.let .arg none (.lam (some pTop) (.lam (some pTop) (.path (.var .here))))
      (.app .here .here) : PTm []).eraseG =
    .let .arg none (.lam none (.lam none (.path (.var .here)))) (.app .here .here) := by decide

example : (PTm.let .recv none (.lam (some pTop) (.path (.var .here)))
      (.app .here .here) : PTm []).eraseG =
    .let .recv none (.lam (some pTop) (.path (.var .here))) (.app .here .here) := by decide

end ClassifiersFrontend
