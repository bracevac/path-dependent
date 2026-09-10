import Coercions.CapturesCC.FCdot.Debruijn

namespace CapturesCC

/-!
# DOT-MNF^cc syntax

WadlerFest DOT in monadic normal form, with capture sets.  `let` right-hand
sides are arbitrary terms, application and selection take variables.  The
scoping discipline is the one of `FCdot.Debruijn`, reused verbatim:
signatures, bound variables, renamings, and the label type are shared with
the target so that the translation of Plan III §8 is the identity on
signatures.

Stage A3a splits what the vanilla line called a type, exactly as stage A0
did for the target: a *shape* is the vanilla type former, and a *type* is a
shape with a capture set beside it, written `S ^ C`.  Shapes gain a capture
member `{C : c₁..c₂}` and the box former `□ T`; terms gain the unboxing
`C ⊸ x` and values the box `□ x`.  Type-member bounds are shapes, so a
capturing type enters a type member through a box.

`Path` is an inductive with a single constructor.  Every judgment that
mentions a receiver takes a `Path`, so that pDOT (§9) can add `sel` without
restructuring anything here.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Paths -/

/-- Paths.  In this plan a path is a variable. -/
inductive Path : Sig → Type where
  | var : BVar s .var → Path s
deriving DecidableEq

/-- The variable at the root of a path. -/
def Path.root : Path s → BVar s .var
  | .var x => x

def Path.rename : Path s1 → Rename s1 s2 → Path s2
  | .var x, ρ => .var (ρ.var x)

def Path.weaken (p : Path s) : Path (s,,k) := p.rename Rename.succ

/-- Instantiate the innermost binder of a path by a variable. -/
def Path.substVar (p : Path (s,,k)) (y : BVar s k) : Path s := p.rename (Rename.subst y)

@[simp] theorem Path.root_rename (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).root = ρ.var p.root := by
  cases p <;> rfl

/-! ## Capture sets

A capture atom is a term binder `{x}`, a capture binder `{κ}`, the capture
member `C` of a term binder, `{x.C}`, or the inert `any` of stage A3b.  A
capture set is a list of atoms, read as the finite set of its members.  This mirrors the target's
`FCdot.CapAtom` and `FCdot.CaptureSet`, with `sel` for what the target calls
`name`. -/

inductive CapAtom : Sig → Type where
  /-- `{x}`, the capability of a term binder. -/
  | var : BVar s .var → CapAtom s
  /-- `{κ}`, a platform capture binder. -/
  | cvar : BVar s .cap → CapAtom s
  /-- `{x.C}`, the capture member `C` of the object `x`. -/
  | sel : BVar s .var → Label → CapAtom s
  /-- `any`, the notation read by position (stage A3b).  It is inert: no
      rule of `Subcap`, `SubShape`, `Sub`, `HasTy` or `DefsTy` mentions it,
      `elem` compares it syntactically like any other atom, and renaming
      maps it to itself.  `CaptureSet.expand` is what gives it a reading. -/
  | any : CapAtom s
deriving DecidableEq, Repr

/-- A capture set: a list of atoms, read as a finite set. -/
abbrev CaptureSet (s : Sig) : Type := List (CapAtom s)

/-- Union of capture sets is concatenation of the underlying lists. -/
instance CaptureSet.instUnion : Union (CaptureSet s) := ⟨List.append⟩

@[simp] theorem CaptureSet.union_def (C D : CaptureSet s) : C ∪ D = C ++ D := rfl

/-- Membership test. -/
def CaptureSet.elem : CaptureSet s → CapAtom s → Bool
  | [], _ => false
  | b :: C, a => if a = b then true else CaptureSet.elem C a

theorem CaptureSet.elem_iff {s : Sig} {a : CapAtom s} :
    ∀ C : CaptureSet s, C.elem a = true ↔ a ∈ C
  | [] => by simp [CaptureSet.elem]
  | b :: C => by
      by_cases h : a = b
      · simp [CaptureSet.elem, h]
      · simp [CaptureSet.elem, h, List.mem_cons, CaptureSet.elem_iff C]

/-- Every atom of the first set is an atom of the second, decided. -/
def CaptureSet.subset : CaptureSet s → CaptureSet s → Bool
  | [], _ => true
  | a :: C, D => D.elem a && CaptureSet.subset C D

/-- Every atom of the first set is an atom of the second, as a proposition. -/
def CaptureSet.Subset (C D : CaptureSet s) : Prop := ∀ a, a ∈ C → a ∈ D

theorem CaptureSet.subset_iff {s : Sig} :
    ∀ C D : CaptureSet s, C.subset D = true ↔ C.Subset D
  | [], D => by
      simp only [CaptureSet.subset, CaptureSet.Subset]
      refine ⟨fun _ a ha => ?_, fun _ => trivial⟩
      cases ha
  | a :: C, D => by
      simp only [CaptureSet.subset, Bool.and_eq_true, CaptureSet.elem_iff,
        CaptureSet.subset_iff C D, CaptureSet.Subset]
      constructor
      · intro ⟨ha, hC⟩ b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hC b hb
      · intro h
        exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
          fun b hb => h b (List.mem_cons.mpr (Or.inr hb))⟩

instance CaptureSet.instDecidableSubset (C D : CaptureSet s) : Decidable (C.Subset D) :=
  if h : C.subset D = true then
    .isTrue ((CaptureSet.subset_iff C D).mp h)
  else
    .isFalse (fun hs => h ((CaptureSet.subset_iff C D).mpr hs))

/-- The empty set is below every set. -/
theorem CaptureSet.nil_subset {s : Sig} (C : CaptureSet s) :
    ([] : CaptureSet s).Subset C := by
  intro a ha; cases ha

/-- Renaming of a capture atom: the three variable forms carry variables
only, and `any` is mapped to itself. -/
def CapAtom.rename : CapAtom s1 → Rename s1 s2 → CapAtom s2
  | .var x, ρ => .var (ρ.var x)
  | .cvar κ, ρ => .cvar (ρ.var κ)
  | .sel x C, ρ => .sel (ρ.var x) C
  | .any, _ => .any

/-- Renaming of a capture set is pointwise. -/
def CaptureSet.rename (C : CaptureSet s1) (ρ : Rename s1 s2) : CaptureSet s2 :=
  C.map (fun a => a.rename ρ)

def CapAtom.weaken (a : CapAtom s) : CapAtom (s,,k) := a.rename Rename.succ
def CaptureSet.weaken (C : CaptureSet s) : CaptureSet (s,,k) := C.rename Rename.succ

/-- Instantiate the innermost binder of a capture set by a variable. -/
def CaptureSet.substVar (C : CaptureSet (s,,k)) (y : BVar s k) : CaptureSet s :=
  C.rename (Rename.subst y)

@[simp] theorem CaptureSet.rename_nil {s1 s2 : Sig} (ρ : Rename s1 s2) :
    CaptureSet.rename ([] : CaptureSet s1) ρ = [] := rfl

@[simp] theorem CaptureSet.weaken_nil {s : Sig} {k : Kind} :
    CaptureSet.weaken ([] : CaptureSet s) (k := k) = [] := rfl

/-! `CaptureSet` is a list, so a compound capture set is written with the
qualified function name: dot notation on a `::` or a `++` would look the
functions up in `List`. -/

@[simp] theorem CaptureSet.rename_cons {s1 s2 : Sig} (a : CapAtom s1) (C : CaptureSet s1)
    (ρ : Rename s1 s2) :
    CaptureSet.rename (a :: C) ρ = a.rename ρ :: CaptureSet.rename C ρ := rfl

@[simp] theorem CaptureSet.rename_append {s1 s2 : Sig} (C D : CaptureSet s1)
    (ρ : Rename s1 s2) :
    CaptureSet.rename (C ++ D) ρ = CaptureSet.rename C ρ ++ CaptureSet.rename D ρ := by
  simp [CaptureSet.rename]

theorem CapAtom.rename_rename {s1 s2 s3 : Sig} (a : CapAtom s1) (ρ : Rename s1 s2)
    (σ : Rename s2 s3) : (a.rename ρ).rename σ = a.rename (ρ.comp σ) := by
  cases a <;> rfl

theorem CaptureSet.rename_rename {s1 s2 s3 : Sig} (C : CaptureSet s1) (ρ : Rename s1 s2)
    (σ : Rename s2 s3) :
    CaptureSet.rename (CaptureSet.rename C ρ) σ = CaptureSet.rename C (ρ.comp σ) := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      simp only [CaptureSet.rename_cons, CapAtom.rename_rename a ρ σ, ih]

/-- Renaming a weakened set under a lifted renaming is weakening the renamed
set: the two ways round `,,k` agree. -/
theorem CaptureSet.weaken_rename {s1 s2 : Sig} {k : Kind} (C : CaptureSet s1)
    (ρ : Rename s1 s2) :
    CaptureSet.rename (C.weaken (k := k)) ρ.lift = (CaptureSet.rename C ρ).weaken := by
  simp only [CaptureSet.weaken, CaptureSet.rename_rename, Rename.succ_lift]

/-! ### `any` and expansion

`any` is a notation the calculus never interprets: it is an atom like any
other, compared syntactically by `elem`, and no rule of `Subcap`,
`SubShape`, `Sub`, `HasTy` or `DefsTy` mentions it.  Its meaning is by
position, and `expand` is what gives it that meaning.  A set is expanded by
the set `D` its position reads `any` as: the codomain of an arrow reads
`any` as the arrow's own set with the parameter, a field type or a
capture-member upper bound of an object reads it as the object's set with
the self, and the top of a program reads it as the platform set.  Each
former resets the reading for what is under it, so nested occurrences are
read by their own enclosing former and no level is needed.  An expanded set
holds no `any`, so an expanded program is a program of stage A3a. -/

/-- `C.expand D`: every `any` of `C` replaced by the atoms of `D`. -/
def CaptureSet.expand : CaptureSet s → CaptureSet s → CaptureSet s
  | [], _ => []
  | .any :: C, D => D ++ CaptureSet.expand C D
  | .var x :: C, D => .var x :: CaptureSet.expand C D
  | .cvar κ :: C, D => .cvar κ :: CaptureSet.expand C D
  | .sel x A :: C, D => .sel x A :: CaptureSet.expand C D

@[simp] theorem CaptureSet.expand_nil {s : Sig} (D : CaptureSet s) :
    CaptureSet.expand [] D = [] := rfl

@[simp] theorem CaptureSet.expand_cons_any {s : Sig} (C D : CaptureSet s) :
    CaptureSet.expand (CapAtom.any :: C) D = D ++ CaptureSet.expand C D := rfl

@[simp] theorem CaptureSet.expand_cons_var {s : Sig} (x : BVar s .var) (C D : CaptureSet s) :
    CaptureSet.expand (CapAtom.var x :: C) D = .var x :: CaptureSet.expand C D := rfl

@[simp] theorem CaptureSet.expand_cons_cvar {s : Sig} (κ : BVar s .cap) (C D : CaptureSet s) :
    CaptureSet.expand (CapAtom.cvar κ :: C) D = .cvar κ :: CaptureSet.expand C D := rfl

@[simp] theorem CaptureSet.expand_cons_sel {s : Sig} (x : BVar s .var) (A : Label)
    (C D : CaptureSet s) :
    CaptureSet.expand (CapAtom.sel x A :: C) D = .sel x A :: CaptureSet.expand C D := rfl

/-- Expansion leaves every atom other than `any` where it is. -/
theorem CaptureSet.expand_cons_of_ne {s : Sig} {a : CapAtom s} (h : a ≠ .any)
    (C D : CaptureSet s) :
    CaptureSet.expand (a :: C) D = a :: CaptureSet.expand C D := by
  cases a
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h

@[simp] theorem CaptureSet.expand_append {s : Sig} (C C' D : CaptureSet s) :
    CaptureSet.expand (C ++ C') D = CaptureSet.expand C D ++ CaptureSet.expand C' D := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [ih]

/-- Expansion commutes with renaming, the reading set renamed too. -/
theorem CaptureSet.expand_rename {s1 s2 : Sig} (C D : CaptureSet s1) (ρ : Rename s1 s2) :
    CaptureSet.rename (CaptureSet.expand C D) ρ
      = CaptureSet.expand (CaptureSet.rename C ρ) (CaptureSet.rename D ρ) := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [CapAtom.rename, ih]

/-! ### No `any` at all

`noAny` is the decision procedure and `NoAny` the proposition it decides.  A
set, a shape or a type with no `any` is one of stage A3a, and expansion is
the identity on it. -/

/-- No `any` occurs in the set. -/
def CaptureSet.noAny : CaptureSet s → Bool
  | [] => true
  | .any :: _ => false
  | .var _ :: C => CaptureSet.noAny C
  | .cvar _ :: C => CaptureSet.noAny C
  | .sel _ _ :: C => CaptureSet.noAny C

/-- No `any` occurs in the set, as a proposition. -/
def CaptureSet.NoAny (C : CaptureSet s) : Prop := C.noAny = true

instance CaptureSet.NoAny.instDecidable {s : Sig} (C : CaptureSet s) : Decidable C.NoAny :=
  decidable_of_iff (C.noAny = true) Iff.rfl

theorem CaptureSet.noAny_nil {s : Sig} : CaptureSet.NoAny ([] : CaptureSet s) := rfl

theorem CaptureSet.noAny_cons_of_ne {s : Sig} {a : CapAtom s} (h : a ≠ .any)
    {C : CaptureSet s} (hC : C.NoAny) : CaptureSet.NoAny (a :: C) := by
  cases a
  · exact hC
  · exact hC
  · exact hC
  · exact absurd rfl h

theorem CaptureSet.noAny_of_cons {s : Sig} {a : CapAtom s} {C : CaptureSet s}
    (h : CaptureSet.NoAny (a :: C)) : C.NoAny := by
  cases a
  · exact h
  · exact h
  · exact h
  · exact absurd h (by simp [CaptureSet.NoAny, CaptureSet.noAny])

theorem CaptureSet.noAny_append {s : Sig} {C D : CaptureSet s} (hC : C.NoAny)
    (hD : D.NoAny) : CaptureSet.NoAny (C ++ D) := by
  induction C with
  | nil => exact hD
  | cons a C ih =>
      cases a
      · exact CaptureSet.noAny_cons_of_ne (by simp) (ih (CaptureSet.noAny_of_cons hC))
      · exact CaptureSet.noAny_cons_of_ne (by simp) (ih (CaptureSet.noAny_of_cons hC))
      · exact CaptureSet.noAny_cons_of_ne (by simp) (ih (CaptureSet.noAny_of_cons hC))
      · exact absurd hC (by simp [CaptureSet.NoAny, CaptureSet.noAny])

theorem CaptureSet.noAny_rename {s1 s2 : Sig} {C : CaptureSet s1} (h : C.NoAny)
    (ρ : Rename s1 s2) : CaptureSet.NoAny (CaptureSet.rename C ρ) := by
  induction C with
  | nil => exact CaptureSet.noAny_nil
  | cons a C ih =>
      cases a
      · exact CaptureSet.noAny_cons_of_ne (by simp [CapAtom.rename])
          (ih (CaptureSet.noAny_of_cons h))
      · exact CaptureSet.noAny_cons_of_ne (by simp [CapAtom.rename])
          (ih (CaptureSet.noAny_of_cons h))
      · exact CaptureSet.noAny_cons_of_ne (by simp [CapAtom.rename])
          (ih (CaptureSet.noAny_of_cons h))
      · exact absurd h (by simp [CaptureSet.NoAny, CaptureSet.noAny])

theorem CaptureSet.noAny_weaken {s : Sig} {k : Kind} {C : CaptureSet s} (h : C.NoAny) :
    CaptureSet.NoAny (C.weaken (k := k)) := CaptureSet.noAny_rename h Rename.succ

/-- Expansion is the identity on a set with no `any`. -/
theorem CaptureSet.expand_of_noAny {s : Sig} {C : CaptureSet s} (h : C.NoAny)
    (D : CaptureSet s) : CaptureSet.expand C D = C := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      cases a
      · simp [ih (CaptureSet.noAny_of_cons h)]
      · simp [ih (CaptureSet.noAny_of_cons h)]
      · simp [ih (CaptureSet.noAny_of_cons h)]
      · exact absurd h (by simp [CaptureSet.NoAny, CaptureSet.noAny])

/-- Expanding by a set with no `any` leaves no `any`. -/
theorem CaptureSet.noAny_expand {s : Sig} {D : CaptureSet s} (hD : D.NoAny)
    (C : CaptureSet s) : CaptureSet.NoAny (CaptureSet.expand C D) := by
  induction C with
  | nil => exact CaptureSet.noAny_nil
  | cons a C ih =>
      cases a
      · exact CaptureSet.noAny_cons_of_ne (by simp) ih
      · exact CaptureSet.noAny_cons_of_ne (by simp) ih
      · exact CaptureSet.noAny_cons_of_ne (by simp) ih
      · exact CaptureSet.noAny_append hD ih

/-- The set an arrow or an object reads `any` as under its own binder is its
own set weakened, with the binder itself; renaming commutes with that. -/
theorem CaptureSet.self_rename {s1 s2 : Sig} (D : CaptureSet s1) (ρ : Rename s1 s2) :
    CaptureSet.rename (D.weaken (k := .var) ∪ [CapAtom.var .here]) ρ.lift
      = (CaptureSet.rename D ρ).weaken ∪ [CapAtom.var .here] := by
  simp only [CaptureSet.union_def, CaptureSet.rename_append, CaptureSet.weaken_rename D ρ,
    CaptureSet.rename_cons, CaptureSet.rename_nil, CapAtom.rename, Rename.lift_here]

theorem CaptureSet.noAny_self {s : Sig} {D : CaptureSet s} (h : D.NoAny) :
    CaptureSet.NoAny (D.weaken (k := .var) ∪ [CapAtom.var .here]) :=
  CaptureSet.noAny_append (CaptureSet.noAny_weaken h)
    (CaptureSet.noAny_cons_of_ne (by simp) CaptureSet.noAny_nil)

/-- The same set under an arrow's two binders: the arrow's capture binder is
in the way, so the set is weakened twice. -/
theorem CaptureSet.selfC_rename {s1 s2 : Sig} (D : CaptureSet s1) (ρ : Rename s1 s2) :
    CaptureSet.rename
        (CaptureSet.weaken (CaptureSet.weaken (k := .cap) D) ∪ [CapAtom.var .here])
        ρ.lift.lift
      = CaptureSet.weaken (CaptureSet.weaken (k := .cap) (CaptureSet.rename D ρ))
          ∪ [CapAtom.var .here] := by
  simp only [CaptureSet.union_def, CaptureSet.rename_append, CaptureSet.weaken_rename,
    CaptureSet.rename_cons, CaptureSet.rename_nil, CapAtom.rename, Rename.lift_here]

theorem CaptureSet.noAny_selfC {s : Sig} {D : CaptureSet s} (h : D.NoAny) :
    CaptureSet.NoAny
      (CaptureSet.weaken (CaptureSet.weaken (k := .cap) D) ∪ [CapAtom.var .here]) :=
  CaptureSet.noAny_append (CaptureSet.noAny_weaken (CaptureSet.noAny_weaken h))
    (CaptureSet.noAny_cons_of_ne (by simp) CaptureSet.noAny_nil)

/-! ## Shapes and types

A shape is the vanilla line's type former, with the capture member and the
box added; a type is a shape with a capture set. -/

mutual

/-- Shapes of DOT-MNF^cc. -/
inductive Shape : Sig → Type where
  | top : Shape s
  | bot : Shape s
  /-- Type declaration `{A : S..T}`.  Bounds are shapes.  Bad bounds are
      allowed. -/
  | typ : Label → Shape s → Shape s → Shape s
  /-- Field declaration `{a : T}`; the field's type is a capturing type. -/
  | fld : Label → Ty s → Shape s
  /-- Capture declaration `{C : c₁..c₂}`, at a type label, as the compiler
      desugars a capture-set parameter to a type parameter. -/
  | cap : Label → CaptureSet s → CaptureSet s → Shape s
  /-- Type selection `p.A`. -/
  | sel : Path s → Label → Shape s
  /-- Recursive self shape `μ(x. S)`. -/
  | mu : Shape (s,x) → Shape s
  /-- Dependent function shape `∀[κ](x : T₁) T₂`, on capturing types.  The
      arrow binds a capture binder `κ` before its parameter, so its domain
      lives in `Sig.dom s` and its codomain in `Sig.cod s`, exactly as the
      target's `FCdot.Shape.pi` does. -/
  | all : Ty (Sig.dom s) → Ty (Sig.cod s) → Shape s
  /-- Intersection `S ∧ T`. -/
  | and : Shape s → Shape s → Shape s
  /-- The box former `□ T`.  Inert: not a declaration. -/
  | box : Ty s → Shape s

/-- A type is a shape with a capture set, written `S ^ C`. -/
inductive Ty : Sig → Type where
  | capt : CaptureSet s → Shape s → Ty s

end

deriving instance DecidableEq for Shape, Ty

/-! ### Notation `S ^ C` -/

scoped notation:75 S:76 " ^ " C:76 => Ty.capt C S

/-- A shape with the empty capture set. -/
abbrev Ty.pure (S : Shape s) : Ty s := .capt [] S

/-- The shape of a type.  The vanilla line's `Ty` is exactly this shape: a
statement that read a vanilla type reads this projection. -/
def Ty.shape : Ty s → Shape s
  | .capt _ S => S

/-- The capture set of a type. -/
def Ty.captureSet : Ty s → CaptureSet s
  | .capt C _ => C

@[simp] theorem Ty.shape_capt (C : CaptureSet s) (S : Shape s) : (S ^ C).shape = S := rfl
@[simp] theorem Ty.captureSet_capt (C : CaptureSet s) (S : Shape s) :
    (S ^ C).captureSet = C := rfl

theorem Ty.eta (T : Ty s) : T = T.shape ^ T.captureSet := by cases T; rfl

/-- The domain of an arrow, behind one name.  It sits under the arrow's own
capture binder, as the target's `FCdot.Dom` does. -/
abbrev Dom (s : Sig) : Type := Ty (Sig.dom s)
/-- The codomain of an arrow, behind one name: it may mention the arrow's
capture binder and the parameter. -/
abbrev Cod (s : Sig) : Type := Ty (Sig.cod s)

mutual

def Shape.rename : Shape s1 → Rename s1 s2 → Shape s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, ρ => .typ A (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .cap C c1 c2, ρ => .cap C (c1.rename ρ) (c2.rename ρ)
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu S, ρ => .mu (S.rename ρ.lift)
  | .all T1 T2, ρ => .all (T1.rename ρ.lift) (T2.rename ρ.lift.lift)
  | .and S T, ρ => .and (S.rename ρ) (T.rename ρ)
  | .box T, ρ => .box (T.rename ρ)

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .capt C S, ρ => .capt (C.rename ρ) (S.rename ρ)

end

def Shape.weaken (S : Shape s) : Shape (s,,k) := S.rename Rename.succ
def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ

/-- Instantiate the innermost binder of a shape or a type by a variable. -/
def Shape.substVar (S : Shape (s,,k)) (y : BVar s k) : Shape s := S.rename (Rename.subst y)
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)

/-! ### The domain and the codomain under a scope

A lambda body is a scope: its own root, then the arrow's capture binder,
then the parameter.  These three abbreviations are the source's copies of
`FCdot.Dom.underRoot`, `FCdot.Dom.inBody` and `FCdot.Cod.underRoot`, at the
same signatures and by the same renamings, so that the translation is the
identity on them. -/

/-- The domain under the body root. -/
abbrev Dom.underRoot (T : Dom s) : Ty ((s,c),c) := T.rename Rename.succ.lift
/-- The domain as the body's parameter binding reads it. -/
abbrev Dom.inBody (T : Dom s) : Ty (((s,c),c),x) := T.underRoot.weaken
/-- The codomain under the body root. -/
abbrev Cod.underRoot (E : Cod s) : Ty (((s,c),c),x) := E.rename Rename.succ.lift.lift

@[simp] theorem Ty.shape_rename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).shape = T.shape.rename ρ := by cases T; rfl

@[simp] theorem Ty.captureSet_rename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).captureSet = T.captureSet.rename ρ := by cases T; rfl

@[simp] theorem Ty.shape_weaken {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).shape = T.shape.weaken := by cases T; rfl

@[simp] theorem Ty.captureSet_weaken {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).captureSet = T.captureSet.weaken := by cases T; rfl

/-! ## Expansion of `any` in a type

`expand` gives every `any` of a type the reading its position prescribes.
The reading set `D₀` of a shape is the capture set of the type the shape
sits in.  An arrow reads the `any` of its codomain as its own set with the
parameter, an object reads the `any` of a field type or of a capture-member
upper bound as its own set with the self, and each former resets the
reading for what is under it.  Four positions get no reading and are given
the empty set instead, because a program is well formed there only if it
holds no `any` at all (`AnyOk`): the outer set of a parameter type, a
type-member bound, the lower bound of a capture member, and everything
under a box. -/

mutual

/-- `S.expand D₀`, where `D₀` is the set the enclosing type reads `any` as. -/
def Shape.expand : Shape s → CaptureSet s → Shape s
  | .top, _ => .top
  | .bot, _ => .bot
  | .sel p A, _ => .sel p A
  | .typ A S T, _ => .typ A (S.expand []) (T.expand [])
  | .fld a T, D₀ => .fld a (T.expand D₀)
  | .cap A c1 c2, D₀ =>
      .cap A (CaptureSet.expand c1 []) (CaptureSet.expand c2 D₀)
  | .mu S, D₀ => .mu (S.expand (CaptureSet.weaken D₀ ∪ [CapAtom.var .here]))
  | .all T1 T2, D₀ =>
      .all (T1.expand [])
        (T2.expand (CaptureSet.weaken (CaptureSet.weaken (k := .cap) D₀) ∪ [CapAtom.var .here]))
  | .and S T, D₀ => .and (S.expand D₀) (T.expand D₀)
  | .box T, _ => .box (T.expand [])

/-- `T.expand D`, where `D` is the set the enclosing former reads `any` as:
the type's own set is expanded first, and is the reading set of its shape. -/
def Ty.expand : Ty s → CaptureSet s → Ty s
  | .capt C S, D => .capt (CaptureSet.expand C D) (S.expand (CaptureSet.expand C D))

end

/-- The body of a `μ`, whose reading set is already under the self: the
plan's `expandSelf`, which is `expand` at the self's signature. -/
def Shape.expandSelf (S : Shape (s,x)) (D : CaptureSet (s,x)) : Shape (s,x) := S.expand D

@[simp] theorem Shape.expandSelf_eq {s : Sig} (S : Shape (s,x)) (D : CaptureSet (s,x)) :
    S.expandSelf D = S.expand D := rfl

/-- The `μ` clause in the plan's words: the body is expanded by the object's
own set, weakened, with the self. -/
theorem Shape.expand_mu {s : Sig} (S : Shape (s,x)) (D₀ : CaptureSet s) :
    (Shape.mu S).expand D₀
      = .mu (S.expandSelf (CaptureSet.weaken D₀ ∪ [CapAtom.var .here])) := rfl

/-! ## No `any`, and `any` only where it is read

`NoAny` says a shape or a type holds no `any` at all, so that it is a shape
or a type of stage A3a.  `AnyOk` says every `any` it holds is in a position
`expand` gives a reading to.  Both are decided. -/

mutual

/-- No `any` anywhere in the shape. -/
def Shape.noAny : Shape s → Bool
  | .top => true
  | .bot => true
  | .sel _ _ => true
  | .typ _ S T => S.noAny && T.noAny
  | .fld _ T => T.noAny
  | .cap _ c1 c2 => CaptureSet.noAny c1 && CaptureSet.noAny c2
  | .mu S => S.noAny
  | .all T1 T2 => T1.noAny && T2.noAny
  | .and S T => S.noAny && T.noAny
  | .box T => T.noAny

/-- No `any` anywhere in the type. -/
def Ty.noAny : Ty s → Bool
  | .capt C S => CaptureSet.noAny C && S.noAny

end

mutual

/-- Every `any` of the shape is in a position `expand` reads. -/
def Shape.anyOk : Shape s → Bool
  | .top => true
  | .bot => true
  | .sel _ _ => true
  | .typ _ S T => S.noAny && T.noAny
  | .fld _ T => T.anyOk
  | .cap _ c1 _ => CaptureSet.noAny c1
  | .mu S => S.anyOk
  | .all (.capt C1 S1) T2 => CaptureSet.noAny C1 && S1.anyOk && T2.anyOk
  | .and S T => S.anyOk && T.anyOk
  | .box T => T.noAny

/-- Every `any` of the type is in a position `expand` reads. -/
def Ty.anyOk : Ty s → Bool
  | .capt _ S => S.anyOk

end

/-- No `any` anywhere in the shape, as a proposition. -/
def Shape.NoAny (S : Shape s) : Prop := S.noAny = true

/-- No `any` anywhere in the type, as a proposition. -/
def Ty.NoAny (T : Ty s) : Prop := T.noAny = true

/-- Every `any` of the shape is read, as a proposition. -/
def Shape.AnyOk (S : Shape s) : Prop := S.anyOk = true

/-- Every `any` of the type is read, as a proposition. -/
def Ty.AnyOk (T : Ty s) : Prop := T.anyOk = true

instance Shape.NoAny.instDecidable {s : Sig} (S : Shape s) : Decidable S.NoAny :=
  decidable_of_iff (S.noAny = true) Iff.rfl

instance Ty.NoAny.instDecidable {s : Sig} (T : Ty s) : Decidable T.NoAny :=
  decidable_of_iff (T.noAny = true) Iff.rfl

instance Shape.AnyOk.instDecidable {s : Sig} (S : Shape s) : Decidable S.AnyOk :=
  decidable_of_iff (S.anyOk = true) Iff.rfl

instance Ty.AnyOk.instDecidable {s : Sig} (T : Ty s) : Decidable T.AnyOk :=
  decidable_of_iff (T.anyOk = true) Iff.rfl

/-! The clauses of the four predicates, as the propositions they stand for. -/

@[simp] theorem Shape.noAny_top {s : Sig} : Shape.NoAny (.top : Shape s) := rfl
@[simp] theorem Shape.noAny_bot {s : Sig} : Shape.NoAny (.bot : Shape s) := rfl
@[simp] theorem Shape.noAny_sel {s : Sig} (p : Path s) (A : Label) :
    Shape.NoAny (.sel p A) := rfl

@[simp] theorem Shape.noAny_typ {s : Sig} (A : Label) (S T : Shape s) :
    Shape.NoAny (.typ A S T) ↔ S.NoAny ∧ T.NoAny := by
  simp [Shape.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_fld {s : Sig} (a : Label) (T : Ty s) :
    Shape.NoAny (.fld a T) ↔ T.NoAny := by simp [Shape.NoAny, Ty.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_cap {s : Sig} (A : Label) (c1 c2 : CaptureSet s) :
    Shape.NoAny (.cap A c1 c2) ↔ c1.NoAny ∧ c2.NoAny := by
  simp [Shape.NoAny, CaptureSet.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_mu {s : Sig} (S : Shape (s,x)) :
    Shape.NoAny (.mu S) ↔ S.NoAny := by simp [Shape.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_all {s : Sig} (T1 : Dom s) (T2 : Cod s) :
    Shape.NoAny (.all T1 T2) ↔ T1.NoAny ∧ T2.NoAny := by
  simp [Shape.NoAny, Ty.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_and {s : Sig} (S T : Shape s) :
    Shape.NoAny (.and S T) ↔ S.NoAny ∧ T.NoAny := by simp [Shape.NoAny, Shape.noAny]

@[simp] theorem Shape.noAny_box {s : Sig} (T : Ty s) :
    Shape.NoAny (.box T) ↔ T.NoAny := by simp [Shape.NoAny, Ty.NoAny, Shape.noAny]

@[simp] theorem Ty.noAny_capt {s : Sig} (C : CaptureSet s) (S : Shape s) :
    Ty.NoAny (S ^ C) ↔ C.NoAny ∧ S.NoAny := by
  simp [Ty.NoAny, Shape.NoAny, CaptureSet.NoAny, Ty.noAny]

@[simp] theorem Shape.anyOk_top {s : Sig} : Shape.AnyOk (.top : Shape s) := rfl
@[simp] theorem Shape.anyOk_bot {s : Sig} : Shape.AnyOk (.bot : Shape s) := rfl
@[simp] theorem Shape.anyOk_sel {s : Sig} (p : Path s) (A : Label) :
    Shape.AnyOk (.sel p A) := rfl

@[simp] theorem Shape.anyOk_typ {s : Sig} (A : Label) (S T : Shape s) :
    Shape.AnyOk (.typ A S T) ↔ S.NoAny ∧ T.NoAny := by
  simp [Shape.AnyOk, Shape.NoAny, Shape.anyOk]

@[simp] theorem Shape.anyOk_fld {s : Sig} (a : Label) (T : Ty s) :
    Shape.AnyOk (.fld a T) ↔ T.AnyOk := by simp [Shape.AnyOk, Ty.AnyOk, Shape.anyOk]

@[simp] theorem Shape.anyOk_cap {s : Sig} (A : Label) (c1 c2 : CaptureSet s) :
    Shape.AnyOk (.cap A c1 c2) ↔ c1.NoAny := by
  simp [Shape.AnyOk, CaptureSet.NoAny, Shape.anyOk]

@[simp] theorem Shape.anyOk_mu {s : Sig} (S : Shape (s,x)) :
    Shape.AnyOk (.mu S) ↔ S.AnyOk := by simp [Shape.AnyOk, Shape.anyOk]

@[simp] theorem Shape.anyOk_all {s : Sig} (C1 : CaptureSet (Sig.dom s)) (S1 : Shape (Sig.dom s))
    (T2 : Cod s) :
    Shape.AnyOk (.all (S1 ^ C1) T2) ↔ C1.NoAny ∧ S1.AnyOk ∧ T2.AnyOk := by
  simp [Shape.AnyOk, Ty.AnyOk, CaptureSet.NoAny, Shape.anyOk, and_assoc]

@[simp] theorem Shape.anyOk_and {s : Sig} (S T : Shape s) :
    Shape.AnyOk (.and S T) ↔ S.AnyOk ∧ T.AnyOk := by simp [Shape.AnyOk, Shape.anyOk]

@[simp] theorem Shape.anyOk_box {s : Sig} (T : Ty s) :
    Shape.AnyOk (.box T) ↔ T.NoAny := by simp [Shape.AnyOk, Ty.NoAny, Shape.anyOk]

@[simp] theorem Ty.anyOk_capt {s : Sig} (C : CaptureSet s) (S : Shape s) :
    Ty.AnyOk (S ^ C) ↔ S.AnyOk := by simp [Ty.AnyOk, Shape.AnyOk, Ty.anyOk]

/-! ### Expansion is the identity where there is no `any` -/

mutual

/-- Expansion is the identity on a shape with no `any`. -/
theorem Shape.expand_of_noAny {s : Sig} :
    ∀ (S : Shape s), S.NoAny → ∀ D₀ : CaptureSet s, S.expand D₀ = S
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .typ A S T, h, _ => by
      rw [Shape.noAny_typ] at h
      simp only [Shape.expand, Shape.expand_of_noAny S h.1, Shape.expand_of_noAny T h.2]
  | .fld a T, h, D₀ => by
      rw [Shape.noAny_fld] at h
      simp only [Shape.expand, Ty.expand_of_noAny T h]
  | .cap A c1 c2, h, D₀ => by
      rw [Shape.noAny_cap] at h
      simp only [Shape.expand, CaptureSet.expand_of_noAny h.1, CaptureSet.expand_of_noAny h.2]
  | .mu S, h, D₀ => by
      rw [Shape.noAny_mu] at h
      simp only [Shape.expand, Shape.expand_of_noAny S h]
  | .all T1 T2, h, D₀ => by
      rw [Shape.noAny_all] at h
      simp only [Shape.expand, Ty.expand_of_noAny T1 h.1, Ty.expand_of_noAny T2 h.2]
  | .and S T, h, D₀ => by
      rw [Shape.noAny_and] at h
      simp only [Shape.expand, Shape.expand_of_noAny S h.1, Shape.expand_of_noAny T h.2]
  | .box T, h, _ => by
      rw [Shape.noAny_box] at h
      simp only [Shape.expand, Ty.expand_of_noAny T h]

/-- Expansion is the identity on a type with no `any`. -/
theorem Ty.expand_of_noAny {s : Sig} :
    ∀ (T : Ty s), T.NoAny → ∀ D : CaptureSet s, T.expand D = T
  | .capt C S, h, D => by
      rw [Ty.noAny_capt] at h
      simp only [Ty.expand, CaptureSet.expand_of_noAny h.1, Shape.expand_of_noAny S h.2]

end

/-! ### Expansion of an `AnyOk` type leaves no `any` -/

mutual

/-- Expanding an `AnyOk` shape by a set with no `any` leaves no `any`. -/
theorem Shape.noAny_expand {s : Sig} :
    ∀ (S : Shape s) (D₀ : CaptureSet s), S.AnyOk → D₀.NoAny → Shape.NoAny (S.expand D₀)
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .sel _ _, _, _, _ => rfl
  | .typ A S T, _, h, _ => by
      rw [Shape.anyOk_typ] at h
      rw [Shape.expand, Shape.noAny_typ, Shape.expand_of_noAny S h.1,
        Shape.expand_of_noAny T h.2]
      exact h
  | .fld a T, D₀, h, hD => by
      rw [Shape.anyOk_fld] at h
      rw [Shape.expand, Shape.noAny_fld]
      exact Ty.noAny_expand T D₀ h hD
  | .cap A c1 c2, D₀, h, hD => by
      rw [Shape.anyOk_cap] at h
      rw [Shape.expand, Shape.noAny_cap, CaptureSet.expand_of_noAny h]
      exact ⟨h, CaptureSet.noAny_expand hD c2⟩
  | .mu S, D₀, h, hD => by
      rw [Shape.anyOk_mu] at h
      rw [Shape.expand, Shape.noAny_mu]
      exact Shape.noAny_expand S _ h (CaptureSet.noAny_self hD)
  | .all (.capt C1 S1) T2, D₀, h, hD => by
      rw [Shape.anyOk_all] at h
      rw [Shape.expand, Shape.noAny_all]
      refine ⟨Ty.noAny_expand (S1 ^ C1) [] ?_ CaptureSet.noAny_nil,
        Ty.noAny_expand T2 _ h.2.2 (CaptureSet.noAny_selfC hD)⟩
      rw [Ty.anyOk_capt]
      exact h.2.1
  | .and S T, D₀, h, hD => by
      rw [Shape.anyOk_and] at h
      rw [Shape.expand, Shape.noAny_and]
      exact ⟨Shape.noAny_expand S D₀ h.1 hD, Shape.noAny_expand T D₀ h.2 hD⟩
  | .box T, _, h, _ => by
      rw [Shape.anyOk_box] at h
      rw [Shape.expand, Shape.noAny_box, Ty.expand_of_noAny T h]
      exact h

/-- Expanding an `AnyOk` type by a set with no `any` leaves no `any`. -/
theorem Ty.noAny_expand {s : Sig} :
    ∀ (T : Ty s) (D : CaptureSet s), T.AnyOk → D.NoAny → Ty.NoAny (T.expand D)
  | .capt C S, D, h, hD => by
      rw [Ty.anyOk_capt] at h
      rw [Ty.expand, Ty.noAny_capt]
      exact ⟨CaptureSet.noAny_expand hD C,
        Shape.noAny_expand S _ h (CaptureSet.noAny_expand hD C)⟩

end

/-! ### Expansion commutes with renaming -/

mutual

/-- Expansion of a shape commutes with renaming, the reading set renamed. -/
theorem Shape.expand_rename {s1 s2 : Sig} :
    ∀ (S : Shape s1) (D₀ : CaptureSet s1) (ρ : Rename s1 s2),
      (S.expand D₀).rename ρ = (S.rename ρ).expand (CaptureSet.rename D₀ ρ)
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .typ A S T, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Shape.expand_rename S [] ρ,
        Shape.expand_rename T [] ρ, CaptureSet.rename_nil]
  | .fld a T, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Ty.expand_rename T D₀ ρ]
  | .cap A c1 c2, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, CaptureSet.expand_rename, CaptureSet.rename_nil]
  | .mu S, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Shape.expand_rename S _ ρ.lift,
        CaptureSet.self_rename D₀ ρ]
  | .all T1 T2, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Ty.expand_rename T1 [] ρ.lift,
        Ty.expand_rename T2 _ ρ.lift.lift, CaptureSet.selfC_rename D₀ ρ,
        CaptureSet.rename_nil]
  | .and S T, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Shape.expand_rename S D₀ ρ,
        Shape.expand_rename T D₀ ρ]
  | .box T, D₀, ρ => by
      simp only [Shape.expand, Shape.rename, Ty.expand_rename T [] ρ, CaptureSet.rename_nil]

/-- Expansion of a type commutes with renaming, the reading set renamed. -/
theorem Ty.expand_rename {s1 s2 : Sig} :
    ∀ (T : Ty s1) (D : CaptureSet s1) (ρ : Rename s1 s2),
      (T.expand D).rename ρ = (T.rename ρ).expand (CaptureSet.rename D ρ)
  | .capt C S, D, ρ => by
      simp only [Ty.expand, Ty.rename, CaptureSet.expand_rename, Shape.expand_rename S _ ρ]

end

/-- Expansion of a shape commutes with weakening. -/
theorem Shape.expand_weaken {s : Sig} {k : Kind} (S : Shape s) (D₀ : CaptureSet s) :
    (S.expand D₀).weaken (k := k) = (S.weaken).expand (D₀.weaken) :=
  Shape.expand_rename S D₀ Rename.succ

/-- Expansion of a type commutes with weakening. -/
theorem Ty.expand_weaken {s : Sig} {k : Kind} (T : Ty s) (D : CaptureSet s) :
    (T.expand D).weaken (k := k) = (T.weaken).expand (D.weaken) :=
  Ty.expand_rename T D Rename.succ

/-! ## Terms, values, definitions -/

mutual

/-- Terms.  Application, projection and unboxing take variables (monadic
normal form). -/
inductive Tm : Sig → Type where
  | path : Path s → Tm s
  | val : Value s → Tm s
  | app : BVar s .var → BVar s .var → Tm s
  | proj : BVar s .var → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s
  /-- Unboxing `C ⊸ x`: it charges `C` against the ambient use set. -/
  | unbox : CaptureSet s → BVar s .var → Tm s

/-- Values.  Object literals carry no type annotation. -/
inductive Value : Sig → Type where
  /-- An object literal, whose body is under the class root and the self. -/
  | obj : Defs ((s,c),x) → Value s
  /-- A closure, whose body is under the body root, the arrow's capture
      binder and the parameter. -/
  | lam : Ty (Sig.dom s) → Tm (Sig.body s) → Value s
  /-- Boxing `□ x`: a value, so that it erases as the target's box does. -/
  | box : BVar s .var → Value s

/-- Definitions of an object literal. -/
inductive Defs : Sig → Type where
  | typ : Label → Shape s → Defs s
  /-- A capture member definition `{C = c}`. -/
  | cap : Label → CaptureSet s → Defs s
  | trm : Label → Tm s → Defs s
  | and : Defs s → Defs s → Defs s

end

deriving instance DecidableEq for Tm, Value, Defs

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .path p, ρ => .path (p.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | .proj x a, ρ => .proj (ρ.var x) a
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .unbox C x, ρ => .unbox (C.rename ρ) (ρ.var x)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .obj d, ρ => .obj (d.rename ρ.lift.lift)
  | .lam T t, ρ => .lam (T.rename ρ.lift) (t.rename ρ.lift.lift.lift)
  | .box x, ρ => .box (ρ.var x)

def Defs.rename : Defs s1 → Rename s1 s2 → Defs s2
  | .typ A S, ρ => .typ A (S.rename ρ)
  | .cap C c, ρ => .cap C (c.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d1 d2, ρ => .and (d1.rename ρ) (d2.rename ρ)

end

/-- Weakening of a term, a value or a definition list, under a binder of any
kind: a capture binder carries no runtime content but a store has a slot for
it, so weakening is kind generic here as it is in `Runtime`. -/
def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,,k) := v.rename Rename.succ
def Defs.weaken (d : Defs s) : Defs (s,,k) := d.rename Rename.succ

/-- Instantiate the innermost binder of a term by a variable. -/
def Tm.substVar (t : Tm (s,x)) (y : BVar s .var) : Tm s := t.rename (Rename.subst y)
def Value.substVar (v : Value (s,x)) (y : BVar s .var) : Value s := v.rename (Rename.subst y)
def Defs.substVar (d : Defs (s,x)) (y : BVar s .var) : Defs s := d.rename (Rename.subst y)

/-! ## Substitution

The source's substitution mirrors the target's `FCdot.Subst` binder for
binder (B1.2).  Its term component maps a variable to a variable, because
the source has no atoms and every substitution the source performs is at a
variable.  Its capture component maps a capture binder to a capture *atom*,
because a call instantiates the arrow's capture binder by the argument, a
term variable, and a step that enters a body instantiates the body root by
the outermost reading, which is what the source writes `any`.  `any` itself
is inert and maps to itself. -/

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var → BVar s2 .var
  cvar : BVar s1 .cap → CapAtom s2

namespace Subst

def ofRename (ρ : Rename s1 s2) : Subst s1 s2 where
  var := fun x => ρ.var x
  cvar := fun κ => .cvar (ρ.var κ)

def lift (σ : Subst s1 s2) : Subst (s1,x) (s2,x) where
  var := fun
    | .here => .here
    | .there x => .there (σ.var x)
  cvar := fun
    | .there κ => (σ.cvar κ).rename Rename.succ

/-- Pass under a capture binder.  (`liftᶜ` of the plan: `ᶜ` is not a legal
Lean identifier character, so the capture-sort twin of a name carries the
suffix `C`.) -/
def liftC (σ : Subst s1 s2) : Subst (s1,c) (s2,c) where
  var := fun
    | .there x => .there (σ.var x)
  cvar := fun
    | .here => .cvar .here
    | .there κ => (σ.cvar κ).rename Rename.succ

/-- Instantiate the innermost capture binder by an atom. -/
def singleC (a : CapAtom s) : Subst (s,c) s where
  var := fun
    | .there x => x
  cvar := fun
    | .here => a
    | .there κ => .cvar κ

/-- What an application does to a codomain: the parameter goes to the
argument and the arrow's capture binder to the argument. -/
def arg (y : BVar s .var) : Subst ((s,c),x) s where
  var := fun
    | .here => y
    | .there (.there z) => z
  cvar := fun
    | .there .here => .var y
    | .there (.there κ) => .cvar κ

/-- What a step does when it enters a closure body: the parameter by the
argument, the arrow's binder by the argument, the body root by the
outermost reading.  This is `FCdot.Subst.enter` with `any` where the target
writes the universal root. -/
def enter (y : BVar s .var) : Subst (((s,c),c),x) s where
  var := fun
    | .here => y
    | .there (.there (.there z)) => z
  cvar := fun
    | .there .here => .var y
    | .there (.there .here) => .any
    | .there (.there (.there κ)) => .cvar κ

/-- The same when a projection enters an object body: the self by the
receiver, the class root by the outermost reading. -/
def enterObj (y : BVar s .var) : Subst ((s,c),x) s where
  var := fun
    | .here => y
    | .there (.there z) => z
  cvar := fun
    | .there .here => .any
    | .there (.there κ) => .cvar κ

end Subst

/-! ### The traversals

Clause for clause with the renamings above, differing only at a capture
atom. -/

def CapAtom.subst : CapAtom s1 → Subst s1 s2 → CapAtom s2
  | .var x, σ => .var (σ.var x)
  | .cvar κ, σ => σ.cvar κ
  | .sel x A, σ => .sel (σ.var x) A
  | .any, _ => .any

def CaptureSet.subst (C : CaptureSet s1) (σ : Subst s1 s2) : CaptureSet s2 :=
  C.map (fun a => a.subst σ)

def Path.subst : Path s1 → Subst s1 s2 → Path s2
  | .var x, σ => .var (σ.var x)

mutual

def Shape.subst : Shape s1 → Subst s1 s2 → Shape s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, σ => .typ A (S.subst σ) (T.subst σ)
  | .fld a T, σ => .fld a (T.subst σ)
  | .cap C c1 c2, σ => .cap C (c1.subst σ) (c2.subst σ)
  | .sel p A, σ => .sel (p.subst σ) A
  | .mu S, σ => .mu (S.subst σ.lift)
  | .all T1 T2, σ => .all (T1.subst σ.liftC) (T2.subst σ.liftC.lift)
  | .and S T, σ => .and (S.subst σ) (T.subst σ)
  | .box T, σ => .box (T.subst σ)

def Ty.subst : Ty s1 → Subst s1 s2 → Ty s2
  | .capt C S, σ => .capt (C.subst σ) (S.subst σ)

end

mutual

def Tm.subst : Tm s1 → Subst s1 s2 → Tm s2
  | .path p, σ => .path (p.subst σ)
  | .val v, σ => .val (v.subst σ)
  | .app x y, σ => .app (σ.var x) (σ.var y)
  | .proj x a, σ => .proj (σ.var x) a
  | .let t u, σ => .let (t.subst σ) (u.subst σ.lift)
  | .unbox C x, σ => .unbox (C.subst σ) (σ.var x)

def Value.subst : Value s1 → Subst s1 s2 → Value s2
  | .obj d, σ => .obj (d.subst σ.liftC.lift)
  | .lam T t, σ => .lam (T.subst σ.liftC) (t.subst σ.liftC.liftC.lift)
  | .box x, σ => .box (σ.var x)

def Defs.subst : Defs s1 → Subst s1 s2 → Defs s2
  | .typ A S, σ => .typ A (S.subst σ)
  | .cap C c, σ => .cap C (c.subst σ)
  | .trm a t, σ => .trm a (t.subst σ)
  | .and d1 d2, σ => .and (d1.subst σ) (d2.subst σ)

end

/-! ### A substitution of a renaming is that renaming

The one identity that keeps the whole existing renaming library in use. -/

theorem Subst.funext {s1 s2 : Sig} {σ τ : Subst s1 s2}
    (hv : ∀ x, σ.var x = τ.var x) (hc : ∀ κ, σ.cvar κ = τ.cvar κ) : σ = τ := by
  cases σ with
  | mk v c =>
    cases τ with
    | mk v' c' =>
      have h1 : v = v' := _root_.funext hv
      have h2 : c = c' := _root_.funext hc
      subst h1; subst h2; rfl

@[simp] theorem Subst.ofRename_lift {s1 s2 : Sig} (ρ : Rename s1 s2) :
    Subst.ofRename (Rename.lift (k := .var) ρ) = (Subst.ofRename ρ).lift :=
  Subst.funext (fun z => by cases z <;> rfl) (fun z => by cases z; rfl)

@[simp] theorem Subst.ofRename_liftC {s1 s2 : Sig} (ρ : Rename s1 s2) :
    Subst.ofRename (Rename.lift (k := .cap) ρ) = (Subst.ofRename ρ).liftC :=
  Subst.funext (fun z => by cases z; rfl) (fun z => by cases z <;> rfl)

@[simp] theorem CapAtom.subst_ofRename {s1 s2 : Sig} (a : CapAtom s1) (ρ : Rename s1 s2) :
    a.subst (Subst.ofRename ρ) = a.rename ρ := by
  cases a <;> rfl

@[simp] theorem CaptureSet.subst_ofRename {s1 s2 : Sig} (C : CaptureSet s1) (ρ : Rename s1 s2) :
    C.subst (Subst.ofRename ρ) = C.rename ρ := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      show (a.subst (Subst.ofRename ρ)) :: (CaptureSet.subst C (Subst.ofRename ρ)) = _
      rw [CapAtom.subst_ofRename, ih]
      rfl

@[simp] theorem Path.subst_ofRename {s1 s2 : Sig} (p : Path s1) (ρ : Rename s1 s2) :
    p.subst (Subst.ofRename ρ) = p.rename ρ := by
  cases p; rfl

mutual

@[simp] theorem Shape.subst_ofRename {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2) :
    S.subst (Subst.ofRename ρ) = S.rename ρ := by
  match S with
  | .top => rfl
  | .bot => rfl
  | .typ A S T =>
      simp only [Shape.subst, Shape.rename, Shape.subst_ofRename S ρ, Shape.subst_ofRename T ρ]
  | .fld a T => simp only [Shape.subst, Shape.rename, Ty.subst_ofRename T ρ]
  | .cap C c1 c2 => simp only [Shape.subst, Shape.rename, CaptureSet.subst_ofRename]
  | .sel p A => simp only [Shape.subst, Shape.rename, Path.subst_ofRename]
  | .mu S =>
      simp only [Shape.subst, Shape.rename, ← Subst.ofRename_lift,
        Shape.subst_ofRename S ρ.lift]
  | .all T1 T2 =>
      simp only [Shape.subst, Shape.rename, ← Subst.ofRename_lift, ← Subst.ofRename_liftC,
        Ty.subst_ofRename T1 ρ.lift, Ty.subst_ofRename T2 ρ.lift.lift]
  | .and S T =>
      simp only [Shape.subst, Shape.rename, Shape.subst_ofRename S ρ, Shape.subst_ofRename T ρ]
  | .box T => simp only [Shape.subst, Shape.rename, Ty.subst_ofRename T ρ]

@[simp] theorem Ty.subst_ofRename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    T.subst (Subst.ofRename ρ) = T.rename ρ := by
  match T with
  | .capt C S =>
      simp only [Ty.subst, Ty.rename, CaptureSet.subst_ofRename, Shape.subst_ofRename S ρ]

end

mutual

@[simp] theorem Tm.subst_ofRename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    t.subst (Subst.ofRename ρ) = t.rename ρ := by
  match t with
  | .path p => simp only [Tm.subst, Tm.rename, Path.subst_ofRename]
  | .val v => simp only [Tm.subst, Tm.rename, Value.subst_ofRename v ρ]
  | .app x y => rfl
  | .proj x a => rfl
  | .let t u =>
      simp only [Tm.subst, Tm.rename, ← Subst.ofRename_lift, Tm.subst_ofRename t ρ,
        Tm.subst_ofRename u ρ.lift]
  | .unbox C x =>
      simp only [Tm.subst, Tm.rename, CaptureSet.subst_ofRename]
      rfl

@[simp] theorem Value.subst_ofRename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    v.subst (Subst.ofRename ρ) = v.rename ρ := by
  match v with
  | .obj d =>
      simp only [Value.subst, Value.rename, ← Subst.ofRename_lift, ← Subst.ofRename_liftC,
        Defs.subst_ofRename d ρ.lift.lift]
  | .lam T t =>
      simp only [Value.subst, Value.rename, ← Subst.ofRename_lift, ← Subst.ofRename_liftC,
        Ty.subst_ofRename T ρ.lift, Tm.subst_ofRename t ρ.lift.lift.lift]
  | .box x => rfl

@[simp] theorem Defs.subst_ofRename {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2) :
    d.subst (Subst.ofRename ρ) = d.rename ρ := by
  match d with
  | .typ A S => simp only [Defs.subst, Defs.rename, Shape.subst_ofRename]
  | .cap C c => simp only [Defs.subst, Defs.rename, CaptureSet.subst_ofRename]
  | .trm a t => simp only [Defs.subst, Defs.rename, Tm.subst_ofRename t ρ]
  | .and d1 d2 =>
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename d1 ρ, Defs.subst_ofRename d2 ρ]

end

/-! ## The inspected root

The variable whose stored value the next step reads: the function of an
application, the receiver of a projection, and the box of an unboxing.
Every other term reads no slot.  This is the target's `FCdot.Tm.inspects`,
on the source's terms. -/

def Tm.inspects : Tm s → Option (BVar s .var)
  | .app x _ => some x
  | .proj x _ => some x
  | .unbox _ x => some x
  | _ => none

@[simp] theorem Tm.inspects_app (x y : BVar s .var) : (Tm.app x y).inspects = some x := rfl
@[simp] theorem Tm.inspects_proj (x : BVar s .var) (ℓ : Label) :
    (Tm.proj x ℓ).inspects = some x := rfl
@[simp] theorem Tm.inspects_unbox (C : CaptureSet s) (x : BVar s .var) :
    (Tm.unbox C x).inspects = some x := rfl
@[simp] theorem Tm.inspects_path (p : Path s) : (Tm.path p).inspects = none := rfl
@[simp] theorem Tm.inspects_val (v : Value s) : (Tm.val v).inspects = none := rfl
@[simp] theorem Tm.inspects_let (t : Tm s) (u : Tm (s,x)) : (Tm.let t u).inspects = none := rfl

theorem Tm.inspects_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).inspects = t.inspects.map ρ.var := by
  match t with
  | .path p => simp [Tm.rename]
  | .val v => simp [Tm.rename]
  | .app x y => simp [Tm.rename]
  | .proj x ℓ => simp [Tm.rename]
  | .let t u => simp [Tm.rename]
  | .unbox C x => simp [Tm.rename]

/-! ## Definition lookup -/

/-- The labels defined by a definition list, across the three kinds. -/
def Defs.labels : Defs s → List Label
  | .typ A _ => [A]
  | .cap C _ => [C]
  | .trm a _ => [a]
  | .and d1 d2 => d1.labels ++ d2.labels

/-- The type member at a label, if any.  The right conjunct shadows. -/
def Defs.lookupTyp : Defs s → Label → Option (Shape s)
  | .typ A S, ℓ => if ℓ = A then some S else none
  | .cap _ _, _ => none
  | .trm _ _, _ => none
  | .and d1 d2, ℓ => (d2.lookupTyp ℓ).or (d1.lookupTyp ℓ)

/-- The capture member at a label, if any.  The right conjunct shadows. -/
def Defs.lookupCap : Defs s → Label → Option (CaptureSet s)
  | .typ _ _, _ => none
  | .cap C c, ℓ => if ℓ = C then some c else none
  | .trm _ _, _ => none
  | .and d1 d2, ℓ => (d2.lookupCap ℓ).or (d1.lookupCap ℓ)

/-- The term member at a label, if any.  The right conjunct shadows. -/
def Defs.lookupTrm : Defs s → Label → Option (Tm s)
  | .typ _ _, _ => none
  | .cap _ _, _ => none
  | .trm a t, ℓ => if ℓ = a then some t else none
  | .and d1 d2, ℓ => (d2.lookupTrm ℓ).or (d1.lookupTrm ℓ)

/-! ## The fragment: declaration shapes, well-formedness, distinctness -/

/-- Declaration-shaped shapes: the shapes a `μ` may bind.  The capture
member is a declaration; the box is not. -/
inductive Shape.Decl : {s : Sig} → Shape s → Prop where
  | top : Shape.Decl (.top : Shape s)
  | typ : Shape.Decl (.typ A S T)
  | cap : Shape.Decl (.cap C c1 c2)
  | fld : Shape.Decl (.fld a T)
  | mu : Shape.Decl S → Shape.Decl (.mu S)
  | and : Shape.Decl S → Shape.Decl T → Shape.Decl (.and S T)

/-- The decision procedure for `Shape.Decl` (`Shape.isDecl_iff`).  It is what
the translation consults on the body of a `μ`, and it makes `Shape.Decl`
decidable, so that a derivation may discharge the premises of `Wf.mu`,
`Rec-I` and `Rec-E` by `decide`. -/
def Shape.isDecl : Shape s → Bool
  | .top => true
  | .typ _ _ _ => true
  | .cap _ _ _ => true
  | .fld _ _ => true
  | .mu S => S.isDecl
  | .and S T => S.isDecl && T.isDecl
  | .bot => false
  | .sel _ _ => false
  | .all _ _ => false
  | .box _ => false

theorem Shape.isDecl_iff : ∀ {s : Sig} (S : Shape s), S.isDecl = true ↔ Shape.Decl S
  | _, .top => ⟨fun _ => .top, fun _ => rfl⟩
  | _, .typ _ _ _ => ⟨fun _ => .typ, fun _ => rfl⟩
  | _, .cap _ _ _ => ⟨fun _ => .cap, fun _ => rfl⟩
  | _, .fld _ _ => ⟨fun _ => .fld, fun _ => rfl⟩
  | _, .bot => ⟨fun h => by simp [Shape.isDecl] at h, fun h => by cases h⟩
  | _, .sel _ _ => ⟨fun h => by simp [Shape.isDecl] at h, fun h => by cases h⟩
  | _, .all _ _ => ⟨fun h => by simp [Shape.isDecl] at h, fun h => by cases h⟩
  | _, .box _ => ⟨fun h => by simp [Shape.isDecl] at h, fun h => by cases h⟩
  | _, .mu S =>
      ⟨fun h => .mu ((Shape.isDecl_iff S).mp h), fun h => by
        cases h with | mu h' => exact (Shape.isDecl_iff S).mpr h'⟩
  | _, .and S T =>
      ⟨fun h => by
        rw [Shape.isDecl, Bool.and_eq_true] at h
        exact .and ((Shape.isDecl_iff S).mp h.1) ((Shape.isDecl_iff T).mp h.2),
       fun h => by
        cases h with
        | and hS hT =>
            rw [Shape.isDecl, Bool.and_eq_true]
            exact ⟨(Shape.isDecl_iff S).mpr hS, (Shape.isDecl_iff T).mpr hT⟩⟩

instance Shape.Decl.instDecidable {s : Sig} (S : Shape s) : Decidable (Shape.Decl S) :=
  decidable_of_iff _ (Shape.isDecl_iff S)

/-! Well-formedness.  Structural, except that the body of a recursive shape
is restricted to declaration shapes.  Intersections are unrestricted: a
non-declaration operand translates to a self-bound proposition (plan §13
item 9).  Bounds are arbitrary: `Wf {A : S..T}` does not ask for `S <: T`.
A capture member is well formed outright, its parts being capture sets, and
a box is well formed when the type inside it is. -/
mutual

/-- Well-formed shapes. -/
inductive Shape.Wf : {s : Sig} → Shape s → Prop where
  | top : Shape.Wf (.top : Shape s)
  | bot : Shape.Wf (.bot : Shape s)
  | sel : Shape.Wf (.sel p A)
  | typ : Shape.Wf S → Shape.Wf T → Shape.Wf (.typ A S T)
  | fld : Ty.Wf T → Shape.Wf (.fld a T)
  | cap : Shape.Wf (.cap C c1 c2)
  | mu : Shape.Wf S → Shape.Decl S → Shape.Wf (.mu S)
  | all : Ty.Wf T1 → Ty.Wf T2 → Shape.Wf (.all T1 T2)
  | and : Shape.Wf S → Shape.Wf T → Shape.Wf (.and S T)
  | box : Ty.Wf T → Shape.Wf (.box T)

/-- A type is well formed when its shape is: a capture set has no
well-formedness condition of its own. -/
inductive Ty.Wf : {s : Sig} → Ty s → Prop where
  | capt : Shape.Wf S → Ty.Wf (S ^ C)

end

/-- The labels of a definition list are pairwise distinct, across the three
definition kinds. -/
inductive Defs.Distinct : {s : Sig} → Defs s → Prop where
  | typ : Defs.Distinct (.typ A S)
  | cap : Defs.Distinct (.cap C c)
  | trm : Defs.Distinct (.trm a t)
  | and :
      Defs.Distinct d1 → Defs.Distinct d2 →
      (∀ ℓ, ℓ ∈ d1.labels → ℓ ∉ d2.labels) →
      Defs.Distinct (.and d1 d2)

end DotMNF

end CapturesCC
