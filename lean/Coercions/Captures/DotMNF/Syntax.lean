import Coercions.Captures.FCdot.Debruijn

namespace Captures

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

A capture atom is a term binder `{x}`, a capture binder `{κ}`, or the
capture member `C` of a term binder, `{x.C}`.  A capture set is a list of
atoms, read as the finite set of its members.  This mirrors the target's
`FCdot.CapAtom` and `FCdot.CaptureSet`, with `sel` for what the target calls
`name`. -/

inductive CapAtom : Sig → Type where
  /-- `{x}`, the capability of a term binder. -/
  | var : BVar s .var → CapAtom s
  /-- `{κ}`, a platform capture binder. -/
  | cvar : BVar s .cap → CapAtom s
  /-- `{x.C}`, the capture member `C` of the object `x`. -/
  | sel : BVar s .var → Label → CapAtom s
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

/-- Renaming of a capture atom: all three forms carry variables only. -/
def CapAtom.rename : CapAtom s1 → Rename s1 s2 → CapAtom s2
  | .var x, ρ => .var (ρ.var x)
  | .cvar κ, ρ => .cvar (ρ.var κ)
  | .sel x C, ρ => .sel (ρ.var x) C

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
  /-- Dependent function shape `∀(x : T₁) T₂`, on capturing types. -/
  | all : Ty s → Ty (s,x) → Shape s
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

mutual

def Shape.rename : Shape s1 → Rename s1 s2 → Shape s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, ρ => .typ A (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .cap C c1 c2, ρ => .cap C (c1.rename ρ) (c2.rename ρ)
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu S, ρ => .mu (S.rename ρ.lift)
  | .all T1 T2, ρ => .all (T1.rename ρ) (T2.rename ρ.lift)
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

@[simp] theorem Ty.shape_rename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).shape = T.shape.rename ρ := by cases T; rfl

@[simp] theorem Ty.captureSet_rename {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).captureSet = T.captureSet.rename ρ := by cases T; rfl

@[simp] theorem Ty.shape_weaken {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).shape = T.shape.weaken := by cases T; rfl

@[simp] theorem Ty.captureSet_weaken {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).captureSet = T.captureSet.weaken := by cases T; rfl

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
  | obj : Defs (s,x) → Value s
  | lam : Ty s → Tm (s,x) → Value s
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
  | .obj d, ρ => .obj (d.rename ρ.lift)
  | .lam T t, ρ => .lam (T.rename ρ) (t.rename ρ.lift)
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

end Captures
