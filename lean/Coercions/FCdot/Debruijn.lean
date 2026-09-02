/-!
# De Bruijn signatures for FCdot

The scoping discipline follows the ModalCapybara mechanization: a signature
is a list of binder kinds, a bound variable is a position of a given kind,
and renamings are functions on bound variables with lifting under binders.
This plan has a single binder kind; the discipline is kept so that further
kinds (capture variables, later) are additive.
-/

namespace FCdot

/-- Member labels.  Type labels and term labels are disjoint. -/
inductive Label : Type where
  | typ : Nat → Label
  | trm : Nat → Label
deriving DecidableEq, Repr

/-- Binder kinds.  Only term variables in this plan. -/
inductive Kind : Type where
  | var : Kind
deriving DecidableEq, Repr

/-- A signature: the shape of a context, newest binder first. -/
@[reducible]
def Sig : Type := List Kind

instance Sig.instEmptyCollection : EmptyCollection Sig where
  emptyCollection := []

/-- Extend a signature with one binder. -/
@[reducible] def Sig.extend (s : Sig) (k : Kind) : Sig := k :: s

/-- Extend a signature with a term variable. -/
@[reducible] def Sig.extend_var (s : Sig) : Sig := Sig.extend s .var

/-- Extend by a block of binders; the head of the block is newest. -/
def Sig.extendMany : Sig → Sig → Sig
  | s, [] => s
  | s, k :: K => (s.extendMany K).extend k

postfix:80 ",x" => Sig.extend_var
infixl:65 ",," => Sig.extend

instance Sig.instAppend : Append Sig where
  append := Sig.extendMany

@[simp] theorem Sig.extendMany_nil (s : Sig) : s.extendMany [] = s := rfl
@[simp] theorem Sig.extendMany_cons (s : Sig) (k : Kind) (K : Sig) :
    s.extendMany (k :: K) = (s.extendMany K).extend k := rfl

/-- Bound variables, de Bruijn indexed by position and kind. -/
inductive BVar : Sig → Kind → Type where
  | here : BVar (s,,k) k
  | there : BVar s k → BVar (s,,k0) k
deriving DecidableEq, Repr

/-- Renamings map bound variables between signatures, kind-preserving. -/
structure Rename (s1 s2 : Sig) where
  var : ∀ {k}, BVar s1 k → BVar s2 k

namespace Rename

def id {s : Sig} : Rename s s where
  var := fun x => x

def comp {s1 s2 s3 : Sig} (f : Rename s1 s2) (g : Rename s2 s3) : Rename s1 s3 where
  var := fun x => g.var (f.var x)

/-- Lift under one binder: the new binder maps to itself. -/
def lift {s1 s2 : Sig} (f : Rename s1 s2) {k : Kind} : Rename (s1,,k) (s2,,k) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

/-- Weakening: shift every variable under one new binder. -/
def succ {s : Sig} {k : Kind} : Rename s (s,,k) where
  var := fun x => .there x

/-- Substitute the innermost binder by a variable of the outer signature. -/
def subst {s : Sig} {k : Kind} (y : BVar s k) : Rename (s,,k) s where
  var := fun
    | .here => y
    | .there x => x

/-- Swap the two innermost binders. -/
def swap {s : Sig} {k1 k2 : Kind} : Rename (s,,k1,,k2) (s,,k2,,k1) where
  var := fun
    | .here => .there .here
    | .there .here => .here
    | .there (.there x) => .there (.there x)

theorem funext' {s1 s2 : Sig} {f g : Rename s1 s2}
    (h : ∀ {k} (x : BVar s1 k), f.var x = g.var x) : f = g := by
  cases f; cases g
  simp only [Rename.mk.injEq]
  funext k x
  exact h x

@[simp] theorem id_var {s : Sig} {k : Kind} (x : BVar s k) : (id : Rename s s).var x = x := rfl
@[simp] theorem comp_var {s1 s2 s3 : Sig} (f : Rename s1 s2) (g : Rename s2 s3) {k} (x : BVar s1 k) :
    (f.comp g).var x = g.var (f.var x) := rfl
@[simp] theorem lift_here {s1 s2 : Sig} (f : Rename s1 s2) {k : Kind} :
    (f.lift (k := k)).var .here = .here := rfl
@[simp] theorem lift_there {s1 s2 : Sig} (f : Rename s1 s2) {k k0 : Kind} (x : BVar s1 k) :
    (f.lift (k := k0)).var (.there x) = .there (f.var x) := rfl
@[simp] theorem succ_var {s : Sig} {k k0 : Kind} (x : BVar s k) :
    (succ (k := k0)).var x = .there x := rfl
@[simp] theorem subst_here {s : Sig} {k : Kind} (y : BVar s k) : (subst y).var .here = y := rfl
@[simp] theorem subst_there {s : Sig} {k k0 : Kind} (y : BVar s k0) (x : BVar s k) :
    (subst y).var (.there x) = x := rfl

theorem lift_id {s : Sig} {k : Kind} : (id : Rename s s).lift (k := k) = id := by
  apply funext'; intro k x; cases x <;> rfl

theorem lift_comp {s1 s2 s3 : Sig} (f : Rename s1 s2) (g : Rename s2 s3) {k : Kind} :
    (f.comp g).lift (k := k) = f.lift.comp g.lift := by
  apply funext'; intro k x; cases x <;> rfl

theorem succ_lift {s1 s2 : Sig} (f : Rename s1 s2) {k : Kind} :
    (succ (k := k)).comp f.lift = f.comp succ := by
  apply funext'; intro k x; rfl

theorem succ_subst {s : Sig} {k : Kind} (y : BVar s k) :
    (succ (k := k)).comp (subst y) = id := by
  apply funext'; intro k x; rfl

theorem id_comp {s1 s2 : Sig} (f : Rename s1 s2) : id.comp f = f := by
  apply funext'; intro k x; rfl

theorem comp_id {s1 s2 : Sig} (f : Rename s1 s2) : f.comp id = f := by
  apply funext'; intro k x; rfl

theorem comp_assoc {s1 s2 s3 s4 : Sig} (f : Rename s1 s2) (g : Rename s2 s3) (h : Rename s3 s4) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply funext'; intro k x; rfl

end Rename

end FCdot
