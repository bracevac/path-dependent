import Coercions.DotMNF.WadlerFest.LabelSorted

/-!
# The label-sorted public source calculus

These subtypes enforce the two label categories of the published grammar.
Their constructors take distinct `TypeLabel` and `TermLabel` types. Typing
and subtyping carry certificates for the entire internal derivation, not
merely its endpoints; hence every context and intermediate type is sorted.
Retained-let reduction is restricted to sorted terms and is closed on them.
The underlying representation and the FCdot translation are unchanged.
-/

namespace WadlerFest.Sorted

open FCdot (Sig BVar Rename Label)

structure TypeLabel where
  name : Nat
deriving DecidableEq

structure TermLabel where
  name : Nat
deriving DecidableEq

def TypeLabel.raw (A : TypeLabel) : Label := .typ A.name
def TermLabel.raw (a : TermLabel) : Label := .trm a.name

theorem labels_disjoint (A : TypeLabel) (a : TermLabel) : A.raw ≠ a.raw := by
  intro h
  cases h

abbrev Ty (s : Sig) := { T : DotMNF.Ty s // T.LabelSorted }
abbrev Tm (s : Sig) := { t : WadlerFest.Tm s // t.LabelSorted }
abbrev Value (s : Sig) := { v : WadlerFest.Value s // v.LabelSorted }
abbrev Defs (s : Sig) := { d : WadlerFest.Defs s // d.LabelSorted }
abbrev Ctx (s : Sig) := { Γ : WadlerFest.Ctx s // Γ.LabelSorted }
abbrev Store (s : Sig) := { σ : WadlerFest.Store s // σ.LabelSorted }

def Ty.top : Ty s := ⟨.top, .top⟩
def Ty.bot : Ty s := ⟨.bot, .bot⟩
def Ty.typ (A : TypeLabel) (S T : Ty s) : Ty s := ⟨.typ A.raw S.1 T.1, .typ S.property T.property⟩
def Ty.fld (a : TermLabel) (T : Ty s) : Ty s := ⟨.fld a.raw T.1, .fld T.property⟩
def Ty.sel (x : BVar s .var) (A : TypeLabel) : Ty s := ⟨.sel (.var x) A.raw, .sel⟩
def Ty.mu (T : Ty (s,x)) : Ty s := ⟨.mu T.1, .mu T.property⟩
def Ty.all (S : Ty s) (T : Ty (s,x)) : Ty s := ⟨.all S.1 T.1, .all S.property T.property⟩
def Ty.and (S T : Ty s) : Ty s := ⟨.and S.1 T.1, .and S.property T.property⟩

def Ty.rename (T : Ty s₁) (ρ : Rename s₁ s₂) : Ty s₂ := ⟨T.1.rename ρ, T.property.rename ρ⟩
def Ty.weaken (T : Ty s) : Ty (s,x) := T.rename Rename.succ
def Ty.substVar (T : Ty (s,x)) (y : BVar s .var) : Ty s := ⟨T.1.substVar y, T.property.substVar y⟩

@[simp] theorem Ty.open_self (T : Ty (s,x)) :
    (T.rename Rename.succ.lift).substVar .here = T :=
  Subtype.ext (DotMNF.Ty.open_self T.1)

def Tm.var (x : BVar s .var) : Tm s := ⟨.path (.var x), .path⟩
def Tm.val (v : Value s) : Tm s := ⟨.val v.1, .val v.property⟩
def Tm.app (x y : BVar s .var) : Tm s := ⟨.app x y, .app⟩
def Tm.proj (x : BVar s .var) (a : TermLabel) : Tm s := ⟨.proj x a.raw, .proj⟩
def Tm.«let» (t : Tm s) (u : Tm (s,x)) : Tm s := ⟨.let t.1 u.1, .let t.property u.property⟩
def Value.obj (T : Ty (s,x)) (d : Defs (s,x)) : Value s := ⟨.obj T.1 d.1, .obj T.property d.property⟩
def Value.lam (S : Ty s) (t : Tm (s,x)) : Value s := ⟨.lam S.1 t.1, .lam S.property t.property⟩
def Defs.typ (A : TypeLabel) (T : Ty s) : Defs s := ⟨.typ A.raw T.1, .typ T.property⟩
def Defs.trm (a : TermLabel) (t : Tm s) : Defs s := ⟨.trm a.raw t.1, .trm t.property⟩
def Defs.and (d₁ d₂ : Defs s) : Defs s := ⟨.and d₁.1 d₂.1, .and d₁.property d₂.property⟩
def Defs.labels (d : Defs s) : List Label := d.1.labels

def Tm.rename (t : Tm s₁) (ρ : Rename s₁ s₂) : Tm s₂ := ⟨t.1.rename ρ, t.property.rename ρ⟩
def Value.rename (v : Value s₁) (ρ : Rename s₁ s₂) : Value s₂ := ⟨v.1.rename ρ, v.property.rename ρ⟩
def Defs.rename (d : Defs s₁) (ρ : Rename s₁ s₂) : Defs s₂ := ⟨d.1.rename ρ, d.property.rename ρ⟩
def Tm.substVar (t : Tm (s,x)) (y : BVar s .var) : Tm s := ⟨t.1.substVar y, t.property.substVar y⟩

def Ctx.nil : Ctx [] := ⟨.nil, .nil⟩
def Ctx.extend (Γ : Ctx s) (T : Ty (s,x)) : Ctx (s,x) := ⟨Γ.1.extend T.1, Γ.property.extend T.property⟩
def Ctx.cons (Γ : Ctx s) (T : Ty s) : Ctx (s,x) := ⟨Γ.1.cons T.1, Γ.property.cons T.property⟩
def Ctx.lookup (Γ : Ctx s) (x : BVar s .var) : Ty s := ⟨Γ.1.lookup x, Γ.property x⟩

def Store.nil : Store [] := ⟨.nil, .nil⟩
def Store.cons (σ : Store s) (v : Value s) : Store (s,x) := ⟨.cons σ.1 v.1, .cons σ.property v.property⟩
def Store.lookup (σ : Store s) (x : BVar s .var) : Value s := ⟨σ.1.lookup x, σ.property.lookup x⟩

/-- A subtyping derivation whose every judgment respects label categories. -/
structure Sub (Γ : Ctx s) (S T : Ty s) where
  raw : WadlerFest.Sub Γ.1 S.1 T.1
  sorted : raw.LabelSorted

/-- A typing derivation whose contexts, terms, and intermediate types are sorted. -/
structure HasTy (Γ : Ctx s) (t : Tm s) (T : Ty s) where
  raw : WadlerFest.HasTy Γ.1 t.1 T.1
  sorted : raw.LabelSorted

structure DefsTy (Γ : Ctx s) (d : Defs s) (T : Ty s) where
  raw : WadlerFest.DefsTy Γ.1 d.1 T.1
  sorted : raw.LabelSorted

def Sub.top {Γ : Ctx s} {T : Ty s} : Sub Γ T .top :=
  ⟨.top, Γ.property, T.property, .top, trivial⟩
def Sub.bot {Γ : Ctx s} {T : Ty s} : Sub Γ .bot T :=
  ⟨.bot, Γ.property, .bot, T.property, trivial⟩
def Sub.refl {Γ : Ctx s} {T : Ty s} : Sub Γ T T :=
  ⟨.refl, Γ.property, T.property, T.property, trivial⟩
def Sub.trans {Γ : Ctx s} {S M T : Ty s} (h₁ : Sub Γ S M) (h₂ : Sub Γ M T) : Sub Γ S T :=
  ⟨.trans h₁.raw h₂.raw, Γ.property, S.property, T.property, h₁.sorted, h₂.sorted⟩
def Sub.and1 {Γ : Ctx s} {S T : Ty s} : Sub Γ (.and S T) S :=
  ⟨.and1, Γ.property, .and S.property T.property, S.property, trivial⟩
def Sub.and2 {Γ : Ctx s} {S T : Ty s} : Sub Γ (.and S T) T :=
  ⟨.and2, Γ.property, .and S.property T.property, T.property, trivial⟩
def Sub.and {Γ : Ctx s} {S T U : Ty s} (h₁ : Sub Γ S T) (h₂ : Sub Γ S U) : Sub Γ S (.and T U) :=
  ⟨.and h₁.raw h₂.raw, Γ.property, S.property, .and T.property U.property, h₁.sorted, h₂.sorted⟩
def Sub.fld {Γ : Ctx s} {T U : Ty s} {a : TermLabel} (h : Sub Γ T U) : Sub Γ (.fld a T) (.fld a U) :=
  ⟨.fld h.raw, Γ.property, .fld T.property, .fld U.property, h.sorted⟩
def Sub.typ {Γ : Ctx s} {S₁ S₂ T₁ T₂ : Ty s} {A : TypeLabel}
    (h₁ : Sub Γ S₂ S₁) (h₂ : Sub Γ T₁ T₂) : Sub Γ (.typ A S₁ T₁) (.typ A S₂ T₂) :=
  ⟨.typ h₁.raw h₂.raw, Γ.property, .typ S₁.property T₁.property,
    .typ S₂.property T₂.property, h₁.sorted, h₂.sorted⟩
def Sub.selUpper {Γ : Ctx s} {x : BVar s .var} {A : TypeLabel} {S T : Ty s}
    (h : HasTy Γ (.var x) (.typ A S T)) : Sub Γ (.sel x A) T :=
  ⟨.selUpper h.raw, Γ.property, .sel, T.property, h.sorted⟩
def Sub.selLower {Γ : Ctx s} {x : BVar s .var} {A : TypeLabel} {S T : Ty s}
    (h : HasTy Γ (.var x) (.typ A S T)) : Sub Γ S (.sel x A) :=
  ⟨.selLower h.raw, Γ.property, S.property, .sel, h.sorted⟩
def Sub.all {Γ : Ctx s} {S₁ S₂ : Ty s} {T₁ T₂ : Ty (s,x)}
    (h₁ : Sub Γ S₂ S₁) (h₂ : Sub (Γ.cons S₂) T₁ T₂) : Sub Γ (.all S₁ T₁) (.all S₂ T₂) :=
  ⟨.all h₁.raw h₂.raw, Γ.property, .all S₁.property T₁.property,
    .all S₂.property T₂.property, h₁.sorted, h₂.sorted⟩

def HasTy.var {Γ : Ctx s} {x : BVar s .var} : HasTy Γ (.var x) (Γ.lookup x) :=
  ⟨.var, Γ.property, .path, Γ.property x, trivial⟩
def HasTy.lam {Γ : Ctx s} {S : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (h : HasTy (Γ.cons S) t T) : HasTy Γ (.val (.lam S t)) (.all S T) :=
  ⟨.lam h.raw, Γ.property, .val (.lam S.property t.property), .all S.property T.property, h.sorted⟩
def HasTy.app {Γ : Ctx s} {x y : BVar s .var} {S : Ty s} {T : Ty (s,x)}
    (h₁ : HasTy Γ (.var x) (.all S T)) (h₂ : HasTy Γ (.var y) S) : HasTy Γ (.app x y) (T.substVar y) :=
  ⟨.app h₁.raw h₂.raw, Γ.property, .app, T.property.substVar y, h₁.sorted, h₂.sorted⟩
def HasTy.obj {Γ : Ctx s} {T : Ty (s,x)} {d : Defs (s,x)}
    (h : DefsTy (Γ.extend T) d T) : HasTy Γ (.val (.obj T d)) (.mu T) :=
  ⟨.obj h.raw, Γ.property, .val (.obj T.property d.property), .mu T.property, h.sorted⟩
def HasTy.proj {Γ : Ctx s} {x : BVar s .var} {a : TermLabel} {T : Ty s}
    (h : HasTy Γ (.var x) (.fld a T)) : HasTy Γ (.proj x a) T :=
  ⟨.proj h.raw, Γ.property, .proj, T.property, h.sorted⟩
def HasTy.«let» {Γ : Ctx s} {t : Tm s} {u : Tm (s,x)} {T U : Ty s}
    (h₁ : HasTy Γ t T) (h₂ : HasTy (Γ.cons T) u U.weaken) : HasTy Γ (.let t u) U :=
  ⟨.let h₁.raw h₂.raw, Γ.property, .let t.property u.property, U.property, h₁.sorted, h₂.sorted⟩
def HasTy.recI {Γ : Ctx s} {x : BVar s .var} {T : Ty (s,x)}
    (h : HasTy Γ (.var x) (T.substVar x)) : HasTy Γ (.var x) (.mu T) :=
  ⟨.recI h.raw, Γ.property, .path, .mu T.property, h.sorted⟩
def HasTy.recE {Γ : Ctx s} {x : BVar s .var} {T : Ty (s,x)}
    (h : HasTy Γ (.var x) (.mu T)) : HasTy Γ (.var x) (T.substVar x) :=
  ⟨.recE h.raw, Γ.property, .path, T.property.substVar x, h.sorted⟩
def HasTy.andI {Γ : Ctx s} {x : BVar s .var} {T U : Ty s}
    (h₁ : HasTy Γ (.var x) T) (h₂ : HasTy Γ (.var x) U) : HasTy Γ (.var x) (.and T U) :=
  ⟨.andI h₁.raw h₂.raw, Γ.property, .path, .and T.property U.property, h₁.sorted, h₂.sorted⟩
def HasTy.sub {Γ : Ctx s} {t : Tm s} {T U : Ty s}
    (h₁ : HasTy Γ t T) (h₂ : Sub Γ T U) : HasTy Γ t U :=
  ⟨.sub h₁.raw h₂.raw, Γ.property, t.property, U.property, h₁.sorted, h₂.sorted⟩

def DefsTy.typ {Γ : Ctx s} {A : TypeLabel} {T : Ty s} : DefsTy Γ (.typ A T) (.typ A T T) :=
  ⟨.typ, Γ.property, .typ T.property, .typ T.property T.property, trivial⟩
def DefsTy.trm {Γ : Ctx s} {a : TermLabel} {t : Tm s} {T : Ty s}
    (h : HasTy Γ t T) : DefsTy Γ (.trm a t) (.fld a T) :=
  ⟨.trm h.raw, Γ.property, .trm t.property, .fld T.property, h.sorted⟩
def DefsTy.and {Γ : Ctx s} {d₁ d₂ : Defs s} {T₁ T₂ : Ty s}
    (h₁ : DefsTy Γ d₁ T₁) (h₂ : DefsTy Γ d₂ T₂)
    (hd : ∀ ℓ, ℓ ∈ d₁.labels → ℓ ∉ d₂.labels) : DefsTy Γ (.and d₁ d₂) (.and T₁ T₂) :=
  ⟨.and h₁.raw h₂.raw hd, Γ.property, .and d₁.property d₂.property,
    .and T₁.property T₂.property, h₁.sorted, h₂.sorted⟩

/-- The public reduction relates only label-sorted terms and ambient stores. -/
def Red (σ : Store s) (t u : Tm s) : Prop := WadlerFest.Retained.Red σ.1 t.1 u.1

/-- Every intermediate term in a public execution belongs to sorted syntax. -/
inductive Steps (σ : Store s) : Tm s → Tm s → Prop where
  | refl : Steps σ t t
  | tail : Steps σ t u → Red σ u v → Steps σ t v

def Answer (t : Tm s) : Prop := WadlerFest.Retained.Answer t.1
def Stuck (σ : Store s) (t : Tm s) : Prop := ¬ Answer t ∧ ¬ ∃ u, Red σ t u

/-- Every internal step from a public term has a public target. -/
theorem Red.closed {σ : Store s} {t : Tm s} {u : WadlerFest.Tm s}
    (h : WadlerFest.Retained.Red σ.1 t.1 u) :
    ∃ u' : Tm s, u'.1 = u ∧ Red σ t u' :=
  ⟨⟨u, h.labelSorted σ.property t.property⟩, rfl, h⟩

theorem Steps.raw {σ : Store s} {t u : Tm s} (h : Steps σ t u) :
    WadlerFest.Retained.Steps σ.1 t.1 u.1 := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih h

theorem Steps.ofRaw {σ : Store s} {t u : WadlerFest.Tm s}
    (h : WadlerFest.Retained.Steps σ.1 t u) (ht : t.LabelSorted) :
    Steps σ ⟨t, ht⟩ ⟨u, h.labelSorted σ.property ht⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih h

theorem Steps.closed {σ : Store s} {t : Tm s} {u : WadlerFest.Tm s}
    (h : WadlerFest.Retained.Steps σ.1 t.1 u) :
    ∃ u' : Tm s, u'.1 = u ∧ Steps σ t u' :=
  ⟨⟨u, h.labelSorted σ.property t.property⟩, rfl, Steps.ofRaw h t.property⟩

theorem Steps.single {σ : Store s} {t u : Tm s} (h : Red σ t u) : Steps σ t u := .tail .refl h
theorem Steps.trans {σ : Store s} {t u v : Tm s} (h₁ : Steps σ t u) (h₂ : Steps σ u v) :
    Steps σ t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

/-- Wrong label categories cannot be packaged as public syntax. -/
theorem reject_type_field (T : DotMNF.Ty s) (A : Nat) :
    ¬ (DotMNF.Ty.fld (.typ A) T).LabelSorted := by intro h; cases h

theorem reject_term_selection (x : BVar s .var) (a : Nat) :
    ¬ (DotMNF.Ty.sel (.var x) (.trm a)).LabelSorted := by intro h; cases h

theorem reject_type_projection (x : BVar s .var) (A : Nat) :
    ¬ (WadlerFest.Tm.proj x (.typ A)).LabelSorted := by intro h; cases h

theorem reject_term_definition (T : DotMNF.Ty s) (a : Nat) :
    ¬ (WadlerFest.Defs.typ (.trm a) T).LabelSorted := by intro h; cases h

namespace Examples

/-- Equal numeric names still inhabit disjoint label categories. -/
def A : TypeLabel := ⟨0⟩
def a : TermLabel := ⟨0⟩

def selfType : Ty ([],x) :=
  .and (.typ A .top .top) (.fld a (.sel .here A))

def objectDefs : Defs ([],x) :=
  .and (.typ A .top) (.trm a (.var .here))

def object : Tm [] := .val (.obj selfType objectDefs)
def openedSelf : Ctx ([],x) := Ctx.nil.extend selfType

def selfAlias : HasTy openedSelf (.var .here) (.typ A .top .top) :=
  .sub .var .and1

def selfAtSelection : HasTy openedSelf (.var .here) (.sel .here A) :=
  .sub .var (.trans .top (.selLower selfAlias))

def objectDefs_typed : DefsTy openedSelf objectDefs selfType :=
  .and .typ (.trm selfAtSelection) (by
    intro ℓ h
    simp only [Defs.labels, Defs.typ, Defs.trm, WadlerFest.Defs.labels,
      List.mem_singleton] at h ⊢
    subst ℓ
    exact labels_disjoint A a)

def object_typed : HasTy .nil object (.mu selfType) := .obj objectDefs_typed
def boundObject : Ctx ([],x) := Ctx.nil.cons (.mu selfType)

def boundSelf : HasTy boundObject (.var .here) selfType := by
  have h : HasTy boundObject (.var .here)
      ((selfType.rename Rename.succ.lift).substVar .here) := .recE .var
  simpa only [Ty.open_self] using h

def projection_typed : HasTy boundObject (.proj .here a) .top :=
  .sub (.proj (.sub boundSelf .and2)) (.selUpper (.sub boundSelf .and1))

/-- The self-dependent example is constructed and typed entirely through
the public interface, with a certificate for every intermediate judgment. -/
def program : Tm [] := .let object (.proj .here a)
def program_typed : HasTy .nil program .top := .let object_typed projection_typed
def answer : Tm [] := .let object (.var .here)

/-- Projection returns the object itself under its retained value binding. -/
theorem program_step : Red .nil program answer :=
  WadlerFest.Retained.Red.letValue
    (.proj (t := .path (.var .here)) rfl (.andRight .trm))

theorem program_runs : Steps .nil program answer := Steps.single program_step
theorem answer_isAnswer : Answer answer := .letValue .path

end Examples

end WadlerFest.Sorted
