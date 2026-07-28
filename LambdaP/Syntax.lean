import LambdaP.Debruijn

/-!
Syntax of λ_p: paths, types, and terms (monadic normal form).

Compared to the paper draft:
- Pair types ⟨x: S, a: T⟩ and ⟨x: S, A: S'..T'⟩ are two constructors
  (`pairTm`, `pairTy`) with the interval inlined, avoiding the mutual
  `Ty`/`Tau` inductives of the earlier skeleton. Judgments that need the
  paper's "generalized types" τ use a separate non-recursive wrapper.
- Pair terms hold variables (not paths), as in the paper; at runtime these
  are always heap locations, keeping stored values resolved.
-/

namespace LambdaP

/-- Member labels (both term members `a` and type members `A`). -/
abbrev Name : Type := Nat

/-- A path: a variable, first-projection, or term-member selection.
Type-member selections `p.A` are types, not paths (see `Ty.tsel`). -/
inductive Path : Sig -> Type where
| var : Var s -> Path s
| fst : Path s -> Path s
| sel : Path s -> Name -> Path s

/-- A type of λ_p. -/
inductive Ty : Sig -> Type where
/-- The top type ⊤. -/
| top : Ty s
/-- The bottom type ⊥. -/
| bot : Ty s
/-- Dependent function type (x: S) → T. -/
| arrow : Ty s -> Ty (s+1) -> Ty s
/-- Dependent pair type with a term member: ⟨x: S, a: T⟩. -/
| pairTm : Ty s -> Name -> Ty (s+1) -> Ty s
/-- Dependent pair type with a type member: ⟨x: S, A: S'..T'⟩,
    the interval S'..T' inlined as two types. -/
| pairTy : Ty s -> Name -> Ty (s+1) -> Ty (s+1) -> Ty s
/-- Singleton type: the path p seen as a type. -/
| single : Path s -> Ty s
/-- Type-member selection p.A. -/
| tsel : Path s -> Name -> Ty s

/-- A term of λ_p, in monadic normal form. -/
inductive Tm : Sig -> Type where
/-- Paths are terms (subsumes variables). -/
| path : Path s -> Tm s
/-- λ(x: T) t -/
| abs : Ty s -> Tm (s+1) -> Tm s
/-- Term-member pair ⟨y, a = z⟩. -/
| pairTm : Var s -> Name -> Var s -> Tm s
/-- Type-member pair ⟨y, A = T⟩. -/
| pairTy : Var s -> Name -> Ty s -> Tm s
/-- Application p q of paths. -/
| app : Path s -> Path s -> Tm s
/-- let x = s in t -/
| letin : Tm s -> Tm (s+1) -> Tm s
/-- Type ascription t : T. -/
| typed : Tm s -> Ty s -> Tm s

instance : Coe (Path s) (Ty s) where
  coe := Ty.single

instance : Coe (Path s) (Tm s) where
  coe := Tm.path

/-- Values: λ-abstractions and pairs. -/
inductive Tm.IsValue : Tm s -> Prop where
| abs : Tm.IsValue (.abs T t)
| pairTm : Tm.IsValue (.pairTm y a z)
| pairTy : Tm.IsValue (.pairTy y A T)

/-- Bound-variable predicate, for scoping rules to bound-rooted paths. -/
def Var.IsBound : Var s -> Prop
| .bound _ => True
| .free _ => False

/-- The root variable of a path (the only variable it contains). -/
def Path.root : Path s -> Var s
| .var x => x
| .fst p => p.root
| .sel p _ => p.root

/-! ### Renaming -/

/-- Applies a renaming to all bound variables in a path. -/
def Path.rename : Path s1 -> Rename s1 s2 -> Path s2
| .var x, f => .var (x.rename f)
| .fst p, f => .fst (p.rename f)
| .sel p a, f => .sel (p.rename f) a

theorem Path.root_rename {p : Path s1} {f : Rename s1 s2} :
    (p.rename f).root = p.root.rename f := by
  induction p with
  | var v => rfl
  | fst p ih => exact ih
  | sel p a ih => exact ih

theorem Path.root_isBound_rename {p : Path s1} {f : Rename s1 s2}
    (h : p.root.IsBound) : (p.rename f).root.IsBound := by
  rw [Path.root_rename]
  cases hv : p.root with
  | bound x => trivial
  | free ℓ => rw [hv] at h; exact h.elim

/-- Applies a renaming to all bound variables in a type. -/
def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .top, _ => .top
| .bot, _ => .bot
| .arrow S T, f => .arrow (S.rename f) (T.rename f.lift)
| .pairTm S a T, f => .pairTm (S.rename f) a (T.rename f.lift)
| .pairTy S A T1 T2, f => .pairTy (S.rename f) A (T1.rename f.lift) (T2.rename f.lift)
| .single p, f => .single (p.rename f)
| .tsel p A, f => .tsel (p.rename f) A

/-- Applies a renaming to all bound variables in a term. -/
def Tm.rename : Tm s1 -> Rename s1 s2 -> Tm s2
| .path p, f => .path (p.rename f)
| .abs T t, f => .abs (T.rename f) (t.rename f.lift)
| .pairTm y a z, f => .pairTm (y.rename f) a (z.rename f)
| .pairTy y A T, f => .pairTy (y.rename f) A (T.rename f)
| .app p q, f => .app (p.rename f) (q.rename f)
| .letin t1 t2, f => .letin (t1.rename f) (t2.rename f.lift)
| .typed t T, f => .typed (t.rename f) (T.rename f)

/-- Weakening by one binder. -/
def Path.weaken (p : Path s) : Path (s+1) := p.rename Rename.succ
/-- Weakening by one binder. -/
def Ty.weaken (T : Ty s) : Ty (s+1) := T.rename Rename.succ
/-- Weakening by one binder. -/
def Tm.weaken (t : Tm s) : Tm (s+1) := t.rename Rename.succ

/-- Renaming preserves being a value. -/
theorem Tm.IsValue.rename {t : Tm s1} (h : t.IsValue) (f : Rename s1 s2) :
    (t.rename f).IsValue := by
  cases h <;> constructor

/-- Renaming by the identity renaming leaves a path unchanged. -/
theorem Path.rename_id {p : Path s} : p.rename Rename.id = p := by
  induction p with
  | var x => simp [Path.rename, Var.rename_id]
  | fst p ih => simp [Path.rename, ih]
  | sel p a ih => simp [Path.rename, ih]

/-- Renaming distributes over composition of renamings. -/
theorem Path.rename_comp {p : Path s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (p.rename f).rename g = p.rename (f.comp g) := by
  induction p with
  | var x => simp [Path.rename, Var.rename_comp]
  | fst p ih => simp [Path.rename, ih]
  | sel p a ih => simp [Path.rename, ih]

/-- Renaming by the identity renaming leaves a type unchanged. -/
theorem Ty.rename_id {T : Ty s} : T.rename Rename.id = T := by
  induction T with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 =>
    simp [Ty.rename, Rename.lift_id, ih1, ih2]
  | pairTm S a T ih1 ih2 =>
    simp [Ty.rename, Rename.lift_id, ih1, ih2]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.rename, Rename.lift_id, ih1, ih2, ih3]
  | single p => simp [Ty.rename, Path.rename_id]
  | tsel p A => simp [Ty.rename, Path.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem Ty.rename_comp {T : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 =>
    simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  | pairTm S a T ih1 ih2 =>
    simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.rename, Rename.lift_comp, ih1, ih2, ih3]
  | single p => simp [Ty.rename, Path.rename_comp]
  | tsel p A => simp [Ty.rename, Path.rename_comp]

/-- Renaming by the identity renaming leaves a term unchanged. -/
theorem Tm.rename_id {t : Tm s} : t.rename Rename.id = t := by
  induction t with
  | path p => simp [Tm.rename, Path.rename_id]
  | abs T t ih => simp [Tm.rename, Rename.lift_id, Ty.rename_id, ih]
  | pairTm y a z => simp [Tm.rename, Var.rename_id]
  | pairTy y A T => simp [Tm.rename, Var.rename_id, Ty.rename_id]
  | app p q => simp [Tm.rename, Path.rename_id]
  | letin t1 t2 ih1 ih2 => simp [Tm.rename, Rename.lift_id, ih1, ih2]
  | typed t T ih => simp [Tm.rename, Ty.rename_id, ih]

/-- Renaming distributes over composition of renamings. -/
theorem Tm.rename_comp {t : Tm s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3 with
  | path p => simp [Tm.rename, Path.rename_comp]
  | abs T t ih => simp [Tm.rename, Rename.lift_comp, Ty.rename_comp, ih]
  | pairTm y a z => simp [Tm.rename, Var.rename_comp]
  | pairTy y A T => simp [Tm.rename, Var.rename_comp, Ty.rename_comp]
  | app p q => simp [Tm.rename, Path.rename_comp]
  | letin t1 t2 ih1 ih2 => simp [Tm.rename, Rename.lift_comp, ih1, ih2]
  | typed t T ih => simp [Tm.rename, Ty.rename_comp, ih]

/-- Weakening commutes with renaming under a binder. -/
theorem Path.weaken_rename_comm {p : Path s1} {f : Rename s1 s2} :
    p.weaken.rename f.lift = (p.rename f).weaken := by
  simp [Path.weaken, Path.rename_comp, Rename.succ_lift_comm]

/-- Weakening commutes with renaming under a binder. -/
theorem Ty.weaken_rename_comm {T : Ty s1} {f : Rename s1 s2} :
    T.weaken.rename f.lift = (T.rename f).weaken := by
  simp [Ty.weaken, Ty.rename_comp, Rename.succ_lift_comm]

/-- Weakening commutes with renaming under a binder. -/
theorem Tm.weaken_rename_comm {t : Tm s1} {f : Rename s1 s2} :
    t.weaken.rename f.lift = (t.rename f).weaken := by
  simp [Tm.weaken, Tm.rename_comp, Rename.succ_lift_comm]

end LambdaP
