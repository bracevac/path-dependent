import LambdaP.Syntax

/-!
Substitution for λ_p, ported from CoreCapybara's `Substitution.lean`.

λ_p substitutes *paths* for variables in types (`[x := p.1]τ`, `[z := q]T`),
but terms contain bare variables in pair components, so there are two
substitution structures sharing one lemma library:

- `Subst`  maps bound variables to paths; it acts on `Path` and `Ty` and is
  what the typing rules use.
- `VSubst` maps bound variables to variables (capybara's `Subst.var` field
  exactly); it acts on `Tm` (embedded types via `VSubst.toSubst`). All
  runtime steps use `VSubst`s whose images are heap locations.
-/

namespace LambdaP

/-- A substitution mapping bound variables to paths. -/
structure Subst (s1 s2 : Sig) where
  var : BVar s1 -> Path s2

/-- Lifts a substitution under a binder. The newly bound variable maps to itself. -/
def Subst.lift (σ : Subst s1 s2) : Subst (s1+1) (s2+1) where
  var := fun
    | .here => .var (.bound .here)
    | .there x => (σ.var x).rename Rename.succ

/-- The identity substitution. -/
def Subst.id {s : Sig} : Subst s s where
  var := fun x => .var (.bound x)

/-- Substitution that opens a binder by replacing the innermost bound variable
with the path `p`. -/
def Subst.openPath (p : Path s) : Subst (s+1) s where
  var := fun
    | .here => p
    | .there x => .var (.bound x)

/-- Function extensionality for substitutions. -/
theorem Subst.funext {σ1 σ2 : Subst s1 s2}
    (hvar : ∀ (x : BVar s1), σ1.var x = σ2.var x) : σ1 = σ2 := by
  cases σ1; cases σ2; congr 1; funext x; exact hvar x

/-- Applies a substitution to a variable, yielding a path.
Free variables remain unchanged. -/
def Var.subst : Var s1 -> Subst s1 s2 -> Path s2
| .bound x, σ => σ.var x
| .free n, _ => .var (.free n)

/-- Applies a substitution to a path. -/
def Path.subst : Path s1 -> Subst s1 s2 -> Path s2
| .var x, σ => x.subst σ
| .fst p, σ => .fst (p.subst σ)
| .sel p a, σ => .sel (p.subst σ) a

theorem Path.root_isBound_subst {p : Path s1} {σ : Subst s1 s2}
    (h : p.root.IsBound) (hb : ∀ x : BVar s1, (σ.var x).root.IsBound) :
    (p.subst σ).root.IsBound := by
  induction p with
  | var v => cases v with
    | bound x => exact hb x
    | free ℓ => exact h.elim
  | fst p ih => exact ih h
  | sel p a ih => exact ih h

/-- Applies a substitution to a type. -/
def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .top, _ => .top
| .bot, _ => .bot
| .arrow S T, σ => .arrow (S.subst σ) (T.subst σ.lift)
| .pairTm S a T, σ => .pairTm (S.subst σ) a (T.subst σ.lift)
| .pairTy S A T1 T2, σ => .pairTy (S.subst σ) A (T1.subst σ.lift) (T2.subst σ.lift)
| .single p, σ => .single (p.subst σ)
| .tsel p A, σ => .tsel (p.subst σ) A

/-- Composition of substitutions (diagrammatic order). -/
def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2

/-- Post-composes a substitution with a renaming: substitute, then rename the images. -/
def Subst.compRename (σ : Subst s1 s2) (f : Rename s2 s3) : Subst s1 s3 where
  var := fun x => (σ.var x).rename f

/-- Pre-composes a renaming with a substitution: rename the variable, then substitute. -/
def Rename.compSubst (f : Rename s1 s2) (σ : Subst s2 s3) : Subst s1 s3 where
  var := fun x => σ.var (f.var x)

/-- Converts a renaming to a substitution. -/
def Rename.asSubst (f : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .var (.bound (f.var x))

/-! ### Substitute-then-rename equals substituting by `σ.compRename f` -/

theorem Var.subst_rename_comm {x : Var s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
    (x.subst σ).rename f = x.subst (σ.compRename f) := by
  cases x <;> rfl

theorem Path.subst_rename_comm {p : Path s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
    (p.subst σ).rename f = p.subst (σ.compRename f) := by
  induction p with
  | var x => exact Var.subst_rename_comm
  | fst p ih => simp [Path.subst, Path.rename, ih]
  | sel p a ih => simp [Path.subst, Path.rename, ih]

/-- `compRename` commutes with lifting. -/
theorem Subst.compRename_lift {σ : Subst s1 s2} {f : Rename s2 s3} :
    (σ.compRename f).lift = σ.lift.compRename f.lift := by
  apply Subst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    simp [Subst.lift, Subst.compRename, Path.rename_comp, Rename.succ_lift_comm]

theorem Ty.subst_rename_comm {T : Ty s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
    (T.subst σ).rename f = T.subst (σ.compRename f) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, Subst.compRename_lift]
  | pairTm S a T ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, Subst.compRename_lift]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, ih3, Subst.compRename_lift]
  | single p => simp [Ty.subst, Ty.rename, Path.subst_rename_comm]
  | tsel p A => simp [Ty.subst, Ty.rename, Path.subst_rename_comm]

/-! ### Rename-then-substitute equals substituting by `f.compSubst σ` -/

theorem Var.rename_subst_comm {x : Var s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
    (x.rename f).subst σ = x.subst (f.compSubst σ) := by
  cases x <;> rfl

theorem Path.rename_subst_comm {p : Path s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
    (p.rename f).subst σ = p.subst (f.compSubst σ) := by
  induction p with
  | var x => exact Var.rename_subst_comm
  | fst p ih => simp [Path.subst, Path.rename, ih]
  | sel p a ih => simp [Path.subst, Path.rename, ih]

/-- `compSubst` commutes with lifting. -/
theorem Rename.compSubst_lift {f : Rename s1 s2} {σ : Subst s2 s3} :
    (f.compSubst σ).lift = f.lift.compSubst σ.lift := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Ty.rename_subst_comm {T : Ty s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
    (T.rename f).subst σ = T.subst (f.compSubst σ) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, Rename.compSubst_lift]
  | pairTm S a T ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, Rename.compSubst_lift]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.subst, Ty.rename, ih1, ih2, ih3, Rename.compSubst_lift]
  | single p => simp [Ty.subst, Ty.rename, Path.rename_subst_comm]
  | tsel p A => simp [Ty.subst, Ty.rename, Path.rename_subst_comm]

/-- Weakening then substituting under the lift is substituting then weakening,
at the level of substitutions. -/
theorem Subst.succ_lift_comm {σ : Subst s1 s2} :
    Rename.succ.compSubst σ.lift = σ.compRename Rename.succ := by
  apply Subst.funext
  intro x
  rfl

/-- Weakening commutes with substitution under a binder. -/
theorem Ty.weaken_subst_comm {T : Ty s1} {σ : Subst s1 s2} :
    T.weaken.subst σ.lift = (T.subst σ).weaken := by
  simp [Ty.weaken, Ty.rename_subst_comm, Ty.subst_rename_comm, Subst.succ_lift_comm]

theorem Path.weaken_subst_comm {p : Path s1} {σ : Subst s1 s2} :
    p.weaken.subst σ.lift = (p.subst σ).weaken := by
  simp [Path.weaken, Path.rename_subst_comm, Path.subst_rename_comm, Subst.succ_lift_comm]

/-! ### Composition -/

theorem Var.subst_comp {x : Var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
    (x.subst σ1).subst σ2 = x.subst (σ1.comp σ2) := by
  cases x <;> rfl

theorem Path.subst_comp {p : Path s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
    (p.subst σ1).subst σ2 = p.subst (σ1.comp σ2) := by
  induction p with
  | var x => exact Var.subst_comp
  | fst p ih => simp [Path.subst, ih]
  | sel p a ih => simp [Path.subst, ih]

/-- Composition of substitutions commutes with lifting. -/
theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
    (σ1.comp σ2).lift = σ1.lift.comp σ2.lift := by
  apply Subst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    show ((σ1.var x).subst σ2).rename Rename.succ
       = ((σ1.var x).rename Rename.succ).subst σ2.lift
    simp [Path.subst_rename_comm, Path.rename_subst_comm, Subst.succ_lift_comm]

theorem Ty.subst_comp {T : Ty s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
    (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]
  | pairTm S a T ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.subst, ih1, ih2, ih3, Subst.comp_lift]
  | single p => simp [Ty.subst, Path.subst_comp]
  | tsel p A => simp [Ty.subst, Path.subst_comp]

/-! ### Identity -/

theorem Subst.lift_id : (Subst.id (s := s)).lift = Subst.id := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Var.subst_id {x : Var s} : x.subst Subst.id = .var x := by
  cases x <;> rfl

theorem Path.subst_id {p : Path s} : p.subst Subst.id = p := by
  induction p with
  | var x => exact Var.subst_id
  | fst p ih => simp [Path.subst, ih]
  | sel p a ih => simp [Path.subst, ih]

theorem Ty.subst_id {T : Ty s} : T.subst Subst.id = T := by
  induction T with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 => simp [Ty.subst, Subst.lift_id, ih1, ih2]
  | pairTm S a T ih1 ih2 => simp [Ty.subst, Subst.lift_id, ih1, ih2]
  | pairTy S A T1 T2 ih1 ih2 ih3 => simp [Ty.subst, Subst.lift_id, ih1, ih2, ih3]
  | single p => simp [Ty.subst, Path.subst_id]
  | tsel p A => simp [Ty.subst, Path.subst_id]

/-! ### Renamings as substitutions -/

theorem Rename.asSubst_lift {f : Rename s1 s2} : f.lift.asSubst = f.asSubst.lift := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Var.subst_asSubst {x : Var s1} {f : Rename s1 s2} :
    x.subst f.asSubst = .var (x.rename f) := by
  cases x <;> rfl

theorem Path.subst_asSubst {p : Path s1} {f : Rename s1 s2} :
    p.subst f.asSubst = p.rename f := by
  induction p with
  | var x => exact Var.subst_asSubst
  | fst p ih => simp [Path.subst, Path.rename, ih]
  | sel p a ih => simp [Path.subst, Path.rename, ih]

theorem Ty.subst_asSubst {T : Ty s1} {f : Rename s1 s2} :
    T.subst f.asSubst = T.rename f := by
  induction T generalizing s2 with
  | top => rfl
  | bot => rfl
  | arrow S T ih1 ih2 => simp [Ty.subst, Ty.rename, ← Rename.asSubst_lift, ih1, ih2]
  | pairTm S a T ih1 ih2 => simp [Ty.subst, Ty.rename, ← Rename.asSubst_lift, ih1, ih2]
  | pairTy S A T1 T2 ih1 ih2 ih3 =>
    simp [Ty.subst, Ty.rename, ← Rename.asSubst_lift, ih1, ih2, ih3]
  | single p => simp [Ty.subst, Ty.rename, Path.subst_asSubst]
  | tsel p A => simp [Ty.subst, Ty.rename, Path.subst_asSubst]

/-! ### Opening -/

/-- Weakening followed by opening is the identity, at the level of substitutions. -/
theorem Subst.weaken_openPath {p : Path s} :
    Rename.succ.compSubst (Subst.openPath p) = Subst.id := by
  apply Subst.funext
  intro x
  rfl

/-- Opens the innermost binder of a type with a path. -/
def Ty.open (T : Ty (s+1)) (p : Path s) : Ty s := T.subst (Subst.openPath p)

/-- Weakening then opening is the identity. -/
theorem Ty.weaken_open {T : Ty s} {p : Path s} : T.weaken.open p = T := by
  simp [Ty.open, Ty.weaken, Ty.rename_subst_comm, Subst.weaken_openPath, Ty.subst_id]

theorem Path.weaken_open {q : Path s} {p : Path s} :
    q.weaken.subst (Subst.openPath p) = q := by
  simp [Path.weaken, Path.rename_subst_comm, Subst.weaken_openPath, Path.subst_id]

/-- Renaming commutes with opening. -/
theorem Subst.openPath_rename_comm {p : Path s1} {f : Rename s1 s2} :
    f.lift.compSubst (Subst.openPath (p.rename f)) = (Subst.openPath p).compRename f := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Ty.open_rename_comm {T : Ty (s1+1)} {p : Path s1} {f : Rename s1 s2} :
    (T.rename f.lift).open (p.rename f) = (T.open p).rename f := by
  simp [Ty.open, Ty.rename_subst_comm, Ty.subst_rename_comm, Subst.openPath_rename_comm]

/-- Substitution commutes with opening, at the level of substitutions. -/
theorem Subst.openPath_subst_comm {p : Path s1} {σ : Subst s1 s2} :
    σ.lift.comp (Subst.openPath (p.subst σ)) = (Subst.openPath p).comp σ := by
  apply Subst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    show ((σ.var x).rename Rename.succ).subst (Subst.openPath (p.subst σ)) = σ.var x
    simp [Path.rename_subst_comm, Subst.weaken_openPath, Path.subst_id]

/-- Substitution commutes with opening. -/
theorem Ty.open_subst_comm {T : Ty (s1+1)} {p : Path s1} {σ : Subst s1 s2} :
    (T.subst σ.lift).open (p.subst σ) = (T.open p).subst σ := by
  simp [Ty.open, Ty.subst_comp, Subst.openPath_subst_comm]

/-! ### Variable substitutions (for terms) -/

/-- A substitution mapping bound variables to variables (not general paths).
Terms hold bare variables in pair components, so term substitution requires
variable images; at runtime all images are heap locations. -/
structure VSubst (s1 s2 : Sig) where
  var : BVar s1 -> Var s2

/-- Lifts a variable substitution under a binder. -/
def VSubst.lift (σ : VSubst s1 s2) : VSubst (s1+1) (s2+1) where
  var := fun
    | .here => .bound .here
    | .there x => (σ.var x).rename Rename.succ

/-- The identity variable substitution. -/
def VSubst.id {s : Sig} : VSubst s s where
  var := fun x => .bound x

/-- Opens a binder with the variable `y`. -/
def VSubst.openVar (y : Var s) : VSubst (s+1) s where
  var := fun
    | .here => y
    | .there x => .bound x

/-- Every variable substitution is a path substitution. -/
def VSubst.toSubst (σ : VSubst s1 s2) : Subst s1 s2 where
  var := fun x => .var (σ.var x)

theorem VSubst.funext {σ1 σ2 : VSubst s1 s2}
    (hvar : ∀ (x : BVar s1), σ1.var x = σ2.var x) : σ1 = σ2 := by
  cases σ1; cases σ2; congr 1; funext x; exact hvar x

/-- Applies a variable substitution to a variable. -/
def Var.vsubst : Var s1 -> VSubst s1 s2 -> Var s2
| .bound x, σ => σ.var x
| .free n, _ => .free n

/-- Applies a variable substitution to a term. Embedded paths and types are
substituted via `VSubst.toSubst`. -/
def Tm.subst : Tm s1 -> VSubst s1 s2 -> Tm s2
| .path p, σ => .path (p.subst σ.toSubst)
| .abs T t, σ => .abs (T.subst σ.toSubst) (t.subst σ.lift)
| .pairTm y a z, σ => .pairTm (y.vsubst σ) a (z.vsubst σ)
| .pairTy y A T, σ => .pairTy (y.vsubst σ) A (T.subst σ.toSubst)
| .app p q, σ => .app (p.subst σ.toSubst) (q.subst σ.toSubst)
| .letin t1 t2, σ => .letin (t1.subst σ) (t2.subst σ.lift)
| .typed t T, σ => .typed (t.subst σ) (T.subst σ.toSubst)

/-- Opens the innermost binder of a term with a variable. -/
def Tm.open (t : Tm (s+1)) (y : Var s) : Tm s := t.subst (VSubst.openVar y)

/-- `toSubst` commutes with lifting. -/
theorem VSubst.toSubst_lift {σ : VSubst s1 s2} : σ.lift.toSubst = σ.toSubst.lift := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem VSubst.toSubst_id : (VSubst.id (s := s)).toSubst = Subst.id := by
  apply Subst.funext
  intro x
  rfl

theorem VSubst.openVar_toSubst {y : Var s} :
    (VSubst.openVar y).toSubst = Subst.openPath (.var y) := by
  apply Subst.funext
  intro x
  cases x <;> rfl

/-- Substitution preserves being a value. -/
theorem Tm.IsValue.subst {t : Tm s1} (h : t.IsValue) (σ : VSubst s1 s2) :
    (t.subst σ).IsValue := by
  cases h <;> constructor

/-! ### Composition and identity for variable substitutions -/

/-- Composition of variable substitutions. -/
def VSubst.comp (σ1 : VSubst s1 s2) (σ2 : VSubst s2 s3) : VSubst s1 s3 where
  var := fun x => (σ1.var x).vsubst σ2

/-- Post-composes a variable substitution with a renaming. -/
def VSubst.compRename (σ : VSubst s1 s2) (f : Rename s2 s3) : VSubst s1 s3 where
  var := fun x => (σ.var x).rename f

/-- Pre-composes a renaming with a variable substitution. -/
def Rename.compVSubst (f : Rename s1 s2) (σ : VSubst s2 s3) : VSubst s1 s3 where
  var := fun x => σ.var (f.var x)

theorem Var.vsubst_id {x : Var s} : x.vsubst VSubst.id = x := by
  cases x <;> rfl

theorem VSubst.lift_id : (VSubst.id (s := s)).lift = VSubst.id := by
  apply VSubst.funext
  intro x
  cases x <;> rfl

theorem Tm.subst_id {t : Tm s} : t.subst VSubst.id = t := by
  induction t with
  | path p => simp [Tm.subst, VSubst.toSubst_id, Path.subst_id]
  | abs T t ih => simp [Tm.subst, VSubst.toSubst_id, VSubst.lift_id, Ty.subst_id, ih]
  | pairTm y a z => simp [Tm.subst, Var.vsubst_id]
  | pairTy y A T => simp [Tm.subst, VSubst.toSubst_id, Var.vsubst_id, Ty.subst_id]
  | app p q => simp [Tm.subst, VSubst.toSubst_id, Path.subst_id]
  | letin t1 t2 ih1 ih2 => simp [Tm.subst, VSubst.lift_id, ih1, ih2]
  | typed t T ih => simp [Tm.subst, VSubst.toSubst_id, Ty.subst_id, ih]

/-! ### Commutation lemmas for variable substitutions on terms -/

theorem Var.vsubst_rename_comm {x : Var s1} {σ : VSubst s1 s2} {f : Rename s2 s3} :
    (x.vsubst σ).rename f = x.vsubst (σ.compRename f) := by
  cases x <;> rfl

theorem Var.rename_vsubst_comm {x : Var s1} {f : Rename s1 s2} {σ : VSubst s2 s3} :
    (x.rename f).vsubst σ = x.vsubst (f.compVSubst σ) := by
  cases x <;> rfl

theorem Var.vsubst_comp {x : Var s1} {σ1 : VSubst s1 s2} {σ2 : VSubst s2 s3} :
    (x.vsubst σ1).vsubst σ2 = x.vsubst (σ1.comp σ2) := by
  cases x <;> rfl

theorem VSubst.compRename_lift {σ : VSubst s1 s2} {f : Rename s2 s3} :
    (σ.compRename f).lift = σ.lift.compRename f.lift := by
  apply VSubst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    simp [VSubst.lift, VSubst.compRename, Var.rename_comp, Rename.succ_lift_comm]

theorem Rename.compVSubst_lift {f : Rename s1 s2} {σ : VSubst s2 s3} :
    (f.compVSubst σ).lift = f.lift.compVSubst σ.lift := by
  apply VSubst.funext
  intro x
  cases x <;> rfl

theorem VSubst.comp_lift {σ1 : VSubst s1 s2} {σ2 : VSubst s2 s3} :
    (σ1.comp σ2).lift = σ1.lift.comp σ2.lift := by
  apply VSubst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    show ((σ1.var x).vsubst σ2).rename Rename.succ
       = ((σ1.var x).rename Rename.succ).vsubst σ2.lift
    cases h : σ1.var x <;> rfl

/-- `toSubst` of `compRename` is `compRename` of `toSubst`. -/
theorem VSubst.toSubst_compRename {σ : VSubst s1 s2} {f : Rename s2 s3} :
    (σ.compRename f).toSubst = σ.toSubst.compRename f := by
  apply Subst.funext
  intro x
  rfl

/-- `toSubst` of `compVSubst` is `compSubst` of `toSubst`. -/
theorem Rename.compVSubst_toSubst {f : Rename s1 s2} {σ : VSubst s2 s3} :
    (f.compVSubst σ).toSubst = f.compSubst σ.toSubst := by
  apply Subst.funext
  intro x
  rfl

/-- `toSubst` of a composition is the composition of `toSubst`s. -/
theorem VSubst.toSubst_comp {σ1 : VSubst s1 s2} {σ2 : VSubst s2 s3} :
    (σ1.comp σ2).toSubst = σ1.toSubst.comp σ2.toSubst := by
  apply Subst.funext
  intro x
  show Path.var ((σ1.var x).vsubst σ2) = (Path.var (σ1.var x)).subst σ2.toSubst
  cases h : σ1.var x <;> rfl

theorem Tm.subst_rename_comm {t : Tm s1} {σ : VSubst s1 s2} {f : Rename s2 s3} :
    (t.subst σ).rename f = t.subst (σ.compRename f) := by
  induction t generalizing s2 s3 with
  | path p =>
    simp [Tm.subst, Tm.rename, Path.subst_rename_comm, VSubst.toSubst_compRename]
  | abs T t ih =>
    simp [Tm.subst, Tm.rename, Ty.subst_rename_comm, VSubst.toSubst_compRename,
          VSubst.compRename_lift, ih]
  | pairTm y a z =>
    simp [Tm.subst, Tm.rename, Var.vsubst_rename_comm]
  | pairTy y A T =>
    simp [Tm.subst, Tm.rename, Var.vsubst_rename_comm, Ty.subst_rename_comm,
          VSubst.toSubst_compRename]
  | app p q =>
    simp [Tm.subst, Tm.rename, Path.subst_rename_comm, VSubst.toSubst_compRename]
  | letin t1 t2 ih1 ih2 =>
    simp [Tm.subst, Tm.rename, VSubst.compRename_lift, ih1, ih2]
  | typed t T ih =>
    simp [Tm.subst, Tm.rename, Ty.subst_rename_comm, VSubst.toSubst_compRename, ih]

theorem Tm.rename_subst_comm {t : Tm s1} {f : Rename s1 s2} {σ : VSubst s2 s3} :
    (t.rename f).subst σ = t.subst (f.compVSubst σ) := by
  induction t generalizing s2 s3 with
  | path p =>
    simp [Tm.subst, Tm.rename, Path.rename_subst_comm, Rename.compVSubst_toSubst]
  | abs T t ih =>
    simp [Tm.subst, Tm.rename, Ty.rename_subst_comm, Rename.compVSubst_toSubst,
          Rename.compVSubst_lift, ih]
  | pairTm y a z =>
    simp [Tm.subst, Tm.rename, Var.rename_vsubst_comm]
  | pairTy y A T =>
    simp [Tm.subst, Tm.rename, Var.rename_vsubst_comm, Ty.rename_subst_comm,
          Rename.compVSubst_toSubst]
  | app p q =>
    simp [Tm.subst, Tm.rename, Path.rename_subst_comm, Rename.compVSubst_toSubst]
  | letin t1 t2 ih1 ih2 =>
    simp [Tm.subst, Tm.rename, Rename.compVSubst_lift, ih1, ih2]
  | typed t T ih =>
    simp [Tm.subst, Tm.rename, Ty.rename_subst_comm, Rename.compVSubst_toSubst, ih]

theorem Tm.subst_comp {t : Tm s1} {σ1 : VSubst s1 s2} {σ2 : VSubst s2 s3} :
    (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | path p =>
    simp [Tm.subst, Path.subst_comp, VSubst.toSubst_comp]
  | abs T t ih =>
    simp [Tm.subst, Ty.subst_comp, VSubst.toSubst_comp, VSubst.comp_lift, ih]
  | pairTm y a z =>
    simp [Tm.subst, Var.vsubst_comp]
  | pairTy y A T =>
    simp [Tm.subst, Var.vsubst_comp, Ty.subst_comp, VSubst.toSubst_comp]
  | app p q =>
    simp [Tm.subst, Path.subst_comp, VSubst.toSubst_comp]
  | letin t1 t2 ih1 ih2 =>
    simp [Tm.subst, VSubst.comp_lift, ih1, ih2]
  | typed t T ih =>
    simp [Tm.subst, Ty.subst_comp, VSubst.toSubst_comp, ih]

/-! ### Opening lemmas for terms -/

/-- Weakening followed by opening is the identity, for variable substitutions. -/
theorem VSubst.weaken_openVar {y : Var s} :
    Rename.succ.compVSubst (VSubst.openVar y) = VSubst.id := by
  apply VSubst.funext
  intro x
  rfl

theorem Tm.weaken_open {t : Tm s} {y : Var s} : t.weaken.open y = t := by
  simp [Tm.open, Tm.weaken, Tm.rename_subst_comm, VSubst.weaken_openVar, Tm.subst_id]

/-- Renaming commutes with opening a term. -/
theorem VSubst.openVar_rename_comm {y : Var s1} {f : Rename s1 s2} :
    f.lift.compVSubst (VSubst.openVar (y.rename f)) = (VSubst.openVar y).compRename f := by
  apply VSubst.funext
  intro x
  cases x <;> rfl

theorem Tm.open_rename_comm {t : Tm (s1+1)} {y : Var s1} {f : Rename s1 s2} :
    (t.rename f.lift).open (y.rename f) = (t.open y).rename f := by
  simp [Tm.open, Tm.rename_subst_comm, Tm.subst_rename_comm, VSubst.openVar_rename_comm]

/-- Substitution commutes with opening a term. -/
theorem VSubst.openVar_subst_comm {y : Var s1} {σ : VSubst s1 s2} :
    σ.lift.comp (VSubst.openVar (y.vsubst σ)) = (VSubst.openVar y).comp σ := by
  apply VSubst.funext
  intro x
  cases x with
  | here => rfl
  | there x =>
    show ((σ.var x).rename Rename.succ).vsubst (VSubst.openVar (y.vsubst σ)) = σ.var x
    cases h : σ.var x <;> rfl

theorem Tm.open_subst_comm {t : Tm (s1+1)} {y : Var s1} {σ : VSubst s1 s2} :
    (t.subst σ.lift).open (y.vsubst σ) = (t.open y).subst σ := by
  simp [Tm.open, Tm.subst_comp, VSubst.openVar_subst_comm]

/-! ### Binder swap (hoisted from the superseded transfer file) -/

/-- Swaps the two innermost binders. -/
def Rename.swap {s : Sig} : Rename (s+2) (s+2) where
  var := fun
    | .here => .there .here
    | .there .here => .here
    | .there (.there x) => .there (.there x)

/-- Filling the outer slot with `r`, then the remaining slot with `q`,
equals swapping, filling with `q`, then filling with `r`. Stated in the
substitution spelling that `Den`'s clauses expose after simplification. -/
theorem Ty.openlift_open {T : Ty (s+2)} {r q : Path s} :
    (T.subst (Subst.openPath r).lift).subst (Subst.openPath q)
      = ((T.rename Rename.swap).subst (Subst.openPath q).lift).subst (Subst.openPath r) := by
  have wo : ∀ (u v : Path s),
      (u.rename Rename.succ).subst (Subst.openPath v) = u :=
    fun u v => Path.weaken_open
  simp only [Ty.subst_comp, Ty.rename_subst_comm]
  congr 1
  apply Subst.funext
  intro x
  cases x with
  | here =>
    show q = (q.rename Rename.succ).subst (Subst.openPath r)
    exact (wo q r).symm
  | there y =>
    cases y with
    | here =>
      show (r.rename Rename.succ).subst (Subst.openPath q) = r
      exact wo r q
    | there z => rfl

/-- Opening a swap-renamed type with a weakened path fills the outer slot. -/
theorem Ty.swap_open_weaken {T : Ty (s+2)} {r : Path s} :
    (T.rename Rename.swap).open (r.rename Rename.succ)
      = T.subst (Subst.openPath r).lift := by
  simp only [Ty.open, Ty.rename_subst_comm]
  congr 1
  apply Subst.funext
  intro x
  match x with
  | .here => rfl
  | .there .here => rfl
  | .there (.there x) => rfl

end LambdaP
