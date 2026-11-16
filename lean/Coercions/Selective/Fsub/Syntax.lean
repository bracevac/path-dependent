/-!
# Syntax of plain full F-sub

Intrinsically scoped types `Ty n` over `n` type variables (`Fin n`, index `0` is the
innermost binder), renaming, substitution, ordered contexts of upper bounds (each
bound is scoped before its own binder) and telescopes of further binders. The
lemmas at the end are the de Bruijn bookkeeping used by the context operations.
-/
namespace SelFsub

/-- Types `Top | X | S → T | ∀(X <: S). T`; the body of `all` has one more variable. -/
inductive Ty : Nat → Type where
  | top : Ty n
  | var : Fin n → Ty n
  | arr : Ty n → Ty n → Ty n
  | all : Ty n → Ty (n+1) → Ty n
  deriving DecidableEq, Repr

def liftRen (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def Ty.rename : (Fin n → Fin m) → Ty n → Ty m
  | _, .top => .top
  | ρ, .var x => .var (ρ x)
  | ρ, .arr A B => .arr (A.rename ρ) (B.rename ρ)
  | ρ, .all A B => .all (A.rename ρ) (B.rename (liftRen ρ))

def Ty.weaken (A : Ty n) : Ty (n+1) := A.rename Fin.succ

/-- A substitution under one more binder: the new variable maps to itself. -/
def liftS (σ : Fin n → Ty m) : Fin (n+1) → Ty (m+1) :=
  Fin.cases (.var 0) (fun i => (σ i).weaken)

def Ty.subst : (Fin n → Ty m) → Ty n → Ty m
  | _, .top => .top
  | σ, .var x => σ x
  | σ, .arr A B => .arr (A.subst σ) (B.subst σ)
  | σ, .all A B => .all (A.subst σ) (B.subst (liftS σ))

/-- Substitution of `V` for the innermost variable. -/
def sub0 (V : Ty n) : Fin (n+1) → Ty n := Fin.cases V .var

/-- `liftS` iterated `k` times. -/
def liftN : (k : Nat) → (Fin n → Ty m) → Fin (n+k) → Ty (m+k)
  | 0, σ => σ
  | k+1, σ => liftS (liftN k σ)

/-- Ordered contexts of upper bounds; the bound of a binder lives in the scope before it. -/
inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | snoc : Ctx n → Ty n → Ctx (n+1)

def Ctx.lookup : Ctx n → Fin n → Ty n
  | .nil, x => Fin.elim0 x
  | .snoc Γ A, x => Fin.cases A.weaken (fun i => (Γ.lookup i).weaken) x

/-- `k` further binders over a scope of `n` variables. -/
inductive Tele (n : Nat) : Nat → Type where
  | nil : Tele n 0
  | snoc : Tele n k → Ty (n+k) → Tele n (k+1)

def Ctx.append (Γ : Ctx n) : Tele n k → Ctx (n+k)
  | .nil => Γ
  | .snoc Θ B => (Γ.append Θ).snoc B

def Tele.subst (σ : Fin n → Ty m) : Tele n k → Tele m k
  | .nil => .nil
  | .snoc (k := k) Θ B => .snoc (Θ.subst σ) (B.subst (liftN k σ))

/-! ## De Bruijn bookkeeping -/

theorem liftRen_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    liftRen ρ' ∘ liftRen ρ = liftRen (ρ' ∘ ρ) := by
  funext i; cases i using Fin.cases <;> rfl

theorem Ty.rename_rename (A : Ty n) :
    ∀ {m k} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k),
      (A.rename ρ).rename ρ' = A.rename (ρ' ∘ ρ) := by
  induction A with
  | top => intros; rfl
  | var => intros; rfl
  | arr A B iA iB => intros; simp [Ty.rename, iA, iB]
  | all A B iA iB => intros; simp [Ty.rename, iA, iB, liftRen_comp]

theorem Ty.rename_weaken (A : Ty n) (ρ : Fin n → Fin m) :
    (A.rename ρ).weaken = A.weaken.rename (liftRen ρ) := by
  simp only [Ty.weaken, Ty.rename_rename]; rfl

theorem Ty.subst_rename (A : Ty n) :
    ∀ {m k} (ρ : Fin n → Fin m) (σ : Fin m → Ty k),
      (A.rename ρ).subst σ = A.subst (σ ∘ ρ) := by
  induction A with
  | top => intros; rfl
  | var => intros; rfl
  | arr A B iA iB => intros; simp [Ty.rename, Ty.subst, iA, iB]
  | all A B iA iB =>
    intro _ _ ρ σ
    simp only [Ty.rename, Ty.subst, iA, iB]
    congr 2; funext i; cases i using Fin.cases <;> rfl

theorem Ty.rename_subst (A : Ty n) :
    ∀ {m k} (σ : Fin n → Ty m) (ρ : Fin m → Fin k),
      (A.subst σ).rename ρ = A.subst (Ty.rename ρ ∘ σ) := by
  induction A with
  | top => intros; rfl
  | var => intros; rfl
  | arr A B iA iB => intros; simp [Ty.rename, Ty.subst, iA, iB]
  | all A B iA iB =>
    intro _ _ σ ρ
    simp only [Ty.rename, Ty.subst, iA, iB]
    congr 2; funext i; cases i using Fin.cases
    · rfl
    · simp only [Function.comp, liftS, Fin.cases_succ, Ty.weaken, Ty.rename_rename]; rfl

theorem liftS_var : liftS (.var : Fin n → Ty n) = .var := by
  funext i; cases i using Fin.cases <;> rfl

theorem Ty.subst_var (A : Ty n) : A.subst .var = A := by
  induction A with
  | top => rfl
  | var => rfl
  | arr A B iA iB => simp [Ty.subst, iA, iB]
  | all A B iA iB => simp [Ty.subst, liftS_var, iA, iB]

theorem Ty.weaken_subst (A : Ty n) (σ : Fin n → Ty m) :
    A.weaken.subst (liftS σ) = (A.subst σ).weaken := by
  simp only [Ty.weaken, Ty.subst_rename, Ty.rename_subst]; rfl

theorem Ty.weaken_sub0 (A : Ty n) (V : Ty n) : A.weaken.subst (sub0 V) = A := by
  simp only [Ty.weaken, Ty.subst_rename]; exact A.subst_var

theorem liftN_var : ∀ k, liftN k (.var : Fin n → Ty n) = .var
  | 0 => rfl
  | k+1 => by simp only [liftN, liftN_var k, liftS_var]

theorem Tele.subst_var : (Θ : Tele n k) → Θ.subst .var = Θ
  | .nil => rfl
  | .snoc Θ B => by simp only [Tele.subst, Θ.subst_var, liftN_var, Ty.subst_var]

end SelFsub
