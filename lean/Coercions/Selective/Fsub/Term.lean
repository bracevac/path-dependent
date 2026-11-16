import Coercions.Selective.Fsub.Invert
/-!
# Terms

One term syntax over `n` type variables: term variables are de Bruijn indices (`0` the
innermost term binder), abstractions carry their domain or bound, and `t ▷ c` is an
explicit cast by a stored certificate. `erase` removes every cast; the erased terms are
the ordinary F-sub terms (`Tm.erase_erase`). The rest is syntactic bookkeeping: type
renaming, type substitution of erased terms, substitution of a term for a term variable,
and the commutation lemmas they need.
-/
namespace SelFsub

/-- `x | λ(x : S). t | t u | Λ(X <: S). t | t [U] | t ▷ c`. -/
inductive Tm : Nat → Type where
  | var : Nat → Tm n
  | lam : Ty n → Tm n → Tm n
  | app : Tm n → Tm n → Tm n
  | tlam : Ty n → Tm (n+1) → Tm n
  | tapp : Tm n → Ty n → Tm n
  | cast : Tm n → Cert n → Tm n
  deriving DecidableEq, Repr

/-- The erased program: all casts removed. -/
def Tm.erase : Tm n → Tm n
  | .var x => .var x
  | .lam S t => .lam S t.erase
  | .app t u => .app t.erase u.erase
  | .tlam S t => .tlam S t.erase
  | .tapp t U => .tapp t.erase U
  | .cast t _ => t.erase

theorem Tm.erase_erase : (t : Tm n) → t.erase.erase = t.erase
  | .var _ => rfl
  | .lam _ t | .tlam _ t => by simp only [Tm.erase, t.erase_erase]
  | .app t u => by simp only [Tm.erase, t.erase_erase, u.erase_erase]
  | .tapp t _ | .cast t _ => by simp only [Tm.erase, t.erase_erase]

def Tm.renTy : (Fin n → Fin m) → Tm n → Tm m
  | _, .var x => .var x
  | ρ, .lam S t => .lam (S.rename ρ) (t.renTy ρ)
  | ρ, .app t u => .app (t.renTy ρ) (u.renTy ρ)
  | ρ, .tlam S t => .tlam (S.rename ρ) (t.renTy (liftRen ρ))
  | ρ, .tapp t U => .tapp (t.renTy ρ) (U.rename ρ)
  | ρ, .cast t c => .cast (t.renTy ρ) (c.rename ρ)

/-- Type substitution of erased terms. A stored certificate is transported only together
with evidence for the substituted bounds (`Cert.subst`), which this function does not
have, so a cast is dropped; on erased terms, where it is used, no cast occurs. -/
def Tm.substTy : (Fin n → Ty m) → Tm n → Tm m
  | _, .var x => .var x
  | σ, .lam S t => .lam (S.subst σ) (t.substTy σ)
  | σ, .app t u => .app (t.substTy σ) (u.substTy σ)
  | σ, .tlam S t => .tlam (S.subst σ) (t.substTy (liftS σ))
  | σ, .tapp t U => .tapp (t.substTy σ) (U.subst σ)
  | σ, .cast t _ => t.substTy σ

/-- `t.subst k w` replaces the term variable `k` by `w` and lowers the variables above
it. `w` is not shifted under term binders: substitution is applied only to term-closed
`w` (a value of a closed program, or a typed annotation of one), for which this is
capture-free. Under a type binder `w` is weakened. -/
def Tm.subst : Tm n → Nat → Tm n → Tm n
  | .var x, k, w => if x < k then .var x else if x = k then w else .var (x - 1)
  | .lam S t, k, w => .lam S (t.subst (k+1) w)
  | .app t u, k, w => .app (t.subst k w) (u.subst k w)
  | .tlam S t, k, w => .tlam S (t.subst k (w.renTy Fin.succ))
  | .tapp t U, k, w => .tapp (t.subst k w) U
  | .cast t c, k, w => .cast (t.subst k w) c

theorem Tm.erase_renTy : (t : Tm n) → ∀ {m} (ρ : Fin n → Fin m),
    (t.renTy ρ).erase = t.erase.renTy ρ
  | .var _, _, _ => rfl
  | .lam _ t, _, ρ => by simp only [Tm.renTy, Tm.erase, t.erase_renTy]
  | .app t u, _, ρ => by simp only [Tm.renTy, Tm.erase, t.erase_renTy, u.erase_renTy]
  | .tlam _ t, _, ρ => by simp only [Tm.renTy, Tm.erase, t.erase_renTy]
  | .tapp t _, _, ρ => by simp only [Tm.renTy, Tm.erase, t.erase_renTy]
  | .cast t _, _, ρ => by simp only [Tm.renTy, Tm.erase, t.erase_renTy]

theorem Tm.erase_subst : (t : Tm n) → ∀ (k : Nat) (w : Tm n),
    (t.subst k w).erase = t.erase.subst k w.erase
  | .var x, k, w => by
    simp only [Tm.subst, Tm.erase]; split
    · rfl
    · split <;> rfl
  | .lam _ t, k, w => by simp only [Tm.subst, Tm.erase, t.erase_subst]
  | .app t u, k, w => by simp only [Tm.subst, Tm.erase, t.erase_subst, u.erase_subst]
  | .tlam _ t, k, w => by simp only [Tm.subst, Tm.erase, t.erase_subst, w.erase_renTy]
  | .tapp t _, k, w => by simp only [Tm.subst, Tm.erase, t.erase_subst]
  | .cast t _, k, w => by simp only [Tm.subst, Tm.erase, t.erase_subst]

/-! ## Commutation of types with the innermost substitution -/

theorem Ty.rename_sub0 (T : Ty (n+1)) (U : Ty n) (ρ : Fin n → Fin m) :
    (T.subst (sub0 U)).rename ρ = (T.rename (liftRen ρ)).subst (sub0 (U.rename ρ)) := by
  rw [Ty.rename_subst, Ty.subst_rename]; congr 1; funext i; cases i using Fin.cases <;> rfl

theorem liftS_comp (σ : Fin n → Ty m) (σ' : Fin m → Ty k) :
    (fun i => (liftS σ i).subst (liftS σ')) = liftS (fun i => (σ i).subst σ') := by
  funext i; cases i using Fin.cases
  · rfl
  · exact Ty.weaken_subst _ _

theorem Ty.subst_subst (A : Ty n) :
    ∀ {m k} (σ : Fin n → Ty m) (σ' : Fin m → Ty k),
      (A.subst σ).subst σ' = A.subst (fun i => (σ i).subst σ') := by
  induction A with
  | top => intros; rfl
  | var => intros; rfl
  | arr A B iA iB => intros; simp [Ty.subst, iA, iB]
  | all A B iA iB => intros; simp only [Ty.subst, iA, iB, liftS_comp]

theorem Ty.subst_sub0 (T : Ty (n+1)) (U : Ty n) (σ : Fin n → Ty m) :
    (T.subst (sub0 U)).subst σ = (T.subst (liftS σ)).subst (sub0 (U.subst σ)) := by
  rw [Ty.subst_subst, Ty.subst_subst]; congr 1; funext i; cases i using Fin.cases
  · rfl
  · exact (Ty.weaken_sub0 _ _).symm

end SelFsub
