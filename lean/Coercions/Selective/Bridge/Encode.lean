import Coercions.Selective.Fsub.Complete
import Coercions.Selective.Negative

/-!
# The encoding of F-sub into DOT-MNF

A type variable `X` becomes the selection `x_X.A` on a term variable, a binding
`X <: U` becomes `x_X : {A : ⊥ .. ⟦U⟧}`, `∀(X <: U). T` becomes the dependent
function type `∀(x : {A : ⊥ .. ⟦U⟧}) ⟦T⟧`, an arrow `S → T` becomes the
non-dependent function type `∀(_ : ⟦S⟧) ⟦T⟧↑` (the codomain weakened past the
unused binder), and `Top` becomes `⊤`. The type label is `Selective.lA`
(`.typ 0`) throughout.

F-sub scopes `Ty n` by `Fin n` with index `0` innermost; DOT-MNF scopes by a
signature, newest binder first. `sig n` is the signature of `n` term
variables, `bv` maps `Fin n` to its bound variable and `toFin` is its inverse.
`renF ρ` is the DOT-MNF renaming induced by an F-sub renaming `ρ`.

Certificates are encoded homomorphically: `step[S, T] ↦ step[⟦S⟧, ⟦T⟧]`,
`c ; d ↦ ⟦c⟧ ; ⟦d⟧`.

The commutation lemmas are `enc_rename` and `enc_weaken` (types) and
`encCtx_lookup` (the encoded context declares `{A : ⊥ .. ⟦Γ(X)⟧}` at `x_X`).
-/

namespace Bridge

open FCdot (Kind Sig BVar Rename Label)

/-- The signature of `n` term variables. -/
def sig : Nat → Sig
  | 0 => []
  | n+1 => (sig n),x

/-- The term variable `x_X` of the F-sub type variable `X`. -/
def bv : {n : Nat} → Fin n → BVar (sig n) .var
  | _+1, i => Fin.cases .here (fun j => .there (bv j)) i

/-- The F-sub type variable of a term variable. -/
def toFin : {n : Nat} → BVar (sig n) .var → Fin n
  | 0, x => nomatch x
  | _+1, .here => 0
  | _+1, .there y => (toFin y).succ

theorem toFin_bv : {n : Nat} → (i : Fin n) → toFin (bv i) = i
  | _+1, i => by
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simp only [bv, Fin.cases_succ, toFin, toFin_bv j]

theorem bv_toFin : {n : Nat} → (x : BVar (sig n) .var) → bv (toFin x) = x
  | 0, x => nomatch x
  | _+1, .here => rfl
  | _+1, .there y => by simp only [toFin, bv, Fin.cases_succ, bv_toFin y]

theorem bv_injective {n : Nat} {i j : Fin n} (h : bv i = bv j) : i = j := by
  rw [← toFin_bv i, ← toFin_bv j, h]

/-- The DOT-MNF renaming induced by an F-sub renaming. -/
def renF {n m : Nat} (ρ : Fin n → Fin m) : Rename (sig n) (sig m) where
  var := fun {k} x => match k, x with
    | .var, x => bv (ρ (toFin x))

@[simp] theorem renF_bv {n m : Nat} (ρ : Fin n → Fin m) (i : Fin n) :
    (renF ρ).var (bv i) = bv (ρ i) := by
  simp only [renF, toFin_bv]

theorem renF_ext {n m : Nat} {f g : Rename (sig n) (sig m)}
    (h : ∀ i : Fin n, f.var (bv i) = g.var (bv i)) : f = g := by
  apply Rename.funext'
  intro k x
  cases k
  rw [← bv_toFin x]; exact h _

theorem renF_lift {n m : Nat} (ρ : Fin n → Fin m) :
    renF (SelFsub.liftRen ρ) = (renF ρ).lift (k := .var) := by
  apply renF_ext; intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    rw [renF_bv]
    show bv (ρ j).succ = .there ((renF ρ).var (bv j))
    rw [renF_bv]; rfl

theorem renF_succ {n : Nat} : renF (Fin.succ : Fin n → Fin (n+1)) = Rename.succ (k := .var) := by
  apply renF_ext; intro i
  simp only [renF_bv]; rfl

/-! ## Types, contexts, certificates -/

/-- `⟦·⟧` on types. -/
def enc : {n : Nat} → SelFsub.Ty n → DotMNF.Ty (sig n)
  | _, .top => .top
  | _, .var x => .sel (.var (bv x)) Selective.lA
  | _, .arr S T => .all (enc S) (enc T).weaken
  | _, .all U T => .all (.typ Selective.lA .bot (enc U)) (enc T)

/-- `⟦·⟧` on contexts: each bound `X <: U` becomes `x_X : {A : ⊥ .. ⟦U⟧}`. -/
def encCtx : {n : Nat} → SelFsub.Ctx n → DotMNF.Ctx (sig n)
  | _, .nil => .nil
  | _, .snoc Γ U => .cons (encCtx Γ) (.typ Selective.lA .bot (enc U))

/-- `⟦·⟧` on certificates, homomorphically. -/
def encCert {n : Nat} : SelFsub.Cert n → Selective.Cert (sig n)
  | .step S T => .step (enc S) (enc T)
  | .seq c d => .seq (encCert c) (encCert d)
termination_by structural c => c

/-! ## Commutation lemmas -/

theorem enc_rename {n : Nat} (A : SelFsub.Ty n) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), enc (A.rename ρ) = (enc A).rename (renF ρ) := by
  induction A with
  | top => intros; rfl
  | var x => intro _ ρ; simp [SelFsub.Ty.rename, enc, DotMNF.Ty.rename, DotMNF.Path.rename]
  | arr A B iA iB =>
    intro _ ρ
    simp only [SelFsub.Ty.rename, enc, DotMNF.Ty.rename, iA, iB, DotMNF.Ty.weaken_rename]
  | all A B iA iB =>
    intro _ ρ
    simp only [SelFsub.Ty.rename, enc, DotMNF.Ty.rename, iA, iB, renF_lift]
    rfl

theorem enc_weaken {n : Nat} (A : SelFsub.Ty n) :
    enc A.weaken = (enc A).weaken (k := .var) := by
  simp only [SelFsub.Ty.weaken, enc_rename, renF_succ]; rfl

/-- The encoded context declares `{A : ⊥ .. ⟦Γ(X)⟧}` at `x_X`. -/
theorem encCtx_lookup {n : Nat} (Γ : SelFsub.Ctx n) (x : Fin n) :
    (encCtx Γ).lookup (bv x) = .typ Selective.lA .bot (enc (Γ.lookup x)) := by
  induction Γ with
  | nil => exact Fin.elim0 x
  | snoc Γ A ih =>
    cases x using Fin.cases with
    | zero =>
      show (DotMNF.Ty.typ Selective.lA .bot (enc A)).weaken = _
      simp only [SelFsub.Ctx.lookup, Fin.cases_zero, enc_weaken]; rfl
    | succ i =>
      show ((encCtx Γ).lookup (bv i)).weaken = _
      simp only [SelFsub.Ctx.lookup, Fin.cases_succ, enc_weaken, ih]; rfl

end Bridge
