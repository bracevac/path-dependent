import Coercions.Selective.Fsub.Lift
/-!
# Certified substitution

A certified substitution from `Γ` to `Δ` maps each variable `x` to a type `σ x` and
to an entry `τ x`: either `some c` with `c : σ x ⇒ Γ(x)[σ]` in `Δ`, or `none` when
`σ x ≤₀ Γ(x)[σ]` holds primitively in `Δ`. Applying it to a certificate is a function
on certificates: `;` is kept, and each primitive step is rebuilt from its two stored
types, a bound step on `x` becoming `τ x`. Narrowing and type substitution, under any
inner binders, are instances.
-/
namespace SelFsub

/-- The certificate of an entry: the stored certificate, or the primitive step. -/
def entry (o : Option (Cert m)) (S T : Ty m) : Cert m := o.getD (.step S T)

def EntryTy (Δ : Ctx m) : Option (Cert m) → Ty m → Ty m → Prop
  | some c, S, T => CTy Δ c S T
  | none, S, T => Prim Δ S T

theorem EntryTy.cert {o : Option (Cert m)} (h : EntryTy Δ o S T) : CTy Δ (entry o S T) S T := by
  cases o
  · exact .step h
  · exact h

def CSub (Γ : Ctx n) (Δ : Ctx m) (σ : Fin n → Ty m) (τ : Fin n → Option (Cert m)) : Prop :=
  ∀ x, EntryTy Δ (τ x) (σ x) ((Γ.lookup x).subst σ)

/-- Under a binder the new variable keeps its primitive bound step. -/
def liftT (τ : Fin n → Option (Cert m)) : Fin (n+1) → Option (Cert (m+1)) :=
  Fin.cases none (fun i => (τ i).map Cert.weaken)

def liftNT : (k : Nat) → (Fin n → Option (Cert m)) → Fin (n+k) → Option (Cert (m+k))
  | 0, τ => τ
  | k+1, τ => liftT (liftNT k τ)

theorem CSub.lift {Γ : Ctx n} {Δ : Ctx m} {σ τ} (h : CSub Γ Δ σ τ) (B : Ty n) :
    CSub (Γ.snoc B) (Δ.snoc (B.subst σ)) (liftS σ) (liftT τ) := by
  intro x; cases x using Fin.cases
  · show Prim _ (.var 0) (B.weaken.subst (liftS σ)); rw [Ty.weaken_subst]; exact .bound 0
  · rename_i i
    show EntryTy _ ((τ i).map Cert.weaken) (σ i).weaken ((Γ.lookup i).weaken.subst (liftS σ))
    rw [Ty.weaken_subst]
    have hi := h i
    revert hi; cases τ i
    · exact Prim.weaken _
    · exact CTy.weaken _

theorem CSub.liftTele {Γ : Ctx n} {Δ : Ctx m} {σ τ} (h : CSub Γ Δ σ τ) :
    (Θ : Tele n k) → CSub (Γ.append Θ) (Δ.append (Θ.subst σ)) (liftN k σ) (liftNT k τ)
  | .nil => h
  | .snoc Θ B => (h.liftTele Θ).lift B

/-- A primitive step `cond p S T ≤₀ cond p T S` rebuilt after substitution; structural
recursion on `S`, with the polarity `p` flipped at contravariant positions. -/
def Cert.ofPrim : Bool → (Fin n → Ty m) → (Fin n → Option (Cert m)) → Ty n → Ty n → Cert m
  | p, σ, τ, S, T =>
    if cond p S T = cond p T S ∨ cond p T S = .top then
      .step ((cond p S T).subst σ) ((cond p T S).subst σ)
    else match cond p S T with
    | .var x => entry (τ x) (σ x) ((cond p T S).subst σ)
    | _ => match S, T with
      | .arr A₁ A₂, .arr B₁ B₂ => Cert.arr (ofPrim (!p) σ τ A₁ B₁) (ofPrim p σ τ A₂ B₂)
      | .all A₁ A₂, .all B₁ B₂ =>
        Cert.all (ofPrim (!p) σ τ A₁ B₁) (ofPrim p (liftS σ) (liftT τ) A₂ B₂)
      | _, _ => .step ((cond p S T).subst σ) ((cond p T S).subst σ)

theorem Cert.ofPrim_typed (S : Ty n) :
    ∀ (p : Bool) {m} {Γ : Ctx n} {Δ : Ctx m} {σ τ} (T : Ty n), CSub Γ Δ σ τ →
      Prim Γ (cond p S T) (cond p T S) →
      CTy Δ (ofPrim p σ τ S T) ((cond p S T).subst σ) ((cond p T S).subst σ) := by
  induction S with
  | top | var | arr C₁ C₂ i₁ i₂ | all C₁ C₂ i₁ i₂ =>
    intro p m Γ Δ σ τ T hτ h
    unfold Cert.ofPrim
    split
    · next hc => rcases hc with e | e <;> rw [e] <;> first | exact .step .refl | exact .step .top
    · next hc =>
      rcases Prim.inv h with e | e | ⟨x, eL, eR⟩ | ⟨A₁, A₂, B₁, B₂, eL, eR, h₁, h₂⟩ |
        ⟨A₁, A₂, B₁, B₂, eL, eR, h₁, h₂⟩
      · exact absurd (.inl e) hc
      · exact absurd (.inr e) hc
      · simp only [eL, eR]; exact (hτ x).cert
      all_goals cases p <;> simp only [cond] at eL eR <;> cases eL <;> cases eR
      all_goals first
        | exact .arr (i₁ _ _ hτ h₁) (i₂ _ _ hτ h₂)
        | exact .all (i₁ _ _ hτ h₁) (i₂ _ _ (hτ.lift _) h₂)

/-- A certified substitution applied to a certificate. -/
def Cert.subst (σ : Fin n → Ty m) (τ : Fin n → Option (Cert m)) : Cert n → Cert m
  | .step S T => Cert.ofPrim true σ τ S T
  | .seq c d => .seq (c.subst σ τ) (d.subst σ τ)

theorem CTy.subst {Γ : Ctx n} {Δ : Ctx m} {σ τ} (hτ : CSub Γ Δ σ τ) (h : CTy Γ c S T) :
    CTy Δ (c.subst σ τ) (S.subst σ) (T.subst σ) := by
  induction h with
  | step h => exact Cert.ofPrim_typed _ true _ hτ h
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

/-! ## Narrowing -/

/-- The entries of narrowing `X <: U` to `X <: d.src` with `d : d.src ⇒ U`, under `k`
inner binders: the bound step on `X` becomes `step[X, d.src] ; d`. -/
def narrowT (k : Nat) (d : Cert n) : Fin (n+1+k) → Option (Cert (n+1+k)) :=
  liftNT k (Fin.cases (some (.seq (.step (.var 0) d.src.weaken) d.weaken)) (fun _ => none))

def Cert.narrow (k : Nat) (c : Cert (n+1+k)) (d : Cert n) : Cert (n+1+k) :=
  c.subst .var (narrowT k d)

theorem CSub.narrow {Γ : Ctx n} (hd : CTy Γ d U' U) (Θ : Tele (n+1) k) :
    CSub ((Γ.snoc U).append Θ) ((Γ.snoc U').append Θ) .var (narrowT k d) := by
  have base : CSub (Γ.snoc U) (Γ.snoc U') .var
      (Fin.cases (some (.seq (.step (.var 0) d.src.weaken) d.weaken)) (fun _ => none)) := by
    intro x; cases x using Fin.cases
    · show CTy _ _ _ (U.weaken.subst .var)
      rw [Ty.subst_var, hd.endpoints.1]; exact .seq (.step (.bound 0)) (hd.weaken U')
    · show Prim _ _ (Ty.subst .var _); rw [Ty.subst_var]; exact .bound _
  have h := base.liftTele Θ
  rwa [Tele.subst_var, liftN_var] at h

/-- Narrowing under inner binders `Θ`, with the same endpoints. -/
theorem CTy.narrow {Γ : Ctx n} (Θ : Tele (n+1) k) (hd : CTy Γ d U' U)
    (h : CTy ((Γ.snoc U).append Θ) c S T) :
    CTy ((Γ.snoc U').append Θ) (c.narrow k d) S T := by
  have h' := h.subst (CSub.narrow hd Θ)
  rwa [Ty.subst_var, Ty.subst_var] at h'

/-! ## Type substitution -/

/-- The entries of substituting a type for `X <: U` given `d : V ⇒ U`, under `k` inner
binders: the bound step on `X` becomes `d`. -/
def instT (k : Nat) (d : Cert n) : Fin (n+1+k) → Option (Cert (n+k)) :=
  liftNT k (Fin.cases (some d) (fun _ => none))

def Cert.inst (k : Nat) (c : Cert (n+1+k)) (V : Ty n) (d : Cert n) : Cert (n+k) :=
  c.subst (liftN k (sub0 V)) (instT k d)

theorem CSub.inst {Γ : Ctx n} (hd : CTy Γ d V U) (Θ : Tele (n+1) k) :
    CSub ((Γ.snoc U).append Θ) (Γ.append (Θ.subst (sub0 V))) (liftN k (sub0 V)) (instT k d) := by
  have base : CSub (Γ.snoc U) Γ (sub0 V) (Fin.cases (some d) (fun _ => none)) := by
    intro x; cases x using Fin.cases
    · show CTy _ _ _ (U.weaken.subst (sub0 V)); rw [Ty.weaken_sub0]; exact hd
    · show Prim _ _ ((Γ.lookup _).weaken.subst (sub0 V)); rw [Ty.weaken_sub0]; exact .bound _
  exact base.liftTele Θ

/-- Type substitution `[V/X]` under inner binders `Θ`. -/
theorem CTy.inst {Γ : Ctx n} (Θ : Tele (n+1) k) (hd : CTy Γ d V U)
    (h : CTy ((Γ.snoc U).append Θ) c S T) :
    CTy (Γ.append (Θ.subst (sub0 V))) (c.inst k V d)
      (S.subst (liftN k (sub0 V))) (T.subst (liftN k (sub0 V))) :=
  h.subst (CSub.inst hd Θ)

end SelFsub
