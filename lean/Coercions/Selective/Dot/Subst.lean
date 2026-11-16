import Coercions.Selective.Dot.Rename

/-!
# Selective DOT: substitution of typed paths

A path substitution maps each variable to a path. On a type it acts through
the roots of the paths, so on judgment-level types it is the renaming
`σ.ren`; on endpoints and certificates it replaces each variable by its
path, casts included. When every path has the renamed type of its variable,
path typing, validity, primitive subtyping and certificate typing are preserved
exactly. Term typing is preserved up to erasure: the implicit comparison at an
application is restated as an explicit step on the argument path.

Narrowing and the substitution of a typed path for the newest variable are
instances.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-- A substitution of paths for variables. -/
def PSubst (s1 s2 : Sig) := BVar s1 .var → Path s2

/-- The renaming of roots induced by a path substitution. -/
def PSubst.ren (σ : PSubst s1 s2) : Rename s1 s2 where
  var := fun {k} x => match k, x with
    | .var, x => (σ x).root

@[simp] theorem PSubst.ren_var (σ : PSubst s1 s2) (x : BVar s1 .var) :
    σ.ren.var x = (σ x).root := rfl

/-- Lift a path substitution under a binder. -/
def PSubst.lift (σ : PSubst s1 s2) : PSubst (s1,x) (s2,x)
  | .here => .var .here
  | .there x => (σ x).weaken

theorem PSubst.lift_ren (σ : PSubst s1 s2) : σ.lift.ren = σ.ren.lift := by
  apply Rename.funext'
  intro k x
  cases k
  cases x with
  | here => rfl
  | there x =>
      show (σ x).weaken.root = .there (σ x).root
      simp only [Path.weaken, Path.root_rename, Rename.succ_var]

mutual

def Path.psubst : Path s1 → PSubst s1 s2 → Path s2
  | .var x, σ => σ x
  | .cast p c, σ => .cast (p.psubst σ) (c.psubst σ)

def ATy.psubst : ATy s1 → PSubst s1 s2 → ATy s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, σ => .typ A (S.psubst σ) (T.psubst σ)
  | .fld a T, σ => .fld a (T.psubst σ)
  | .sel p A, σ => .sel (p.psubst σ) A
  | .mu T, σ => .mu (T.psubst σ.lift)
  | .all S T, σ => .all (S.psubst σ) (T.psubst σ.lift)
  | .and S T, σ => .and (S.psubst σ) (T.psubst σ)

def Cert.psubst : Cert s1 → PSubst s1 s2 → Cert s2
  | .step S T, σ => .step (S.psubst σ) (T.psubst σ)
  | .seq c d, σ => .seq (c.psubst σ) (d.psubst σ)

end

@[simp] theorem Path.root_psubst : ∀ {s1 s2 : Sig} (p : Path s1) (σ : PSubst s1 s2),
    (p.psubst σ).root = σ.ren.var p.root
  | _, _, .var _, _ => rfl
  | _, _, .cast p _, σ => Path.root_psubst p σ

/-- On erasures a path substitution acts as the renaming of roots. -/
theorem ATy.erase_psubst : ∀ {s1 s2 : Sig} (S : ATy s1) (σ : PSubst s1 s2),
    (S.psubst σ).erase = S.erase.rename σ.ren
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .typ _ S T, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, ATy.erase_psubst S σ, ATy.erase_psubst T σ]
  | _, _, .fld _ T, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, ATy.erase_psubst T σ]
  | _, _, .sel p _, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, Path.root_psubst]
  | _, _, .mu T, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, ATy.erase_psubst T σ.lift, PSubst.lift_ren]
  | _, _, .all S T, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, ATy.erase_psubst S σ,
        ATy.erase_psubst T σ.lift, PSubst.lift_ren]
  | _, _, .and S T, σ => by
      simp only [ATy.psubst, ATy.erase, Ty.rename, ATy.erase_psubst S σ, ATy.erase_psubst T σ]

/-! ## Typed substitutions -/

/-- Every path of `σ` has, in `Δ`, the renamed type of its variable in `Γ`. -/
def PSubst.Typed (σ : PSubst s1 s2) (Γ : Ctx s1) (Δ : Ctx s2) : Prop :=
  ∀ x, PathTy Δ (σ x) ((Γ.lookup x).rename σ.ren)

theorem PSubst.Typed.lift {σ : PSubst s1 s2} {Γ : Ctx s1} {Δ : Ctx s2}
    (hσ : σ.Typed Γ Δ) (S : Ty s1) : σ.lift.Typed (Γ.cons S) (Δ.cons (S.rename σ.ren)) := by
  intro x
  cases x with
  | here =>
      show PathTy _ (.var .here) (S.weaken.rename σ.lift.ren)
      rw [PSubst.lift_ren, Ty.weaken_rename]
      exact .var
  | there x =>
      show PathTy _ (σ x).weaken ((Γ.lookup x).weaken.rename σ.lift.ren)
      rw [PSubst.lift_ren, Ty.weaken_rename]
      exact (hσ x).weaken _

/-! ## Substitution in paths, endpoints, primitive subtyping, certificates -/

mutual

theorem PathTy.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {p : Path s1} {T : Ty s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → PathTy Γ p T → PathTy Δ (p.psubst σ) (T.rename σ.ren)
  | _, _, _, _, _, _, _, hσ, @PathTy.var _ _ x => hσ x
  | _, _, _, _, _, _, _, hσ, .cast hp hc => .cast (PathTy.psubst hσ hp) (CertTy.psubst hσ hc)
  | _, _, _, _, _, _, _, hσ, .keep hp hc hq =>
      .keep (PathTy.psubst hσ hp) (CertTy.psubst hσ hc) (PathTy.psubst hσ hq)
  | _, _, _, _, _, _, _, hσ, .recI hp => by
      have ih := PathTy.psubst hσ hp
      simp only [Ty.substVar_rename, ← Path.root_psubst] at ih
      exact .recI ih
  | _, _, _, _, _, _, _, hσ, .recE hp => by
      have ih := PathTy.psubst hσ hp
      simp only [Ty.substVar_rename, ← Path.root_psubst]
      exact .recE ih
  | _, _, _, _, _, _, _, hσ, .andI hp hq => .andI (PathTy.psubst hσ hp) (PathTy.psubst hσ hq)

theorem Wf.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {S : ATy s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → Wf Γ S → Wf Δ (S.psubst σ)
  | _, _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, _, .bot => .bot
  | _, _, _, _, _, _, hσ, .typ hS hT => .typ (Wf.psubst hσ hS) (Wf.psubst hσ hT)
  | _, _, _, _, _, _, hσ, .fld hT => .fld (Wf.psubst hσ hT)
  | _, _, _, _, _, _, hσ, .sel hp => .sel (PathTy.psubst hσ hp)
  | _, _, _, _, _, σ, hσ, @Wf.mu _ T _ hT => by
      have ih := Wf.psubst (hσ.lift _) hT
      show Wf _ (.mu (T.psubst σ.lift))
      refine .mu ?_
      rw [ATy.erase_psubst, PSubst.lift_ren]
      exact ih
  | _, _, _, _, _, _, hσ, .all hS hT => by
      have ih := Wf.psubst (hσ.lift _) hT
      simp only [← ATy.erase_psubst] at ih
      exact .all (Wf.psubst hσ hS) ih
  | _, _, _, _, _, _, hσ, .and hS hT => .and (Wf.psubst hσ hS) (Wf.psubst hσ hT)

theorem Prim.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {S T : ATy s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → Prim Γ S T → Prim Δ (S.psubst σ) (T.psubst σ)
  | _, _, _, _, _, _, _, hσ, .top hS => .top (Wf.psubst hσ hS)
  | _, _, _, _, _, _, _, hσ, .bot hT => .bot (Wf.psubst hσ hT)
  | _, _, _, _, _, _, _, hσ, .refl hS hT e =>
      .refl (Wf.psubst hσ hS) (Wf.psubst hσ hT)
        (by rw [ATy.erase_psubst, ATy.erase_psubst, e])
  | _, _, _, _, _, _, _, hσ, .andL1 hS hT => .andL1 (Prim.psubst hσ hS) (Wf.psubst hσ hT)
  | _, _, _, _, _, _, _, hσ, .andL2 hS hT => .andL2 (Wf.psubst hσ hS) (Prim.psubst hσ hT)
  | _, _, _, _, _, _, _, hσ, .andR hT hU => .andR (Prim.psubst hσ hT) (Prim.psubst hσ hU)
  | _, _, _, _, _, _, _, hσ, .fld hT => .fld (Prim.psubst hσ hT)
  | _, _, _, _, _, _, _, hσ, .typ hS hT => .typ (Prim.psubst hσ hS) (Prim.psubst hσ hT)
  | _, _, _, _, _, _, _, hσ, .all hS hT => by
      have ih := Prim.psubst (hσ.lift _) hT
      simp only [← ATy.erase_psubst] at ih
      exact .all (Prim.psubst hσ hS) ih
  | _, _, _, _, _, _, _, hσ, .selU hp hT e =>
      .selU (PathTy.psubst hσ hp) (Wf.psubst hσ hT) (by rw [ATy.erase_psubst, e])
  | _, _, _, _, _, _, _, hσ, .selL hp hS e =>
      .selL (PathTy.psubst hσ hp) (Wf.psubst hσ hS) (by rw [ATy.erase_psubst, e])

theorem CertTy.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {c : Cert s1} {S T : Ty s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → CertTy Γ c S T → CertTy Δ (c.psubst σ) (S.rename σ.ren) (T.rename σ.ren)
  | _, _, _, _, _, _, _, _, hσ, .step hp => by
      have ih := CertTy.step (Prim.psubst hσ hp)
      simp only [ATy.erase_psubst] at ih
      exact ih
  | _, _, _, _, _, _, _, _, hσ, .seq hc hd => .seq (CertTy.psubst hσ hc) (CertTy.psubst hσ hd)

end

/-! ## Substitution in terms and definitions -/

/-- The implicit comparison at an application, after a path substitution, as an
explicit step between the substituted embeddings. -/
theorem Prim₀.psubst_step {Γ : Ctx s1} {Δ : Ctx s2} {σ : PSubst s1 s2} {S T : Ty s1}
    (hσ : σ.Typed Γ Δ) (h : Prim₀ Γ S T) :
    CertTy Δ (.step (S.embed.psubst σ) (T.embed.psubst σ)) (S.rename σ.ren) (T.rename σ.ren) := by
  have ih := CertTy.step (Prim.psubst hσ h)
  simp only [ATy.erase_psubst, Ty.erase_embed] at ih
  exact ih

/-- Reflexivity of the implicit comparison. -/
theorem Prim₀.refl (Γ : Ctx s) (T : Ty s) : Prim₀ Γ T T :=
  Prim.refl (Wf.embed Γ T) (Wf.embed Γ T) rfl

mutual

theorem HasTy.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {t : Tm s1} {T : Ty s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → HasTy Γ t T →
    ∃ t', t'.erase = t.erase.rename σ.ren ∧ HasTy Δ t' (T.rename σ.ren)
  | _, _, _, @Tm.path _ p, _, _, σ, hσ, .path hp =>
      ⟨.path (p.psubst σ), by simp only [Tm.erase, Tm.rename, Path.rename, Path.root_psubst],
        .path (PathTy.psubst hσ hp)⟩
  | _, _, _, @Tm.val _ (.lam S t), _, _, σ, hσ, .lam ht => by
      obtain ⟨t', e, ht'⟩ := HasTy.psubst (hσ.lift S) ht
      rw [PSubst.lift_ren] at e ht'
      exact ⟨.val (.lam (S.rename σ.ren) t'),
        by simp only [Tm.erase, Value.erase, Tm.rename, Value.rename, e], .lam ht'⟩
  | _, _, _, @Tm.app _ p q, _, _, σ, hσ, @HasTy.app _ _ _ S T _ S' hp hq hpr => by
      have hc := Prim₀.psubst_step hσ hpr
      have hq' : PathTy _ (.cast (q.psubst σ) (.step (S'.embed.psubst σ) (S.embed.psubst σ)))
          (S.rename σ.ren) := .cast (PathTy.psubst hσ hq) hc
      have ht := HasTy.app (PathTy.psubst hσ hp) hq' (Prim₀.refl _ _)
      refine ⟨.app (p.psubst σ) (.cast (q.psubst σ) (.step (S'.embed.psubst σ) (S.embed.psubst σ))),
        ?_, ?_⟩
      · simp only [Tm.erase, Tm.rename, Path.rename, Path.root_psubst, Path.root]
      · simp only [Path.root, Path.root_psubst] at ht
        rw [Ty.substVar_rename]
        exact ht
  | _, _, _, @Tm.val _ (.obj d), _, _, σ, hσ, @HasTy.obj _ _ T _ hd hdis => by
      obtain ⟨d', e, hd'⟩ := DefsTy.psubst (hσ.lift (.mu T)) hd
      rw [PSubst.lift_ren] at e hd'
      have hdis' : d'.Distinct := by
        apply Defs.Distinct.of_erase
        rw [e]
        exact hdis.erase.rename _
      exact ⟨.val (.obj d'),
        by simp only [Tm.erase, Value.erase, Tm.rename, Value.rename, e], .obj hd' hdis'⟩
  | _, _, _, @Tm.proj _ p a, _, _, σ, hσ, .proj hp =>
      ⟨.proj (p.psubst σ) a, by simp only [Tm.erase, Tm.rename, Path.rename, Path.root_psubst],
        .proj (PathTy.psubst hσ hp)⟩
  | _, _, _, _, _, _, σ, hσ, @HasTy.let _ _ _ T _ U ht hu => by
      obtain ⟨t', e1, ht'⟩ := HasTy.psubst hσ ht
      obtain ⟨u', e2, hu'⟩ := HasTy.psubst (hσ.lift T) hu
      rw [PSubst.lift_ren] at e2 hu'
      rw [Ty.weaken_rename] at hu'
      exact ⟨.let t' u', by simp only [Tm.erase, Tm.rename, e1, e2], .let ht' hu'⟩
  | _, _, _, _, _, _, σ, hσ, @HasTy.cast _ _ _ _ c _ ht hc => by
      obtain ⟨t', e, ht'⟩ := HasTy.psubst hσ ht
      exact ⟨.cast t' (c.psubst σ), by simp only [Tm.erase, e], .cast ht' (CertTy.psubst hσ hc)⟩

theorem DefsTy.psubst : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {d : Defs s1} {T : Ty s1}
    {Δ : Ctx s2} {σ : PSubst s1 s2},
    σ.Typed Γ Δ → DefsTy Γ d T →
    ∃ d', d'.erase = d.erase.rename σ.ren ∧ DefsTy Δ d' (T.rename σ.ren)
  | _, _, _, @Defs.typ _ A T, _, _, σ, _, .typ => ⟨.typ A (T.rename σ.ren), rfl, .typ⟩
  | _, _, _, @Defs.trm _ a _, _, _, σ, hσ, .trm ht => by
      obtain ⟨t', e, ht'⟩ := HasTy.psubst hσ ht
      exact ⟨.trm a t', by simp only [Defs.erase, Defs.rename, e], .trm ht'⟩
  | _, _, _, _, _, _, σ, hσ, .and hd1 hd2 => by
      obtain ⟨d1', e1, hd1'⟩ := DefsTy.psubst hσ hd1
      obtain ⟨d2', e2, hd2'⟩ := DefsTy.psubst hσ hd2
      exact ⟨.and d1' d2', by simp only [Defs.erase, Defs.rename, e1, e2], .and hd1' hd2'⟩

end

/-! ## Narrowing

The newest variable is replaced by itself under a cast by the certificate
`c : S' ⇒ S`. The roots do not change. -/

/-- The substitution that casts the newest variable by `c`. -/
def PSubst.narrow (c : Cert s) : PSubst (s,x) (s,x)
  | .here => .cast (.var .here) c.weaken
  | .there z => .var (.there z)

theorem PSubst.narrow_ren (c : Cert s) : (PSubst.narrow c).ren = Rename.id := by
  apply Rename.funext'
  intro k x
  cases k
  cases x <;> rfl

theorem PSubst.narrow_typed {Γ : Ctx s} {c : Cert s} {S' S : Ty s} (hc : CertTy Γ c S' S) :
    (PSubst.narrow c).Typed (Γ.cons S) (Γ.cons S') := by
  intro x
  rw [PSubst.narrow_ren, Ty.rename_id]
  cases x with
  | here => exact .cast (S := S'.weaken) .var (hc.weaken S')
  | there z => exact .var

theorem PathTy.narrow {Γ : Ctx s} {c : Cert s} {S' S : Ty s} {p : Path (s,x)} {T : Ty (s,x)}
    (hc : CertTy Γ c S' S) (h : PathTy (Γ.cons S) p T) :
    ∃ p', p'.root = p.root ∧ PathTy (Γ.cons S') p' T := by
  have h' := PathTy.psubst (PSubst.narrow_typed hc) h
  rw [PSubst.narrow_ren, Ty.rename_id] at h'
  exact ⟨_, by rw [Path.root_psubst, PSubst.narrow_ren]; rfl, h'⟩

theorem Wf.narrow {Γ : Ctx s} {c : Cert s} {S' S : Ty s} {T : ATy (s,x)}
    (hc : CertTy Γ c S' S) (h : Wf (Γ.cons S) T) :
    ∃ T', T'.erase = T.erase ∧ Wf (Γ.cons S') T' := by
  have h' := Wf.psubst (PSubst.narrow_typed hc) h
  exact ⟨_, by rw [ATy.erase_psubst, PSubst.narrow_ren, Ty.rename_id], h'⟩

theorem Prim.narrow {Γ : Ctx s} {c : Cert s} {S' S : Ty s} {T U : ATy (s,x)}
    (hc : CertTy Γ c S' S) (h : Prim (Γ.cons S) T U) :
    ∃ T' U', T'.erase = T.erase ∧ U'.erase = U.erase ∧ Prim (Γ.cons S') T' U' := by
  have h' := Prim.psubst (PSubst.narrow_typed hc) h
  exact ⟨_, _, by rw [ATy.erase_psubst, PSubst.narrow_ren, Ty.rename_id],
    by rw [ATy.erase_psubst, PSubst.narrow_ren, Ty.rename_id], h'⟩

theorem CertTy.narrow {Γ : Ctx s} {c : Cert s} {S' S : Ty s} {d : Cert (s,x)} {T U : Ty (s,x)}
    (hc : CertTy Γ c S' S) (h : CertTy (Γ.cons S) d T U) :
    ∃ d', CertTy (Γ.cons S') d' T U := by
  have h' := CertTy.psubst (PSubst.narrow_typed hc) h
  rw [PSubst.narrow_ren, Ty.rename_id, Ty.rename_id] at h'
  exact ⟨_, h'⟩

theorem HasTy.narrow {Γ : Ctx s} {c : Cert s} {S' S : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (hc : CertTy Γ c S' S) (h : HasTy (Γ.cons S) t T) :
    ∃ t', t'.erase = t.erase ∧ HasTy (Γ.cons S') t' T := by
  obtain ⟨t', e, h'⟩ := HasTy.psubst (PSubst.narrow_typed hc) h
  rw [PSubst.narrow_ren, Ty.rename_id] at h'
  rw [PSubst.narrow_ren, Tm.rename_id] at e
  exact ⟨t', e, h'⟩

/-! ## Substitution of a typed path for the newest variable

On judgment-level types this is the instantiation by the root of the path. -/

/-- The substitution of `p` for the newest variable. -/
def PSubst.single (p : Path s) : PSubst (s,x) s
  | .here => p
  | .there z => .var z

theorem PSubst.single_ren (p : Path s) : (PSubst.single p).ren = Rename.subst p.root := by
  apply Rename.funext'
  intro k x
  cases k
  cases x <;> rfl

theorem PSubst.single_typed {Γ : Ctx s} {p : Path s} {S : Ty s} (hp : PathTy Γ p S) :
    (PSubst.single p).Typed (Γ.cons S) Γ := by
  intro x
  rw [PSubst.single_ren]
  cases x with
  | here =>
      show PathTy Γ p (S.weaken.substVar p.root)
      rw [Ty.weaken_substVar]
      exact hp
  | there z =>
      show PathTy Γ (.var z) ((Γ.lookup z).weaken.substVar p.root)
      rw [Ty.weaken_substVar]
      exact .var

theorem PathTy.substPath {Γ : Ctx s} {p : Path s} {S : Ty s} {q : Path (s,x)} {T : Ty (s,x)}
    (hp : PathTy Γ p S) (h : PathTy (Γ.cons S) q T) :
    ∃ q', q'.root = (Rename.subst p.root).var q.root ∧ PathTy Γ q' (T.substVar p.root) := by
  have h' := PathTy.psubst (PSubst.single_typed hp) h
  rw [PSubst.single_ren] at h'
  exact ⟨_, by rw [Path.root_psubst, PSubst.single_ren], h'⟩

theorem CertTy.substPath {Γ : Ctx s} {p : Path s} {S : Ty s} {d : Cert (s,x)} {T U : Ty (s,x)}
    (hp : PathTy Γ p S) (h : CertTy (Γ.cons S) d T U) :
    ∃ d', CertTy Γ d' (T.substVar p.root) (U.substVar p.root) := by
  have h' := CertTy.psubst (PSubst.single_typed hp) h
  rw [PSubst.single_ren] at h'
  exact ⟨_, h'⟩

theorem HasTy.substPath {Γ : Ctx s} {p : Path s} {S : Ty s} {t : Tm (s,x)} {T : Ty (s,x)}
    (hp : PathTy Γ p S) (h : HasTy (Γ.cons S) t T) :
    ∃ t', t'.erase = t.erase.substVar p.root ∧ HasTy Γ t' (T.substVar p.root) := by
  obtain ⟨t', e, h'⟩ := HasTy.psubst (PSubst.single_typed hp) h
  rw [PSubst.single_ren] at e h'
  exact ⟨t', e, h'⟩

end SelDot
