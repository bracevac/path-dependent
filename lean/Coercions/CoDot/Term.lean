import Coercions.CoDot.Subst

/-!
# Terms with coerced references, static typing, substitution of references

Terms are DOT-MNF terms in which every variable occurrence is a reference
`x ▷ c` and every value in term position carries a coercion `v ▷ c`; `cast`
coerces any term. There is no subsumption: all three typing judgments are
syntax-directed up to the coercions. The three judgments are one inductive
family `Typed` over the sum `J`, so that `induction` applies.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Syntax -/

mutual

inductive Tm : Sig → Type where
  /-- A reference `x ▷ c`. -/
  | ref : BVar s .var → Co s → Tm s
  /-- A coerced value `v ▷ c`. -/
  | val : Value s → Co s → Tm s
  /-- `(x ▷ c) (y ▷ d)`. -/
  | app : BVar s .var → Co s → BVar s .var → Co s → Tm s
  /-- `(x ▷ c).a`. -/
  | proj : BVar s .var → Co s → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s
  /-- `t ▷ c`, for a coercion that needs no subject. -/
  | cast : Tm s → Co s → Tm s

inductive Value : Sig → Type where
  | obj : Defs (s,x) → Value s
  | lam : Ty s → Tm (s,x) → Value s

inductive Defs : Sig → Type where
  | typ : Label → Ty s → Defs s
  | trm : Label → Tm s → Defs s
  | and : Defs s → Defs s → Defs s

end

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .ref x c, ρ => .ref (ρ.var x) (c.rename ρ)
  | .val v c, ρ => .val (v.rename ρ) (c.rename ρ)
  | .app x c y d, ρ => .app (ρ.var x) (c.rename ρ) (ρ.var y) (d.rename ρ)
  | .proj x c a, ρ => .proj (ρ.var x) (c.rename ρ) a
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .cast t c, ρ => .cast (t.rename ρ) (c.rename ρ)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .obj d, ρ => .obj (d.rename ρ.lift)
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)

def Defs.rename : Defs s1 → Rename s1 s2 → Defs s2
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d1 d2, ρ => .and (d1.rename ρ) (d2.rename ρ)

end

mutual

/-- Apply a coerced renaming: the coercion of each variable goes in front of
the coercion of every reference to it. -/
def Tm.csubst : Tm s1 → CoSub s1 s2 → Tm s2
  | .ref x c, σ => .ref (σ.ρ.var x) (.seq (σ.η x) (c.csubst σ))
  | .val v c, σ => .val (v.csubst σ) (c.csubst σ)
  | .app x c y d, σ =>
      .app (σ.ρ.var x) (.seq (σ.η x) (c.csubst σ)) (σ.ρ.var y) (.seq (σ.η y) (d.csubst σ))
  | .proj x c a, σ => .proj (σ.ρ.var x) (.seq (σ.η x) (c.csubst σ)) a
  | .let t u, σ => .let (t.csubst σ) (u.csubst σ.lift)
  | .cast t c, σ => .cast (t.csubst σ) (c.csubst σ)

def Value.csubst : Value s1 → CoSub s1 s2 → Value s2
  | .obj d, σ => .obj (d.csubst σ.lift)
  | .lam S t, σ => .lam (S.rename σ.ρ) (t.csubst σ.lift)

def Defs.csubst : Defs s1 → CoSub s1 s2 → Defs s2
  | .typ A T, σ => .typ A (T.rename σ.ρ)
  | .trm a t, σ => .trm a (t.csubst σ)
  | .and d1 d2, σ => .and (d1.csubst σ) (d2.csubst σ)

end

def Defs.labels : Defs s → List Label
  | .typ A _ => [A]
  | .trm a _ => [a]
  | .and d1 d2 => d1.labels ++ d2.labels

/-- The type member at a label. Same bias as `member` on record types. -/
def Defs.lookupTyp : Defs s → Label → Option (Ty s)
  | .typ B T, A => if A = B then some T else none
  | .trm _ _, _ => none
  | .and d1 d2, A => (d2.lookupTyp A).or (d1.lookupTyp A)

/-- The field at a label. -/
def Defs.lookupTrm : Defs s → Label → Option (Tm s)
  | .typ _ _, _ => none
  | .trm b t, a => if a = b then some t else none
  | .and d1 d2, a => (d2.lookupTrm a).or (d1.lookupTrm a)

/-! ## Static typing -/

/-- The three judgments: a term, a value (at the type of its introduction
rule), a definition list. -/
inductive J (s : Sig) : Type where
  | tm : Tm s → Ty s → J s
  | val : Value s → Ty s → J s
  | defs : Defs s → Ty s → J s

def J.rename : J s1 → Rename s1 s2 → J s2
  | .tm t T, ρ => .tm (t.rename ρ) (T.rename ρ)
  | .val v T, ρ => .val (v.rename ρ) (T.rename ρ)
  | .defs d T, ρ => .defs (d.rename ρ) (T.rename ρ)

def J.csubst : J s1 → CoSub s1 s2 → J s2
  | .tm t T, σ => .tm (t.csubst σ) (T.rename σ.ρ)
  | .val v T, σ => .val (v.csubst σ) (T.rename σ.ρ)
  | .defs d T, σ => .defs (d.csubst σ) (T.rename σ.ρ)

inductive Typed : {s : Sig} → Ctx s → J s → Prop where
  | ref : CoTy Γ (some x) c (Γ.lookup x) T → Typed Γ (.tm (.ref x c) T)
  | val : Typed Γ (.val v P) → CoTy Γ none c P T → Typed Γ (.tm (.val v c) T)
  | app : CoTy Γ (some x) c (Γ.lookup x) (.all S T) → CoTy Γ (some y) d (Γ.lookup y) S →
      Typed Γ (.tm (.app x c y d) (T.substVar y))
  | proj : CoTy Γ (some x) c (Γ.lookup x) (.fld a T) → Typed Γ (.tm (.proj x c a) T)
  | «let» : Typed Γ (.tm t T) → Typed (Γ.cons T) (.tm u U.weaken) → Typed Γ (.tm (.let t u) U)
  | cast : Typed Γ (.tm t S) → CoTy Γ none c S T → Typed Γ (.tm (.cast t c) T)
  /-- `All-I`. -/
  | lam : Typed (Γ.cons S) (.tm t T) → Typed Γ (.val (.lam S t) (.all S T))
  /-- `{}-I`, with the self variable at `μ(T)`. -/
  | obj : Typed (Γ.cons (.mu T)) (.defs d T) → Typed Γ (.val (.obj d) (.mu T))
  | dtyp : Typed Γ (.defs (.typ A T) (.typ A T T))
  | dtrm : Typed Γ (.tm t T) → Typed Γ (.defs (.trm a t) (.fld a T))
  | dand : Typed Γ (.defs d1 T1) → Typed Γ (.defs d2 T2) →
      (∀ ℓ, ℓ ∈ d1.labels → ℓ ∉ d2.labels) →
      Typed Γ (.defs (.and d1 d2) (.and T1 T2))

/-! ## Structural lemmas -/

theorem Defs.labels_rename (d : Defs s1) (ρ : Rename s1 s2) : (d.rename ρ).labels = d.labels := by
  match d with
  | .typ _ _ | .trm _ _ => rfl
  | .and d1 d2 =>
    show (d1.rename ρ).labels ++ (d2.rename ρ).labels = d1.labels ++ d2.labels
    rw [Defs.labels_rename d1 ρ, Defs.labels_rename d2 ρ]

theorem Defs.labels_csubst (d : Defs s1) (σ : CoSub s1 s2) : (d.csubst σ).labels = d.labels := by
  match d with
  | .typ _ _ | .trm _ _ => rfl
  | .and d1 d2 =>
    show (d1.csubst σ).labels ++ (d2.csubst σ).labels = d1.labels ++ d2.labels
    rw [Defs.labels_csubst d1 σ, Defs.labels_csubst d2 σ]

/-- Lookup preservation lifts under a binder. -/
theorem Ctx.cons_renames {Γ1 : Ctx s1} {Γ2 : Ctx s2} {ρ : Rename s1 s2}
    (hρ : ∀ x, Γ2.lookup (ρ.var x) = (Γ1.lookup x).rename ρ) (S : Ty s1) :
    ∀ x, (Γ2.cons (S.rename ρ)).lookup (ρ.lift.var x) = ((Γ1.cons S).lookup x).rename ρ.lift := by
  intro x
  cases x with
  | here => exact (Ty.weaken_rename S ρ).symm
  | there y =>
    show (Γ2.lookup (ρ.var y)).weaken = (Γ1.lookup y).weaken.rename ρ.lift
    rw [hρ y, Ty.weaken_rename]

theorem Comp.mem_labels {T C : Ty s} (hc : Comp T C) :
    ∀ a U, C = .fld a U → a ∈ labels T := by
  induction hc with
  | refl => intro a U e; subst e; simp [labels]
  | left _ ih => intro a U e; simp [labels, ih a U e]
  | right _ ih => intro a U e; simp [labels, ih a U e]

theorem Defs.lookupTrm_mem {a : Label} {t : Tm s} :
    (d : Defs s) → d.lookupTrm a = some t → a ∈ d.labels
  | .typ _ _, h => by simp [Defs.lookupTrm] at h
  | .trm b _, h => by
    simp only [Defs.lookupTrm] at h
    by_cases hab : a = b
    · simp [Defs.labels, hab]
    · simp [hab] at h
  | .and d1 d2, h => by
    simp only [Defs.lookupTrm] at h
    cases h2 : d2.lookupTrm a with
    | some t2 =>
      have := Defs.lookupTrm_mem d2 h2
      simp [Defs.labels, this]
    | none =>
      rw [h2] at h
      have := Defs.lookupTrm_mem d1 h
      simp [Defs.labels, this]

/-- Renaming under lookup preservation (weakening is the instance `succ`). -/
theorem Typed.rename {Γ1 : Ctx s1} {Γ2 : Ctx s2} {ρ : Rename s1 s2}
    (hρ : ∀ x, Γ2.lookup (ρ.var x) = (Γ1.lookup x).rename ρ)
    {j : J s1} (h : Typed Γ1 j) : Typed Γ2 (j.rename ρ) := by
  induction h generalizing s2 Γ2 with
  | @ref _ Γ1 x c T h =>
    have h' := CoTy.rename hρ h
    rw [← hρ x] at h'
    exact .ref h'
  | @val _ Γ1 v P c T _ hc ih => exact .val (ih hρ) (CoTy.rename hρ hc)
  | @app _ Γ1 x c S T y d h1 h2 =>
    have h1' := CoTy.rename hρ h1
    have h2' := CoTy.rename hρ h2
    rw [← hρ x] at h1'
    rw [← hρ y] at h2'
    show Typed Γ2 (.tm (.app (ρ.var x) (c.rename ρ) (ρ.var y) (d.rename ρ)) ((T.substVar y).rename ρ))
    rw [Ty.substVar_rename]
    exact .app h1' h2'
  | @proj _ Γ1 x c a T h =>
    have h' := CoTy.rename hρ h
    rw [← hρ x] at h'
    exact .proj h'
  | @«let» _ Γ1 t T u U _ _ ih1 ih2 =>
    have h2 : Typed (Γ2.cons (T.rename ρ)) (.tm (u.rename ρ.lift) (U.weaken.rename ρ.lift)) :=
      ih2 (Ctx.cons_renames hρ T)
    rw [Ty.weaken_rename] at h2
    exact .let (ih1 hρ) h2
  | @cast _ Γ1 t S c T _ hc ih => exact .cast (ih hρ) (CoTy.rename hρ hc)
  | @lam _ t T Γ1 S _ ih => exact .lam (ih (Ctx.cons_renames hρ S))
  | @obj _ d T Γ1 _ ih => exact .obj (T := T.rename ρ.lift) (ih (Ctx.cons_renames hρ (.mu T)))
  | dtyp => exact .dtyp
  | dtrm _ ih => exact .dtrm (ih hρ)
  | @dand _ Γ1 d1 T1 d2 T2 _ _ hdis ih1 ih2 =>
    refine .dand (ih1 hρ) (ih2 hρ) ?_
    simpa only [Defs.labels_rename] using hdis

/-- Coerced substitution for terms, values and definitions. -/
theorem Typed.csubst {Γ1 : Ctx s1} {Γ2 : Ctx s2} {σ : CoSub s1 s2} (hσ : CoSub.Ok Γ1 Γ2 σ)
    {j : J s1} (h : Typed Γ1 j) : Typed Γ2 (j.csubst σ) := by
  induction h generalizing s2 Γ2 with
  | @ref _ Γ1 x c T h => exact .ref (.seq (hσ x) (CoTy.csubst hσ h))
  | @val _ Γ1 v P c T _ hc ih => exact .val (ih hσ) (CoTy.csubst hσ hc)
  | @app _ Γ1 x c S T y d h1 h2 =>
    show Typed Γ2 (.tm (.app (σ.ρ.var x) (.seq (σ.η x) (c.csubst σ)) (σ.ρ.var y)
      (.seq (σ.η y) (d.csubst σ))) ((T.substVar y).rename σ.ρ))
    rw [Ty.substVar_rename]
    exact .app (.seq (hσ x) (CoTy.csubst hσ h1)) (.seq (hσ y) (CoTy.csubst hσ h2))
  | @proj _ Γ1 x c a T h => exact .proj (.seq (hσ x) (CoTy.csubst hσ h))
  | @«let» _ Γ1 t T u U _ _ ih1 ih2 =>
    have h2 : Typed (Γ2.cons (T.rename σ.ρ)) (.tm (u.csubst σ.lift) (U.weaken.rename σ.ρ.lift)) :=
      ih2 (hσ.lift T)
    rw [Ty.weaken_rename] at h2
    exact .let (ih1 hσ) h2
  | @cast _ Γ1 t S c T _ hc ih => exact .cast (ih hσ) (CoTy.csubst hσ hc)
  | @lam _ t T Γ1 S _ ih => exact .lam (ih (hσ.lift S))
  | @obj _ d T Γ1 _ ih => exact .obj (T := T.rename σ.ρ.lift) (ih (hσ.lift (.mu T)))
  | dtyp => exact .dtyp
  | dtrm _ ih => exact .dtrm (ih hσ)
  | @dand _ Γ1 d1 T1 d2 T2 _ _ hdis ih1 ih2 =>
    refine .dand (ih1 hσ) (ih2 hσ) ?_
    simpa only [Defs.labels_csubst] using hdis

/-- Replace the innermost variable, of type `S`, by the reference `z ▷ e` at
`S`. This is the typing of the application step on a bare function and of the
selection step on a bare object (with `e = id`). -/
theorem Typed.inst {Γ : Ctx s} {S : Ty s} {t : Tm (s,x)} {T : Ty (s,x)} {z : BVar s .var} {e : Co s}
    (ht : Typed (Γ.cons S) (.tm t T)) (he : CoTy Γ (some z) e (Γ.lookup z) S) :
    Typed Γ (.tm (t.csubst (CoSub.inst z e)) (T.substVar z)) :=
  Typed.csubst (CoSub.inst_ok he) ht

/-- The `let` step on a reference answer: the body's type does not mention
the bound variable and is unchanged. -/
theorem Typed.letRef {Γ : Ctx s} {S U : Ty s} {u : Tm (s,x)} {z : BVar s .var} {e : Co s}
    (hu : Typed (Γ.cons S) (.tm u U.weaken)) (he : CoTy Γ (some z) e (Γ.lookup z) S) :
    Typed Γ (.tm (u.csubst (CoSub.inst z e)) U) := by
  have h := Typed.inst hu he
  rw [Ty.weaken_substVar] at h
  exact h

/-- Keep the innermost variable but put `c` in front of its references. -/
def CoSub.narrow (c : Co (s,x)) : CoSub (s,x) (s,x) where
  ρ := Rename.id
  η
    | .here => c
    | .there _ => .id

/-- The `let` step on a value answer `v ▷ c`: the value is allocated at its
precise type `P`, and the body, typed for a variable of type `S`, is typed
for the new location once `c : P ⇒ S` is put in front of its references. -/
theorem Typed.alloc {Γ : Ctx s} {P S U : Ty s} {u : Tm (s,x)} {c : Co s}
    (hu : Typed (Γ.cons S) (.tm u U.weaken)) (hc : CoTy Γ none c P S) :
    Typed (Γ.cons P) (.tm (u.csubst (CoSub.narrow c.weaken)) U.weaken) := by
  have hok : CoSub.Ok (Γ.cons S) (Γ.cons P) (CoSub.narrow c.weaken) := by
    intro x
    cases x with
    | here =>
      show CoTy (Γ.cons P) (some .here) c.weaken P.weaken (S.weaken.rename Rename.id)
      rw [Ty.rename_id]
      exact (CoTy.rename (Γ2 := Γ.cons P) (ρ := Rename.succ) (fun _ => rfl) hc).anySubject _
    | there y =>
      show CoTy (Γ.cons P) (some (.there y)) .id (Γ.lookup y).weaken
        ((Γ.lookup y).weaken.rename Rename.id)
      rw [Ty.rename_id]
      exact .id
  have h : Typed (Γ.cons P) (.tm (u.csubst (CoSub.narrow c.weaken)) (U.weaken.rename Rename.id)) :=
    Typed.csubst hok hu
  rw [Ty.rename_id] at h
  exact h

theorem Typed.defs_record_aux {Γ : Ctx s} {j : J s} (h : Typed Γ j) :
    ∀ d T, j = .defs d T → Record T ∧ labels T = d.labels ∧ ∀ A, member T A = d.lookupTyp A := by
  induction h with
  | dtyp => intro d T e; cases e; exact ⟨.typ, rfl, fun _ => rfl⟩
  | dtrm _ _ => intro d T e; cases e; exact ⟨.fld, rfl, fun _ => rfl⟩
  | @dand _ _ d1 T1 d2 T2 _ _ hdis ih1 ih2 =>
    intro d T e
    cases e
    obtain ⟨r1, l1, m1⟩ := ih1 _ _ rfl
    obtain ⟨r2, l2, m2⟩ := ih2 _ _ rfl
    refine ⟨.and r1 r2 ?_, ?_, ?_⟩
    · intro ℓ h1 h2
      rw [l1] at h1
      rw [l2] at h2
      exact hdis ℓ h1 h2
    · show labels T1 ++ labels T2 = d1.labels ++ d2.labels
      rw [l1, l2]
    · intro A
      show (member T2 A).or (member T1 A) = (d2.lookupTyp A).or (d1.lookupTyp A)
      rw [m1, m2]
  | _ => intro d T e; cases e

theorem Typed.defs_field_aux {Γ : Ctx s} {j : J s} (h : Typed Γ j) :
    ∀ d T, j = .defs d T → ∀ a U, Comp T (.fld a U) →
      ∃ t, d.lookupTrm a = some t ∧ Typed Γ (.tm t U) := by
  induction h with
  | dtyp => intro d T e a U hc; cases e; cases hc
  | @dtrm _ _ t T b ht _ =>
    intro d T' e a U hc
    cases e
    cases hc
    exact ⟨t, by simp [Defs.lookupTrm], ht⟩
  | @dand _ _ d1 T1 d2 T2 h1 _ hdis ih1 ih2 =>
    intro d T e a U hc
    cases e
    cases hc with
    | left hc1 =>
      obtain ⟨t, ht, hty⟩ := ih1 _ _ rfl a U hc1
      have ha : a ∈ d1.labels := by
        rw [← (Typed.defs_record_aux h1 _ _ rfl).2.1]
        exact Comp.mem_labels hc1 a U rfl
      have hn : d2.lookupTrm a = none := by
        cases h2 : d2.lookupTrm a with
        | none => rfl
        | some t2 => exact absurd (Defs.lookupTrm_mem d2 h2) (hdis a ha)
      refine ⟨t, ?_, hty⟩
      show (d2.lookupTrm a).or (d1.lookupTrm a) = some t
      rw [hn, ht]; rfl
    | right hc2 =>
      obtain ⟨t, ht, hty⟩ := ih2 _ _ rfl a U hc2
      refine ⟨t, ?_, hty⟩
      show (d2.lookupTrm a).or (d1.lookupTrm a) = some t
      rw [ht]; rfl
  | _ => intro d T e; cases e

/-- Definition typing assigns a record type whose type members are those of
the definitions. -/
theorem Typed.defs_record {Γ : Ctx s} {d : Defs s} {T : Ty s} (h : Typed Γ (.defs d T)) :
    Record T ∧ labels T = d.labels ∧ ∀ A, member T A = d.lookupTyp A :=
  Typed.defs_record_aux h d T rfl

/-- A field declaration that is a component of the type of a definition list
is the type of the field that lookup finds. -/
theorem Typed.defs_field {Γ : Ctx s} {d : Defs s} {T : Ty s} (h : Typed Γ (.defs d T))
    {a : Label} {U : Ty s} (hc : Comp T (.fld a U)) :
    ∃ t, d.lookupTrm a = some t ∧ Typed Γ (.tm t U) :=
  Typed.defs_field_aux h d T rfl a U hc

end CoDot
