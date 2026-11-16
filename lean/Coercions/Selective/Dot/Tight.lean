import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.RenameTy

/-!
# Selective DOT: inert contexts and tight typing

The inert-context analysis of Rapoport, Kabir, He and Lhoták, "A Simpler
Syntactic Soundness Proof for Dependent Object Types" (OOPSLA 2017), for the
calculus of `Typing.lean`.

* Inert types are function types and recursive records; an inert context
  declares only inert types.
* Precise typing of a variable gives its declared type, the opened record, and
  the parts of that record.
* Tight subtyping and tight typing read the bounds of a selection only from a
  precise tight type declaration.
* Invertible typing is closed under tight subtyping in an inert context, and it
  contains tight typing. Its inversion lemmas give the shapes of the types of a
  variable.
* General to tight: in an inert context, path typing, primitive subtyping and
  certificates are tight.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Inert types and contexts -/

/-- Labels declared by a record type. -/
def Ty.labels : Ty s → List Label
  | .typ A _ _ => [A]
  | .fld a _ => [a]
  | .and S T => S.labels ++ T.labels
  | _ => []

/-- Record types: intersections of field declarations and tight type
declarations, with distinct labels. -/
inductive Ty.Record {s : Sig} : Ty s → Prop
  | typ : Ty.Record (.typ A T T)
  | fld : Ty.Record (.fld a T)
  | and : Ty.Record T → Ty.Record U → (∀ ℓ, ℓ ∈ T.labels → ℓ ∉ U.labels) →
      Ty.Record (.and T U)

/-- Inert types: function types and recursive records. -/
inductive Ty.Inert {s : Sig} : Ty s → Prop
  | all {S : Ty s} {T : Ty (s,x)} : Ty.Inert (.all S T)
  | obj {T : Ty (s,x)} : Ty.Record T → Ty.Inert (.mu T)

/-- Inert contexts: every declared type is inert. -/
inductive Ctx.Inert : {s : Sig} → Ctx s → Prop
  | nil : Ctx.Inert .nil
  | cons : Ctx.Inert Γ → Ty.Inert T → Ctx.Inert (.cons Γ T)

/-! ## The judgments of the proof -/

/-- Precise typing of a variable: its declared type, opened, and the parts of
the opened record. -/
inductive Precise {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Ty s → Prop
  | var : Precise Γ x (Γ.lookup x)
  | recE {T : Ty (s,x)} : Precise Γ x (.mu T) → Precise Γ x (T.substVar x)
  | and1 : Precise Γ x (.and T U) → Precise Γ x T
  | and2 : Precise Γ x (.and T U) → Precise Γ x U

/-- General subtyping: a certificate exists. -/
def GSub {s : Sig} (Γ : Ctx s) (S T : Ty s) : Prop := ∃ c, CertTy Γ c S T

/-- Tight subtyping: declarative, with transitivity; the bounds of a selection
are read only from a precise tight type declaration. -/
inductive TSub {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Prop
  | top : TSub Γ T .top
  | bot : TSub Γ .bot T
  | refl : TSub Γ T T
  | trans : TSub Γ S M → TSub Γ M T → TSub Γ S T
  | and1 : TSub Γ (.and S T) S
  | and2 : TSub Γ (.and S T) T
  | and : TSub Γ S T → TSub Γ S U → TSub Γ S (.and T U)
  | fld : TSub Γ T U → TSub Γ (.fld a T) (.fld a U)
  | typ : TSub Γ S2 S1 → TSub Γ T1 T2 → TSub Γ (.typ A S1 T1) (.typ A S2 T2)
  | all {S1 S2 : Ty s} {T1 T2 : Ty (s,x)} :
      TSub Γ S2 S1 → GSub (Γ.cons S2) T1 T2 → TSub Γ (.all S1 T1) (.all S2 T2)
  | selU {x : BVar s .var} : Precise Γ x (.typ A T T) → TSub Γ (.sel x A) T
  | selL {x : BVar s .var} : Precise Γ x (.typ A T T) → TSub Γ T (.sel x A)

/-- Tight typing of a variable. -/
inductive TTy {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Ty s → Prop
  | var : TTy Γ x (Γ.lookup x)
  | recI {T : Ty (s,x)} : TTy Γ x (T.substVar x) → TTy Γ x (.mu T)
  | recE {T : Ty (s,x)} : TTy Γ x (.mu T) → TTy Γ x (T.substVar x)
  | andI : TTy Γ x T → TTy Γ x U → TTy Γ x (.and T U)
  | sub : TTy Γ x T → TSub Γ T U → TTy Γ x U

/-- Invertible typing of a variable: precise typing closed under subtyping of
the parts of a type, rule by rule. -/
inductive Inv {s : Sig} (Γ : Ctx s) (x : BVar s .var) : Ty s → Prop
  | prec : Precise Γ x T → Inv Γ x T
  | fld : Inv Γ x (.fld a T) → TSub Γ T U → Inv Γ x (.fld a U)
  | typ : Inv Γ x (.typ A T U) → TSub Γ T' T → TSub Γ U U' → Inv Γ x (.typ A T' U')
  | all {S S' : Ty s} {T T' : Ty (s,x)} :
      Inv Γ x (.all S T) → TSub Γ S' S → GSub (Γ.cons S') T T' → Inv Γ x (.all S' T')
  | and : Inv Γ x S → Inv Γ x T → Inv Γ x (.and S T)
  | sel {y : BVar s .var} : Inv Γ x S → Precise Γ y (.typ A S S) → Inv Γ x (.sel y A)
  | mu {T : Ty (s,x)} : Inv Γ x (T.substVar x) → Inv Γ x (.mu T)
  | top : Inv Γ x .top

/-- `AllSub Γ S0 T0 S T`: `∀(x:S0)T0` is below `∀(x:S)T` by a chain of
function-subtyping layers. -/
inductive AllSub {s : Sig} (Γ : Ctx s) (S0 : Ty s) (T0 : Ty (s,x)) : Ty s → Ty (s,x) → Prop
  | refl : AllSub Γ S0 T0 S0 T0
  | step {S S' : Ty s} {T T' : Ty (s,x)} :
      AllSub Γ S0 T0 S T → TSub Γ S' S → GSub (Γ.cons S') T T' → AllSub Γ S0 T0 S' T'

/-! ## Stability under renaming -/

@[simp] theorem Ty.labels_rename (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).labels = T.labels := by
  induction T generalizing s2 with
  | and _ _ ih1 ih2 => simp [Ty.rename, Ty.labels, ih1, ih2]
  | _ => simp [Ty.rename, Ty.labels]

theorem Ty.Record.rename {T : Ty s1} (h : T.Record) (ρ : Rename s1 s2) :
    (T.rename ρ).Record := by
  induction h with
  | typ => exact .typ
  | fld => exact .fld
  | and _ _ hd ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Ty.labels_rename] using hd)

theorem Ty.Inert.rename {T : Ty s1} (h : T.Inert) (ρ : Rename s1 s2) :
    (T.rename ρ).Inert := by
  cases h with
  | all => exact .all
  | obj hr => exact .obj (hr.rename _)

/-- The declared type of a variable in an inert context is inert. -/
theorem Ctx.Inert.lookup {Γ : Ctx s} (h : Γ.Inert) {x : BVar s .var} :
    (Γ.lookup x).Inert := by
  induction h with
  | nil => cases x
  | cons _ hT ih =>
      cases x with
      | here => exact hT.rename _
      | there y => exact (ih (x := y)).rename _

/-! ## Conjuncts of a record -/

/-- `Conj T R`: `T` is `R` or one of the conjuncts of `R`. -/
inductive Ty.Conj {s : Sig} (T : Ty s) : Ty s → Prop
  | refl : Ty.Conj T T
  | left : Ty.Conj T R1 → Ty.Conj T (.and R1 R2)
  | right : Ty.Conj T R2 → Ty.Conj T (.and R1 R2)

theorem Ty.Conj.and_left {T U R : Ty s} (h : Ty.Conj (.and T U) R) : Ty.Conj T R := by
  induction h with
  | refl => exact .left .refl
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem Ty.Conj.and_right {T U R : Ty s} (h : Ty.Conj (.and T U) R) : Ty.Conj U R := by
  induction h with
  | refl => exact .right .refl
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem Ty.Conj.record {T R : Ty s} (h : Ty.Conj T R) (hR : R.Record) : T.Record := by
  induction h with
  | refl => exact hR
  | left _ ih => cases hR with | and h1 _ _ => exact ih h1
  | right _ ih => cases hR with | and _ h2 _ => exact ih h2

theorem Ty.Conj.labels {T R : Ty s} (h : Ty.Conj T R) {ℓ : Label} (hl : ℓ ∈ T.labels) :
    ℓ ∈ R.labels := by
  induction h with
  | refl => exact hl
  | left _ ih => exact List.mem_append_left _ ih
  | right _ ih => exact List.mem_append_right _ ih

/-- Two declarations with a common label in one record are the same. -/
theorem Ty.Conj.unique {R : Ty s} (hR : R.Record) :
    ∀ {V W : Ty s} {ℓ : Label}, Ty.Conj V R → Ty.Conj W R → ℓ ∈ V.labels → ℓ ∈ W.labels →
      (∀ V1 V2, V ≠ .and V1 V2) → (∀ W1 W2, W ≠ .and W1 W2) → V = W := by
  induction hR with
  | typ =>
      intro V W ℓ hV hW _ _ _ _
      cases hV; cases hW; rfl
  | fld =>
      intro V W ℓ hV hW _ _ _ _
      cases hV; cases hW; rfl
  | and _ _ hd ih1 ih2 =>
      intro V W ℓ hV hW hlV hlW hVa hWa
      cases hV with
      | refl => exact absurd rfl (hVa _ _)
      | left hV1 =>
          cases hW with
          | refl => exact absurd rfl (hWa _ _)
          | left hW1 => exact ih1 hV1 hW1 hlV hlW hVa hWa
          | right hW2 => exact absurd (hW2.labels hlW) (hd ℓ (hV1.labels hlV))
      | right hV2 =>
          cases hW with
          | refl => exact absurd rfl (hWa _ _)
          | left hW1 => exact absurd (hV2.labels hlV) (hd ℓ (hW1.labels hlW))
          | right hW2 => exact ih2 hV2 hW2 hlV hlW hVa hWa

/-! ## Shapes of precise types -/

theorem Ctx.Inert.lookup_mu {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {R : Ty (s,x)}
    (e : Γ.lookup x = .mu R) : R.Record := by
  have h := hΓ.lookup (x := x)
  rw [e] at h
  cases h with
  | obj hr => exact hr

/-- A precise type of a variable in an inert context is its declared type, or a
part of the opened record that it declares. -/
theorem Precise.shape {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {T : Ty s}
    (h : Precise Γ x T) :
    T = Γ.lookup x ∨ ∃ R, Γ.lookup x = .mu R ∧ Ty.Conj T (R.substVar x) := by
  induction h with
  | var => exact .inl rfl
  | recE _ ih =>
      rcases ih with e | ⟨R, e, hc⟩
      · exact .inr ⟨_, e.symm, .refl⟩
      · have hr := hc.record ((hΓ.lookup_mu e).rename _)
        cases hr
  | and1 _ ih =>
      rcases ih with e | ⟨R, e, hc⟩
      · have hI := hΓ.lookup (x := x)
        rw [← e] at hI
        cases hI
      · exact .inr ⟨R, e, hc.and_left⟩
  | and2 _ ih =>
      rcases ih with e | ⟨R, e, hc⟩
      · have hI := hΓ.lookup (x := x)
        rw [← e] at hI
        cases hI
      · exact .inr ⟨R, e, hc.and_right⟩

/-- A precise type that is not inert is a part of the opened record. -/
theorem Precise.record_part {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {T : Ty s}
    (h : Precise Γ x T) (hT : ¬ T.Inert) :
    ∃ R, Γ.lookup x = .mu R ∧ Ty.Conj T (R.substVar x) ∧ T.Record := by
  rcases h.shape hΓ with e | ⟨R, e, hc⟩
  · exact absurd (e ▸ hΓ.lookup) hT
  · exact ⟨R, e, hc, hc.record ((hΓ.lookup_mu e).rename _)⟩

theorem Precise.not_sel {Γ : Ctx s} (hΓ : Γ.Inert) {x y : BVar s .var} {A : Label} :
    ¬ Precise Γ x (.sel y A) := by
  intro h
  obtain ⟨_, _, _, hr⟩ := h.record_part hΓ (fun h => by cases h)
  cases hr

theorem Precise.not_bot {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} :
    ¬ Precise Γ x .bot := by
  intro h
  obtain ⟨_, _, _, hr⟩ := h.record_part hΓ (fun h => by cases h)
  cases hr

theorem Precise.not_top {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} :
    ¬ Precise Γ x .top := by
  intro h
  obtain ⟨_, _, _, hr⟩ := h.record_part hΓ (fun h => by cases h)
  cases hr

theorem Precise.all_inv {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {S : Ty s}
    {T : Ty (s,x)} (h : Precise Γ x (.all S T)) : Γ.lookup x = .all S T := by
  rcases h.shape hΓ with e | ⟨R, e, hc⟩
  · exact e.symm
  · have hr := hc.record ((hΓ.lookup_mu e).rename _)
    cases hr

theorem Precise.mu_inv {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {T : Ty (s,x)}
    (h : Precise Γ x (.mu T)) : Γ.lookup x = .mu T := by
  rcases h.shape hΓ with e | ⟨R, e, hc⟩
  · exact e.symm
  · have hr := hc.record ((hΓ.lookup_mu e).rename _)
    cases hr

theorem Precise.typ_tight {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {A : Label}
    {S U : Ty s} (h : Precise Γ x (.typ A S U)) : S = U := by
  obtain ⟨_, _, _, hr⟩ := h.record_part hΓ (fun h => by cases h)
  cases hr
  rfl

theorem Precise.typ_unique {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {A : Label}
    {T T' : Ty s} (h : Precise Γ x (.typ A T T)) (h' : Precise Γ x (.typ A T' T')) :
    T = T' := by
  obtain ⟨R, e, hc, _⟩ := h.record_part hΓ (fun h => by cases h)
  obtain ⟨R', e', hc', _⟩ := h'.record_part hΓ (fun h => by cases h)
  rw [e] at e'
  cases e'
  have := Ty.Conj.unique ((hΓ.lookup_mu e).rename _) hc hc' (ℓ := A)
    (by simp [Ty.labels]) (by simp [Ty.labels]) (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)
  cases this
  rfl

theorem Precise.fld_unique {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {a : Label}
    {T T' : Ty s} (h : Precise Γ x (.fld a T)) (h' : Precise Γ x (.fld a T')) :
    T = T' := by
  obtain ⟨R, e, hc, _⟩ := h.record_part hΓ (fun h => by cases h)
  obtain ⟨R', e', hc', _⟩ := h'.record_part hΓ (fun h => by cases h)
  rw [e] at e'
  cases e'
  have := Ty.Conj.unique ((hΓ.lookup_mu e).rename _) hc hc' (ℓ := a)
    (by simp [Ty.labels]) (by simp [Ty.labels]) (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)
  cases this
  rfl

/-! ## Invertible typing -/

theorem Inv.mu_inv {Γ : Ctx s} {x : BVar s .var} {T : Ty (s,x)}
    (h : Inv Γ x (.mu T)) : Inv Γ x (T.substVar x) := by
  cases h with
  | prec hp => exact .prec hp.recE
  | mu h => exact h

theorem Inv.and_inv {Γ : Ctx s} {x : BVar s .var} {T U : Ty s}
    (h : Inv Γ x (.and T U)) : Inv Γ x T ∧ Inv Γ x U := by
  cases h with
  | prec hp => exact ⟨.prec hp.and1, .prec hp.and2⟩
  | and h1 h2 => exact ⟨h1, h2⟩

/-- Invertible typing is closed under tight subtyping in an inert context. -/
theorem Inv.sub {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {T U : Ty s}
    (h : Inv Γ x T) (hTU : TSub Γ T U) : Inv Γ x U := by
  revert h
  induction hTU with
  | top => intro _; exact .top
  | bot =>
      intro h
      cases h with
      | prec hp => exact absurd hp (Precise.not_bot hΓ)
  | refl => intro h; exact h
  | trans _ _ ih1 ih2 => intro h; exact ih2 (ih1 h)
  | and1 => intro h; exact h.and_inv.1
  | and2 => intro h; exact h.and_inv.2
  | and _ _ ih1 ih2 => intro h; exact .and (ih1 h) (ih2 h)
  | fld hs _ => intro h; exact .fld h hs
  | typ h1 h2 _ _ => intro h; exact .typ h h1 h2
  | all h1 h2 _ => intro h; exact .all h h1 h2
  | selU hp =>
      intro h
      cases h with
      | prec hq => exact absurd hq (Precise.not_sel hΓ)
      | sel h' hq =>
          cases Precise.typ_unique hΓ hq hp
          exact h'
  | selL hp => intro h; exact .sel h hp

/-- Tight typing is invertible typing in an inert context. -/
theorem TTy.inv {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {T : Ty s}
    (h : TTy Γ x T) : Inv Γ x T := by
  induction h with
  | var => exact .prec .var
  | recI _ ih => exact .mu ih
  | recE _ ih => exact ih.mu_inv
  | andI _ _ ih1 ih2 => exact .and ih1 ih2
  | sub _ hs ih => exact ih.sub hΓ hs

theorem Inv.typ_inv {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {A : Label} {S U : Ty s}
    (h : Inv Γ x (.typ A S U)) :
    ∃ T, Precise Γ x (.typ A T T) ∧ TSub Γ S T ∧ TSub Γ T U := by
  generalize e : Ty.typ A S U = V at h
  induction h generalizing S U with
  | prec hp =>
      subst e
      cases hp.typ_tight hΓ
      exact ⟨_, hp, .refl, .refl⟩
  | typ _ hT hU ih =>
      cases e
      obtain ⟨T0, hp, h1, h2⟩ := ih rfl
      exact ⟨T0, hp, .trans hT h1, .trans h2 hU⟩
  | _ => cases e

theorem Inv.fld_inv {Γ : Ctx s} (_hΓ : Γ.Inert) {x : BVar s .var} {a : Label} {T : Ty s}
    (h : Inv Γ x (.fld a T)) :
    ∃ T0, Precise Γ x (.fld a T0) ∧ TSub Γ T0 T := by
  generalize e : Ty.fld a T = V at h
  induction h generalizing T with
  | prec hp =>
      subst e
      exact ⟨_, hp, .refl⟩
  | fld _ hT ih =>
      cases e
      obtain ⟨T0, hp, h1⟩ := ih rfl
      exact ⟨T0, hp, .trans h1 hT⟩
  | _ => cases e

theorem Inv.all_inv {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {S : Ty s} {T : Ty (s,x)}
    (h : Inv Γ x (.all S T)) :
    ∃ S0 T0, Γ.lookup x = .all S0 T0 ∧ AllSub Γ S0 T0 S T := by
  generalize e : Ty.all S T = V at h
  induction h generalizing S T with
  | prec hp =>
      subst e
      exact ⟨_, _, hp.all_inv hΓ, .refl⟩
  | all _ hS hT ih =>
      cases e
      obtain ⟨S0, T0, hl, hc⟩ := ih rfl
      exact ⟨S0, T0, hl, .step hc hS hT⟩
  | _ => cases e

/-- The bounds of a tight type declaration of a variable bound its selection. -/
theorem TTy.sel_bounds {Γ : Ctx s} (hΓ : Γ.Inert) {x : BVar s .var} {A : Label} {S U : Ty s}
    (h : TTy Γ x (.typ A S U)) : TSub Γ S (.sel x A) ∧ TSub Γ (.sel x A) U := by
  obtain ⟨T, hp, h1, h2⟩ := (h.inv hΓ).typ_inv hΓ
  exact ⟨.trans h1 (.selL hp), .trans (.selU hp) h2⟩

/-! ## General to tight -/

mutual

/-- Path typing in an inert context is tight typing of the root. -/
theorem PathTy.tight {Γ : Ctx s} (hΓ : Γ.Inert) :
    ∀ {p : Path s} {T : Ty s}, PathTy Γ p T → TTy Γ p.root T
  | _, _, .var => .var
  | _, _, .cast hp hc =>
      have ih := PathTy.tight hΓ hp
      .sub ih (CertTy.tight hΓ hc)
  | _, _, .keep _ _ hp =>
      have ih := PathTy.tight hΓ hp
      ih
  | _, _, .recI hp => .recI (PathTy.tight hΓ hp)
  | _, _, .recE hp => .recE (PathTy.tight hΓ hp)
  | _, _, .andI h1 h2 => .andI (PathTy.tight hΓ h1) (PathTy.tight hΓ h2)

/-- Primitive subtyping in an inert context is tight between the erasures. -/
theorem Prim.tight {Γ : Ctx s} (hΓ : Γ.Inert) :
    ∀ {S T : ATy s}, Prim Γ S T → TSub Γ S.erase T.erase
  | _, _, .top _ => .top
  | _, _, .bot _ => .bot
  | _, _, .refl _ _ e => e ▸ .refl
  | _, _, .andL1 h _ => .trans .and1 (Prim.tight hΓ h)
  | _, _, .andL2 _ h => .trans .and2 (Prim.tight hΓ h)
  | _, _, .andR h1 h2 => .and (Prim.tight hΓ h1) (Prim.tight hΓ h2)
  | _, _, .fld h => .fld (Prim.tight hΓ h)
  | _, _, .typ h1 h2 => .typ (Prim.tight hΓ h1) (Prim.tight hΓ h2)
  | _, _, .all h1 h2 => .all (Prim.tight hΓ h1) ⟨.step _ _, .step h2⟩
  | _, _, .selU hp _ e => e ▸ (TTy.sel_bounds hΓ (PathTy.tight hΓ hp)).2
  | _, _, .selL hp _ e => e ▸ (TTy.sel_bounds hΓ (PathTy.tight hΓ hp)).1

/-- A certificate in an inert context is a tight subtyping. -/
theorem CertTy.tight {Γ : Ctx s} (hΓ : Γ.Inert) :
    ∀ {c : Cert s} {S T : Ty s}, CertTy Γ c S T → TSub Γ S T
  | _, _, _, .step h => Prim.tight hΓ h
  | _, _, _, .seq h1 h2 => .trans (CertTy.tight hΓ h1) (CertTy.tight hΓ h2)

end

/-- General subtyping in an inert context is tight. -/
theorem GSub.tight {Γ : Ctx s} (hΓ : Γ.Inert) {S T : Ty s} (h : GSub Γ S T) : TSub Γ S T :=
  let ⟨_, hc⟩ := h; hc.tight hΓ

/-! ## Inversion of path typing -/

theorem PathTy.inv {Γ : Ctx s} (hΓ : Γ.Inert) {p : Path s} {T : Ty s}
    (h : PathTy Γ p T) : Inv Γ p.root T :=
  (h.tight hΓ).inv hΓ

theorem PathTy.fun_inv {Γ : Ctx s} (hΓ : Γ.Inert) {p : Path s} {S : Ty s} {T : Ty (s,x)}
    (h : PathTy Γ p (.all S T)) :
    ∃ S0 T0, Γ.lookup p.root = .all S0 T0 ∧ AllSub Γ S0 T0 S T :=
  (h.inv hΓ).all_inv hΓ

theorem PathTy.fld_inv {Γ : Ctx s} (hΓ : Γ.Inert) {p : Path s} {a : Label} {T : Ty s}
    (h : PathTy Γ p (.fld a T)) :
    ∃ T0, Precise Γ p.root (.fld a T0) ∧ TSub Γ T0 T :=
  (h.inv hΓ).fld_inv hΓ

theorem PathTy.typ_inv {Γ : Ctx s} (hΓ : Γ.Inert) {p : Path s} {A : Label} {S U : Ty s}
    (h : PathTy Γ p (.typ A S U)) :
    ∃ T, Precise Γ p.root (.typ A T T) ∧ TSub Γ S T ∧ TSub Γ T U :=
  (h.inv hΓ).typ_inv hΓ

end SelDot
