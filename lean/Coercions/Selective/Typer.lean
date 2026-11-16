import Coercions.Selective.Check

/-!
# The term checker: sound and complete, no search

`synthTm Γ t` is the finite list of types `T` with `HTy Γ t T`
(`synthTm_iff`), computed by structural recursion on the term.  Terms
synthesise a *set* of types because field lookup `FExp` may choose among
several fields with one label; every other former is deterministic.

* Atoms and certificates go to the evidence checker (`synthA`, `synthC`).
* The two implicit `≤₀` steps (application argument, cast subject) call the
  decision procedure `prim?` on a synthesised source and a written target.
* `let` strengthens each type of the body out of the bound variable's scope
  by `Ty.unweaken?` (`Ty.unweaken?_spec`); the body's type must be a
  weakening, as in DOT-MNF.
* An object literal `ν(x : T) d` is checked against its annotation `T`;
  distinctness of its labels is decided by `Defs.distinct?`
  (`Defs.distinct?_iff`).
* Field lookup enumerates `fexps x V a`, all fields `a` exposed by `V` at
  `x`, with fuel `sz V`, which suffices because unfolding `μ` at a variable
  preserves size (`sz_substVar`, `fexps_iff`).
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Strengthening of types -/

/-- A partial renaming of term variables: the inverse of a renaming,
undefined off its image. -/
structure PRename (s1 s2 : Sig) where
  var : BVar s1 .var → Option (BVar s2 .var)

/-- Lift under one term binder: the new binder maps to itself. -/
def PRename.lift {s1 s2 : Sig} (f : PRename s1 s2) : PRename (s1,x) (s2,x) where
  var := fun
    | .here => some .here
    | .there x => (f.var x).map .there

/-- The inverse of weakening: undefined at the newest binder. -/
def PRename.unsucc {s : Sig} : PRename (s,x) s where
  var := fun
    | .here => none
    | .there x => some x

/-- `f` inverts `ρ`: it is defined exactly on the image of `ρ`, and there it
returns the preimage. -/
def PRename.Inverts {s1 s2 : Sig} (f : PRename s1 s2) (ρ : Rename s2 s1) : Prop :=
  ∀ (x : BVar s1 .var) (y : BVar s2 .var), f.var x = some y ↔ ρ.var y = x

theorem PRename.Inverts.lift {s1 s2 : Sig} {f : PRename s1 s2} {ρ : Rename s2 s1}
    (h : f.Inverts ρ) : f.lift.Inverts (ρ.lift (k := .var)) := by
  intro x y
  cases x with
  | here =>
      cases y with
      | here => simp [PRename.lift]
      | there y => simp [PRename.lift]
  | there x =>
      cases y with
      | here => simp [PRename.lift]
      | there y =>
          simp only [PRename.lift, Rename.lift_there, Option.map_eq_some_iff, BVar.there.injEq]
          constructor
          · rintro ⟨z, hz, rfl⟩; exact (h x z).mp hz
          · intro hy; exact ⟨y, (h x y).mpr hy, rfl⟩

theorem PRename.unsucc_inverts {s : Sig} :
    (PRename.unsucc : PRename (s,x) s).Inverts (Rename.succ (k := .var)) := by
  intro x y
  cases x with
  | here => simp [PRename.unsucc]
  | there x =>
      simp only [PRename.unsucc, Rename.succ_var, Option.some.injEq, BVar.there.injEq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Strengthening along a partial renaming. -/
def _root_.DotMNF.Ty.unrename {s1 s2 : Sig} : Ty s1 → PRename s1 s2 → Option (Ty s2)
  | .top, _ => some .top
  | .bot, _ => some .bot
  | .typ A L U, f =>
      match L.unrename f, U.unrename f with
      | some L', some U' => some (.typ A L' U')
      | _, _ => none
  | .fld a T, f => (T.unrename f).map (.fld a)
  | .sel (.var x) A, f => (f.var x).map (fun y => .sel (.var y) A)
  | .mu T, f => (T.unrename f.lift).map .mu
  | .all S T, f =>
      match S.unrename f, T.unrename f.lift with
      | some S', some T' => some (.all S' T')
      | _, _ => none
  | .and S T, f =>
      match S.unrename f, T.unrename f with
      | some S', some T' => some (.and S' T')
      | _, _ => none

theorem _root_.DotMNF.Ty.unrename_rename {s2 : Sig} (U : Ty s2) :
    ∀ {s1 : Sig} (ρ : Rename s2 s1) (f : PRename s1 s2), f.Inverts ρ →
    (U.rename ρ).unrename f = some U := by
  induction U with
  | top | bot => intro _ _ _ _; rfl
  | typ A L U ih1 ih2 =>
      intro _ ρ f h; simp [DotMNF.Ty.rename, DotMNF.Ty.unrename, ih1 ρ f h, ih2 ρ f h]
  | fld a T ih => intro _ ρ f h; simp [DotMNF.Ty.rename, DotMNF.Ty.unrename, ih ρ f h]
  | sel p A =>
      intro _ ρ f h
      cases p with
      | var y =>
          simp only [DotMNF.Ty.rename, DotMNF.Path.rename, DotMNF.Ty.unrename]
          rw [(h (ρ.var y) y).mpr rfl]; rfl
  | mu T ih => intro _ ρ f h; simp [DotMNF.Ty.rename, DotMNF.Ty.unrename, ih ρ.lift f.lift h.lift]
  | all S T ih1 ih2 =>
      intro _ ρ f h; simp [DotMNF.Ty.rename, DotMNF.Ty.unrename, ih1 ρ f h, ih2 ρ.lift f.lift h.lift]
  | and S T ih1 ih2 =>
      intro _ ρ f h; simp [DotMNF.Ty.rename, DotMNF.Ty.unrename, ih1 ρ f h, ih2 ρ f h]

theorem _root_.DotMNF.Ty.rename_of_unrename {s1 : Sig} (T : Ty s1) :
    ∀ {s2 : Sig} (ρ : Rename s2 s1) (f : PRename s1 s2), f.Inverts ρ →
    ∀ {U : Ty s2}, T.unrename f = some U → U.rename ρ = T := by
  induction T with
  | top => intro _ _ _ _ U h; cases h; rfl
  | bot => intro _ _ _ _ U h; cases h; rfl
  | typ A L U ih1 ih2 =>
      intro _ ρ f hf V h
      simp only [DotMNF.Ty.unrename] at h
      cases h1 : L.unrename f <;> cases h2 : U.unrename f <;> rw [h1, h2] at h <;> try cases h
      simp [DotMNF.Ty.rename, ih1 ρ f hf h1, ih2 ρ f hf h2]
  | fld a T ih =>
      intro _ ρ f hf V h
      simp only [DotMNF.Ty.unrename, Option.map_eq_some_iff] at h
      obtain ⟨T', h1, rfl⟩ := h
      simp [DotMNF.Ty.rename, ih ρ f hf h1]
  | sel p A =>
      intro _ ρ f hf V h
      cases p with
      | var x =>
          simp only [DotMNF.Ty.unrename, Option.map_eq_some_iff] at h
          obtain ⟨y, hy, rfl⟩ := h
          simp [DotMNF.Ty.rename, DotMNF.Path.rename, (hf x y).mp hy]
  | mu T ih =>
      intro _ ρ f hf V h
      simp only [DotMNF.Ty.unrename, Option.map_eq_some_iff] at h
      obtain ⟨T', h1, rfl⟩ := h
      simp [DotMNF.Ty.rename, ih ρ.lift f.lift hf.lift h1]
  | all S T ih1 ih2 =>
      intro _ ρ f hf V h
      simp only [DotMNF.Ty.unrename] at h
      cases h1 : S.unrename f <;> cases h2 : T.unrename f.lift <;> rw [h1, h2] at h <;> try cases h
      simp [DotMNF.Ty.rename, ih1 ρ f hf h1, ih2 ρ.lift f.lift hf.lift h2]
  | and S T ih1 ih2 =>
      intro _ ρ f hf V h
      simp only [DotMNF.Ty.unrename] at h
      cases h1 : S.unrename f <;> cases h2 : T.unrename f <;> rw [h1, h2] at h <;> try cases h
      simp [DotMNF.Ty.rename, ih1 ρ f hf h1, ih2 ρ f hf h2]

theorem _root_.DotMNF.Ty.unrename_iff {s1 s2 : Sig} {ρ : Rename s2 s1} {f : PRename s1 s2} (hf : f.Inverts ρ)
    {T : Ty s1} {U : Ty s2} : T.unrename f = some U ↔ U.rename ρ = T :=
  ⟨DotMNF.Ty.rename_of_unrename T ρ f hf, fun h => h ▸ DotMNF.Ty.unrename_rename U ρ f hf⟩

/-- Strengthening out of the newest binder: the inverse of `Ty.weaken`. -/
def _root_.DotMNF.Ty.unweaken? {s : Sig} (U' : Ty (s,x)) : Option (Ty s) := U'.unrename PRename.unsucc

theorem _root_.DotMNF.Ty.unweaken?_spec {s : Sig} {U : Ty s} {U' : Ty (s,x)} :
    U'.unweaken? = some U ↔ U.weaken = U' :=
  DotMNF.Ty.unrename_iff PRename.unsucc_inverts

/-! ## Distinct labels -/

def _root_.DotMNF.Defs.distinct? {s : Sig} : DotMNF.Defs s → Bool
  | .typ _ _ => true
  | .trm _ _ => true
  | .and d1 d2 => d1.distinct? && d2.distinct? && d1.labels.all (fun ℓ => decide (ℓ ∉ d2.labels))

theorem _root_.DotMNF.Defs.distinct?_iff {s : Sig} : {d : DotMNF.Defs s} → d.distinct? = true ↔ d.Distinct
  | .typ _ _ => ⟨fun _ => .typ, fun _ => rfl⟩
  | .trm _ _ => ⟨fun _ => .trm, fun _ => rfl⟩
  | .and d1 d2 => by
      simp only [DotMNF.Defs.distinct?, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      rw [DotMNF.Defs.distinct?_iff, DotMNF.Defs.distinct?_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact .and h1 h2 h3
      · intro h; cases h with | and h1 h2 h3 => exact ⟨⟨h1, h2⟩, h3⟩

/-! ## Field lookup -/

/-- The fields with label `a` exposed by `V` at `x`, within fuel `n`. -/
def fexpN {s : Sig} (x : BVar s .var) : Nat → Ty s → Label → List (Ty s)
  | 0, _, _ => []
  | _ + 1, .fld b T, a => if b = a then [T] else []
  | n + 1, .and S U, a => fexpN x n S a ++ fexpN x n U a
  | n + 1, .mu T, a => fexpN x n (T.substVar x) a
  | _ + 1, _, _ => []

/-- All fields with label `a` exposed by `V` at `x`. -/
def fexps {s : Sig} (x : BVar s .var) (V : Ty s) (a : Label) : List (Ty s) := fexpN x (sz V) V a

theorem fexpN_sound {s : Sig} (x : BVar s .var) :
    ∀ (n : Nat) (V : Ty s) (a : Label) (T : Ty s), T ∈ fexpN x n V a → FExp x V a T
  | 0, _, _, _, h => by simp [fexpN] at h
  | n + 1, .fld b T', a, T, h => by
      simp only [fexpN] at h
      split at h
      · rename_i hab; subst hab; simp at h; subst h; exact .fld
      · simp at h
  | n + 1, .and S U, a, T, h => by
      simp only [fexpN, List.mem_append] at h
      rcases h with h | h
      · exact .andL (fexpN_sound x n S a T h)
      · exact .andR (fexpN_sound x n U a T h)
  | n + 1, .mu T', a, T, h => by
      simp only [fexpN] at h; exact .mu (fexpN_sound x n _ a T h)
  | n + 1, .top, _, _, h | n + 1, .bot, _, _, h | n + 1, .typ _ _ _, _, _, h
  | n + 1, .sel _ _, _, _, h | n + 1, .all _ _, _, _, h => by simp [fexpN] at h

theorem fexpN_complete {s : Sig} {x : BVar s .var} {V : Ty s} {a : Label} {T : Ty s}
    (h : FExp x V a T) : ∀ n, sz V ≤ n → T ∈ fexpN x n V a := by
  induction h with
  | fld =>
      intro n hn; cases n with
      | zero => simp [sz] at hn
      | succ n => simp [fexpN]
  | andL _ ih =>
      intro n hn; cases n with
      | zero => simp [sz] at hn
      | succ n => simp only [sz] at hn; simp only [fexpN, List.mem_append]; exact .inl (ih n (by omega))
  | andR _ ih =>
      intro n hn; cases n with
      | zero => simp [sz] at hn
      | succ n => simp only [sz] at hn; simp only [fexpN, List.mem_append]; exact .inr (ih n (by omega))
  | mu _ ih =>
      intro n hn; cases n with
      | zero => simp [sz] at hn
      | succ n =>
          simp only [sz] at hn; simp only [fexpN]
          exact ih n (by rw [sz_substVar]; omega)

theorem fexps_iff {s : Sig} {x : BVar s .var} {V : Ty s} {a : Label} {T : Ty s} :
    T ∈ fexps x V a ↔ FExp x V a T :=
  ⟨fexpN_sound x _ V a T, fun h => fexpN_complete h _ (Nat.le_refl _)⟩

/-! ## The checker -/

mutual
def synthTm {s : Sig} (Γ : Ctx s) : HTm s → List (Ty s)
  | .atom a => (synthA Γ a).toList
  | .val v => synthVal Γ v
  | .app a b =>
      match synthA Γ a, synthA Γ b with
      | some (.all S T), some V => if prim? Γ V S then [T.substVar b.root] else []
      | _, _ => []
  | .proj a ℓ =>
      match synthA Γ a with
      | some V => fexps a.root V ℓ
      | none => []
  | .let t u => (synthTm Γ t).flatMap (fun T => (synthTm (Γ.cons T) u).filterMap Ty.unweaken?)
  | .cast t c =>
      match synthC Γ c with
      | some (S, T) => if (synthTm Γ t).any (fun S0 => prim? Γ S0 S) then [T] else []
      | none => []
def synthVal {s : Sig} (Γ : Ctx s) : HVal s → List (Ty s)
  | .lam S t => (synthTm (Γ.cons S) t).map (.all S)
  | .obj T d =>
      if decide (T ∈ synthDefs (Γ.consSelf d.erase T) d) && d.erase.distinct? then [.mu T]
      else []
def synthDefs {s : Sig} (Γ : Ctx s) : HDefs s → List (Ty s)
  | .typ A T => [.typ A T T]
  | .trm a t => (synthTm Γ t).map (.fld a)
  | .and d1 d2 => (synthDefs Γ d1).flatMap (fun T1 => (synthDefs Γ d2).map (.and T1))
end

/-! ### Soundness -/

mutual
theorem synthTm_sound {s : Sig} {Γ : Ctx s} : (t : HTm s) → {T : Ty s} → T ∈ synthTm Γ t → HTy Γ t T
  | .atom a, T, h => by
      simp only [synthTm, Option.mem_toList] at h; exact .atom (synthA_sound a h)
  | .val v, T, h => by simp only [synthTm] at h; exact synthVal_sound v h
  | .app a b, T, h => by
      simp only [synthTm] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some F =>
        cases hb : synthA Γ b with
        | none => cases F <;> simp [ha, hb] at h
        | some V =>
          cases F with
          | all S T' =>
              simp only [ha, hb] at h
              split at h
              · rename_i hp; simp at h; subst h
                exact .app (synthA_sound a ha) (synthA_sound b hb) (prim?_sound hp)
              · simp at h
          | _ => simp [ha, hb] at h
  | .proj a ℓ, T, h => by
      simp only [synthTm] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some V =>
        simp only [ha] at h
        exact .proj (synthA_sound a ha) (fexps_iff.mp h)
  | .let t u, U, h => by
      simp only [synthTm, List.mem_flatMap, List.mem_filterMap] at h
      obtain ⟨T, hT, U', hU', he⟩ := h
      have hw := DotMNF.Ty.unweaken?_spec.mp he
      subst hw
      exact .let (synthTm_sound t hT) (synthTm_sound u hU')
  | .cast t c, T, h => by
      simp only [synthTm] at h
      cases hc : synthC Γ c with
      | none => simp [hc] at h
      | some p =>
        obtain ⟨S, T'⟩ := p
        simp only [hc] at h
        split at h
        · rename_i hany
          simp at h; subst h
          obtain ⟨S0, hS0, hp⟩ := List.any_eq_true.mp hany
          exact .cast (synthTm_sound t hS0) (prim?_sound hp) (synthC_sound c hc)
        · simp at h
theorem synthVal_sound {s : Sig} {Γ : Ctx s} : (v : HVal s) → {T : Ty s} →
    T ∈ synthVal Γ v → HTy Γ (.val v) T
  | .lam S t, T, h => by
      simp only [synthVal, List.mem_map] at h
      obtain ⟨T', hT', rfl⟩ := h
      exact .lam (synthTm_sound t hT')
  | .obj T' d, T, h => by
      simp only [synthVal] at h
      split at h
      · rename_i hc
        simp at h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact .obj (synthDefs_sound d hc.1) (DotMNF.Defs.distinct?_iff.mp hc.2)
      · simp at h
theorem synthDefs_sound {s : Sig} {Γ : Ctx s} : (d : HDefs s) → {T : Ty s} →
    T ∈ synthDefs Γ d → HDefsTy Γ d T
  | .typ A T', T, h => by simp only [synthDefs, List.mem_singleton] at h; subst h; exact .typ
  | .trm a t, T, h => by
      simp only [synthDefs, List.mem_map] at h
      obtain ⟨T', hT', rfl⟩ := h
      exact .trm (synthTm_sound t hT')
  | .and d1 d2, T, h => by
      simp only [synthDefs, List.mem_flatMap, List.mem_map] at h
      obtain ⟨T1, h1, T2, h2, rfl⟩ := h
      exact .and (synthDefs_sound d1 h1) (synthDefs_sound d2 h2)
end

/-! ### Completeness -/

mutual
theorem synthTm_complete {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} :
    HTy Γ t T → T ∈ synthTm Γ t
  | .atom h => by simp [synthTm, synthA_complete h]
  | .lam h => by
      simp only [synthTm, synthVal, List.mem_map]
      exact ⟨_, synthTm_complete h, rfl⟩
  | .app ha hb hp => by simp [synthTm, synthA_complete ha, synthA_complete hb, prim?_complete hp]
  | .obj hd hdist => by
      have h1 := synthDefs_complete hd
      have h2 := DotMNF.Defs.distinct?_iff.mpr hdist
      simp [synthTm, synthVal, h1, h2]
  | .proj ha hf => by
      simp only [synthTm, synthA_complete ha]
      exact fexps_iff.mpr hf
  | .let h1 h2 => by
      simp only [synthTm, List.mem_flatMap, List.mem_filterMap]
      exact ⟨_, synthTm_complete h1, _, synthTm_complete h2, DotMNF.Ty.unweaken?_spec.mpr rfl⟩
  | .cast ht hp hc => by
      simp only [synthTm, synthC_complete hc]
      have : (synthTm Γ _).any (fun S0 => prim? Γ S0 _) = true :=
        List.any_eq_true.mpr ⟨_, synthTm_complete ht, prim?_complete hp⟩
      simp [this]
theorem synthDefs_complete {s : Sig} {Γ : Ctx s} {d : HDefs s} {T : Ty s} :
    HDefsTy Γ d T → T ∈ synthDefs Γ d
  | .typ => by simp [synthDefs]
  | .trm h => by
      simp only [synthDefs, List.mem_map]
      exact ⟨_, synthTm_complete h, rfl⟩
  | .and h1 h2 => by
      simp only [synthDefs, List.mem_flatMap, List.mem_map]
      exact ⟨_, synthDefs_complete h1, _, synthDefs_complete h2, rfl⟩
end

/-- **Term typing is decided**: the checker lists exactly the types of a term. -/
theorem synthTm_iff {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} :
    T ∈ synthTm Γ t ↔ HTy Γ t T := ⟨synthTm_sound t, synthTm_complete⟩

theorem synthDefs_iff {s : Sig} {Γ : Ctx s} {d : HDefs s} {T : Ty s} :
    T ∈ synthDefs Γ d ↔ HDefsTy Γ d T := ⟨synthDefs_sound d, synthDefs_complete⟩

instance HTy.decidable {s : Sig} (Γ : Ctx s) (t : HTm s) (T : Ty s) : Decidable (HTy Γ t T) :=
  decidable_of_iff _ synthTm_iff

/-- A computed empty list of types: the term has no type. -/
theorem untypable_of_synthTm {s : Sig} {Γ : Ctx s} {t : HTm s} (h : synthTm Γ t = []) :
    ∀ T, ¬ HTy Γ t T := fun T hT => by
  have := synthTm_iff.mpr hT; rw [h] at this; cases this

end Selective
