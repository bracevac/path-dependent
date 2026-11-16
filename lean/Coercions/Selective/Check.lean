import Coercions.Selective.Typing

/-!
# The evidence checker: structural synthesis, no fuel, no search

`synthA`, `synthC` and `synthP` recurse on the stored evidence.  `seq`
compares the middle type by `=`, `cast` compares the atom's type with the
certificate's source, a leaf checks that the receiver's type exposes the
member at the receiver's root (`memU`, `memL`), and `step` calls the decision
procedure `prim?`.  The checker is sound and complete for the judgments
(`synthA_iff`, `synthC_iff`, `synthP_iff`, `checkC_iff`), so atoms and
certificates determine their types (`ATy.unique`, `CTy.endpoints_unique`).
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

def memU {s : Sig} (x : BVar s .var) (R : Ty s) (A : Label) (U : Ty s) : Bool :=
  (members x R).any (fun m => decide (m.1 = A) && decide (m.2.2 = U))

def memL {s : Sig} (x : BVar s .var) (R : Ty s) (A : Label) (L : Ty s) : Bool :=
  (members x R).any (fun m => decide (m.1 = A) && decide (m.2.1 = L))

theorem memU_iff {s : Sig} {x : BVar s .var} {R : Ty s} {A : Label} {U : Ty s} :
    memU x R A U = true ↔ ∃ L, Exp x R A L U := by
  simp only [memU, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨B, L, U'⟩, hm, rfl, rfl⟩; exact ⟨L, (exp_iff_members _ _ _ _ _).mpr hm⟩
  · rintro ⟨L, he⟩; exact ⟨⟨A, L, U⟩, (exp_iff_members _ _ _ _ _).mp he, rfl, rfl⟩

theorem memL_iff {s : Sig} {x : BVar s .var} {R : Ty s} {A : Label} {L : Ty s} :
    memL x R A L = true ↔ ∃ U, Exp x R A L U := by
  simp only [memL, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨B, L', U⟩, hm, rfl, rfl⟩; exact ⟨U, (exp_iff_members _ _ _ _ _).mpr hm⟩
  · rintro ⟨U, he⟩; exact ⟨⟨A, L, U⟩, (exp_iff_members _ _ _ _ _).mp he, rfl, rfl⟩

mutual
def synthA {s : Sig} (Γ : Ctx s) : Atom s → Option (Ty s)
  | .var x => some (Γ.lookup x)
  | .cast a c =>
      match synthA Γ a, synthC Γ c with
      | some S, some (S', T) => if S = S' then some T else none
      | _, _ => none
  | .unfold a =>
      match synthA Γ a with
      | some (.mu T) => some (T.substVar a.root)
      | _ => none
  | .fold T a =>
      match synthA Γ a with
      | some S => if S = T.substVar a.root then some (.mu T) else none
      | none => none
  | .both a b =>
      match synthA Γ a, synthA Γ b with
      | some S, some T => if a.root = b.root then some (.and S T) else none
      | _, _ => none
def synthC {s : Sig} (Γ : Ctx s) : Cert s → Option (Ty s × Ty s)
  | .step S T => if prim? Γ S T then some (S, T) else none
  | .seq c d =>
      match synthC Γ c, synthC Γ d with
      | some (S, M), some (M', T) => if M = M' then some (S, T) else none
      | _, _ => none
  | .pos k => synthP Γ k
def synthP {s : Sig} (Γ : Ctx s) : Pos s → Option (Ty s × Ty s)
  | .selU a A U =>
      match synthA Γ a with
      | some R => if memU a.root R A U then some (.sel (.var a.root) A, U) else none
      | none => none
  | .selL a A L =>
      match synthA Γ a with
      | some R => if memL a.root R A L then some (L, .sel (.var a.root) A) else none
      | none => none
  | .fld ℓ k => (synthP Γ k).map (fun p => (.fld ℓ p.1, .fld ℓ p.2))
  | .typL A k U => (synthP Γ k).map (fun p => (.typ A p.2 U, .typ A p.1 U))
  | .typU A L k => (synthP Γ k).map (fun p => (.typ A L p.1, .typ A L p.2))
  | .allD k T => (synthP Γ k).map (fun p => (.all p.2 T, .all p.1 T))
  | .allC S k => (synthP (Γ.cons S) k).map (fun p => (.all S p.1, .all S p.2))
  | .andL k U => (synthP Γ k).map (fun p => (.and p.1 U, .and p.2 U))
  | .andR U k => (synthP Γ k).map (fun p => (.and U p.1, .and U p.2))
end

/-! ### Completeness -/

mutual
theorem synthA_complete {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    ATy Γ a T → synthA Γ a = some T
  | .var => by simp [synthA]
  | .cast ha hc => by simp [synthA, synthA_complete ha, synthC_complete hc]
  | .unfold ha => by simp [synthA, synthA_complete ha]
  | .fold ha => by simp [synthA, synthA_complete ha]
  | .both ha hb hr => by simp [synthA, synthA_complete ha, synthA_complete hb, hr]
theorem synthC_complete {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    CTy Γ c S T → synthC Γ c = some (S, T)
  | .step p => by simp [synthC, prim?_complete p]
  | .seq h1 h2 => by simp [synthC, synthC_complete h1, synthC_complete h2]
  | .pos h => by simp [synthC, synthP_complete h]
theorem synthP_complete {s : Sig} {Γ : Ctx s} {k : Pos s} {S T : Ty s} :
    PTy Γ k S T → synthP Γ k = some (S, T)
  | .selU ha he => by
      have hm : memU _ _ _ _ = true := memU_iff.mpr ⟨_, he⟩
      simp [synthP, synthA_complete ha, hm]
  | .selL ha he => by
      have hm : memL _ _ _ _ = true := memL_iff.mpr ⟨_, he⟩
      simp [synthP, synthA_complete ha, hm]
  | .fld h => by simp [synthP, synthP_complete h]
  | .typL h => by simp [synthP, synthP_complete h]
  | .typU h => by simp [synthP, synthP_complete h]
  | .allD h => by simp [synthP, synthP_complete h]
  | .allC h => by simp [synthP, synthP_complete h]
  | .andL h => by simp [synthP, synthP_complete h]
  | .andR h => by simp [synthP, synthP_complete h]
end

/-! ### Soundness -/

mutual
theorem synthA_sound {s : Sig} {Γ : Ctx s} :
    (a : Atom s) → {T : Ty s} → synthA Γ a = some T → ATy Γ a T
  | .var x, T, h => by
      simp only [synthA, Option.some.injEq] at h; subst h; exact .var
  | .cast a c, T, h => by
      simp only [synthA] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some S =>
        cases hc : synthC Γ c with
        | none => simp [ha, hc] at h
        | some p =>
          obtain ⟨S', T'⟩ := p
          simp only [ha, hc] at h
          split at h
          · rename_i hS; subst hS; cases h
            exact .cast (synthA_sound a ha) (synthC_sound c hc)
          · cases h
  | .unfold a, T, h => by
      simp only [synthA] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some S =>
        rw [ha] at h
        cases S with
        | mu T' => simp only [Option.some.injEq] at h; subst h; exact .unfold (synthA_sound a ha)
        | _ => simp at h
  | .fold T' a, T, h => by
      simp only [synthA] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some S =>
        simp only [ha] at h
        split at h
        · rename_i hS; subst hS; cases h; exact .fold (synthA_sound a ha)
        · cases h
  | .both a b, T, h => by
      simp only [synthA] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some S =>
        cases hb : synthA Γ b with
        | none => simp [ha, hb] at h
        | some U =>
          simp only [ha, hb] at h
          split at h
          · rename_i hr; cases h
            exact .both (synthA_sound a ha) (synthA_sound b hb) hr
          · cases h
theorem synthC_sound {s : Sig} {Γ : Ctx s} :
    (c : Cert s) → {S T : Ty s} → synthC Γ c = some (S, T) → CTy Γ c S T
  | .step S' T', S, T, h => by
      simp only [synthC] at h
      split at h
      · rename_i hp; cases h; exact .step (prim?_sound hp)
      · cases h
  | .seq c d, S, T, h => by
      simp only [synthC] at h
      cases hc : synthC Γ c with
      | none => simp [hc] at h
      | some p =>
        obtain ⟨S1, M⟩ := p
        cases hd : synthC Γ d with
        | none => simp [hc, hd] at h
        | some q =>
          obtain ⟨M', T1⟩ := q
          simp only [hc, hd] at h
          split at h
          · rename_i hM; subst hM
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .seq (synthC_sound c hc) (synthC_sound d hd)
          · cases h
  | .pos k, S, T, h => by
      simp only [synthC] at h; exact .pos (synthP_sound k h)
theorem synthP_sound {s : Sig} {Γ : Ctx s} :
    (k : Pos s) → {S T : Ty s} → synthP Γ k = some (S, T) → PTy Γ k S T
  | .selU a A U, S, T, h => by
      simp only [synthP] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some R =>
        simp only [ha] at h
        split at h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨L, he⟩ := memU_iff.mp hm
          exact .selU (synthA_sound a ha) he
        · cases h
  | .selL a A L, S, T, h => by
      simp only [synthP] at h
      cases ha : synthA Γ a with
      | none => simp [ha] at h
      | some R =>
        simp only [ha] at h
        split at h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨U, he⟩ := memL_iff.mp hm
          exact .selL (synthA_sound a ha) he
        · cases h
  | .fld ℓ k, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .fld (synthP_sound k hk)
  | .typL A k U, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .typL (synthP_sound k hk)
  | .typU A L k, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .typU (synthP_sound k hk)
  | .allD k T', S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .allD (synthP_sound k hk)
  | .allC S' k, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .allC (synthP_sound k hk)
  | .andL k U, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .andL (synthP_sound k hk)
  | .andR U k, S, T, h => by
      simp only [synthP, Option.map_eq_some_iff] at h
      obtain ⟨⟨S1, T1⟩, hk, he⟩ := h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .andR (synthP_sound k hk)
end

theorem synthA_iff {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    synthA Γ a = some T ↔ ATy Γ a T := ⟨synthA_sound a, synthA_complete⟩
theorem synthC_iff {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    synthC Γ c = some (S, T) ↔ CTy Γ c S T := ⟨synthC_sound c, synthC_complete⟩
theorem synthP_iff {s : Sig} {Γ : Ctx s} {k : Pos s} {S T : Ty s} :
    synthP Γ k = some (S, T) ↔ PTy Γ k S T := ⟨synthP_sound k, synthP_complete⟩

def checkC {s : Sig} (Γ : Ctx s) (c : Cert s) (S T : Ty s) : Bool := decide (synthC Γ c = some (S, T))

theorem checkC_iff {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    checkC Γ c S T = true ↔ CTy Γ c S T := by simp [checkC, synthC_iff]

/-- Endpoints of a certificate are determined by the certificate. -/
theorem CTy.endpoints_unique {s : Sig} {Γ : Ctx s} {c : Cert s} {S T S' T' : Ty s}
    (h : CTy Γ c S T) (h' : CTy Γ c S' T') : S = S' ∧ T = T' := by
  have e1 := synthC_complete h; have e2 := synthC_complete h'
  rw [e1] at e2; simp only [Option.some.injEq, Prod.mk.injEq] at e2; exact e2

/-- Atoms synthesise a unique type. -/
theorem ATy.unique {s : Sig} {Γ : Ctx s} {a : Atom s} {T T' : Ty s}
    (h : ATy Γ a T) (h' : ATy Γ a T') : T = T' := by
  have e1 := synthA_complete h; have e2 := synthA_complete h'
  rw [e1] at e2; exact Option.some.inj e2

end Selective
