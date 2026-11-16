import Coercions.Selective.Fsub.Term
/-!
# Typing of annotated terms

`HTy Γ Δ t T` types `t` in the type context `Γ` and the term context `Δ` (a list, index
`0` the innermost term variable). There is no subsumption rule. A primitive step `≤₀` is
checked implicitly at exactly two positions: the argument of an application (`V ≤₀ S`
against the callee's domain) and the argument of a type application (`U ≤₀ S` against
the callee's bound). A cast `t ▷ c` requires the type of `t` to be exactly the source of
`c`. Anything beyond one primitive step is written: a cast on the argument, or a cast on
the callee (a bound change is a certificate between universal types). The callee of an
application must have an arrow type, and that of a type application a universal type,
syntactically; a variable type is promoted only by a cast.

Types are unique, and `synthTm` decides typing by structural recursion on the term.
-/
namespace SelFsub

inductive HTy : Ctx n → List (Ty n) → Tm n → Ty n → Prop where
  | var : Δ[x]? = some T → HTy Γ Δ (.var x) T
  | lam : HTy Γ (S :: Δ) t T → HTy Γ Δ (.lam S t) (.arr S T)
  | app : HTy Γ Δ t (.arr S T) → HTy Γ Δ u V → Prim Γ V S → HTy Γ Δ (.app t u) T
  | tlam : HTy (Γ.snoc S) (Δ.map Ty.weaken) t T → HTy Γ Δ (.tlam S t) (.all S T)
  | tapp : HTy Γ Δ t (.all S T) → Prim Γ U S → HTy Γ Δ (.tapp t U) (T.subst (sub0 U))
  | cast : HTy Γ Δ t S → CTy Γ c S T → HTy Γ Δ (.cast t c) T

theorem HTy.unique (h : HTy Γ Δ t T) (h' : HTy Γ Δ t T') : T = T' := by
  induction h with
  | var e => cases h' with | var e' => exact Option.some.inj (e.symm.trans e')
  | lam _ ih => cases h' with | lam h' => rw [ih h']
  | app _ _ _ ih => cases h' with | app h₁ _ _ => cases ih h₁; rfl
  | tlam _ ih => cases h' with | tlam h' => rw [ih h']
  | tapp _ _ ih => cases h' with | tapp h₁ _ => cases ih h₁; rfl
  | cast _ hc => cases h' with | cast _ hc' => exact (hc.endpoints_unique hc').2

/-! ## Checker -/

def synthTm (Γ : Ctx n) (Δ : List (Ty n)) : Tm n → Option (Ty n)
  | .var x => Δ[x]?
  | .lam S t => (synthTm Γ (S :: Δ) t).map (.arr S)
  | .app t u =>
    match synthTm Γ Δ t, synthTm Γ Δ u with
    | some (.arr S T), some V => if prim? Γ V S then some T else none
    | _, _ => none
  | .tlam S t => (synthTm (Γ.snoc S) (Δ.map Ty.weaken) t).map (.all S)
  | .tapp t U =>
    match synthTm Γ Δ t with
    | some (.all S T) => if prim? Γ U S then some (T.subst (sub0 U)) else none
    | _ => none
  | .cast t c =>
    match synthTm Γ Δ t, synthC Γ c with
    | some S, some (S', T) => if S = S' then some T else none
    | _, _ => none

theorem synthTm_sound : (t : Tm n) → ∀ {Γ : Ctx n} {Δ T},
    synthTm Γ Δ t = some T → HTy Γ Δ t T
  | .var _, _, _, _, h => .var h
  | .lam _ t, _, _, _, h => by
    simp only [synthTm, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .lam (synthTm_sound t h)
  | .tlam _ t, _, _, _, h => by
    simp only [synthTm, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .tlam (synthTm_sound t h)
  | .app t u, Γ, Δ, _, h => by
    simp only [synthTm] at h; split at h
    · next ht hu => split at h
                    · next hp => cases h; exact .app (synthTm_sound t ht) (synthTm_sound u hu)
                                   (prim?_iff.mp hp)
                    · cases h
    · cases h
  | .tapp t _, Γ, Δ, _, h => by
    simp only [synthTm] at h; split at h
    · next ht => split at h
                 · next hp => cases h; exact .tapp (synthTm_sound t ht) (prim?_iff.mp hp)
                 · cases h
    · cases h
  | .cast t _, Γ, Δ, _, h => by
    simp only [synthTm] at h; split at h
    · next ht hc => split at h
                    · next e => cases h; subst e
                                exact .cast (synthTm_sound t ht) (synthC_iff.mp hc)
                    · cases h
    · cases h

theorem synthTm_complete (h : HTy Γ Δ t T) : synthTm Γ Δ t = some T := by
  induction h with
  | var e => exact e
  | lam _ ih | tlam _ ih => simp only [synthTm, ih, Option.map_some]
  | app _ _ hp ih₁ ih₂ => simp only [synthTm, ih₁, ih₂, prim?_iff.mpr hp, if_true]
  | tapp _ hp ih => simp only [synthTm, ih, prim?_iff.mpr hp, if_true]
  | cast _ hc ih => simp only [synthTm, ih, synthC_iff.mpr hc, if_true]

theorem synthTm_iff : synthTm Γ Δ t = some T ↔ HTy Γ Δ t T :=
  ⟨synthTm_sound t, synthTm_complete⟩

instance : Decidable (HTy Γ Δ t T) := decidable_of_iff _ synthTm_iff

end SelFsub
