import LambdaP.Store

/-!
Big-step path reduction from the development.  Reduction returns the
store location denoted by a path.  A failed label match follows the first
component, which represents the remainder of a nested record.
-/

namespace LambdaP

/-- Resolve a path to an atomic store location. -/
inductive Path.reduce : Path n -> Store n -> Fin n -> Prop where
| var : Path.reduce (Path.var x) σ x
| fst :
    Path.reduce p σ x ->
    Store.Binds σ x (Tm.pair y a d) ->
    Path.reduce p.fst σ y
| sel_hit :
    Path.reduce p σ x ->
    Store.Binds σ x (Tm.pair y a (Def.val z)) ->
    Path.reduce (p.sel a) σ z
| sel_miss :
    Path.reduce p σ x ->
    Store.Binds σ x (Tm.pair y b d) ->
    a ≠ b ->
    Path.reduce ((Path.var y).sel a) σ z ->
    Path.reduce (p.sel a) σ z

/-- Big-step path reduction is the graph of a partial function. -/
theorem Path.reduce.deterministic
    (h₁ : Path.reduce p σ x₁) (h₂ : Path.reduce p σ x₂) : x₁ = x₂ := by
  induction h₁ generalizing x₂ with
  | var =>
      cases h₂
      rfl
  | fst hp₁ hb₁ ih =>
      cases h₂ with
      | fst hp₂ hb₂ =>
          cases ih hp₂
          cases Store.Binds.unique hb₁ hb₂
          rfl
  | sel_hit hp₁ hb₁ ih =>
      cases h₂ with
      | sel_hit hp₂ hb₂ =>
          cases ih hp₂
          cases Store.Binds.unique hb₁ hb₂
          rfl
      | sel_miss hp₂ hb₂ hne₂ _ =>
          cases ih hp₂
          cases Store.Binds.unique hb₁ hb₂
          exact (hne₂ rfl).elim
  | sel_miss hp₁ hb₁ hne₁ _ ihp ihin =>
      cases h₂ with
      | sel_hit hp₂ hb₂ =>
          cases ihp hp₂
          cases Store.Binds.unique hb₁ hb₂
          exact (hne₁ rfl).elim
      | sel_miss hp₂ hb₂ _ hin₂ =>
          cases ihp hp₂
          cases Store.Binds.unique hb₁ hb₂
          exact ihin hin₂

end LambdaP
