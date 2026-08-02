import LambdaPHistory.PathReduction

/-!
A variant of the original big-step path semantics whose miss rule follows the
same prefix that appears in the static selection rule.  The historical
semantics recurses from `Path.var y`, where `y` is obtained by looking up the
first component; this relation instead recurses directly from `p.fst`.
-/

namespace LambdaPHistory

/-- Static-aligned big-step path lookup. -/
inductive Path.lookup : Path n -> Store n -> Fin n -> Prop where
| var : Path.lookup (Path.var x) σ x
| fst :
    Path.lookup p σ x ->
    Store.Binds σ x (Tm.pair y a d) ->
    Path.lookup p.fst σ y
| sel_hit :
    Path.lookup p σ x ->
    Store.Binds σ x (Tm.pair y a (Def.val z)) ->
    Path.lookup (p.sel a) σ z
| sel_miss :
    Path.lookup p σ x ->
    Store.Binds σ x (Tm.pair y b d) ->
    a ≠ b ->
    Path.lookup (p.fst.sel a) σ z ->
    Path.lookup (p.sel a) σ z

/-- Static-aligned lookup is the graph of a partial function. -/
theorem Path.lookup.deterministic
    (h₁ : Path.lookup p σ x₁) (h₂ : Path.lookup p σ x₂) : x₁ = x₂ := by
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

/-! ## Replacement of co-evaluating prefixes -/

/-- In the historical semantics, selection depends only on the location of
its prefix, not on the syntax of that prefix. -/
theorem Path.reduce.sel_congr
    (hs : Path.reduce (p.sel a) σ z)
    (hp : Path.reduce p σ x)
    (hq : Path.reduce q σ x) :
    Path.reduce (q.sel a) σ z := by
  cases hs with
  | sel_hit hp' hb =>
      cases Path.reduce.deterministic hp hp'
      exact .sel_hit hq hb
  | sel_miss hp' hb hne hin =>
      cases Path.reduce.deterministic hp hp'
      exact .sel_miss hq hb hne hin

/-- Induction-strengthened form of selection-prefix replacement. -/
theorem Path.lookup.sel_congr_of_eq
    {n : Nat} {r : Path n} {σ : Store n} {z : Fin n}
    (hs : Path.lookup r σ z) :
    ∀ {p : Path n} {a : Name}, r = p.sel a ->
      ∀ {x : Fin n} {q : Path n}, Path.lookup p σ x ->
        Path.lookup q σ x -> Path.lookup (q.sel a) σ z := by
  induction hs with
  | var =>
      intro p a hr
      cases hr
  | fst _ _ _ =>
      intro p a hr
      cases hr
  | sel_hit hp hb _ =>
      intro p a hr
      cases hr
      intro x q hp' hq
      cases Path.lookup.deterministic hp' hp
      exact .sel_hit hq hb
  | sel_miss hp hb hne hin _ ihin =>
      intro p a hr
      cases hr
      intro x q hp' hq
      cases Path.lookup.deterministic hp' hp
      exact .sel_miss hq hb hne
        (ihin rfl (.fst hp hb) (.fst hq hb))

/-- Static-aligned lookup likewise depends only on the location of a
selection prefix.  In the miss case the induction replaces the prefix of the
recursive `fst` selection as well. -/
theorem Path.lookup.sel_congr
    (hs : Path.lookup (p.sel a) σ z)
    (hp : Path.lookup p σ x)
    (hq : Path.lookup q σ x) :
    Path.lookup (q.sel a) σ z :=
  hs.sel_congr_of_eq rfl hp hq

/-! ## Equivalence with the historical semantics -/

theorem Path.lookup.toReduce (h : Path.lookup p σ x) :
    Path.reduce p σ x := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih hb
  | sel_hit _ hb ih => exact .sel_hit ih hb
  | sel_miss _ hb hne _ ihp ihin =>
      exact .sel_miss ihp hb hne
        (Path.reduce.sel_congr ihin (.fst ihp hb) .var)

theorem Path.reduce.toLookup (h : Path.reduce p σ x) :
    Path.lookup p σ x := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih hb
  | sel_hit _ hb ih => exact .sel_hit ih hb
  | sel_miss _ hb hne _ ihp ihin =>
      exact .sel_miss ihp hb hne
        (Path.lookup.sel_congr ihin .var (.fst ihp hb))

/-- The static-aligned and historical miss rules define the same lookup
relation without any typing or store-well-formedness assumption. -/
theorem Path.lookup_iff_reduce :
    Path.lookup p σ x ↔ Path.reduce p σ x :=
  ⟨Path.lookup.toReduce, Path.reduce.toLookup⟩

end LambdaPHistory
