import LambdaP.Soundness.Store

/-!
The semantic denotation of closed types over a heap, following the index
discipline of Amin & Rompf's ECOOP'17 development (`dsubsup_total_rec.v`),
adapted to λ_p's stable heap locations:

- A *semantic store typing* `Ξ` assigns to each location/label a tower of
  approximations of its type member's interpretation (their `vseta`,
  store-indexed instead of value-carried — λ_p pairs live at stable
  locations, so no carried-set threading is needed).
- A type selection dereferences the tower **one level up** (`Ξ m A (n+1)`),
  with no recursion into stored syntax — so `Den` is structurally
  recursive in the path-erased size alone, and the level is a parameter.
- A pair type constrains the location's own tower by a sandwich between
  the (opened) bounds at the **immediate predecessor** level.
- `SemStoOk` ties the towers to the stored aliases *exactly*
  (`Ξ ℓ A (n+1) ↔ Den n W`), the analog of their `valtp_to_vseta` shift.
  Exactness at every level is what makes the closure lemma per-level and
  loss-free; no downward-closure lemma is needed anywhere.
-/

namespace LambdaP

/-- Path-erased structural size. Paths (hence singletons and selections)
count zero, so substitution preserves the size. -/
def Ty.structSize : Ty s -> Nat
| .top => 0
| .bot => 0
| .single _ => 0
| .tsel _ _ => 0
| .arrow S T => S.structSize + T.structSize + 1
| .pairTm S _ T => S.structSize + T.structSize + 1
| .pairTy S _ T1 T2 => S.structSize + T1.structSize + T2.structSize + 1

@[simp]
theorem Ty.structSize_subst {T : Ty s1} {σ : Subst s1 s2} :
    (T.subst σ).structSize = T.structSize := by
  induction T generalizing s2 <;> simp [Ty.subst, Ty.structSize, *]

@[simp]
theorem Ty.structSize_open {T : Ty (s+1)} {p : Path s} :
    (T.open p).structSize = T.structSize := by
  simp [Ty.open]

/-- A semantic store typing: for each location, label, and level, the
approximation of the interpretation of that location's type member.
`Ξ ℓ A (n+1) y` reads "at level n+1, location y inhabits the member `A`
of the pair stored at ℓ". Level 0 carries no information. -/
abbrev SemSto : Type := Nat -> Name -> Nat -> Nat -> Prop

/-- The denotation of a closed type as a set of heap locations, at
approximation level `n`, relative to a semantic store typing `Ξ`. -/
def Den (Θ : Sto) (Ξ : SemSto) (h : Heap) : Nat -> Ty 0 -> Nat -> Prop
| _, .top, _ => True
| _, .bot, _ => False
| _, .single q, ℓ => PathEval h q ℓ
| n, .tsel q A, ℓ =>
    ∃ m ℓ1 W, PathEval h q m ∧
      Heap.Lookup h m (.pairTy (.free ℓ1) A W) ∧
      Ξ m A (n+1) ℓ
| _, .arrow S T, ℓ =>
    ∃ T0 t T1, Heap.Lookup h ℓ (.abs T0 t) ∧
      Wf Θ .empty (.ty T0) ∧
      HasType Θ (Ctx.empty.push T0) t T1 ∧
      Sub Θ .empty (.ty S) (.ty T0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T)
| _, .pairTm S a T, ℓ =>
    ∃ ℓ1 ℓ2, Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      (∀ k, Den Θ Ξ h k S ℓ1) ∧
      ∀ (q : Path 0), PathEval h q ℓ1 -> ∀ k, Den Θ Ξ h k (T.open q) ℓ2
| n, .pairTy S A T1 T2, ℓ =>
    ∃ ℓ1 W, Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      (∀ k, Den Θ Ξ h k S ℓ1) ∧
      match n with
      | 0 => True
      | n0+1 =>
        ∀ (q : Path 0), PathEval h q ℓ1 -> ∀ y,
          (Den Θ Ξ h n0 (T1.open q) y -> Ξ ℓ A (n0+1) y) ∧
          (Ξ ℓ A (n0+1) y -> Den Θ Ξ h n0 (T2.open q) y)
termination_by _ T _ => T.structSize
decreasing_by
  all_goals simp_wf
  all_goals simp only [Ty.structSize]
  all_goals omega

/-- The semantic store typing is tied to the stored aliases exactly, one
level up: the level-(n+1) approximation of a stored member `A = W` is the
level-n denotation of `W`. -/
def SemStoOk (Θ : Sto) (Ξ : SemSto) (h : Heap) : Prop :=
  ∀ {ℓ ℓ1 : Nat} {A : Name} {W : Ty 0},
    Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) ->
    ∀ n y, (Ξ ℓ A (n+1) y ↔ Den Θ Ξ h n W y)

/-- Membership at every approximation level (the limit denotation). -/
def DenAll (Θ : Sto) (Ξ : SemSto) (h : Heap) (T : Ty 0) (ℓ : Nat) : Prop :=
  ∀ n, Den Θ Ξ h n T ℓ

end LambdaP
