import LambdaP.Syntax

/-!
An evidence-passing experiment for `lambda_p`.

The source relation in this file contains the unrestricted covariance rule for
dependent pairs with proper members.  `Evidence` refines a source derivation
with an explicit abstraction for the member conversion.  Keeping that
conversion open is the essential point: its bound variable is instantiated
only when evidence is applied to a concrete pair.
-/

namespace LambdaPFC

open LambdaP

/--
Evidence either maps ordinary types or abstracts a map beneath a dependent-pair
binder.  In `abs S T U`, `T` and `U` live in the scope extended by the first
component, whereas `S` lives outside that scope.
-/
inductive EvSort : Nat -> Type where
| map : Ty n -> Ty n -> EvSort n
| abs : Ty n -> Ty (n + 1) -> Ty (n + 1) -> EvSort n

/--
The source subtyping fragment.  Abstracted judgments retain the assumed type
of the pair's first component, allowing its bound singleton to be widened to
that assumption.
-/
inductive Source : {n : Nat} -> EvSort n -> Prop where
| refl : Source (.map T T)
| trans : Source (.map S T) -> Source (.map T U) -> Source (.map S U)
| bot : Source (.map .Bot T)
| top : Source (.map T .Top)
| lift : Source (.map T U) -> Source (.abs S T U)
| bound : Source (.abs S (.Single (.var 0)) S.weaken)
| absTrans :
    Source (.abs S T U) -> Source (.abs S U V) -> Source (.abs S T V)
| pair :
    Source (.map S S') ->
    Source (.abs S T T') ->
    Source (.map (.Pair S a (.ty T)) (.Pair S' a (.ty T')))

/-- Ordinary source subtyping. -/
abbrev Sub (S T : Ty n) : Prop := Source (.map S T)

/-- Source subtyping beneath a dependent-pair binder. -/
abbrev AbsSub (S : Ty n) (T U : Ty (n + 1)) : Prop := Source (.abs S T U)

/-- Explicit, directed subtyping evidence. -/
inductive Evidence : {n : Nat} -> EvSort n -> Type where
| refl : Evidence (.map T T)
| trans : Evidence (.map S T) -> Evidence (.map T U) -> Evidence (.map S U)
| bot : Evidence (.map .Bot T)
| top : Evidence (.map T .Top)
| lam : Evidence (.map T U) -> Evidence (.abs S T U)
| bound : Evidence (.abs S (.Single (.var 0)) S.weaken)
| absTrans :
    Evidence (.abs S T U) -> Evidence (.abs S U V) -> Evidence (.abs S T V)
| pair :
    Evidence (.map S S') ->
    Evidence (.abs S T T') ->
    Evidence (.map (.Pair S a (.ty T)) (.Pair S' a (.ty T')))

/-- The source proposition obtained by erasing an evidence sort. -/
def EvSort.ErasesTo : EvSort n -> Prop
| s => Source s

/-- Erasing evidence recovers a derivation in the source relation. -/
theorem Evidence.erase (c : Evidence s) : s.ErasesTo := by
  induction c with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | lam _ ih => exact .lift ih
  | bound => exact .bound
  | absTrans _ _ ih1 ih2 => exact .absTrans ih1 ih2
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2

/-- Every source derivation admits explicit evidence. -/
theorem Source.hasEvidence (h : Source s) : Nonempty (Evidence s) := by
  induction h with
  | refl => exact ⟨.refl⟩
  | trans _ _ ih1 ih2 =>
      rcases ih1 with ⟨c1⟩
      rcases ih2 with ⟨c2⟩
      exact ⟨.trans c1 c2⟩
  | bot => exact ⟨.bot⟩
  | top => exact ⟨.top⟩
  | lift _ ih =>
      rcases ih with ⟨c⟩
      exact ⟨.lam c⟩
  | bound => exact ⟨.bound⟩
  | absTrans _ _ ih1 ih2 =>
      rcases ih1 with ⟨c1⟩
      rcases ih2 with ⟨c2⟩
      exact ⟨.absTrans c1 c2⟩
  | pair _ _ ih1 ih2 =>
      rcases ih1 with ⟨c1⟩
      rcases ih2 with ⟨c2⟩
      exact ⟨.pair c1 c2⟩

/-- Every ordinary source derivation admits map evidence. -/
theorem Sub.hasEvidence (h : Sub S T) : Nonempty (Evidence (.map S T)) :=
  Source.hasEvidence h

/-- Every abstracted source derivation admits abstraction evidence. -/
theorem AbsSub.hasEvidence (h : AbsSub S T U) :
    Nonempty (Evidence (.abs S T U)) :=
  Source.hasEvidence h

end LambdaPFC
