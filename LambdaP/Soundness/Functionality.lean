import LambdaP.Soundness.Progress
import LambdaP.Lemmas.Locs

/-!
Support for the functionality lemma (`T.open q` and `T.open ℓ` are mutual
subtypes when `q ⇓ ℓ`): bounds on evaluation targets of wellformed paths,
and transport of closed empty-context subtypings into arbitrary contexts.
-/

namespace LambdaP

/-- Wellformed closed paths evaluate into the store. -/
theorem Path.Wf.eval_target_lt {Θ : Sto} {h : Heap} {p : Path 0} {m : Nat}
    (hh : HeapTyped Θ h) (hw : Path.Wf Θ .empty p) (he : PathEval h p m) :
    m < Θ.length :=
  PathEval.target_lt hh.bounded he hw.locsBelow

/-- The vacuous renaming embeds the empty context into any context. -/
theorem Renaming.fromEmpty {s : Sig} {Γ : Ctx s} :
    Renaming .empty (Rename.fromZero (s := s)) Γ := by
  intro x T hx
  exact absurd hx (fun hx => nomatch hx)

/-- A closed subtyping fact transports into any context, with the types
embedded by the vacuous renaming. -/
theorem Sub.of_closed {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau 0}
    (hs : Sub Θ .empty τ1 τ2) :
    Sub Θ Γ (τ1.rename Rename.fromZero) (τ2.rename Rename.fromZero) :=
  hs.rename Renaming.fromEmpty

/-- Wellformedness of closed paths transports into any context. -/
theorem Path.Wf.of_closed {Θ : Sto} {s : Sig} {Γ : Ctx s} {p : Path 0}
    (hw : Path.Wf Θ .empty p) :
    Path.Wf Θ Γ (p.rename Rename.fromZero) :=
  hw.rename Renaming.fromEmpty

end LambdaP
