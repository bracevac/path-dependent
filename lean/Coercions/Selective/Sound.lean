import Coercions.Selective.Check
import Coercions.DotToFCdot

/-!
# Soundness into DOT-MNF and the transported route

Every judgment of `H` maps to a DOT-MNF derivation: a primitive step to a
`DotMNF.Sub` derivation (`primitive_sound`), an atom to a typing of its root
(`ATy.sound`), a certificate or positioned step to a `DotMNF.Sub` derivation
(`coercion_sound`, `PTy.sound`), and an annotated term to a typing of its
erasure (`elaboration_typed`).  Safety of the erased program on DOT-MNF's
store machine then follows from `DotMNF.dot_safety` (`compiled_safety`,
`compiled_not_stuck`); FCdot enters only through that theorem's invariant.

Coercion existence is transitive by the `;` constructor
(`coercion_transitive`, `coercion_exists_transitive`).
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path HasTy Sub DefsTy)

theorem Exp.toHasTy {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {A : Label} {L U : Ty s} :
    Exp x T A L U → Nonempty (HasTy Γ (.path (.var x)) T) →
    Nonempty (HasTy Γ (.path (.var x)) (.typ A L U))
  | .typ, h => h
  | .andL e, ⟨h⟩ => e.toHasTy ⟨.sub h .and1⟩
  | .andR e, ⟨h⟩ => e.toHasTy ⟨.sub h .and2⟩
  | .mu e, ⟨h⟩ => e.toHasTy ⟨.recE h⟩

theorem FExp.toHasTy {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {a : Label} {T : Ty s} :
    FExp x V a T → Nonempty (HasTy Γ (.path (.var x)) V) →
    Nonempty (HasTy Γ (.path (.var x)) (.fld a T))
  | .fld, h => h
  | .andL e, ⟨h⟩ => e.toHasTy ⟨.sub h .and1⟩
  | .andR e, ⟨h⟩ => e.toHasTy ⟨.sub h .and2⟩
  | .mu e, ⟨h⟩ => e.toHasTy ⟨.recE h⟩

/-- **primitive_sound**: a `≤₀` derivation maps to a `DotMNF.Sub` derivation.
`andL1/andL2` become `Sub.trans Sub.and1 _` (an operand middle). -/
theorem primitive_sound {s : Sig} {Γ : Ctx s} {S T : Ty s} : Prim Γ S T → Nonempty (Sub Γ S T)
  | .refl => ⟨.refl⟩
  | .top => ⟨.top⟩
  | .bot => ⟨.bot⟩
  | .andR h1 h2 => by
      obtain ⟨d1⟩ := primitive_sound h1; obtain ⟨d2⟩ := primitive_sound h2; exact ⟨.and d1 d2⟩
  | .andL1 h => by obtain ⟨d⟩ := primitive_sound h; exact ⟨.trans .and1 d⟩
  | .andL2 h => by obtain ⟨d⟩ := primitive_sound h; exact ⟨.trans .and2 d⟩
  | .fld h => by obtain ⟨d⟩ := primitive_sound h; exact ⟨.fld d⟩
  | .typ h1 h2 => by
      obtain ⟨d1⟩ := primitive_sound h1; obtain ⟨d2⟩ := primitive_sound h2; exact ⟨.typ d1 d2⟩
  | .all h1 h2 => by
      obtain ⟨d1⟩ := primitive_sound h1; obtain ⟨d2⟩ := primitive_sound h2; exact ⟨.all d1 d2⟩
  | .selU e => by obtain ⟨h⟩ := e.toHasTy ⟨.var⟩; exact ⟨.selUpper h⟩
  | .selL e => by obtain ⟨h⟩ := e.toHasTy ⟨.var⟩; exact ⟨.selLower h⟩

mutual
theorem ATy.sound {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    ATy Γ a T → Nonempty (HasTy Γ (.path (.var a.root)) T)
  | .var => ⟨.var⟩
  | .cast ha hc => by
      obtain ⟨d⟩ := ATy.sound ha; obtain ⟨e⟩ := CTy.sound hc; exact ⟨.sub d e⟩
  | .unfold ha => by obtain ⟨d⟩ := ATy.sound ha; exact ⟨.recE d⟩
  | .fold ha => by obtain ⟨d⟩ := ATy.sound ha; exact ⟨.recI d⟩
  | .both (a := a) (b := b) ha hb hr => by
      obtain ⟨d⟩ := ATy.sound ha; obtain ⟨e⟩ := ATy.sound hb
      have e' : HasTy Γ (.path (.var a.root)) _ := hr ▸ e
      exact ⟨.andI d e'⟩
theorem CTy.sound {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    CTy Γ c S T → Nonempty (Sub Γ S T)
  | .step p => primitive_sound p
  | .seq h1 h2 => by
      obtain ⟨d1⟩ := CTy.sound h1; obtain ⟨d2⟩ := CTy.sound h2; exact ⟨.trans d1 d2⟩
  | .pos h => PTy.sound h
theorem PTy.sound {s : Sig} {Γ : Ctx s} {k : Pos s} {S T : Ty s} :
    PTy Γ k S T → Nonempty (Sub Γ S T)
  | .selU ha he => by
      obtain ⟨d⟩ := ATy.sound ha; obtain ⟨h⟩ := he.toHasTy ⟨d⟩; exact ⟨.selUpper h⟩
  | .selL ha he => by
      obtain ⟨d⟩ := ATy.sound ha; obtain ⟨h⟩ := he.toHasTy ⟨d⟩; exact ⟨.selLower h⟩
  | .fld h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.fld d⟩
  | .typL h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.typ d .refl⟩
  | .typU h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.typ .refl d⟩
  | .allD h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.all d .refl⟩
  | .allC h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.all .refl d⟩
  | .andL h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.and (.trans .and1 d) .and2⟩
  | .andR h => by obtain ⟨d⟩ := PTy.sound h; exact ⟨.and .and1 (.trans .and2 d)⟩
end

/-- A certificate maps to a DOT-MNF inclusion; `;` becomes `Sub.trans`. -/
theorem coercion_sound {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    CTy Γ c S T → Nonempty (Sub Γ S T) := CTy.sound

mutual
theorem elaboration_typed {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} :
    HTy Γ t T → Nonempty (HasTy Γ t.erase T)
  | .atom h => ATy.sound h
  | .lam h => by obtain ⟨d⟩ := elaboration_typed h; exact ⟨.lam d⟩
  | .app hf hy hp => by
      obtain ⟨df⟩ := ATy.sound hf; obtain ⟨dy⟩ := ATy.sound hy
      obtain ⟨dp⟩ := primitive_sound hp
      exact ⟨.app df (.sub dy dp)⟩
  | .obj hd hdist => by obtain ⟨d⟩ := defs_typed hd; exact ⟨.obj d hdist⟩
  | .proj ha hf => by obtain ⟨d⟩ := hf.toHasTy (ATy.sound ha); exact ⟨.proj d⟩
  | .let h1 h2 => by
      obtain ⟨d1⟩ := elaboration_typed h1; obtain ⟨d2⟩ := elaboration_typed h2
      exact ⟨.let d1 d2⟩
  | .cast ht hp hc => by
      obtain ⟨dt⟩ := elaboration_typed ht; obtain ⟨dp⟩ := primitive_sound hp
      obtain ⟨dc⟩ := CTy.sound hc
      exact ⟨.sub (.sub dt dp) dc⟩
theorem defs_typed {s : Sig} {Γ : Ctx s} {d : HDefs s} {T : Ty s} :
    HDefsTy Γ d T → Nonempty (DefsTy Γ d.erase T)
  | .typ => ⟨.typ⟩
  | .trm h => by obtain ⟨d⟩ := elaboration_typed h; exact ⟨.trm d⟩
  | .and h1 h2 => by
      obtain ⟨d1⟩ := defs_typed h1; obtain ⟨d2⟩ := defs_typed h2; exact ⟨.and d1 d2⟩
end

theorem elaboration_erases {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} (h : HTy Γ t T) :
    ∃ d : HasTy Γ t.erase T, FCdot.Tm.erase d.translate = DotMNF.Tm.erase t.erase := by
  obtain ⟨d⟩ := elaboration_typed h
  exact ⟨d, DotMNF.HasTy.translate_erase d⟩

/-- Safety of the erased program on DOT-MNF's store machine (`DotMNF.Step`). -/
theorem compiled_safety {t : HTm []} {T : Ty []} (h : HTy .nil t T)
    {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, t.erase⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' := by
  obtain ⟨d⟩ := elaboration_typed h
  exact DotMNF.dot_safety d run

/-- No state reachable from the erased program of a closed typed term is stuck. -/
theorem compiled_not_stuck {t : HTm []} {T : Ty []} (h : HTy .nil t T)
    {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, t.erase⟩ : DotMNF.State []) st) : ¬ st.Stuck := by
  obtain ⟨d⟩ := elaboration_typed h
  exact DotMNF.dot_not_stuck d run

/-! ## Composition -/

/-- Coercion existence is transitive, by the `;` constructor. -/
theorem coercion_transitive {s : Sig} {Γ : Ctx s} {c d : Cert s} {S M T : Ty s}
    (hc : CTy Γ c S M) (hd : CTy Γ d M T) : CTy Γ (.seq c d) S T := .seq hc hd

theorem coercion_exists_transitive {s : Sig} {Γ : Ctx s} {S M T : Ty s} :
    (∃ c, CTy Γ c S M) → (∃ d, CTy Γ d M T) → ∃ e, CTy Γ e S T
  | ⟨c, hc⟩, ⟨d, hd⟩ => ⟨.seq c d, .seq hc hd⟩

end Selective
