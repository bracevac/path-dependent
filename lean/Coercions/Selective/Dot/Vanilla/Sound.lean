import Coercions.Selective.Dot.Vanilla.Translate
import Coercions.Selective.Dot.Lift

/-!
# Selective DOT and DOT-MNF: soundness of erasure

The erasure of a typed term of `SelDot` is typed in DOT-MNF at the same type.
A path has the types of its root; a primitive step and a certificate are
subtyping derivations; a cast is subsumption. `PathTy.keep` needs no
counterpart: the root of a cast path is the root of the path under the cast.
-/

namespace SelDot.Vanilla

open FCdot (Kind Sig BVar Rename Label)
open SelDot.Lift (Ty.erase_embed')

mutual

/-- A typed path: its root has the type in DOT-MNF. -/
theorem pathTy_sound {Γ : Ctx s} : ∀ {p : Path s} {T : Ty s}, PathTy Γ p T →
    Nonempty (DotMNF.HasTy Γ.toDot (.path (.var p.root)) T.toDot)
  | _, _, @PathTy.var _ _ x => by
      rw [← Ctx.toDot_lookup]; exact ⟨.var⟩
  | _, _, .cast hp hc => by
      obtain ⟨d⟩ := pathTy_sound hp
      obtain ⟨e⟩ := certTy_sound hc
      exact ⟨.sub d e⟩
  | _, _, .keep _ _ hp => by have h := pathTy_sound hp; exact h
  | _, _, .recI hp => by
      obtain ⟨d⟩ := pathTy_sound hp
      rw [Ty.toDot_substVar] at d
      exact ⟨.recI d⟩
  | _, _, .recE hp => by
      obtain ⟨d⟩ := pathTy_sound hp
      rw [Ty.toDot_substVar]
      exact ⟨.recE d⟩
  | _, _, .andI hp hq => by
      obtain ⟨d1⟩ := pathTy_sound hp
      obtain ⟨d2⟩ := pathTy_sound hq
      exact ⟨.andI d1 d2⟩

/-- A primitive step is a subtyping derivation between the erasures. -/
theorem prim_sound {Γ : Ctx s} : ∀ {S T : ATy s}, Prim Γ S T →
    Nonempty (DotMNF.Sub Γ.toDot S.erase.toDot T.erase.toDot)
  | _, _, .top _ => ⟨.top⟩
  | _, _, .bot _ => ⟨.bot⟩
  | _, _, .refl _ _ e => by rw [e]; exact ⟨.refl⟩
  | _, _, .andL1 h _ => by
      obtain ⟨d⟩ := prim_sound h
      exact ⟨.trans .and1 d⟩
  | _, _, .andL2 _ h => by
      obtain ⟨d⟩ := prim_sound h
      exact ⟨.trans .and2 d⟩
  | _, _, .andR h1 h2 => by
      obtain ⟨d1⟩ := prim_sound h1
      obtain ⟨d2⟩ := prim_sound h2
      exact ⟨.and d1 d2⟩
  | _, _, .fld h => by
      obtain ⟨d⟩ := prim_sound h
      exact ⟨.fld d⟩
  | _, _, .typ h1 h2 => by
      obtain ⟨d1⟩ := prim_sound h1
      obtain ⟨d2⟩ := prim_sound h2
      exact ⟨.typ d1 d2⟩
  | _, _, .all h1 _ h2 => by
      obtain ⟨d1⟩ := prim_sound h1
      obtain ⟨d2⟩ := prim_sound h2
      exact ⟨.all d1 d2⟩
  | _, _, .selU hp _ e => by
      obtain ⟨d⟩ := pathTy_sound hp
      subst e
      exact ⟨.selUpper d⟩
  | _, _, .selL hp _ e => by
      obtain ⟨d⟩ := pathTy_sound hp
      subst e
      exact ⟨.selLower d⟩

/-- A typed certificate is a subtyping derivation. -/
theorem certTy_sound {Γ : Ctx s} : ∀ {c : Cert s} {S T : Ty s}, CertTy Γ c S T →
    Nonempty (DotMNF.Sub Γ.toDot S.toDot T.toDot)
  | _, _, _, .step h => prim_sound h
  | _, _, _, .seq h1 h2 => by
      obtain ⟨d1⟩ := certTy_sound h1
      obtain ⟨d2⟩ := certTy_sound h2
      exact ⟨.trans d1 d2⟩

end

/-- The implicit comparison at an argument is a subtyping derivation. -/
theorem prim₀_sound {Γ : Ctx s} {S T : Ty s} (h : Prim₀ Γ S T) :
    Nonempty (DotMNF.Sub Γ.toDot S.toDot T.toDot) := by
  have h' := prim_sound h
  rwa [Ty.erase_embed', Ty.erase_embed'] at h'

/-- The context of an object literal: lookup does not see the recorded
definitions. -/
theorem consSelf_lookup (Γ : DotMNF.Ctx s) (d : DotMNF.Defs (s,x)) (T : DotMNF.Ty (s,x))
    (y : BVar (s,x) .var) :
    (Γ.consSelf d T).lookup y = (Γ.cons (.mu T)).lookup y := by
  cases y <;> rfl

mutual

/-- Erasure of a typed term is typed in DOT-MNF. -/
theorem hasTy_sound {Γ : Ctx s} : ∀ {t : Tm s} {T : Ty s}, HasTy Γ t T →
    Nonempty (DotMNF.HasTy Γ.toDot t.toDot T.toDot)
  | _, _, .path hp => pathTy_sound hp
  | _, _, .lam h => by
      obtain ⟨d⟩ := hasTy_sound h
      exact ⟨.lam d⟩
  | _, _, .app hp hq hs => by
      obtain ⟨d1⟩ := pathTy_sound hp
      obtain ⟨d2⟩ := pathTy_sound hq
      obtain ⟨e⟩ := prim₀_sound hs
      rw [Ty.toDot_substVar]
      exact ⟨.app d1 (.sub d2 e)⟩
  | _, _, .obj h hd => by
      obtain ⟨D⟩ := defsTy_sound h
      exact ⟨.obj (defsTyTransfer (consSelf_lookup _ _ _) D) hd.toDot⟩
  | _, _, .proj hp => by
      obtain ⟨d⟩ := pathTy_sound hp
      exact ⟨.proj d⟩
  | _, _, .let h1 h2 => by
      obtain ⟨d1⟩ := hasTy_sound h1
      obtain ⟨d2⟩ := hasTy_sound h2
      rw [Ty.toDot_weaken] at d2
      exact ⟨.let d1 d2⟩
  | _, _, .cast h hc => by
      obtain ⟨d⟩ := hasTy_sound h
      obtain ⟨e⟩ := certTy_sound hc
      exact ⟨.sub d e⟩

/-- Erasure of typed definitions is typed in DOT-MNF. -/
theorem defsTy_sound {Γ : Ctx s} : ∀ {d : Defs s} {T : Ty s}, DefsTy Γ d T →
    Nonempty (DotMNF.DefsTy Γ.toDot d.toDot T.toDot)
  | _, _, .typ => ⟨.typ⟩
  | _, _, .trm h => by
      obtain ⟨d⟩ := hasTy_sound h
      exact ⟨.trm d⟩
  | _, _, .and h1 h2 => by
      obtain ⟨d1⟩ := defsTy_sound h1
      obtain ⟨d2⟩ := defsTy_sound h2
      exact ⟨.and d1 d2⟩

end

end SelDot.Vanilla
