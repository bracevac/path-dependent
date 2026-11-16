import Coercions.Selective.Syntax

/-!
# Typing of `H`, indexed by the stored evidence

* `FExp x V a T`: the type `V`, read as the type of `x`, declares the field
  `a : T` (through intersections and `μ` opened at `x`), the field analogue
  of `Exp`.
* `ATy Γ a T` (atoms), `CTy Γ c S T` (certificates), `PTy Γ k S T`
  (positioned steps), mutually.  An atom's typing mirrors DOT-MNF's typing of
  a variable path (`var`, `sub`, `recE`, `recI`, `andI`), with the evidence
  written.  A positioned leaf reads the member off the receiver atom's type,
  at the receiver's root; under `allC S` the hole is checked in `Γ, x : S`.
* `HTy Γ t T`, `HDefsTy Γ d T`.  There is no subsumption rule: an implicit
  `≤₀` step happens only at an application argument and at a cast subject.

The inversion lemmas state, per term former, exactly which premises a
derivation has; `HTy.atom_iff` is the one for atoms.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-- Field exposure, the analogue of `Exp` for term members. -/
inductive FExp : {s : Sig} → BVar s .var → Ty s → Label → Ty s → Prop where
  | fld : FExp x (.fld a T) a T
  | andL : FExp x S a T → FExp x (.and S U) a T
  | andR : FExp x U a T → FExp x (.and S U) a T
  | mu : FExp x (T.substVar x) a U → FExp x (.mu T) a U

mutual
inductive ATy : {s : Sig} → Ctx s → Atom s → Ty s → Prop where
  | var : ATy Γ (.var x) (Γ.lookup x)
  | cast : ATy Γ a S → CTy Γ c S T → ATy Γ (.cast a c) T
  | unfold : ATy Γ a (.mu T) → ATy Γ (.unfold a) (T.substVar a.root)
  | fold : ATy Γ a (T.substVar a.root) → ATy Γ (.fold T a) (.mu T)
  | both : ATy Γ a S → ATy Γ b T → a.root = b.root → ATy Γ (.both a b) (.and S T)
inductive CTy : {s : Sig} → Ctx s → Cert s → Ty s → Ty s → Prop where
  | step : Prim Γ S T → CTy Γ (.step S T) S T
  | seq : CTy Γ c S M → CTy Γ d M T → CTy Γ (.seq c d) S T
  | pos : PTy Γ k S T → CTy Γ (.pos k) S T
inductive PTy : {s : Sig} → Ctx s → Pos s → Ty s → Ty s → Prop where
  | selU : ATy Γ a R → Exp a.root R A L U → PTy Γ (.selU a A U) (.sel (.var a.root) A) U
  | selL : ATy Γ a R → Exp a.root R A L U → PTy Γ (.selL a A L) L (.sel (.var a.root) A)
  | fld : PTy Γ k S T → PTy Γ (.fld ℓ k) (.fld ℓ S) (.fld ℓ T)
  | typL : PTy Γ k L2 L1 → PTy Γ (.typL A k U) (.typ A L1 U) (.typ A L2 U)
  | typU : PTy Γ k U1 U2 → PTy Γ (.typU A L k) (.typ A L U1) (.typ A L U2)
  | allD : PTy Γ k S2 S1 → PTy Γ (.allD k T) (.all S1 T) (.all S2 T)
  | allC : PTy (Γ.cons S) k T1 T2 → PTy Γ (.allC S k) (.all S T1) (.all S T2)
  | andL : PTy Γ k S M → PTy Γ (.andL k U) (.and S U) (.and M U)
  | andR : PTy Γ k S M → PTy Γ (.andR U k) (.and U S) (.and U M)
end

mutual
inductive HTy : {s : Sig} → Ctx s → HTm s → Ty s → Prop where
  | atom : ATy Γ a T → HTy Γ (.atom a) T
  | lam : HTy (Γ.cons S) t T → HTy Γ (.val (.lam S t)) (.all S T)
  /-- One implicit `≤₀` step at the argument; none at the callee. -/
  | app : ATy Γ a (.all S T) → ATy Γ b V → Prim Γ V S → HTy Γ (.app a b) (T.substVar b.root)
  | obj : HDefsTy (Γ.consSelf d.erase T) d T → d.erase.Distinct → HTy Γ (.val (.obj T d)) (.mu T)
  | proj : ATy Γ a V → FExp a.root V ℓ T → HTy Γ (.proj a ℓ) T
  | «let» : HTy Γ t T → HTy (Γ.cons T) u U.weaken → HTy Γ (.let t u) U
  /-- One implicit `≤₀` step at the subject, then the written certificate. -/
  | cast : HTy Γ t S0 → Prim Γ S0 S → CTy Γ c S T → HTy Γ (.cast t c) T
inductive HDefsTy : {s : Sig} → Ctx s → HDefs s → Ty s → Prop where
  | typ : HDefsTy Γ (.typ A T) (.typ A T T)
  | trm : HTy Γ t T → HDefsTy Γ (.trm a t) (.fld a T)
  | and : HDefsTy Γ d1 T1 → HDefsTy Γ d2 T2 → HDefsTy Γ (.and d1 d2) (.and T1 T2)
end

/-! ## Inversion -/

/-- An atom used as a term has exactly its atom types: no subsumption. -/
theorem HTy.atom_iff {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s} :
    HTy Γ (.atom a) T ↔ ATy Γ a T :=
  ⟨fun h => by cases h with | atom h => exact h, .atom⟩

theorem HTy.lam_iff {s : Sig} {Γ : Ctx s} {S : Ty s} {t : HTm (s,x)} {U : Ty s} :
    HTy Γ (.val (.lam S t)) U ↔ ∃ T, U = .all S T ∧ HTy (Γ.cons S) t T :=
  ⟨fun h => by cases h with | lam h => exact ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ .lam h⟩

theorem HTy.app_iff {s : Sig} {Γ : Ctx s} {a b : Atom s} {U : Ty s} :
    HTy Γ (.app a b) U ↔
      ∃ S T V, U = T.substVar b.root ∧ ATy Γ a (.all S T) ∧ ATy Γ b V ∧ Prim Γ V S :=
  ⟨fun h => by cases h with | app ha hb hp => exact ⟨_, _, _, rfl, ha, hb, hp⟩,
   fun ⟨_, _, _, e, ha, hb, hp⟩ => e ▸ .app ha hb hp⟩

theorem HTy.obj_iff {s : Sig} {Γ : Ctx s} {T : Ty (s,x)} {d : HDefs (s,x)} {U : Ty s} :
    HTy Γ (.val (.obj T d)) U ↔
      U = .mu T ∧ HDefsTy (Γ.consSelf d.erase T) d T ∧ d.erase.Distinct :=
  ⟨fun h => by cases h with | obj hd hdist => exact ⟨rfl, hd, hdist⟩,
   fun ⟨e, hd, hdist⟩ => e ▸ .obj hd hdist⟩

theorem HTy.proj_iff {s : Sig} {Γ : Ctx s} {a : Atom s} {ℓ : Label} {T : Ty s} :
    HTy Γ (.proj a ℓ) T ↔ ∃ V, ATy Γ a V ∧ FExp a.root V ℓ T :=
  ⟨fun h => by cases h with | proj ha hf => exact ⟨_, ha, hf⟩, fun ⟨_, ha, hf⟩ => .proj ha hf⟩

theorem HTy.let_iff {s : Sig} {Γ : Ctx s} {t : HTm s} {u : HTm (s,x)} {U : Ty s} :
    HTy Γ (.let t u) U ↔ ∃ T, HTy Γ t T ∧ HTy (Γ.cons T) u U.weaken :=
  ⟨fun h => by cases h with | «let» h1 h2 => exact ⟨_, h1, h2⟩, fun ⟨_, h1, h2⟩ => .let h1 h2⟩

theorem HTy.cast_iff {s : Sig} {Γ : Ctx s} {t : HTm s} {c : Cert s} {T : Ty s} :
    HTy Γ (.cast t c) T ↔ ∃ S0 S, HTy Γ t S0 ∧ Prim Γ S0 S ∧ CTy Γ c S T :=
  ⟨fun h => by cases h with | cast ht hp hc => exact ⟨_, _, ht, hp, hc⟩,
   fun ⟨_, _, ht, hp, hc⟩ => .cast ht hp hc⟩

theorem HDefsTy.typ_iff {s : Sig} {Γ : Ctx s} {A : Label} {T U : Ty s} :
    HDefsTy Γ (.typ A T) U ↔ U = .typ A T T :=
  ⟨fun h => by cases h; rfl, fun e => e ▸ .typ⟩

theorem HDefsTy.trm_iff {s : Sig} {Γ : Ctx s} {a : Label} {t : HTm s} {U : Ty s} :
    HDefsTy Γ (.trm a t) U ↔ ∃ T, U = .fld a T ∧ HTy Γ t T :=
  ⟨fun h => by cases h with | trm h => exact ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ .trm h⟩

theorem HDefsTy.and_iff {s : Sig} {Γ : Ctx s} {d1 d2 : HDefs s} {U : Ty s} :
    HDefsTy Γ (.and d1 d2) U ↔ ∃ T1 T2, U = .and T1 T2 ∧ HDefsTy Γ d1 T1 ∧ HDefsTy Γ d2 T2 :=
  ⟨fun h => by cases h with | and h1 h2 => exact ⟨_, _, rfl, h1, h2⟩,
   fun ⟨_, _, e, h1, h2⟩ => e ▸ .and h1 h2⟩

end Selective
