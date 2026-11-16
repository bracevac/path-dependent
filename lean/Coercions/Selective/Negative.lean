import Coercions.Selective.Matrix

/-!
# Negative theorems

The negative theorems, including those that are not already rows of the
example matrix.  Their locations:

* N1 `realizable_gap`, `primitive_nontrans` (`Witness.lean`, row 3).
* N2 `E3_not_prim`, `E3_rejected` (`Witness.lean`, row 2).
* N3 `R1.rebind_loses_root` (here): root identity is lost when the argument
  atom of `g y u` is bound by a `let` instead of being passed as an atom.
* N4 `reductNaive_untypable` (`Matrix.lean`, row 11).
* N5 `Y_no_receiver_free_chain`, `Y_no_receiver_free_coercion` (here): step and
  seq alone cannot relate the endpoints of `certY`; `certY` (`Matrix.lean`)
  supplies a solution with a scoped receiver.
* N6 `K_receiver_free_chain` (here): the non-`⊤` example under two binders
  has a chain of three `≤₀` steps (domain narrowing), so `goodK`/`badK` are
  regressions of the checker, not of expressiveness.
* N8 `fun_invertible_H` (`Matrix.lean`).

A *step-only* certificate is one built from `step` and `;`; its typings are
exactly the chains of `≤₀` steps (`stepOnly_iff_chain`).
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Step-only certificates are chains -/

/-- A certificate without positioned steps. -/
inductive Cert.StepOnly : Cert s → Prop where
  | step : Cert.StepOnly (.step S T)
  | seq : Cert.StepOnly c → Cert.StepOnly d → Cert.StepOnly (.seq c d)

theorem CTy.chain_of_stepOnly {s : Sig} {Γ : Ctx s} :
    {c : Cert s} → {S T : Ty s} → CTy Γ c S T → c.StepOnly → Chain Γ S T
  | _, _, _, .step p, _ => .single p
  | _, _, _, .seq h1 h2, .seq o1 o2 => (CTy.chain_of_stepOnly h1 o1).append (CTy.chain_of_stepOnly h2 o2)
  | _, _, _, .pos _, o => nomatch o

theorem stepOnly_of_chain {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Chain Γ S T) :
    ∃ c : Cert s, c.StepOnly ∧ CTy Γ c S T := by
  induction h with
  | refl => exact ⟨.step _ _, .step, .step .refl⟩
  | cons p _ ih =>
      obtain ⟨c, hc, hty⟩ := ih
      exact ⟨.seq (.step _ _) c, .seq .step hc, .seq (.step p) hty⟩

theorem stepOnly_iff_chain {s : Sig} {Γ : Ctx s} {S T : Ty s} :
    (∃ c : Cert s, c.StepOnly ∧ CTy Γ c S T) ↔ Chain Γ S T :=
  ⟨fun ⟨_, hc, h⟩ => h.chain_of_stepOnly hc, stepOnly_of_chain⟩

/-! ## N3: re-binding the argument atom loses its root -/

namespace R1

/-- `let y2 = yArg in let h = g y2 in h u`: the argument atom bound by `let`,
so `h : ∀(w : y2.D) ⊤` and `u : y.D` fails `y.D ≤₀ y2.D`. -/
def bodyRebind : HTm S6 :=
  .let (.atom yArg) (.let (.app (.var (.there vg)) (.var .here)) (.app (.var .here) (.var (.there (.there vu)))))

theorem rebind_loses_root : ∀ U, ¬ HTy G6 bodyRebind U :=
  untypable_of_synthTm (by decide)

/-- The same body with the atom passed directly is typed (`hPlain_typed`). -/
theorem atom_keeps_root : HTy G6 body6H .top := by decide

end R1

/-! ## N6: the non-`⊤` example has a receiver-free chain

Narrow `y`'s domain to `x.A ∧ {B:⊥..{a:⊤}}` (contravariance), take the bound
step there, widen back (`x.A ≤₀ {B:..}` is primitive).  Three `≤₀` steps, no
receiver evidence. -/

def NarK : Ty ([],x) := .and (.sel (.var .here) lA) RB
def M1K : Ty [] := .all DomK (.all NarK (.sel (.var .here) lB))
def M2K : Ty [] := .all DomK (.all NarK T1)
def chainK : Cert [] := .seq (.step SrcK M1K) (.seq (.step M1K M2K) (.step M2K DstK))

theorem chainK_stepOnly : chainK.StepOnly := .seq .step (.seq .step .step)
theorem K_receiver_free_chain : checkC .nil chainK SrcK DstK = true := by decide

/-! ## N5: step and seq alone cannot relate the endpoints of `certY`

`y : ⊤ ⊢ ∀(x : {A : ⊤..{B:⊥..{a:⊤}}}) y.B ⇒ ∀(x : …) {a:⊤}` (`certY`).  An
invariant runs forward on codomains, under domains reachable from the final
domain; the outer receiver `y : ⊤` exposes nothing. -/

/-- Types reachable from `{B:⊥..{a:⊤}}` with no members in scope. -/
inductive TypIsh : {s : Sig} → Ty s → Prop where
  | top : TypIsh .top
  | typ : TypIsh (.typ A L U)
  | and : TypIsh S → TypIsh T → TypIsh (.and S T)

theorem TypIsh.weaken {s : Sig} {T : Ty s} (h : TypIsh T) : TypIsh (T.weaken (k := .var)) := by
  induction h with
  | top => exact .top
  | typ => exact .typ
  | and _ _ ih1 ih2 => exact .and ih1 ih2

theorem Γ0_y : Γ0.lookup .here = .top := rfl

theorem typ_step : {S T : Ty ([],x)} → Prim Γ0 S T → TypIsh S → TypIsh T
  | _, _, .refl, h => h
  | _, _, .top, _ => .top
  | _, _, .bot, h => by cases h
  | _, _, .andR h1 h2, h => .and (typ_step h1 h) (typ_step h2 h)
  | _, _, .andL1 h1, h => by cases h with | and h' _ => exact typ_step h1 h'
  | _, _, .andL2 h1, h => by cases h with | and _ h' => exact typ_step h1 h'
  | _, _, .fld _, h => by cases h
  | _, _, .typ _ _, _ => .typ
  | _, _, .all _ _, h => by cases h
  | _, _, .selU _, h => by cases h
  | _, _, .selL (x := x) e, _ => by
      cases x with
      | here => rw [Γ0_y] at e; cases e
      | there v => cases v

/-- Domains reachable from `D0`. -/
inductive DomR : Ty ([],x) → Prop where
  | top : DomR .top
  | typ : TypIsh U → DomR (.typ A L U)
  | and : DomR S → DomR T → DomR (.and S T)

theorem dom_step : {S T : Ty ([],x)} → Prim Γ0 S T → DomR S → DomR T
  | _, _, .refl, h => h
  | _, _, .top, _ => .top
  | _, _, .bot, h => by cases h
  | _, _, .andR h1 h2, h => .and (dom_step h1 h) (dom_step h2 h)
  | _, _, .andL1 h1, h => by cases h with | and h' _ => exact dom_step h1 h'
  | _, _, .andL2 h1, h => by cases h with | and _ h' => exact dom_step h1 h'
  | _, _, .fld _, h => by cases h
  | _, _, .typ _ hU, h => by cases h with | typ hT => exact .typ (typ_step hU hT)
  | _, _, .all _ _, h => by cases h
  | _, _, .selU _, h => by cases h
  | _, _, .selL (x := x) e, _ => by
      cases x with
      | here => rw [Γ0_y] at e; cases e
      | there v => cases v

theorem dom_chain {S T : Ty ([],x)} (h : Chain Γ0 S T) (hS : DomR S) : DomR T := by
  induction h with
  | refl => exact hS
  | cons p _ ih => exact ih (dom_step p hS)

/-- Codomains reachable from `y.B` under a reachable domain. -/
inductive CodOK : Ty ([],x,x) → Prop where
  | top : CodOK .top
  | selY : CodOK (.sel (.var (.there .here)) A)
  | selX : CodOK (.sel (.var .here) A)
  | typ : CodOK (.typ A L U)
  | and : CodOK S → CodOK T → CodOK (.and S T)

theorem TypIsh.codOK {T : Ty ([],x,x)} (h : TypIsh T) : CodOK T := by
  induction h with
  | top => exact .top
  | typ => exact .typ
  | and _ _ ih1 ih2 => exact .and ih1 ih2

theorem exp_domR {D : Ty ([],x)} (hD : DomR D) :
    ∀ {z : BVar ([],x,x) .var} {A : Label} {L U : Ty ([],x,x)},
    Exp z (D.weaken (k := .var)) A L U → TypIsh U := by
  induction hD with
  | top => intro z A L U e; cases e
  | typ hU =>
      intro z A L U e
      simp only [Ty.weaken, Ty.rename] at e
      cases e; exact hU.weaken
  | and _ _ ih1 ih2 =>
      intro z A L U e
      simp only [Ty.weaken, Ty.rename] at e
      cases e with
      | andL e => exact ih1 e
      | andR e => exact ih2 e

theorem cod_step {D : Ty ([],x)} (hD : DomR D) :
    {C C' : Ty ([],x,x)} → Prim (Γ0.cons D) C C' → CodOK C → CodOK C'
  | _, _, .refl, h => h
  | _, _, .top, _ => .top
  | _, _, .bot, h => by cases h
  | _, _, .andR h1 h2, h => .and (cod_step hD h1 h) (cod_step hD h2 h)
  | _, _, .andL1 h1, h => by cases h with | and h' _ => exact cod_step hD h1 h'
  | _, _, .andL2 h1, h => by cases h with | and _ h' => exact cod_step hD h1 h'
  | _, _, .fld _, h => by cases h
  | _, _, .typ _ _, _ => .typ
  | _, _, .all _ _, h => by cases h
  | _, _, .selU (x := x) e, _ => by
      cases x with
      | here => exact (exp_domR hD e).codOK
      | there x =>
          cases x with
          | here => cases e
          | there v => cases v
  | _, _, .selL (x := x) _, _ => by
      cases x with
      | here => exact .selX
      | there x =>
          cases x with
          | here => exact .selY
          | there v => cases v

theorem domR_D0 : DomR D0 := .typ (.typ)

/-- Function types whose codomain stays in `CodOK` whenever their domain is
reachable from `D0` (the final domain). -/
inductive Inv : Ty ([],x) → Prop where
  | top : Inv .top
  | fn : (Chain Γ0 D0 D → CodOK C) → Inv (.all D C)
  | and : Inv S → Inv T → Inv (.and S T)

theorem inv_step : {S T : Ty ([],x)} → Prim Γ0 S T → Inv S → Inv T
  | _, _, .refl, h => h
  | _, _, .top, _ => .top
  | _, _, .bot, h => by cases h
  | _, _, .andR h1 h2, h => .and (inv_step h1 h) (inv_step h2 h)
  | _, _, .andL1 h1, h => by cases h with | and h' _ => exact inv_step h1 h'
  | _, _, .andL2 h1, h => by cases h with | and _ h' => exact inv_step h1 h'
  | _, _, .fld _, h => by cases h
  | _, _, .typ _ _, h => by cases h
  | _, _, .all hD hC, h => by
      cases h with
      | fn hb =>
          refine .fn (fun hc => ?_)
          exact cod_step (dom_chain hc domR_D0) hC (hb (hc.snoc hD))
  | _, _, .selU _, h => by cases h
  | _, _, .selL (x := x) e, _ => by
      cases x with
      | here => rw [Γ0_y] at e; cases e
      | there v => cases v

theorem inv_chain {S T : Ty ([],x)} (h : Chain Γ0 S T) (hS : Inv S) : Inv T := by
  induction h with
  | refl => exact hS
  | cons p _ ih => exact ih (inv_step p hS)

/-- **No receiver-free chain** (`≤₀` steps only) relates the endpoints that
the scoped certificate `certY` relates. -/
theorem Y_no_receiver_free_chain : ¬ Chain Γ0 SrcY DstY := by
  intro h
  have hinv := inv_chain h (.fn (fun _ => .selY))
  cases hinv with
  | fn hb => have := hb .refl; cases this


/-- No step-only certificate relates the endpoints of `certY`. -/
theorem Y_no_receiver_free_coercion : ¬ ∃ c : Cert ([],x), c.StepOnly ∧ CTy Γ0 c SrcY DstY :=
  fun hc => Y_no_receiver_free_chain (stepOnly_iff_chain.mp hc)

end Selective
