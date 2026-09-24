import Coercions.Separation.FCdot.CheckerCompleteness
import Coercions.Separation.FCdot.Store

namespace Separation

/-!
# Term examples: cells, fresh packs and kills in the checker

Kernel `decide` facts on the checker for the terms and rules of plan-5h S0.5.
They import the checker and the store alone, so they build before the
renaming and substitution lemmas of the kill half (group g6) and before the
machine.

* A cell round trip at the type level: `newLet ⟨ℓ, r⟩ = new x in read r`
  and `... in write r x` check, and a write into a binder that is no cell
  does not.
* The name half of C2 and C7: a fresh pack of the cell's location consumes
  it, and the `letexF` body that unpacks the pack may write the payload,
  whose location is the opened name, and may not write the cell itself,
  whose location the head killed.  The same stale write checks in the body
  context of a head that consumed nothing.
* A program value holds no cell, the congruence of `∃ᶠ` checks, and the
  reshaped `let` over a head that consumes nothing is the base rule.
* W1 (decision 38) and O1 (decision 39): the programs of the weakening and
  ownership rounds, refused where the rules refuse them and typed at the ghost
  a step gives where the rounds say they type.
-/

namespace FCdot

namespace TermExamples

/-- A unit binder `x`. -/
abbrev Γ0 : Ctx ([] ,x) := Ctx.nil.cons (.opaque (Ty.capt [] Shape.top))
abbrev x0 : BVar ([] ,x) .var := .here
abbrev U0 : Ty ([] ,x) := Ty.capt [] Shape.top

/-- The signature of a cell body: `x`, a location `ℓ`, the cell `r`. -/
abbrev S1 : Sig := ((([] ,x) ,c) ,x)
abbrev Γc : Ctx S1 := Γ0.cellCtx U0
abbrev r : BVar S1 .var := .here
abbrev ℓ : BVar S1 .cap := .there .here
abbrev x1 : BVar S1 .var := .there (.there .here)

/-! ## A cell round trip -/

/-- A read of the fresh cell, charged to the location the body may consume. -/
abbrev fRead : CapCo S1 :=
  .trans (.modeLe (.var r) .ro .eps)
    (.trans (.capvar (.var r)) (.modeLe (.cvar ℓ) .eps .consume))

abbrev tRead : Tm ([] ,x) := .newLet (.var x0) (.read (.var r)) [] fRead

theorem read_checks : checkTm Γ0 tRead U0 = true := by decide +kernel

/-- A write of `x` into the fresh cell. -/
abbrev fWrite : CapCo S1 :=
  .union (.trans (.capvar (.var r)) (.modeLe (.cvar ℓ) .eps .consume))
    (.trans (.capvar (.var x1)) (.elem [] [.mode .consume (.cvar ℓ)]))

abbrev tWrite : Tm ([] ,x) := .newLet (.var x0) (.write (.var r) (.var x1)) [] fWrite

theorem write_checks : checkTm Γ0 tWrite Ty.unit = true := by decide +kernel

/-- The arguments swapped: `x` is no cell. -/
theorem write_noCell_refused :
    checkTm Γ0 (.newLet (.var x0) (.write (.var x1) (.var r)) [] fWrite) Ty.unit = false := by
  decide +kernel

/-! ## A fresh pack consumes, and its unpacking kills -/

/-- The payload type: a cell at the opened name. -/
abbrev Tcell1 : Ty (S1 ,c) := Ty.capt [CapAtom.cvar .here] (Shape.cell (Ty.capt [] Shape.top))

/-- The residual: the cell's location is below the heir that owns it. -/
abbrev ePack : LeCo (Sig.scope S1) :=
  .capt (.refl (Shape.cell (Ty.capt [] Shape.top)))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there (.there .here)))])

abbrev head : Tm S1 := .atom (.packF [CapAtom.cvar ℓ] ePack (.var r))

theorem head_synth : synthTmE Γc head = some (∃ᶠ Tcell1) := by decide +kernel

/-- The head consumes `ℓ`. -/
theorem head_uses : head.uses = [CapAtom.var r, CapAtom.mode .consume (CapAtom.cvar ℓ)] := by
  decide +kernel

/-- The signature of the unpacking body: the opened name `κ` and the payload
`y` over the cell body. -/
abbrev S2 : Sig := ((S1 ,c) ,x)
abbrev y : BVar S2 .var := .here
abbrev κ2 : BVar S2 .cap := .there .here
abbrev r2 : BVar S2 .var := .there (.there .here)
abbrev ℓ2 : BVar S2 .cap := .there (.there (.there .here))
abbrev x2 : BVar S2 .var := .there (.there (.there (.there .here)))

abbrev Γf : Ctx S2 := Γc.freshCtx head.uses Tcell1

/-- In the body the opened name is live. -/
theorem opened_accessible : decide (Γf.Accessible [CapAtom.cvar κ2]) = true := by
  decide +kernel

/-- In the body the consumed location is killed. -/
theorem consumed_inaccessible : decide (Γf.Accessible [CapAtom.cvar ℓ2]) = false := by
  decide +kernel

/-- The opened name claims the consumed location. -/
theorem opened_claims : Γc.claimsFor head.uses = [CapAtom.cvar ℓ] := by decide +kernel

abbrev D2 : CaptureSet S2 :=
  [CapAtom.cvar ℓ2, CapAtom.mode .consume (CapAtom.cvar κ2)]

abbrev gY : CapCo S2 :=
  .union
    (.trans (.capvar (.var y))
      (.trans (.modeLe (.cvar κ2) .eps .consume) (.elem [.mode .consume (.cvar κ2)] D2)))
    (.trans (.capvar (.var x2)) (.elem [] D2))

abbrev gR : CapCo S2 :=
  .union (.trans (.capvar (.var r2)) (.elem [.cvar ℓ2] D2))
    (.trans (.capvar (.var x2)) (.elem [] D2))

abbrev fOuter : CapCo S1 :=
  .union
    (.union (.trans (.capvar (.var r)) (.modeLe (.cvar ℓ) .eps .consume))
      (.refl [.mode .consume (.cvar ℓ)]))
    (.modeLe (.cvar ℓ) .eps .consume)

/-- The body writes the payload. -/
abbrev tPayload : Tm ([] ,x) :=
  .newLet (.var x0) (.letexF head (.write (.var y) (.var x2)) [CapAtom.cvar ℓ] gY) [] fOuter

/-- The body writes the cell whose location the head consumed. -/
abbrev tStale : Tm ([] ,x) :=
  .newLet (.var x0) (.letexF head (.write (.var r2) (.var x2)) [CapAtom.cvar ℓ] gR) [] fOuter

theorem payload_write_checks : checkTm Γ0 tPayload Ty.unit = true := by decide +kernel

theorem stale_write_refused : checkTm Γ0 tStale Ty.unit = false := by decide +kernel

/-- The stale write fails only its accessibility: in the body context of a
head that consumed nothing it checks. -/
theorem stale_write_checks_unkilled :
    checkTm ((Γc.consC (.loc true [])).cons (.opaque Tcell1))
      (.write (.var r2) (.var x2)) Ty.unit = true := by
  decide +kernel

/-! ## Cell freedom, congruence and the base `let` -/

/-- A cell is a value of the cell type, and no program value. -/
theorem cell_value_synth : synthValue Γc (.cell (.cvar ℓ) (.var x1))
    = some (Ty.capt [CapAtom.cvar ℓ] (Shape.cell (Ty.capt [] Shape.top))) := by
  decide +kernel

theorem cell_term_refused : synthTmE Γc (.val (.cell (.cvar ℓ) (.var x1))) = none := by
  decide +kernel

abbrev Tκ : Ty (([] ,x) ,c) := Ty.capt [CapAtom.cvar .here] Shape.top

theorem congF_checks :
    checkELe Γ0 (.congF (.capt (.refl Shape.top) (.refl [CapAtom.cvar .here])))
      (∃ᶠ Tκ) (∃ᶠ Tκ) = true := by
  decide +kernel

/-- The reshaped `let` over a head that consumes nothing is the base rule. -/
theorem base_let_checks :
    checkTm Γ0 (.let (.atom (.plain (.var x0))) (.atom (.plain (.var .here)))
      [] (.trans (.capvar (.var .here)) (.elem [] []))) U0 = true := by
  decide +kernel

/-! ## W1, the weakening round (plan-5h S0.12, decision 38)

g6's counterexamples to capture weakening, `unkill` and the retyping
composite, and the design round's (G), (P), (F) and (E), as facts of the
checker after decision 38.  (A), (B) and (G) consume a root or a variable
declared at one at a kill site, and `Ctx.KillOk` refuses them.  (C), (D) and
(P) pack an outer name under a pi codomain, and the premise `f.charge = []`
of the pi rule refuses them, while the same cast with a codomain that packs
nothing checks.  (F) reads an outer cell recapped to the body root after a
local consumption, and the expansion of a root into every binder that is no
root refuses it before entering.  (E) is a closure that packs a name another
heir owns, which types under the heir, since term typing reads no mask.  The
refutation's program of the weakening round checks, and its outer frame's
declared set has no consumed leaf. -/

namespace W1

/-! ### (A) and (B): a kill set that consumes the universal root -/

abbrev TA : Ty ([] ,x) := Ty.capt [] Shape.top
abbrev ΓA : Ctx ([] ,x) := Ctx.nil.cons (.opaque (Ty.capt [] Shape.top))
abbrev ePackA : LeCo (Sig.scope ([] ,x)) := .capt (.refl Shape.top) (.refl [])
abbrev headA : Tm ([] ,x) :=
  .atom (.pack [] (.elem [] [.top]) ePackA (.var .here))
abbrev fA : CapCo ((([] ,x) ,c) ,x) :=
  .trans (.capvar (.var .here)) (.elem [] [.mode .consume .top, .cvar (.there .here)])
abbrev tA : Tm ([] ,x) :=
  .letex headA (.atom (.plain (.var .here))) [.mode .consume .top]
    (.modeLe .top .eps .consume) fA

theorem killOk_A : decide (ΓA.KillOk [.mode .consume .top]) = false := by decide +kernel
theorem tA_refused : checkTm ΓA tA TA = false := by decide +kernel

abbrev Tx : Ty [] := Ty.capt [.top] (Shape.cell (Ty.capt [] Shape.top))
abbrev ΓB : Ctx ([] ,x) := Ctx.nil.cons (.opaque Tx)
abbrev f0 : CapCo (([] ,x) ,x) :=
  .trans (.capvar (.var .here)) (.modeLe .top .eps .consume)
abbrev headB : Tm ([] ,x) :=
  .let (.atom (.plain (.var .here))) (.atom (.plain (.var .here))) [.mode .consume .top] f0
abbrev fB : CapCo (([] ,x) ,x) :=
  .trans (.modeLe (.var (.there .here)) .ro .eps) (.capvar (.var (.there .here)))
abbrev tB : Tm ([] ,x) := .let headB (.read (.var (.there .here))) [.top] fB
abbrev UB : Ty ([] ,x) := Ty.capt [] Shape.top

theorem killOk_B : decide (ΓB.KillOk headB.uses) = false := by decide +kernel
theorem tB_refused : checkTm ΓB tB UB = false := by decide +kernel

/-! ### (G): a kill through a variable declared at a consuming root -/

abbrev ΓG : Ctx (([] ,x) ,x) :=
  (Ctx.nil.cons (.opaque (Ty.capt [.top] (Shape.cell (Ty.capt [] Shape.top))))).cons
    (.opaque (Ty.capt [.mode .consume .top] Shape.top))
abbrev xG : BVar (([] ,x) ,x) .var := .there .here
abbrev yG : BVar (([] ,x) ,x) .var := .here
abbrev fG : CapCo ((([] ,x) ,x) ,x) := .refl [.mode .ro (.var (.there xG))]
abbrev tG : Tm (([] ,x) ,x) :=
  .let (.atom (.plain (.var yG))) (.read (.var (.there xG))) [.mode .ro (.var xG)] fG
abbrev UG : Ty (([] ,x) ,x) := Ty.capt [] Shape.top

theorem killOk_G : decide (ΓG.KillOk (Tm.atom (.plain (.var yG))).uses) = false := by
  decide +kernel
theorem tG_refused : checkTm ΓG tG UG = false := by decide +kernel

/-! ### (C) and (D): a pi codomain that packs an outer name -/

abbrev SC : Sig := ([] ,c) ,x
abbrev T1 : Dom ([] ,c) := Ty.capt [] Shape.top
abbrev U1 : Cod ([] ,c) := .ty (Ty.capt [] Shape.top)
abbrev T1' : Dom SC := Ty.capt [] Shape.top
abbrev U2 : Cod SC := ∃ᶠ (Ty.capt [] Shape.top)
abbrev ΓC : Ctx SC := (Ctx.nil.consC (.loc true [])).cons (.opaque (Ty.capt [] (Π(T1) U1)))
abbrev κBody : BVar (Sig.body SC) .cap := .there (.there (.there (.there .here)))
abbrev eDom : LeCo (Sig.scope SC) := .capt (.refl Shape.top) (.refl [])
abbrev eRes : LeCo (Sig.scope (Sig.body SC)) := .capt (.refl Shape.top) (.refl [])
abbrev fCod : ELeCo (Sig.body SC) := .packF [.cvar κBody] eRes
abbrev aC : Atom SC := .cast (.var .here) (.capt (.pi eDom fCod) (.refl []))
abbrev TC : Ty SC := Ty.capt [] (Π(T1') U2)

theorem charge_C : fCod.charge = [.mode .consume (.cvar κBody)] := rfl
theorem aC_refused : checkAtom ΓC aC TC = false := by decide +kernel

/-- The same arrow cast with a codomain that packs nothing checks. -/
abbrev aC0 : Atom SC := .cast (.var .here) (.capt (.pi eDom (.packF [] eRes)) (.refl []))
theorem aC0_checks : checkAtom ΓC aC0 TC = true := by decide +kernel

abbrev ΓD : Ctx ([] ,c) := Ctx.nil.consC (.loc true [])
abbrev S0D : Ty ([] ,c) := Ty.capt [] (Π(T1) U1)
abbrev TD : Ty ([] ,c) := Ty.capt [] (Π(T1) (∃ᶠ (Ty.capt [] Shape.top)))
abbrev fCodD : ELeCo (Sig.body ([] ,c)) := .packF [.cvar (.there (.there (.there .here)))]
  (.capt (.refl Shape.top) (.refl []))
abbrev ED : LeCo ([] ,c) := .capt (.pi (.capt (.refl Shape.top) (.refl [])) fCodD) (.refl [])

theorem ED_refused : checkLe ΓD ED S0D TD = false := by decide +kernel

/-! ### (P): one arrow cast packing an outer name, called twice -/

abbrev SP : Sig := (([] ,c) ,x) ,x
abbrev ΓP : Ctx SP :=
  ((Ctx.nil.consC (.loc true [])).cons
    (.opaque (Ty.capt [] (Π(Ty.capt [] Shape.top) (.ty (Ty.capt [] Shape.top)))))).cons
    (.opaque (Ty.capt [] Shape.top))
abbrev κPB : BVar (Sig.body SP) .cap := .there (.there (.there (.there (.there .here))))
abbrev fP : BVar SP .var := .there .here
abbrev xP : BVar SP .var := .here
abbrev eDomP : LeCo (Sig.scope SP) := .capt (.refl Shape.top) (.refl [])
abbrev eResP : LeCo (Sig.scope (Sig.body SP)) := .capt (.refl Shape.top) (.refl [])
abbrev fCodP : ELeCo (Sig.body SP) := .packF [.cvar κPB] eResP
abbrev aP : Atom SP := .cast (.var fP) (.capt (.pi eDomP fCodP) (.refl []))
abbrev callP : Tm SP := .app aP (.var xP)
abbrev callP2 : Tm ((SP ,c) ,x) :=
  (callP.rename (Rename.succ (k := .cap))).rename (Rename.succ (k := .var))
abbrev innerP : Tm ((SP ,c) ,x) :=
  .letexF callP2 (.val (.obj [] .nil .nil .nil)) []
    (.elem [] [.mode .consume (.cvar (.there .here))])
abbrev progP : Tm SP :=
  .letexF callP innerP [.var fP, .var xP]
    (.elem innerP.uses
      [.var (.there (.there fP)), .var (.there (.there xP)), .mode .consume (.cvar (.there .here))])

theorem callP_refused : synthTmE ΓP callP = none := by decide +kernel
theorem progP_refused : checkTm ΓP progP Ty.unit = false := by decide +kernel

/-! ### (F): a read at the body root after a body-local consumption -/

abbrev S1 : Sig := ((([] ,x) ,c) ,x)
abbrev Tunit {s : Sig} : Ty s := Ty.capt [] Shape.top
abbrev ΓF : Ctx S1 := (Ctx.nil.cons (.opaque (Ty.capt [] Shape.top))).cellCtx Tunit
abbrev x0 : BVar S1 .var := .there (.there .here)
abbrev SB : Sig := Sig.body S1
abbrev SU : Sig := (SB ,c) ,x
abbrev SV : Sig := (SU ,c) ,x
abbrev r0B : BVar SB .var := .there (.there (.there .here))
abbrev r0U : BVar SU .var := .there (.there r0B)
abbrev r0V : BVar SV .var := .there (.there r0U)
abbrev ePk : LeCo (Sig.scope SU) :=
  .capt (.refl (Shape.cell (Ty.capt [] Shape.top)))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there (.there .here)))])
abbrev hd : Tm SU := .atom (.packF [CapAtom.cvar (.there .here)] ePk (.var .here))
abbrev rd : Tm SV := .read (.recap (.var r0V) (.level (.var r0V) .top))
abbrev Uv : CaptureSet SU := [.mode .ro (.var r0U)]
abbrev fv : CapCo SV :=
  .elem rd.uses [.mode .ro (.var r0V), .mode .consume (.cvar (.there .here))]
abbrev uF : Tm SU := .letexF hd rd Uv fv
abbrev Unl : CaptureSet SB := [.mode .ro (.var r0B)]
abbrev Dnl : CaptureSet SU := [.mode .ro (.var r0U), .mode .consume (.cvar (.there .here))]
abbrev fnl : CapCo SU :=
  .union
    (.union
      (.trans (.trans (.capvar (.var .here)) (.modeLe (.cvar (.there .here)) .eps .consume))
        (.elem [.mode .consume (.cvar (.there .here))] Dnl))
      (.elem [.mode .consume (.cvar (.there .here))] Dnl))
    (.elem [.mode .ro (.var r0U)] Dnl)
abbrev bodyF : Tm SB := .newLet (.var .here) uF Unl fnl
abbrev AF : CaptureSet S1 := [.mode .ro (.var .here)]
abbrev gF : CapCo SB := .elem bodyF.uses [.mode .ro (.var r0B), .var .here]
abbrev vF : Value S1 := .lam AF Tunit bodyF gF
abbrev TvF : Ty S1 := Ty.capt AF (Π(Tunit) (.ty Tunit))

/-- The body is refused before entering, as the entered body is. -/
theorem vF_refused : checkValue ΓF vF TvF = false := by decide +kernel
theorem entered_refused : checkTm ΓF (bodyF.subst (Subst.enter (.var x0))) Tunit = false := by
  decide +kernel

/-- The failing premise is the read: `⊤` names the killed local location. -/
abbrev ΓVbody : Ctx SV := (((ΓF.body Tunit).cellCtx Tunit).freshCtx hd.uses
  (Ty.capt [CapAtom.cvar .here] (Shape.cell (Ty.capt [] Shape.top))))
theorem body_read_refused : decide (ΓVbody.Accessible [.top]) = false := by decide +kernel

/-! ### (E): a closure that packs a name another heir owns -/

abbrev ℓE : BVar S1 .cap := .there .here
abbrev rE : BVar S1 .var := .here
abbrev ℓEB : BVar SB .cap := .there (.there (.there ℓE))
abbrev rEB : BVar SB .var := .there (.there (.there rE))
abbrev ePackB : LeCo (Sig.scope SB) :=
  .capt (.refl (Shape.cell (Ty.capt [] Shape.top)))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there ℓEB))])
abbrev bodyE : Tm SB := .atom (.packF [CapAtom.cvar ℓEB] ePackB (.var rEB))
abbrev AE : CaptureSet S1 := [.var rE, .mode .consume (.cvar ℓE)]
abbrev gE : CapCo SB := .elem bodyE.uses [.var rEB, .mode .consume (.cvar ℓEB), .var .here]
abbrev UE : Cod S1 := ∃ᶠ (Ty.capt [CapAtom.cvar .here] (Shape.cell (Ty.capt [] Shape.top)))
abbrev vE : Value S1 := .lam AE Tunit bodyE gE
abbrev TvE : Ty S1 := Ty.capt AE (Π(Tunit) UE)

theorem vE_checks : checkValue ΓF vE TvE = true := by decide +kernel

/-- **(E) types under the heir** of the location it packs. -/
theorem vE_weak_own_checks :
    checkValue (ΓF.consC (.own true [CapAtom.cvar ℓE])) (vE.rename Rename.succ)
      (TvE.rename Rename.succ) = true := by
  decide +kernel

/-- And the reduct of `appVar` at a call that returns it. -/
abbrev TvE2 : Ty ((S1 ,c) ,x) :=
  (TvE.rename (Rename.succ (k := .cap))).rename (Rename.succ (k := .var))
abbrev Tg : Ty S1 := Ty.capt [] (Π(Ty.capt [] Shape.top) (.ty TvE2))
abbrev ΓE2 : Ctx ((S1 ,x) ,c) :=
  (ΓF.cons (.opaque Tg)).consC (.own true [CapAtom.cvar (.there ℓE)])

theorem reductE_checks :
    checkTmE ΓE2 (.val ((vE.rename Rename.succ).rename Rename.succ))
      (.ty ((TvE.rename Rename.succ).rename Rename.succ)) = true := by decide +kernel

/-! ### The refutation's program of the weakening round -/

abbrev Tf : Ty ([] ,x) := Ty.capt [.top] (Π(Tunit) (.ty Tunit))
abbrev SR : Sig := ([] ,x) ,x
abbrev Γ1 : Ctx SR := Γ0.cons (.opaque Tf)
abbrev fR : BVar SR .var := .here
abbrev xR : BVar SR .var := .there .here
abbrev H : Tm SR := tPayload.rename Rename.succ
abbrev SW : Sig := SR ,x
abbrev Bhead : Tm SW := .app (.var (.there .here)) (.var (.there (.there .here)))
abbrev BR : Tm SW :=
  .let Bhead (.val (.obj [] .nil .nil .nil)) [.mode .consume .top]
    (.elem [] [.mode .consume .top])
abbrev UR : CaptureSet SR := [.var fR, .var xR, .mode .consume .top]
abbrev PR : Tm SR := .let H BR UR (.elem BR.uses (UR.rename Rename.succ))

theorem PR_checks : checkTm Γ1 PR Tunit = true := by decide +kernel

/-- The store after the unpack of the refutation's run: a location, the cell,
the heir.  The outer frame's declared set consumes the masked location as a
name and has no consumed leaf, so its frame clause holds at every ghost. -/
abbrev SS : Sig := ((SR ,c) ,x) ,c
abbrev Γs2 : Ctx SS := (Γ1.cellCtx Tunit).consC (.own true [CapAtom.cvar (.there .here)])
abbrev ℓs : BVar SS .cap := .there (.there .here)
abbrev ρR : Rename SR SS :=
  ((Rename.succ (k := .cap)).comp (Rename.succ (k := .var))).comp (Rename.succ (k := .cap))
abbrev U2R : CaptureSet SS := UR.rename ρR

theorem ℓs_masked : decide (Γs2.Masked ℓs) = true := by decide +kernel
theorem ℓs_consumedName : decide (ℓs ∈ Γs2.consumedNames U2R) = true := by decide +kernel
theorem leaves_U2 : Γs2.consumedLeaves U2R = [] := by decide +kernel

end W1

/-! ## O1, the ownership round (plan-5h S0.12, decision 39)

Kernel `decide` facts on the checker of decision 39, rebuilt from the scratch
modules of the ownership round (`Scratch_OwnChecks.lean`,
`Scratch_RefOwnCons.lean`, `Scratch_RefOwnWeak.lean`, `Scratch_InertP.lean`
under `notes-separation-s0/own-note/`).

Refused at typing time: the clause refutation's P1 by the argument premise of
`app`, F7 and its twin in P1's body by the bound premise of `letex`, F6's
body by the second conjunct of `ArgSep`, and T1's call by `ConsumeOk` of the
callee's set.  Typed at the ghost the step gives, with the witness killed and
owned by the live heir: the reducts of g6r's three counterexamples, of F9, of
F10 and of the refuter's S1 to S3. -/

namespace O1

/-! ### g6r's store: the unit, a location `ℓ`, a cell `r` at `ℓ`, an heir `h` of `ℓ` -/

namespace G

abbrev u0 : Value [] := .obj [] .nil .nil .nil
abbrev T0 : Ty [] := (μ (Telescope.ofLiteral .nil .nil [])) ^ []
abbrev Γ1 : Ctx ([] ,x) := Ctx.nil.cons (.transparent T0 u0.witnesses u0.capWitnesses u0.fieldLabels)
abbrev Γ2 : Ctx (([] ,x) ,c) := Γ1.consC (.loc true [])
abbrev cv : Value (([] ,x) ,c) := .cell (.cvar .here) (.var (.there .here))
abbrev Tc : Ty (([] ,x) ,c) :=
  Ty.capt [CapAtom.cvar .here] (Shape.cell ((T0.rename Rename.succ).rename Rename.succ))
abbrev S3 : Sig := (([] ,x) ,c) ,x
abbrev Γ3 : Ctx S3 := Γ2.cons (.transparent Tc cv.witnesses cv.capWitnesses cv.fieldLabels)
abbrev S4 : Sig := S3 ,c
abbrev Γ4 : Ctx S4 := Γ3.consC (.own true [CapAtom.cvar (.there .here)])
abbrev r4 : BVar S4 .var := .there .here
abbrev ℓ4 : BVar S4 .cap := .there (.there .here)
abbrev h4 : BVar S4 .cap := .here
abbrev Scell : Shape S4 := (Γ4.lookupTy r4).shape
abbrev TH : Ty S4 := Ty.capt [CapAtom.cvar h4] Scell
abbrev aH : Atom S4 :=
  .recap (.var r4) (.trans (.capvar (.var r4)) (.ownLe (.cvar h4) [CapAtom.cvar ℓ4]))
abbrev Tcont : Ty S4 := Ty.capt [] (μ (Telescope.ofLiteral .nil .nil []))

theorem aH_checks : checkAtom Γ4 aH TH = true := by decide +kernel

/-- In the store, `ℓ` killed in the ghost is owned by the live heir `h`, so it
is effectively live though its bit is killed. -/
theorem ℓ_owned : Γ4.ownsB h4 ℓ4 = true := by decide +kernel
theorem ℓ_killed : ((Γ4.killNames [ℓ4]).lookupCap ℓ4).live = false := by decide +kernel
theorem ℓ_effLive : decide ((Γ4.killNames [ℓ4]).EffLive ℓ4) = true := by decide +kernel

/-! #### g6r's first counterexample: a read at the ghost `[ℓ]` -/

abbrev body : Tm (S4 ,x) := .read (.recap (.var .here) (.refl [CapAtom.var .here]))

theorem cex1_body_checks :
    checkTm ((Γ4.killNames [ℓ4]).cons (.opaque TH)) body (Tcont.rename Rename.succ) = true := by
  decide +kernel
/-- The reduct checks at the ghost: the read is at `{r}`, whose name `ℓ` the
live heir owns. -/
theorem cex1_reduct_checks : checkTm (Γ4.killNames [ℓ4]) (body.substAtom aH) Tcont = true := by
  decide +kernel
theorem cex1_premise : decide ((Γ4.killNames [ℓ4]).Accessible [CapAtom.var r4]) = true := by
  decide +kernel

/-! #### g6r's second counterexample: no ghost, the body consumes the masked `ℓ` -/

abbrev S5 : Sig := S4 ,x
abbrev ePk : LeCo (Sig.scope S5) :=
  .capt (.refl ((((Scell.rename Rename.succ).rename Rename.succ).rename Rename.succ)))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there (.there ℓ4)))])
abbrev hd5 : Tm S5 := .atom (.packF [CapAtom.cvar (.there ℓ4)] ePk (.var (.there r4)))
abbrev rd5 : Tm ((S5 ,c) ,x) :=
  .read (.recap (.var (.there (.there .here))) (.refl [CapAtom.var (.there (.there .here))]))
abbrev U5 : CaptureSet S5 := [CapAtom.mode .ro (.var .here)]
abbrev f5 : CapCo ((S5 ,c) ,x) :=
  .elem rd5.uses [CapAtom.mode .ro (.var (.there (.there .here))),
    CapAtom.mode .consume (.cvar (.there .here))]
abbrev body5 : Tm S5 := .letexF hd5 rd5 U5 f5

theorem cex2_body_checks :
    checkTm (Γ4.cons (.opaque TH)) body5 (Tcont.rename Rename.succ) = true := by decide +kernel
theorem cex2_reduct_checks : checkTm Γ4 (body5.substAtom aH) Tcont = true := by decide +kernel

/-! #### F6: a phantom consumption at a call, refused by the second conjunct

A closure `g` at `{ℓ}` whose domain is a cell.  A body over `x : cell ^ {h}`
calls `g` recapped to `{consume ℓ}` with `x`.  The names of `x` are `{h}`, and
`h` may own the consumed `ℓ`. -/

abbrev x0B : BVar (((S4 ,c) ,c) ,x) .var :=
  .there (.there (.there (.there (.there (.there .here)))))
abbrev ℓB : BVar (((S4 ,c) ,c) ,x) .cap := .there (.there (.there ℓ4))
abbrev Tdom4 : Dom S4 := Ty.capt [CapAtom.cvar .here] (Scell.rename Rename.succ)
abbrev Tg : Ty S4 := Ty.capt [CapAtom.cvar ℓ4] (Π(Tdom4) (.ty Ty.unit))
abbrev tgt6 : CaptureSet (((S4 ,c) ,c) ,x) := [CapAtom.cvar ℓB, CapAtom.var .here]
abbrev gv : Value S4 :=
  .lam [CapAtom.cvar ℓ4] Tdom4 (.write (.var .here) (.var x0B))
    (.union (.elem [.var .here] tgt6) (.trans (.capvar (.var x0B)) (.elem [] tgt6)))

theorem gv_checks : checkValue Γ4 gv Tg = true := by decide +kernel

abbrev S6 : Sig := S4 ,x
abbrev Γ6 : Ctx S6 := Γ4.cons (.transparent Tg .nil .nil [])
abbrev g6 : BVar (S6 ,x) .var := .there .here
abbrev ℓ6 : BVar (S6 ,x) .cap := .there (.there ℓ4)
abbrev TH6 : Ty S6 := TH.rename Rename.succ
abbrev body6 : Tm (S6 ,x) :=
  .app (.recap (.var g6) (.trans (.capvar (.var g6)) (.modeLe (.cvar ℓ6) .eps .consume)))
    (.recap (.var .here) (.refl [CapAtom.var .here]))

theorem f6_body_refused : checkTm (Γ6.cons (.opaque TH6)) body6 Ty.unit = false := by
  decide +kernel
theorem f6_argSep_second :
    decide ((Γ6.cons (.opaque TH6)).ArgSep [CapAtom.var .here]
      [CapAtom.mode .consume (.cvar ℓ6)]) = false := by decide +kernel

/-! #### F9 and F7 over the store of the unit, `ℓ` and the cell `r` -/

abbrev Tg9 : Ty S3 :=
  Ty.capt [CapAtom.mode .consume (.cvar (.there .here))] (μ (Telescope.ofLiteral .nil .nil []))
abbrev gv9 : Value S3 := .obj [CapAtom.mode .consume (.cvar (.there .here))] .nil .nil .nil
theorem gv9_checks : checkValue Γ3 gv9 Tg9 = true := by decide +kernel

abbrev S9 : Sig := S3 ,x
abbrev Γ9 : Ctx S9 := Γ3.cons (.transparent Tg9 gv9.witnesses gv9.capWitnesses gv9.fieldLabels)
abbrev g9 : BVar S9 .var := .here
abbrev r9 : BVar S9 .var := .there .here
abbrev ℓ9 : BVar S9 .cap := .there (.there .here)
abbrev Scell9 : Shape S9 := (Γ9.lookupTy r9).shape

/-- F7: `let _ = g in letex ⟨c, y⟩ = pack [ℓ] r in write y x`.  The `let`
kills `ℓ`, and the bound `{ℓ}` of the `letex` is killed in its body's kill
context. -/
abbrev eB9 : LeCo (Sig.scope S9) :=
  .capt (.refl ((Scell9.rename Rename.succ).rename Rename.succ))
    (.eqToLe (.symm (.instC (.cvar .here) [CapAtom.cvar (.there (.there ℓ9))])))
abbrev headB9 : Tm S9 := .atom (.pack [CapAtom.cvar ℓ9] (.refl [CapAtom.cvar ℓ9]) eB9 (.var r9))
abbrev x9y : BVar ((S9 ,c) ,x) .var := .there (.there (.there (.there (.there .here))))
abbrev DB9 : CaptureSet ((S9 ,c) ,x) :=
  [CapAtom.cvar (.there (.there ℓ9)), CapAtom.cvar (.there .here)]
abbrev fB9 : CapCo ((S9 ,c) ,x) :=
  .union (.trans (.capvar (.var .here)) (.elem [CapAtom.cvar (.there .here)] DB9))
    (.trans (.capvar (.var x9y)) (.elem [] DB9))
abbrev tB9 : Tm S9 :=
  .letex headB9 (.write (.var .here) (.var x9y)) [CapAtom.cvar ℓ9] (.refl [CapAtom.cvar ℓ9]) fB9
abbrev fL9 : CapCo (S9 ,x) :=
  .union (.trans (.capvar (.var (.there r9))) (.refl [CapAtom.cvar (.there ℓ9)]))
    (.refl [CapAtom.cvar (.there ℓ9)])
abbrev tL9 : Tm S9 :=
  .let (.atom (.plain (.var g9))) (tB9.rename Rename.succ) [CapAtom.cvar ℓ9] fL9

theorem f7_refused : checkTm Γ9 tL9 Ty.unit = false := by decide +kernel
theorem f7_at_ghost_refused : checkTm (Γ9.killNames [ℓ9]) tB9 Ty.unit = false := by
  decide +kernel
theorem f7_bound : decide ((Γ9.killNames [ℓ9]).Accessible [CapAtom.cvar ℓ9]) = false := by
  decide +kernel

end G

/-! ### Over the cell context of this module -/

namespace Cell

abbrev Tu {s : Sig} : Ty s := Ty.capt [] Shape.top

/-- g6r's third counterexample: the frame body reads through the payload.
The reduct runs at the frame's ghost, the head's kill `[ℓ]`, under the heir. -/
abbrev rdU : Tm ((S1 ,c) ,x) := .read (.recap (.var .here) (.refl [CapAtom.var .here]))
abbrev payload : Atom (S1 ,c) :=
  .cast (Atom.weaken (k := .cap) (.var r)) (ePack.subst Subst.instRoot)
abbrev Γheir : Ctx (S1 ,c) := (Γc.killNames [ℓ]).consC (.own true [CapAtom.cvar ℓ])

theorem cex3_frame_checks : checkTm (Γc.freshCtx head.uses Tcell1) rdU Tu = true := by
  decide +kernel
theorem cex3_ghost : Γc.ownClosure (Γc.consumedNames head.uses) = [ℓ] := by decide +kernel
theorem cex3_reduct_checks : checkTm Γheir (rdU.substAtom payload) Tu = true := by
  decide +kernel
theorem cex3_witness : (Γheir.lookupCap (.there ℓ)).live = false ∧
    decide (Γheir.EffLive (.there ℓ)) = true := by decide +kernel

/-! #### P1: a stale cell passed to a function after its location's transfer -/

abbrev Tdom : Dom S1 := Ty.capt [CapAtom.cvar (.there ℓ)] (Shape.cell Tu)
abbrev Tf : Ty S1 := Ty.capt [] (Π(Tdom) (.ty Ty.unit))
abbrev SF : Sig := S1 ,x
abbrev fF : BVar SF .var := .here
abbrev rF : BVar SF .var := .there .here
abbrev ℓF : BVar SF .cap := .there (.there .here)
abbrev ePackF : LeCo (Sig.scope SF) :=
  .capt (.refl (Shape.cell Tu))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there (.there (.there .here))))])
abbrev headF : Tm SF := .atom (.packF [CapAtom.cvar ℓF] ePackF (.var rF))
abbrev TcellF : Ty (SF ,c) := Ty.capt [CapAtom.cvar .here] (Shape.cell Tu)
abbrev S2F : Sig := (SF ,c) ,x
abbrev f2 : BVar S2F .var := .there (.there .here)
abbrev r2F : BVar S2F .var := .there (.there (.there .here))
abbrev ℓ2F : BVar S2F .cap := .there (.there (.there (.there .here)))
abbrev x2F : BVar S2F .var := .there (.there (.there (.there (.there .here))))
abbrev ΓF : Ctx SF := Γc.cons (.opaque Tf)
abbrev ΓB : Ctx S2F := ΓF.freshCtx headF.uses TcellF

/-- **P1 is refused at the call** by the argument premise. -/
theorem p1_refused : checkTm ΓB (.app (.var f2) (.var r2F)) Ty.unit = false := by
  decide +kernel
theorem p1_arg : decide (ΓB.Accessible [CapAtom.var r2F]) = false := by decide +kernel

/-- F7's twin in P1's body: a B2 pack of the stale cell at the witness `{ℓ}`. -/
abbrev eB2 : LeCo (Sig.scope S2F) :=
  .capt (.refl (Shape.cell Tu))
    (.eqToLe (.symm (.instC (.cvar .here) [CapAtom.cvar (.there (.there ℓ2F))])))
abbrev headB2 : Tm S2F :=
  .atom (.pack [CapAtom.cvar ℓ2F] (.refl [CapAtom.cvar ℓ2F]) eB2 (.var r2F))
abbrev DB2 : CaptureSet ((S2F ,c) ,x) :=
  [CapAtom.cvar (.there (.there ℓ2F)), CapAtom.cvar (.there .here)]
abbrev fB2 : CapCo ((S2F ,c) ,x) :=
  .union (.trans (.capvar (.var .here)) (.elem [CapAtom.cvar (.there .here)] DB2))
    (.trans (.capvar (.var (.there (.there x2F)))) (.elem [] DB2))
abbrev tB2 : Tm S2F :=
  .letex headB2 (.write (.var .here) (.var (.there (.there x2F)))) [CapAtom.cvar ℓ2F]
    (.refl [CapAtom.cvar ℓ2F]) fB2

theorem b2_refused : checkTm ΓB tB2 Ty.unit = false := by decide +kernel
theorem b2_bound : decide (ΓB.Accessible [CapAtom.cvar ℓ2F]) = false := by decide +kernel

/-! #### F10: a consumption through the payload's root, read on the callee's set -/

abbrev Tfun : Ty S1 := Ty.capt [CapAtom.cvar ℓ] (Π(Ty.capt [] Shape.top) (.ty Ty.unit))
abbrev S10 : Sig := S1 ,x
abbrev Γ10 : Ctx S10 := Γc.cons (.opaque Tfun)
abbrev f10 : BVar S10 .var := .here
abbrev ℓ10 : BVar S10 .cap := .there (.there .here)
abbrev x10 : BVar S10 .var := .there (.there (.there .here))
abbrev ePk10 : LeCo (Sig.scope S10) :=
  .capt (.refl (Π(Ty.capt [] Shape.top) (.ty Ty.unit)))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there ℓ10))])
abbrev head10 : Tm S10 := .atom (.packF [CapAtom.cvar ℓ10] ePk10 (.var f10))
abbrev yB : BVar ((S10 ,c) ,x) .var := .here
abbrev κB : BVar ((S10 ,c) ,x) .cap := .there .here
abbrev xB : BVar ((S10 ,c) ,x) .var := .there (.there x10)
abbrev body10 : Tm ((S10 ,c) ,x) :=
  .app (.recap (.var yB) (.modeLe (.var yB) .eps .consume)) (.var xB)
abbrev D10 : CaptureSet ((S10 ,c) ,x) := [CapAtom.mode .consume (.cvar κB)]
abbrev g10 : CapCo ((S10 ,c) ,x) :=
  .union (.trans (.capvar (.var yB)) (.modeLe (.cvar κB) .eps .consume))
    (.trans (.capvar (.var xB)) (.elem [] D10))
abbrev t10 : Tm S10 := .letexF head10 body10 [] g10
abbrev payload10 : Atom (S10 ,c) :=
  .cast (Atom.weaken (k := .cap) (.var f10)) (ePk10.subst Subst.instRoot)
abbrev Γr10 : Ctx (S10 ,c) := (Γ10.killNames [ℓ10]).consC (.own true [CapAtom.cvar ℓ10])

theorem f10_checks : checkTm Γ10 t10 Ty.unit = true := by decide +kernel
theorem f10_reduct_checks : checkTm Γr10 (body10.substAtom payload10) Ty.unit = true := by
  decide +kernel
/-- `consume f` on the payload's root consumes nothing, and its names are
effectively live. -/
theorem f10_consumeOk :
    decide (Γr10.ConsumeOk [CapAtom.mode .consume (.var (.there f10))]) = true := by
  decide +kernel
theorem f10_access :
    decide (Γr10.Accessible [CapAtom.mode .consume (.var (.there f10))]) = true := by
  decide +kernel

/-! #### F9: a second kill of the transferred name, after the transfer -/

abbrev Tg9 : Ty S1 := Ty.capt [CapAtom.mode .consume (.cvar ℓ)] Shape.top
abbrev S9 : Sig := S1 ,x
abbrev Γ9 : Ctx S9 := Γc.cons (.opaque Tg9)
abbrev g9 : BVar S9 .var := .here
abbrev r9 : BVar S9 .var := .there .here
abbrev ℓ9 : BVar S9 .cap := .there (.there .here)
abbrev ePk9 : LeCo (Sig.scope S9) :=
  .capt (.refl (Shape.cell Tu))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there ℓ9))])
abbrev head9 : Tm S9 := .atom (.packF [CapAtom.cvar ℓ9] ePk9 (.var r9))
abbrev S9b : Sig := (S9 ,c) ,x
abbrev y9 : BVar S9b .var := .here
abbrev κ9 : BVar S9b .cap := .there .here
abbrev g9b : BVar S9b .var := .there (.there g9)
abbrev ℓ9b : BVar S9b .cap := .there (.there ℓ9)
abbrev rd9 : Tm (S9b ,x) :=
  .read (.recap (.var (.there y9)) (.refl [CapAtom.var (.there y9)]))
abbrev Ul9 : CaptureSet S9b := [CapAtom.mode .ro (.var y9)]
abbrev fl9 : CapCo (S9b ,x) :=
  .elem [CapAtom.mode .ro (.var (.there y9))] [CapAtom.mode .ro (.var (.there y9))]
abbrev inner9 : Tm S9b := .let (.atom (.plain (.var g9b))) rd9 Ul9 fl9
abbrev D9 : CaptureSet S9b :=
  [CapAtom.mode .consume (.cvar ℓ9b), CapAtom.mode .consume (.cvar κ9)]
abbrev f9 : CapCo S9b :=
  .union (.trans (.capvar (.var g9b)) (.elem [CapAtom.mode .consume (.cvar ℓ9b)] D9))
    (.trans (.roMap (.capvar (.var y9)))
      (.trans (.modeLe (.cvar κ9) .ro .consume) (.elem [CapAtom.mode .consume (.cvar κ9)] D9)))
abbrev t9 : Tm S9 := .letexF head9 inner9 [CapAtom.mode .consume (.cvar ℓ9)] f9
abbrev payload9 : Atom (S9 ,c) :=
  .cast (Atom.weaken (k := .cap) (.var r9)) (ePk9.subst Subst.instRoot)
abbrev Γr9 : Ctx (S9 ,c) := (Γ9.killNames [ℓ9]).consC (.own true [CapAtom.cvar ℓ9])

theorem f9_checks : checkTm Γ9 t9 Tu = true := by decide +kernel
theorem f9_ghost : Γ9.ownClosure (Γ9.consumedNames head9.uses) = [ℓ9] := by decide +kernel
/-- The reduct checks at the frame's ghost: the inner read is at `{r}`, whose
name `ℓ` the live heir owns. -/
theorem f9_reduct_checks : checkTm Γr9 (inner9.substAtom payload9) Tu = true := by
  decide +kernel

end Cell

/-! ### The refuter's S1 to S3: a `consume` on the payload variable is inert -/

namespace R

open G (u0 T0 Γ1 Γ2 cv Tc S3 Γ3)

abbrev T0c {s : Sig} : Ty s := Ty.capt [] (μ (Telescope.ofLiteral .nil .nil []))
abbrev r3 : BVar S3 .var := .here
abbrev ℓ3 : BVar S3 .cap := .there .here
abbrev Scell3 : Shape S3 := (Γ3.lookupTy r3).shape
abbrev ePk3 : LeCo (Sig.scope S3) :=
  .capt (.refl ((Scell3.rename Rename.succ).rename Rename.succ))
    (.ownLe (.cvar .here) [CapAtom.cvar (.there (.there ℓ3))])
abbrev head3 : Tm S3 := .atom (.packF [CapAtom.cvar ℓ3] ePk3 (.var r3))
abbrev SB : Sig := (S3 ,c) ,x
abbrev DomU {s : Sig} : Dom s := Ty.capt [] Shape.top

/-- `g = λ^{consume y}(q : ⊤). q` and `k = λ^{consume y}(p : ⊤). g p` over the
payload `y` of the unpack. -/
abbrev Ag : CaptureSet SB := [CapAtom.mode .consume (.var .here)]
abbrev tgtG : CaptureSet (((SB ,c) ,c) ,x) :=
  [CapAtom.mode .consume (.var (.there (.there (.there .here)))), CapAtom.var .here]
abbrev gv : Value SB :=
  .lam Ag DomU (.atom (.plain (.var .here))) (.elem [CapAtom.var .here] tgtG)
abbrev Ak : CaptureSet (SB ,x) := [CapAtom.mode .consume (.var (.there .here))]
abbrev yK : BVar ((((SB ,x) ,c) ,c) ,x) .var := .there (.there (.there (.there .here)))
abbrev gK : BVar ((((SB ,x) ,c) ,c) ,x) .var := .there (.there (.there .here))
abbrev tgtK : CaptureSet ((((SB ,x) ,c) ,c) ,x) :=
  [CapAtom.mode .consume (.var yK), CapAtom.var .here]
abbrev evK : CapCo ((((SB ,x) ,c) ,c) ,x) :=
  .union (.trans (.capvar (.var gK)) (.elem [CapAtom.mode .consume (.var yK)] tgtK))
    (.elem [CapAtom.var .here] tgtK)
abbrev kv : Value (SB ,x) := .lam Ak DomU (.app (.var gK) (.var .here)) evK
abbrev u0In : BVar ((SB ,x) ,x) .var :=
  .there (.there (.there (.there (.there (.there .here)))))
abbrev inner : Tm (SB ,x) :=
  .let (.val kv) (.atom (.plain (.var u0In))) [] (.capvar (.var u0In))
abbrev body : Tm SB := .let (.val gv) inner [] (.elem [] [])
abbrev fX : CapCo SB := .elem [] [CapAtom.mode .consume (.cvar (.there .here))]
abbrev prog : Tm S3 := .letexF head3 body [] fX

abbrev payload : Atom (S3 ,c) :=
  .cast (Atom.weaken (k := .cap) (.var r3)) (ePk3.subst Subst.instRoot)
abbrev ΓhD : Ctx (S3 ,c) := (Γ3.killNames [ℓ3]).consC (.own true [CapAtom.cvar ℓ3])

/-- S1: the program checks, and its reduct checks at the frame's ghost. -/
theorem s1_checks : checkTm Γ3 prog T0c = true := by decide +kernel
theorem s1_ghost : Γ3.ownClosure (Γ3.consumedNames head3.uses) = [ℓ3] := by decide +kernel
theorem s1_reduct_checks : checkTm ΓhD (body.substAtom payload) T0c = true := by
  decide +kernel

/-- S2: F9's literal in the store, and a `let` of it that kills `ℓ` again in
the unpack body. -/
abbrev Tg9 : Ty S3 :=
  Ty.capt [CapAtom.mode .consume (.cvar (.there .here))] (μ (Telescope.ofLiteral .nil .nil []))
abbrev gv9 : Value S3 := .obj [CapAtom.mode .consume (.cvar (.there .here))] .nil .nil .nil
abbrev S9 : Sig := S3 ,x
abbrev Γ9 : Ctx S9 := Γ3.cons (.transparent Tg9 gv9.witnesses gv9.capWitnesses gv9.fieldLabels)
abbrev ℓ9 : BVar S9 .cap := .there (.there .here)
abbrev head9 : Tm S9 := head3.rename Rename.succ
abbrev SB9 : Sig := (S9 ,c) ,x
abbrev g9b : BVar SB9 .var := .there (.there .here)
abbrev ℓ9b : BVar SB9 .cap := .there (.there ℓ9)
abbrev κ9 : BVar SB9 .cap := .there .here
abbrev bodyS9 : Tm SB9 := body.rename (Rename.succ (k := .var)).lift.lift
abbrev D9 : CaptureSet SB9 := [CapAtom.mode .consume (.cvar ℓ9b), CapAtom.mode .consume (.cvar κ9)]
abbrev body9 : Tm SB9 :=
  .let (.atom (.plain (.var g9b))) (bodyS9.rename Rename.succ) [] (.elem [] [])
abbrev f9 : CapCo SB9 :=
  .trans (.capvar (.var g9b)) (.elem [CapAtom.mode .consume (.cvar ℓ9b)] D9)
abbrev prog9 : Tm S9 := .letexF head9 body9 [CapAtom.mode .consume (.cvar ℓ9)] f9
abbrev payload9 : Atom (S9 ,c) := payload.rename Rename.succ.lift
abbrev Γr9 : Ctx (S9 ,c) := (Γ9.killNames [ℓ9]).consC (.own true [CapAtom.cvar ℓ9])

theorem s2_checks : checkTm Γ9 prog9 T0c = true := by decide +kernel
theorem s2_reduct_checks : checkTm Γr9 (body9.substAtom payload9) T0c = true := by
  decide +kernel

/-- S3: the let form over g6r's store, the body of S1 over a binder
`x : cell ^ {h}` at the ghost `[ℓ]`. -/
abbrev Γ4 : Ctx (S3 ,c) := Γ3.consC (.own true [CapAtom.cvar ℓ3])
abbrev h4 : BVar (S3 ,c) .cap := .here
abbrev ℓ4 : BVar (S3 ,c) .cap := .there ℓ3
abbrev r4 : BVar (S3 ,c) .var := .there r3
abbrev TH : Ty (S3 ,c) := Ty.capt [CapAtom.cvar h4] ((Γ4.lookupTy r4).shape)
abbrev aH : Atom (S3 ,c) :=
  .recap (.var r4) (.trans (.capvar (.var r4)) (.ownLe (.cvar h4) [CapAtom.cvar ℓ4]))

theorem s3_body_checks :
    checkTm ((Γ4.killNames [ℓ4]).cons (.opaque TH)) body T0c = true := by decide +kernel
theorem s3_subst_checks :
    checkTm (Γ4.killNames [ℓ4]) (body.substAtom aH) T0c = true := by decide +kernel

end R

/-! ### T1: a callee recapped to `{consume ⊤ᶜ}` is refused on `ConsumeOk` -/

namespace T1

abbrev Tf : Ty [] := Ty.capt [] (Π(Ty.capt [.top] Shape.top) (.ty Ty.unit))
abbrev Γa : Ctx (([] ,x) ,x) :=
  (Ctx.nil.cons (.opaque Tf)).cons (.opaque (Ty.capt [.top] Shape.top))
abbrev fA : BVar (([] ,x) ,x) .var := .there .here
abbrev bA : BVar (([] ,x) ,x) .var := .here
abbrev Craise : CaptureSet (([] ,x) ,x) := [CapAtom.mode .consume .top]
abbrev aA : Atom (([] ,x) ,x) :=
  .recap (.var fA) (.trans (.capvar (.var fA)) (.elem [] Craise))
abbrev call : Tm (([] ,x) ,x) := .app aA (.var bA)

theorem t1_refused : synthTmE Γa call = none := by decide +kernel
theorem t1_consumeOk : decide (Γa.ConsumeOk Craise) = false := by decide +kernel

end T1

end O1

end TermExamples

end FCdot

end Separation
