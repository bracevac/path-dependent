import Coercions.Oopsla16.Lemmas

/-!
# `Htp` must have no packing rule

`HasType` has both `T_VarPack` and `T_VarUnpack` (`dot.v:231-240`), but `Htp`
has only `htp_unpack` (`dot.v:385-388`).  This module shows that the asymmetry
is load-bearing: in an isolated extension that adds the missing packing rule,
and changes nothing else, a two-object store admits a closed subtyping
derivation between two recursive types that gives an ordinary object the
bottom type.

The construction is the one of `DotToFCdot/RecursiveSelectionCounterexample`,
transported to the reference calculus.  Everything except `htp_pack` is an
existing rule, and every existing derivation is reused through the `old`
constructors, so the extension is conservative over `Oopsla16` by construction.
-/

namespace Oopsla16.PackingCounterexample

open FCdot (Kind Sig BVar Rename)

/-! ## The isolated extension

Only `Stp`, `Htp` and `HasType` are re-declared, each embedding the existing
judgment through `old`, and only the rules the construction uses are repeated.
`htp_pack` is the single new rule; it is the exact mirror of `T_VarPack`. -/

mutual

/-- Subtyping, extended only by being able to call the extended `Htp`. -/
inductive StpP : {σ s : Sig} → Store σ σ → Ctx σ s → Ty σ s → Ty σ s → Type where
  /-- Any existing derivation. -/
  | old : Stp G Γ T1 T2 → StpP G Γ T1 T2
  | stp_typ : StpP G Γ T3 T1 → StpP G Γ T2 T4 → StpP G Γ (.TTyp l T1 T2) (.TTyp l T3 T4)
  | stp_sel1 {x : BVar s .var} {T2 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x (.TTyp l .TBot T2) →
      StpP G Γ (.TSel (.abs x) l) (T2.rename (renameUpTo x))
  | stp_sel2 {x : BVar s .var} {T1 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x (.TTyp l T1 .TTop) →
      StpP G Γ (T1.rename (renameUpTo x)) (.TSel (.abs x) l)
  | stp_bindx : StpP G (Γ.cons T1) T1 T2 → StpP G Γ (.TBind T1) (.TBind T2)
  | stp_trans : StpP G Γ T1 T2 → StpP G Γ T2 T3 → StpP G Γ T1 T3

/-- Variable typing for selections, with the packing rule added. -/
inductive HtpP : {σ s : Sig} → Store σ σ → Ctx σ s → (x : BVar s .var) →
    Ty σ (scopeUpTo x) → Type where
  | htp_var : HtpP G Γ x (Γ.lookupAt x)
  | htp_unpack {x : BVar s .var} {TX : Ty σ (scopeUpTo x,x)} :
      HtpP G Γ x (.TBind TX) → HtpP G Γ x (TX.substVr (.abs (varUpTo x)))
  /-- **The new rule.**  The mirror of `T_VarPack` (`dot.v:231-235`), which the
  reference deliberately omits from `htp`. -/
  | htp_pack {x : BVar s .var} {TX : Ty σ (scopeUpTo x,x)} :
      HtpP G Γ x (TX.substVr (.abs (varUpTo x))) → HtpP G Γ x (.TBind TX)
  | htp_sub {x : BVar s .var} {T1 T2 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x T1 → StpP G (Γ.upTo x) T1 T2 → HtpP G Γ x T2

end

/-! ## The store

One namespace object `p` with two type members, and one ordinary object `q`
with a single type member.  Labels are positional, so in `p` the member `B`
has label `0` and `C` has label `1`.

```text
p.B = {A : D .. D'}
p.C = {K : p.B .. p.C} ∧ ({missing : ∀(_:⊤) ⊤} ∧ ⊥)
D   = μ _. p.B          D' = μ _. p.C
q.A = D
``` -/

/-- The label of `p`'s first type member. -/
abbrev B : Lb := 0
/-- The label of `p`'s second type member. -/
abbrev C : Lb := 1
/-- The type member inside `p.B`, and `q`'s only member. -/
abbrev A : Lb := 0
/-- The type member inside `p.C` whose bounds are the bad pair. -/
abbrev K : Lb := 1
/-- A method `p.C` claims to have and `q` does not. -/
abbrev missing : Lb := 2

/-- The store scope: `p` then `q`. -/
abbrev S2 : Sig := ([],x),x

/-- `p`, the older location. -/
abbrev p : BVar S2 .var := .there .here
/-- `q`, the newer location. -/
abbrev q : BVar S2 .var := .here

/-- `p.B`. -/
abbrev pB : Ty S2 s := .TSel (.conc p) B
/-- `p.C`. -/
abbrev pC : Ty S2 s := .TSel (.conc p) C

/-- `D = μ _. p.B`, a recursive type whose body ignores its self. -/
abbrev D : Ty S2 s := .TBind pB
/-- `D' = μ _. p.C`. -/
abbrev D' : Ty S2 s := .TBind pC

/-- The body of `p.B`. -/
abbrev Bbody : Ty S2 s := .TTyp A D D'
/-- The body of `p.C`. -/
abbrev Cbody : Ty S2 s :=
  .TAnd (.TTyp K pB pC) (.TAnd (.TFun missing .TTop .TTop) .TBot)

/-- `p`'s definitions: `B` at position `0`, `C` at position `1`. -/
abbrev pDefs : Dms S2 s := .dcons (.dty Cbody) (.dcons (.dty Bbody) .dnil)
/-- `q`'s single definition, `A = D`. -/
abbrev qDefs : Dms S2 s := .dcons (.dty D) .dnil

/-- The store. -/
abbrev G : Store S2 S2 := .cons (.cons .nil pDefs) qDefs

example : (G.lookup p).get? B = some (.dty Bbody) := rfl
example : (G.lookup p).get? C = some (.dty Cbody) := rfl
example : (G.lookup q).get? A = some (.dty D) := rfl
example : (G.lookup q).get? missing = none := rfl

/-! ## The derivation

Under the self assumption `z : p.B`, the bounds of `z.A` give `D <: D'`.  The
packing step then turns `z : p.B` into `z : D`, subsumption gives `z : D'`, and
unpacking gives `z : p.C`.  Reading the bounds of `z.K` proves `p.B <: p.C`,
which `stp_bindx` abstracts to `D <: D'` in the empty context. -/

/-- The context of the `stp_bindx` premise: the self at its opened type. -/
abbrev Gz : Ctx S2 ([],x) := Ctx.nil.cons pB
/-- The self. -/
abbrev z : BVar ([],x) .var := .here

/-- `z : {A : D .. D'}`, from `p`'s definition of `B`. -/
def bMember : HtpP G Gz z Bbody :=
  .htp_sub .htp_var (.old (.stp_strong_sel1 (T2 := Bbody) rfl (Stp.refl _)))

/-- `D <: z.A`. -/
def dLower : StpP G Gz D (.TSel (.abs z) A) :=
  .stp_sel2 (.htp_sub bMember (.stp_typ (.old (Stp.refl _)) (.old .stp_top)))

/-- `z.A <: D'`. -/
def dUpper : StpP G Gz (.TSel (.abs z) A) D' :=
  .stp_sel1 (.htp_sub bMember (.stp_typ (.old .stp_bot) (.old (Stp.refl _))))

/-- `D <: D'`, under the self assumption. -/
def dSub : StpP G Gz D D' := .stp_trans dLower dUpper

/-- **The step the reference forbids.**  `z : p.B` becomes `z : D`, inside the
judgment that subtyping's type selections go through. -/
def zPacked : HtpP G Gz z D := .htp_pack .htp_var

/-- and then `z : p.C`. -/
def zAsC : HtpP G Gz z pC := .htp_unpack (.htp_sub zPacked dSub)

/-- `z : {K : p.B .. p.C}`. -/
def kMember : HtpP G Gz z (.TTyp K pB pC) :=
  .htp_sub zAsC
    (.old (.stp_trans (.stp_strong_sel1 (T2 := Cbody) rfl (Stp.refl _))
      (.stp_and11 (Stp.refl _))))

/-- The `stp_bindx` premise: `p.B <: p.C` under `z : p.B`. -/
def premise : StpP G Gz pB pC :=
  .stp_trans
    (.stp_sel2 (.htp_sub kMember (.stp_typ (.old (Stp.refl _)) (.old .stp_top))))
    (.stp_sel1 (.htp_sub kMember (.stp_typ (.old .stp_bot) (.old (Stp.refl _)))))

/-- `μ _. p.B <: μ _. p.C`, in the empty context, over an ordinary store. -/
def bad : StpP G Ctx.nil D D' := .stp_bindx premise

/-! ## A stuck program

Term typing needs only three of its rules on top of the existing judgment. -/

/-- Term typing over the extended subtyping. -/
inductive HasTypeP : {σ s : Sig} → Store σ σ → Ctx σ s → Tm σ s → Ty σ s → Type where
  /-- Any existing derivation. -/
  | old : HasType G Γ t T → HasTypeP G Γ t T
  | T_VarPack : HasTypeP G Γ (.tvar v) (T.substVr v) → HasTypeP G Γ (.tvar v) (.TBind T)
  | T_VarUnpack : HasTypeP G Γ (.tvar v) (.TBind T) → HasTypeP G Γ (.tvar v) (T.substVr v)
  | T_App :
      HasTypeP G Γ t1 (.TFun l T1 T2.weaken) → HasTypeP G Γ t2 T1 →
      HasTypeP G Γ (.tapp t1 l t2) T2
  | T_Sub : HasTypeP G Γ t T1 → StpP G Γ T1 T2 → HasTypeP G Γ t T2

/-- `q` at its precise type, by the ordinary rule for a stored object. -/
def qTyped : HasType G Ctx.nil (.tvar (.conc q)) (.TAnd (.TTyp A D D) .TTop) :=
  .T_Vary (x := q) (ds := qDefs) (T := .TAnd (.TTyp A D D) .TTop) (.D_Typ .D_Nil) rfl

/-- `q : {A : D .. D}`. -/
def qAsDecl : HasTypeP G Ctx.nil (.tvar (.conc q)) (.TTyp A D D) :=
  .T_Sub (.old qTyped) (.old (.stp_and11 (Stp.refl _)))

/-- Widening `q`'s upper bound by `bad` gives it `p.B`. -/
def qAsB : HasTypeP G Ctx.nil (.tvar (.conc q)) pB :=
  .T_Sub qAsDecl
    (.stp_trans (.stp_typ (.old (Stp.refl _)) bad)
      (.old (.stp_strong_sel2 (T1 := Bbody) rfl (Stp.refl _))))

/-- Pack, subsume by `bad`, unpack: `q : p.C`. -/
def qAsC : HasTypeP G Ctx.nil (.tvar (.conc q)) pC :=
  .T_VarUnpack (.T_Sub (.T_VarPack qAsB) bad)

/-- `p.C`'s upper bound contains bottom, so `q : ⊥`. -/
def qBottom : HasTypeP G Ctx.nil (.tvar (.conc q)) .TBot :=
  .T_Sub qAsC
    (.old (.stp_trans (.stp_strong_sel1 (T2 := Cbody) rfl (Stp.refl _))
      (.stp_and12 (.stp_and12 (Stp.refl _)))))

/-- Invoking a method `q` does not have. -/
abbrev badTerm : Tm S2 [] := .tapp (.tvar (.conc q)) missing (.tvar (.conc q))

/-- It is well typed at `⊤`. -/
def badTerm_typed : HasTypeP G Ctx.nil badTerm .TTop :=
  .T_App (T1 := .TTop) (T2 := .TTop)
    (.T_Sub qBottom (.old (.stp_bot (T := .TFun missing .TTop .TTop))))
    (.T_Sub qBottom (.old (.stp_bot (T := .TTop))))

/-- It is not an answer. -/
theorem badTerm_not_answer : ¬ badTerm.IsAnswer := by
  intro h; exact h

/-- It does not step: `q` has no member at `missing`, and both operands are
already concrete variables. -/
theorem badTerm_stuck :
    ¬ ∃ (σ' : Sig) (g : Grows S2 σ') (G' : Store σ' σ') (t' : Tm σ' []),
        Step g G badTerm G' t' := by
  rintro ⟨σ', g, G', t', h⟩
  cases h with
  | ST_AppAbs hf =>
      rw [show (G.lookup q).get? missing = none from rfl] at hf
      cases hf
  | ST_App1 h => cases h
  | ST_App2 h => cases h

/-- Adding the packing rule to `Htp` breaks type safety: over an ordinary
store, a closed program is well typed at `⊤`, is not an answer, and cannot
step.  Every rule but `htp_pack` is a rule of `Oopsla16`. -/
theorem packing_is_unsound :
    Nonempty (HasTypeP G Ctx.nil badTerm .TTop) ∧
      ¬ badTerm.IsAnswer ∧
      ¬ ∃ (σ' : Sig) (g : Grows S2 σ') (G' : Store σ' σ') (t' : Tm σ' []),
          Step g G badTerm G' t' :=
  ⟨⟨badTerm_typed⟩, badTerm_not_answer, badTerm_stuck⟩

end Oopsla16.PackingCounterexample
