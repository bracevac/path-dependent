import Coercions.Oopsla16.Lemmas

set_option autoImplicit false

/-!
# Recursive subtyping and packing in `Htp` are jointly unsound

`HasType` has both `T_VarPack` and `T_VarUnpack` (`dot.v:231-240`), but `Htp`,
the judgment that subtyping's type selections go through, has only
`htp_unpack` (`dot.v:380-383`).  Section 3 of the paper calls this the first of
two contractiveness restrictions, says both are "necessary for the proofs",
and conjectures that they "could be lifted without breaking soundness".

This module adds the missing rule and nothing else.  Over a two-object store,
the result is a closed program that is well typed at `⊤`, is not an answer, and
cannot step.

Three things about the scope of the result.

* **The second restriction is kept, and is satisfied.**  `htp_sub` still widens
  in `Γ.upTo x`.  Every use of it here is at the self introduced by
  `stp_bindx`, which is the newest binder, so `Γ.upTo z = Γ` and the reference's
  `length GL = S x` holds with `GU = []`.  The restriction is not stressed —
  it never constrains a selection on the innermost self — but neither is it
  lifted.
* **Most of the derivation needs no new rule.**  `dSubPlain` below derives
  `D <: D'` under `z : p.B` in the *unmodified* calculus.  `htp_pack` buys
  exactly one step: packing that same `z` so that `z.K` becomes readable.
* **The culprit is the interaction, not packing alone.**  WadlerFest DOT and
  pDOT take the `Sel` premise from ordinary typing, with recursive introduction
  available, and are sound — they have no `stp_bindx`.  What is unsound is
  recursive subtyping together with a packing rule in the selection judgment.

The extension is not a conservative extension: it proves `μ(_.p.B) <: μ(_.p.C)`,
which is a statement of the old vocabulary.  It is a *subsystem* of "Oopsla16
with `htp_pack`": every constructor below is either an existing rule with the
same indices, `htp_pack`, or an embedding of an existing derivation.  Nothing
in `Oopsla16` itself is changed.

The construction is the one of `DotToFCdot/RecursiveSelectionCounterexample`,
transported from the WadlerFest extension to the reference calculus.
-/

namespace Oopsla16.PackingCounterexample

open FCdot (Kind Sig BVar Rename)

/-! ## The isolated extension

Only the rules the construction uses are repeated; `old` embeds any existing
derivation.  `htp_pack` is the single new rule, and it is the exact converse of
`htp_unpack`: same `TX : Ty σ (scopeUpTo x,x)`, which is the reference's
`closed (S x) (length G1) 1 TX` (`dot.v:382`). -/

mutual

/-- Subtyping, extended only by being able to call the extended `Htp`. -/
inductive StpP : {σ s : Sig} → Store σ σ → Ctx σ s → Ty σ s → Ty σ s → Type where
  /-- Any existing derivation. -/
  | old {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 : Ty σ s} :
      Stp G Γ T1 T2 → StpP G Γ T1 T2
  | stp_typ {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 T2 T3 T4 : Ty σ s} :
      StpP G Γ T3 T1 → StpP G Γ T2 T4 → StpP G Γ (.TTyp l T1 T2) (.TTyp l T3 T4)
  | stp_sel1 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {x : BVar s .var}
      {T2 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x (.TTyp l .TBot T2) →
      StpP G Γ (.TSel (.abs x) l) (T2.rename (renameUpTo x))
  | stp_sel2 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {x : BVar s .var}
      {T1 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x (.TTyp l T1 .TTop) →
      StpP G Γ (T1.rename (renameUpTo x)) (.TSel (.abs x) l)
  | stp_bindx {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 : Ty σ (s,x)} :
      StpP G (Γ.cons T1) T1 T2 → StpP G Γ (.TBind T1) (.TBind T2)
  | stp_trans {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T3 : Ty σ s} :
      StpP G Γ T1 T2 → StpP G Γ T2 T3 → StpP G Γ T1 T3

/-- Variable typing for selections, with the packing rule added. -/
inductive HtpP : {σ s : Sig} → Store σ σ → Ctx σ s → (x : BVar s .var) →
    Ty σ (scopeUpTo x) → Type where
  | htp_var {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var} :
      HtpP G Γ x (Γ.lookupAt x)
  | htp_unpack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
      {TX : Ty σ (scopeUpTo x,x)} :
      HtpP G Γ x (.TBind TX) → HtpP G Γ x (TX.substVr (.abs (varUpTo x)))
  /-- **The new rule**, the converse of `htp_unpack` and the mirror of
  `T_VarPack` (`dot.v:231-235`), which the reference omits from `htp`. -/
  | htp_pack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
      {TX : Ty σ (scopeUpTo x,x)} :
      HtpP G Γ x (TX.substVr (.abs (varUpTo x))) → HtpP G Γ x (.TBind TX)
  | htp_sub {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
      {T1 T2 : Ty σ (scopeUpTo x)} :
      HtpP G Γ x T1 → StpP G (Γ.upTo x) T1 T2 → HtpP G Γ x T2

end

/-! ## The store

```text
p.B = {A : D .. D'}
p.C = {K : p.B .. p.C} ∧ ({missing : ∀(_:⊤) ⊤} ∧ ⊥)
D   = μ _. p.B          D' = μ _. p.C          q.A = D
```

Labels are positional, so in `p` the member `B` has label `0` and `C` has
label `1`.  Both `D` and `D'` ignore their self binder, which is why the result
does not depend on the closedness index a packing mirror is given. -/

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
abbrev pB {s : Sig} : Ty S2 s := .TSel (.conc p) B
/-- `p.C`. -/
abbrev pC {s : Sig} : Ty S2 s := .TSel (.conc p) C

/-- `D = μ _. p.B`, a recursive type whose body ignores its self. -/
abbrev D {s : Sig} : Ty S2 s := .TBind pB
/-- `D' = μ _. p.C`. -/
abbrev D' {s : Sig} : Ty S2 s := .TBind pC

/-- The body of `p.B`. -/
abbrev Bbody {s : Sig} : Ty S2 s := .TTyp A D D'
/-- The body of `p.C`. -/
abbrev Cbody {s : Sig} : Ty S2 s :=
  .TAnd (.TTyp K pB pC) (.TAnd (.TFun missing .TTop .TTop) .TBot)

/-- `p`'s definitions: `B` at position `0`, `C` at position `1`. -/
abbrev pDefs {s : Sig} : Dms S2 s := .dcons (.dty Cbody) (.dcons (.dty Bbody) .dnil)
/-- `q`'s single definition, `A = D`. -/
abbrev qDefs {s : Sig} : Dms S2 s := .dcons (.dty D) .dnil

/-- The store. -/
abbrev G : Store S2 S2 := .cons (.cons .nil pDefs) qDefs

example : (G.lookup p).get? B = some (.dty Bbody) := rfl
example : (G.lookup p).get? C = some (.dty Cbody) := rfl
example : (G.lookup q).get? A = some (.dty D) := rfl
example : (G.lookup q).get? missing = none := rfl

/-! ## What the unmodified calculus already proves

Under the self assumption `z : p.B`, the bounds of `z.A` already give
`D <: D'`.  No new rule is involved; this is the reference calculus. -/

/-- The context of the `stp_bindx` premise: the self at its opened type. -/
abbrev Gz : Ctx S2 ([],x) := Ctx.nil.cons pB
/-- The self, the newest binder. -/
abbrev z : BVar ([],x) .var := .here

/-- `z : {A : D .. D'}`, from `p`'s definition of `B`. -/
def bMemberPlain : Htp G Gz z Bbody :=
  .htp_sub .htp_var (.stp_strong_sel1 (T2 := Bbody) rfl (Stp.refl _))

/-- `D <: z.A`. -/
def dLowerPlain : Stp G Gz D (.TSel (.abs z) A) :=
  .stp_sel2 (.htp_sub bMemberPlain (.stp_typ (Stp.refl _) .stp_top))

/-- `z.A <: D'`. -/
def dUpperPlain : Stp G Gz (.TSel (.abs z) A) D' :=
  .stp_sel1 (.htp_sub bMemberPlain (.stp_typ .stp_bot (Stp.refl _)))

/-- `D <: D'` under the self assumption, in the **unmodified** calculus. -/
def dSubPlain : Stp G Gz D D' := .stp_trans dLowerPlain dUpperPlain

/-! ## What the packing rule adds

One step: `z : p.B` becomes `z : D`.  Everything after it follows. -/

/-- **The step the reference forbids.** -/
def zPacked : HtpP G Gz z D := .htp_pack .htp_var

/-- Subsuming by `dSubPlain` and unpacking gives `z : p.C`. -/
def zAsC : HtpP G Gz z pC := .htp_unpack (.htp_sub zPacked (.old dSubPlain))

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

/-! ## A stuck program -/

/-- Term typing over the extended subtyping. -/
inductive HasTypeP : {σ s : Sig} → Store σ σ → Ctx σ s → Tm σ s → Ty σ s → Type where
  /-- Any existing derivation. -/
  | old {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Tm σ s} {T : Ty σ s} :
      HasType G Γ t T → HasTypeP G Γ t T
  | T_VarPack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {v : Vr σ s} {T : Ty σ (s,x)} :
      HasTypeP G Γ (.tvar v) (T.substVr v) → HasTypeP G Γ (.tvar v) (.TBind T)
  | T_VarUnpack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {v : Vr σ s} {T : Ty σ (s,x)} :
      HasTypeP G Γ (.tvar v) (.TBind T) → HasTypeP G Γ (.tvar v) (T.substVr v)
  | T_App {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 T2 : Ty σ s}
      {t1 t2 : Tm σ s} :
      HasTypeP G Γ t1 (.TFun l T1 T2.weaken) → HasTypeP G Γ t2 T1 →
      HasTypeP G Γ (.tapp t1 l t2) T2
  | T_Sub {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Tm σ s} {T1 T2 : Ty σ s} :
      HasTypeP G Γ t T1 → StpP G Γ T1 T2 → HasTypeP G Γ t T2

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

/-- It is not an answer: it is an application, not a concrete variable. -/
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

/-- Adding the packing rule to `Htp` breaks type safety.  Over an ordinary
store, a closed program is well typed at `⊤`, is not an answer, and cannot
step, so the progress half of the reference's `type_safety`
(`dot_soundness.v:1131`) fails.  Every rule but `htp_pack` is a rule of
`Oopsla16`, and `htp_pack` is used exactly once, at `zPacked`. -/
theorem packing_is_unsound :
    Nonempty (HasTypeP G Ctx.nil badTerm .TTop) ∧
      ¬ badTerm.IsAnswer ∧
      ¬ ∃ (σ' : Sig) (g : Grows S2 σ') (G' : Store σ' σ') (t' : Tm σ' []),
          Step g G badTerm G' t' :=
  ⟨⟨badTerm_typed⟩, badTerm_not_answer, badTerm_stuck⟩

end Oopsla16.PackingCounterexample
