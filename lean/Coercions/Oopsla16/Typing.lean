import Coercions.Oopsla16.Context
import Coercions.Oopsla16.Semantics

/-!
# The four static judgments

`has_type`, `dms_has_type`, `stp` and `htp` of `dot.v:219-393`, as one mutual
family with the reference's 8 + 3 + 18 + 3 = 32 rules and its rule names.

The judgments live in `Type`, for the reason `Coercions.DotMNF.Typing` gives:
a translation into explicit evidence is a function on derivations and
therefore needs `Type`-valued elimination.

Every `closed` premise of the reference is gone, and with it every `open`
equation: intrinsic scoping discharges them.  What remains is exactly the
content.  Three places carry the calculus's soundness and are worth reading
against the Coq.

* `Htp` types a variable at a type of **its own prefix scope**, `Ty σ
  (scopeUpTo x)`, and `htp_sub` widens in `Γ.upTo x`.  That is the whole of
  the reference's `stp GL G1 T1 T2`, `length GL = S x`, `GH = GU ++ GL`
  (`dot.v:389-395`): hypotheses introduced after `x` — in particular the self
  assumption of an enclosing `stp_bindx` — are not in scope for the widening,
  and here they are not in scope in the ordinary sense of the word.
* `Htp` has `htp_unpack` and **no packing rule**, while `HasType` has both
  `T_VarPack` and `T_VarUnpack`.  A type selection used in subtyping may
  therefore not be justified by first packing its receiver.  This is the rule
  whose absence `DotToFCdot.RecursiveSelectionCounterexample` exploits in the
  WadlerFest extension.
* `stp_strong_sel1` and `stp_strong_sel2` check the stored definition's bound
  in the **empty** local scope, and their endpoint is weakened by `renameNil`.

There is no reflexivity rule: the reference derives reflexivity by induction
on a type-size measure (`dot.v:874-913`).  `stp_trans` is primitive.  There is
no `stp_bind2`; the paper conjectures that the restriction could be lifted but
does not prove it.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-- `eq_some`, `dot.v:216`: an optional annotation is absent or matches.  It
is what lets `dfun` be written in Church or in Curry style. -/
def EqSome {α : Type} (o : Option α) (a : α) : Prop := o = none ∨ o = some a

mutual

/-- `has_type`, `dot.v:219-260`. -/
inductive HasType : {σ s : Sig} → Store σ σ → Ctx σ s → Tm σ s → Ty σ s → Type where
  /-- `T_Vary`, `dot.v:220-226`: a concrete variable is typed by re-typing the
  definitions stored at its location, with its own location substituted for
  the self. -/
  | T_Vary {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar σ .var}
      {ds : Dms σ ([],x)} {T : Ty σ ([],x)} :
      DmsHasType G (Ctx.nil.cons T) ds T →
      ds.substVr (.conc x) = G.lookup x →
      HasType G Γ (.tvar (.conc x)) ((T.substVr (.conc x)).rename renameNil)
  /-- `T_Varz`, `dot.v:227-230`. -/
  | T_Varz {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var} :
      HasType G Γ (.tvar (.abs x)) (Γ.lookup x)
  /-- `T_VarPack`, `dot.v:231-235`: recursive introduction, in either zone. -/
  | T_VarPack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {v : Vr σ s}
      {T : Ty σ (s,x)} :
      HasType G Γ (.tvar v) (T.substVr v) →
      HasType G Γ (.tvar v) (.TBind T)
  /-- `T_VarUnpack`, `dot.v:236-240`: recursive elimination, in either zone. -/
  | T_VarUnpack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {v : Vr σ s}
      {T : Ty σ (s,x)} :
      HasType G Γ (.tvar v) (.TBind T) →
      HasType G Γ (.tvar v) (T.substVr v)
  /-- `T_Obj`, `dot.v:241-245`: an object literal.  Its definitions are typed
  under the *opened* self type, which is why `Ctx.cons` must admit an entry
  mentioning its own binder. -/
  | T_Obj {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {ds : Dms σ (s,x)}
      {T : Ty σ (s,x)} :
      DmsHasType G (Γ.cons T) ds T →
      HasType G Γ (.tobj ds) (.TBind T)
  /-- `T_App`, `dot.v:246-250`: invocation whose result does not mention the
  parameter, which here is the weakening `T2.weaken`. -/
  | T_App {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 T2 : Ty σ s}
      {t1 t2 : Tm σ s} :
      HasType G Γ t1 (.TFun l T1 T2.weaken) →
      HasType G Γ t2 T1 →
      HasType G Γ (.tapp t1 l t2) T2
  /-- `T_AppVar`, `dot.v:251-256`: dependent invocation, the argument being a
  variable. -/
  | T_AppVar {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 : Ty σ s}
      {T2 : Ty σ (s,x)} {t1 : Tm σ s} {v : Vr σ s} :
      HasType G Γ t1 (.TFun l T1 T2) →
      HasType G Γ (.tvar v) T1 →
      HasType G Γ (.tapp t1 l (.tvar v)) (T2.substVr v)
  /-- `T_Sub`, `dot.v:257-260`. -/
  | T_Sub {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Tm σ s} {T1 T2 : Ty σ s} :
      HasType G Γ t T1 → Stp G Γ T1 T2 → HasType G Γ t T2

/-- `dms_has_type`, `dot.v:263-282`.  A definition list has a right-nested
intersection whose labels are the positions in the list. -/
inductive DmsHasType : {σ s : Sig} → Store σ σ → Ctx σ s → Dms σ s → Ty σ s → Type where
  /-- `D_Nil`, `dot.v:264-265`. -/
  | D_Nil {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} : DmsHasType G Γ .dnil .TTop
  /-- `D_Typ`, `dot.v:266-271`: a type member is exact, and its label is the
  length of the remaining list. -/
  | D_Typ {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T11 : Ty σ s} {ds : Dms σ s}
      {TS : Ty σ s} :
      DmsHasType G Γ ds TS →
      DmsHasType G Γ (.dcons (.dty T11) ds) (.TAnd (.TTyp ds.length T11 T11) TS)
  /-- `D_Fun`, `dot.v:272-282`: a method member.  The body is typed under the
  parameter, which does not mention itself, hence the weakening. -/
  | D_Fun {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {OT11 : Option (Ty σ s)}
      {T11 : Ty σ s} {OT12 : Option (Ty σ (s,x))} {T12 : Ty σ (s,x)}
      {t12 : Tm σ (s,x)} {ds : Dms σ s} {TS : Ty σ s} :
      DmsHasType G Γ ds TS →
      HasType G (Γ.cons T11.weaken) t12 T12 →
      EqSome OT11 T11 →
      EqSome OT12 T12 →
      DmsHasType G Γ (.dcons (.dfun OT11 OT12 t12) ds)
        (.TAnd (.TFun ds.length T11 T12) TS)

/-- `stp`, `dot.v:285-377`. -/
inductive Stp : {σ s : Sig} → Store σ σ → Ctx σ s → Ty σ s → Ty σ s → Type where
  /-- `stp_bot`, `dot.v:286-288`. -/
  | stp_bot {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T : Ty σ s} :
      Stp G Γ .TBot T
  /-- `stp_top`, `dot.v:289-291`. -/
  | stp_top {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T : Ty σ s} :
      Stp G Γ T .TTop
  /-- `stp_fun`, `dot.v:292-300`. -/
  | stp_fun {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 T3 : Ty σ s}
      {T2 T4 : Ty σ (s,x)} :
      Stp G Γ T3 T1 →
      Stp G (Γ.cons T3.weaken) T2 T4 →
      Stp G Γ (.TFun l T1 T2) (.TFun l T3 T4)
  /-- `stp_typ`, `dot.v:301-304`. -/
  | stp_typ {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {T1 T2 T3 T4 : Ty σ s} :
      Stp G Γ T3 T1 →
      Stp G Γ T2 T4 →
      Stp G Γ (.TTyp l T1 T2) (.TTyp l T3 T4)
  /-- `stp_strong_sel1`, `dot.v:306-311`: a selection on a concrete receiver,
  resolved precisely against the stored definition. -/
  | stp_strong_sel1 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb}
      {x : BVar σ .var} {TX T2 : Ty σ []} :
      (G.lookup x).get? l = some (.dty TX) →
      Stp G .nil TX T2 →
      Stp G Γ (.TSel (.conc x) l) (T2.rename renameNil)
  /-- `stp_strong_sel2`, `dot.v:312-317`. -/
  | stp_strong_sel2 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb}
      {x : BVar σ .var} {T1 TX : Ty σ []} :
      (G.lookup x).get? l = some (.dty TX) →
      Stp G .nil T1 TX →
      Stp G Γ (T1.rename renameNil) (.TSel (.conc x) l)
  /-- `stp_sel1`, `dot.v:319-321`: a selection on an abstract receiver,
  resolved through the packing-free judgment `Htp`. -/
  | stp_sel1 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {x : BVar s .var}
      {T2 : Ty σ (scopeUpTo x)} :
      Htp G Γ x (.TTyp l .TBot T2) →
      Stp G Γ (.TSel (.abs x) l) (T2.rename (renameUpTo x))
  /-- `stp_sel2`, `dot.v:323-325`. -/
  | stp_sel2 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {x : BVar s .var}
      {T1 : Ty σ (scopeUpTo x)} :
      Htp G Γ x (.TTyp l T1 .TTop) →
      Stp G Γ (T1.rename (renameUpTo x)) (.TSel (.abs x) l)
  /-- `stp_selx`, `dot.v:327-329`. -/
  | stp_selx {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : Lb} {p : Vr σ s} :
      Stp G Γ (.TSel p l) (.TSel p l)
  /-- `stp_bind1`, `dot.v:331-337`: a recursive type on the left only.  The
  reference's `z ∉ FV(T2)` is the weakening. -/
  | stp_bind1 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 : Ty σ (s,x)}
      {T2 : Ty σ s} :
      Stp G (Γ.cons T1) T1 T2.weaken →
      Stp G Γ (.TBind T1) T2
  /-- `stp_bindx`, `dot.v:339-346`: recursive subtyping.  The self is assumed
  at the *left* body; there is no symmetric rule. -/
  | stp_bindx {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 : Ty σ (s,x)} :
      Stp G (Γ.cons T1) T1 T2 →
      Stp G Γ (.TBind T1) (.TBind T2)
  /-- `stp_and11`, `dot.v:348-351`. -/
  | stp_and11 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T1 T → Stp G Γ (.TAnd T1 T2) T
  /-- `stp_and12`, `dot.v:352-355`. -/
  | stp_and12 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T2 T → Stp G Γ (.TAnd T1 T2) T
  /-- `stp_and2`, `dot.v:356-359`. -/
  | stp_and2 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T T1 → Stp G Γ T T2 → Stp G Γ T (.TAnd T1 T2)
  /-- `stp_or21`, `dot.v:361-364`. -/
  | stp_or21 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T T1 → Stp G Γ T (.TOr T1 T2)
  /-- `stp_or22`, `dot.v:365-368`. -/
  | stp_or22 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T T2 → Stp G Γ T (.TOr T1 T2)
  /-- `stp_or1`, `dot.v:369-372`. -/
  | stp_or1 {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T : Ty σ s} :
      Stp G Γ T1 T → Stp G Γ T2 T → Stp G Γ (.TOr T1 T2) T
  /-- `stp_trans`, `dot.v:374-377`. -/
  | stp_trans {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T1 T2 T3 : Ty σ s} :
      Stp G Γ T1 T2 → Stp G Γ T2 T3 → Stp G Γ T1 T3

/-- `htp`, `dot.v:380-395`, written `:!` in the paper.  It types abstract
variables only, at a type of the variable's own prefix scope. -/
inductive Htp : {σ s : Sig} → Store σ σ → Ctx σ s → (x : BVar s .var) →
    Ty σ (scopeUpTo x) → Type where
  /-- `htp_var`, `dot.v:381-384`.  The reference's `index x GH = Some TX` and
  `closed (S x) … TX` are both `Ctx.lookupAt`. -/
  | htp_var {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var} :
      Htp G Γ x (Γ.lookupAt x)
  /-- `htp_unpack`, `dot.v:385-388`: recursive elimination at `x`, opened at
  `x` itself.  There is deliberately no packing counterpart. -/
  | htp_unpack {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
      {TX : Ty σ (scopeUpTo x,x)} :
      Htp G Γ x (.TBind TX) →
      Htp G Γ x (TX.substVr (.abs (varUpTo x)))
  /-- `htp_sub`, `dot.v:389-395`.  The reference restricts the context of the
  subtyping step to `GL` with `length GL = S x`; here that context is
  `Γ.upTo x` and the restriction is the judgment's own scope. -/
  | htp_sub {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
      {T1 T2 : Ty σ (scopeUpTo x)} :
      Htp G Γ x T1 →
      Stp G (Γ.upTo x) T1 T2 →
      Htp G Γ x T2

end

end Oopsla16
