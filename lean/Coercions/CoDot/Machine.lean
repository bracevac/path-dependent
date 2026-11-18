import Coercions.CoDot.Elimination
import Coercions.CoDot.Term

/-!
# The machine and its safety theorem

A state is a store of values, a continuation and a running term. The store
holds objects and functions only: nothing but `alloc` extends it, and `alloc`
is the `let` step of DOT on a value. Reduction reads stored syntax
(`Store.lookup`, `Defs.lookupTrm`, `Store.Defines`), never a typing.

A reference `x ▷ c` keeps its coercion until it is the head of an
elimination. Then the head is evaluated to a view (`Run.sel`, `Run.app`).
The argument of an application stays a reference with its coercion.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Stores -/

/-- A store: one value per binder of the signature. -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)

def Value.weaken (v : Value s) : Value (s,x) := v.rename Rename.succ

/-- The value stored at a location, weakened into the current scope. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken

/-- The object stored at `y` defines the type member `A`. This is all that
coercion evaluation reads from the store. -/
def Store.Defines (σ : Store s) (y : BVar s .var) (A : Label) : Prop :=
  ∃ d U, σ.lookup y = .obj d ∧ d.lookupTyp A = some U

/-! ## Continuations and states -/

/-- Frames: `let x = □ in u` and the cast `□ ▷ c`. -/
inductive Frame : Sig → Type where
  | «let» : Tm (s,x) → Frame s
  | co : Co s → Frame s

def Frame.weaken : Frame s → Frame (s,x)
  | .let u => .let (u.rename Rename.succ.lift)
  | .co c => .co c.weaken

/-- A continuation, innermost frame first. -/
abbrev Cont (s : Sig) : Type := List (Frame s)

def Cont.weaken (K : Cont s) : Cont (s,x) := K.map Frame.weaken

/-- What is running: a term, or an elimination whose head is being evaluated
to a view. In `app e z d` the argument is the reference `z ▷ d`. -/
inductive Run : Sig → Type where
  | tm : Tm s → Run s
  | sel : Ev s → Label → Run s
  | app : Ev s → BVar s .var → Co s → Run s

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Run s

/-- Reduction. The first five rules are the steps of the DOT-MNF machine; the
others are administrative. -/
inductive MStep : State s → State s' → Prop where
  | letPush : MStep ⟨σ, K, .tm (.let t u)⟩ ⟨σ, .let u :: K, .tm t⟩
  /-- A value answer is allocated; its coercion goes in front of the
      references to the new location. -/
  | alloc : MStep ⟨σ, .let u :: K, .tm (.val v c)⟩
      ⟨.cons σ v, Cont.weaken K, .tm (u.csubst (CoSub.narrow c.weaken))⟩
  /-- A reference answer is substituted, with its coercion. -/
  | letRef : MStep ⟨σ, .let u :: K, .tm (.ref y c)⟩ ⟨σ, K, .tm (u.csubst (CoSub.inst y c))⟩
  /-- Application of a bare function to the reference `z ▷ e`. -/
  | beta : σ.lookup f = .lam S t →
      MStep ⟨σ, K, .app (.ret ⟨f, []⟩) z e⟩ ⟨σ, K, .tm (t.csubst (CoSub.inst z e))⟩
  /-- Selection on a bare object; the self variable becomes `y ▷ id`. -/
  | select : σ.lookup y = .obj d → d.lookupTrm a = some t →
      MStep ⟨σ, K, .sel (.ret ⟨y, []⟩) a⟩ ⟨σ, K, .tm (t.csubst (CoSub.inst y .id))⟩
  | castPush : MStep ⟨σ, K, .tm (.cast t c)⟩ ⟨σ, .co c :: K, .tm t⟩
  | coRef : MStep ⟨σ, .co c :: K, .tm (.ref y e)⟩ ⟨σ, K, .tm (.ref y (.seq e c))⟩
  | coVal : MStep ⟨σ, .co c :: K, .tm (.val v e)⟩ ⟨σ, K, .tm (.val v (.seq e c))⟩
  | focusSel : MStep ⟨σ, K, .tm (.proj x c a)⟩ ⟨σ, K, .sel (.app (.ret ⟨x, []⟩) c) a⟩
  | focusApp : MStep ⟨σ, K, .tm (.app x c y d)⟩ ⟨σ, K, .app (.app (.ret ⟨x, []⟩) c) y d⟩
  | evSel : Step σ.Defines e e' → MStep ⟨σ, K, .sel e a⟩ ⟨σ, K, .sel e' a⟩
  | evApp : Step σ.Defines e e' → MStep ⟨σ, K, .app e z d⟩ ⟨σ, K, .app e' z d⟩
  /-- Selection through a `fld` wrapper: the stored coercion becomes a frame. -/
  | peelSel : MStep ⟨σ, K, .sel (.ret ⟨x, .fld a c :: ws⟩) a⟩
      ⟨σ, .co c :: K, .sel (.ret ⟨x, ws⟩) a⟩
  /-- Application through an `all` wrapper: the domain coercion goes behind
      the argument's coercion, the codomain coercion, instantiated by the
      argument reference, becomes a frame. -/
  | peelApp : MStep ⟨σ, K, .app (.ret ⟨f, .all c d :: ws⟩) z e⟩
      ⟨σ, .co (d.csubst (CoSub.inst z e)) :: K, .app (.ret ⟨f, ws⟩) z (.seq e c)⟩

/-- Reflexive transitive closure, across signatures. -/
inductive MSteps : State s → State s' → Prop where
  | refl : MSteps st st
  | tail : MSteps st st' → MStep st' st'' → MSteps st st''

/-- An answer with an empty continuation. -/
def State.Final (st : State s) : Prop :=
  st.K = [] ∧ ((∃ y c, st.t = .tm (.ref y c)) ∨ (∃ v c, st.t = .tm (.val v c)))

/-! ## Runtime typing -/

def Ctx.nil : Ctx [] := ⟨fun x => nomatch x⟩

/-- Store typing: each value at the type of its introduction rule, in the
context of the earlier locations. -/
inductive StoreTy : {s : Sig} → Store s → Ctx s → Prop where
  | nil : StoreTy .nil Ctx.nil
  | cons : StoreTy σ Γ → Typed Γ (.val v P) → StoreTy (.cons σ v) (Γ.cons P)

/-- Typing of what is running. Terms use the static rules. -/
inductive RunTy (Γ : Ctx s) : Run s → Ty s → Prop where
  | tm : Typed Γ (.tm t T) → RunTy Γ (.tm t) T
  | sel : EvTy Γ e (.fld a T) → RunTy Γ (.sel e a) T
  | app : EvTy Γ e (.all S T) → CoTy Γ (some z) d (Γ.lookup z) S →
      RunTy Γ (.app e z d) (T.substVar z)

/-- `ContTy Γ K S A`: the continuation takes an answer of type `S` and the
program's answer has type `A`. -/
inductive ContTy (Γ : Ctx s) : Cont s → Ty s → Ty s → Prop where
  | nil : ContTy Γ [] A A
  | «let» : Typed (Γ.cons S) (.tm u U.weaken) → ContTy Γ K U A → ContTy Γ (.let u :: K) S A
  | co : CoTy Γ none c S T → ContTy Γ K T A → ContTy Γ (.co c :: K) S A

/-- The renaming out of the empty scope. -/
def initRen (s : Sig) : Rename [] s := ⟨fun x => nomatch x⟩

/-- The invariant. `A` is the closed type of the program; in a state of
scope `s` the answer type is `A` renamed into `s`. No type equality is
involved. -/
def State.Ok (A : Ty []) (st : State s) : Prop :=
  ∃ (Γ : Ctx s) (T : Ty s), StoreTy st.σ Γ ∧ RunTy Γ st.t T ∧
    ContTy Γ st.K T (A.rename (initRen s))

/-! ## Helpers -/

/-- Inversion of value typing. -/
theorem Typed.val_inv {Γ : Ctx s} {v : Value s} {P : Ty s} (h : Typed Γ (.val v P)) :
    (∃ d T, v = .obj d ∧ P = .mu T ∧ Typed (Γ.cons (.mu T)) (.defs d T)) ∨
    (∃ S t T, v = .lam S t ∧ P = .all S T ∧ Typed (Γ.cons S) (.tm t T)) := by
  cases h with
  | lam h => exact .inr ⟨_, _, _, rfl, rfl, h⟩
  | obj h => exact .inl ⟨_, _, rfl, rfl, h⟩

/-- A component of a renamed type is the renaming of a component. -/
theorem Comp.rename_inv {R' C : Ty s2} (h : Comp R' C) :
    ∀ {s1} (R : Ty s1) (ρ : Rename s1 s2), R' = R.rename ρ → ∃ C0, Comp R C0 ∧ C = C0.rename ρ := by
  induction h with
  | refl => intro _ R ρ e; exact ⟨R, .refl, e⟩
  | left _ ih =>
    intro _ R ρ e
    cases R with
    | and R1 R2 =>
      simp only [Ty.rename, Ty.and.injEq] at e
      obtain ⟨C0, hc, hC⟩ := ih R1 ρ e.1
      exact ⟨C0, .left hc, hC⟩
    | _ => simp [Ty.rename] at e
  | right _ ih =>
    intro _ R ρ e
    cases R with
    | and R1 R2 =>
      simp only [Ty.rename, Ty.and.injEq] at e
      obtain ⟨C0, hc, hC⟩ := ih R2 ρ e.2
      exact ⟨C0, .right hc, hC⟩
    | _ => simp [Ty.rename] at e

theorem initRen_weaken (A : Ty []) (s : Sig) :
    (A.rename (initRen s)).weaken = A.rename (initRen (s,x)) := by
  simp only [Ty.weaken, Ty.rename_comp]
  congr 1
  apply Rename.funext'
  intro k y
  nomatch y

theorem StoreTy.lookup' {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) (y : BVar s .var) :
    Typed Γ (.val (σ.lookup y) (Γ.lookup y)) := by
  induction h with
  | nil => nomatch y
  | @cons _ σ Γ v P _ hv ih =>
    cases y with
    | here => exact Typed.rename (Γ2 := Γ.cons P) (ρ := Rename.succ) (fun _ => rfl) hv
    | there y => exact Typed.rename (Γ2 := Γ.cons P) (ρ := Rename.succ) (fun _ => rfl) (ih y)

/-- The value stored at a location of object type is an object. -/
theorem StoreTy.obj {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) {y : BVar s .var} {T0 : Ty (s,x)}
    (hl : Γ.lookup y = .mu T0) :
    ∃ d, σ.lookup y = .obj d ∧ Typed (Γ.cons (.mu T0)) (.defs d T0) := by
  have hv := h.lookup' y
  rw [hl] at hv
  rcases Typed.val_inv hv with ⟨d, T, e, hP, hd⟩ | ⟨_, _, _, _, hP, _⟩
  · cases hP; exact ⟨d, e, hd⟩
  · cases hP

/-- The value stored at a location of function type is a function. -/
theorem StoreTy.lam {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) {f : BVar s .var} {S : Ty s}
    {T : Ty (s,x)} (hl : Γ.lookup f = .all S T) :
    ∃ t, σ.lookup f = .lam S t ∧ Typed (Γ.cons S) (.tm t T) := by
  have hv := h.lookup' f
  rw [hl] at hv
  rcases Typed.val_inv hv with ⟨_, _, _, hP, _⟩ | ⟨S', t, T', e, hP, ht⟩
  · cases hP
  · cases hP; exact ⟨t, e, ht⟩

/-- Selection on a bare object: the field exists and its instance is typed. -/
theorem StoreTy.field {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) {y : BVar s .var}
    {T0 : Ty (s,x)} {a : Label} {T : Ty s}
    (hl : Γ.lookup y = .mu T0) (hc : Comp (T0.substVar y) (.fld a T)) :
    ∃ d t, σ.lookup y = .obj d ∧ d.lookupTrm a = some t ∧
      Typed Γ (.tm (t.csubst (CoSub.inst y .id)) T) := by
  obtain ⟨d, hd, hty⟩ := h.obj hl
  obtain ⟨C0, hc0, hC⟩ := Comp.rename_inv hc T0 (Rename.subst y) rfl
  have he : CoTy Γ (some y) .id (Γ.lookup y) (.mu T0) := by rw [hl]; exact .id
  cases C0 with
  | fld b T' =>
    simp only [Ty.rename, Ty.fld.injEq] at hC
    obtain ⟨rfl, rfl⟩ := hC
    obtain ⟨t, ht, htt⟩ := Typed.defs_field hty hc0
    exact ⟨d, t, hd, ht, Typed.inst htt he⟩
  | _ => simp [Ty.rename] at hC

/-- The body of a `let` frame under allocation. -/
theorem Typed.weaken_let {Γ : Ctx s} {S U : Ty s} {u : Tm (s,x)} (P : Ty s)
    (hu : Typed (Γ.cons S) (.tm u U.weaken)) :
    Typed ((Γ.cons P).cons S.weaken) (.tm (u.rename Rename.succ.lift) U.weaken.weaken) := by
  have hu' := Typed.rename (Γ2 := (Γ.cons P).cons S.weaken) (ρ := Rename.succ.lift)
    (Ctx.cons_renames (Γ1 := Γ) (Γ2 := Γ.cons P) (ρ := Rename.succ) (fun _ => rfl) S) hu
  change Typed _ (.tm (u.rename Rename.succ.lift) (U.weaken.rename Rename.succ.lift)) at hu'
  rw [Ty.weaken_rename] at hu'
  exact hu'

/-! ## Store facts, derived from the typing of the stored values -/

/-- A stored value has the type its location has in the store context. -/
theorem StoreTy.lookup {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) (y : BVar s .var) :
    Typed Γ (.val (σ.lookup y) (Γ.lookup y)) := by
  exact h.lookup' y

/-- The store-shape invariant of the evaluator. -/
theorem StoreTy.wf {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) : Γ.WF := by
  intro x
  rcases Typed.val_inv (h.lookup x) with ⟨d, T, _, hP, hd⟩ | ⟨S, t, T, _, hP, _⟩
  · exact .inl ⟨T, hP, (Typed.defs_record hd).1⟩
  · exact .inr ⟨S, T, hP⟩

/-- The type members that the store context declares are defined by the
stored objects. -/
theorem StoreTy.defines {σ : Store s} {Γ : Ctx s} (h : StoreTy σ Γ) {y : BVar s .var} {A : Label}
    (hd : Γ.Defines y A) : σ.Defines y A := by
  obtain ⟨T0, U, hl, hm⟩ := hd
  obtain ⟨d, hσd, hty⟩ := h.obj hl
  refine ⟨d, U, hσd, ?_⟩
  rw [← (Typed.defs_record hty).2.2 A]
  exact hm

/-- Continuation typing is preserved by allocation. -/
theorem ContTy.weaken {Γ : Ctx s} {K : Cont s} {S A : Ty s} (h : ContTy Γ K S A) (P : Ty s) :
    ContTy (Γ.cons P) (Cont.weaken K) S.weaken A.weaken := by
  induction h with
  | nil => exact .nil
  | «let» hu _ ih => exact .let (Typed.weaken_let P hu) ih
  | co hc _ ih =>
    exact .co (CoTy.rename (Γ2 := Γ.cons P) (ρ := Rename.succ) (fun _ => rfl) hc) ih

/-! ## Safety -/

/-- A closed well-typed program is a well-typed initial state. -/
theorem State.Ok.init {t : Tm []} {A : Ty []} (h : Typed Ctx.nil (.tm t A)) :
    State.Ok A (⟨.nil, [], .tm t⟩ : State []) := by
  have e : initRen [] = Rename.id := Rename.funext' (fun x => nomatch x)
  refine ⟨Ctx.nil, A, .nil, .tm h, ?_⟩
  show ContTy Ctx.nil [] A (A.rename (initRen []))
  rw [e, Ty.rename_id]
  exact .nil

/-- Preservation, for every rule, including allocation. -/
theorem State.Ok.step {A : Ty []} {st : State s} {st' : State s'}
    (h : st.Ok A) (hs : MStep st st') : st'.Ok A := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := h
  have wf := StoreTy.wf hσ
  cases hs with
  | letPush =>
    cases ht with
    | tm h =>
      cases h with
      | «let» h1 h2 => exact ⟨Γ, _, hσ, .tm h1, .let h2 hK⟩
  | alloc =>
    cases ht with
    | tm h =>
      cases h with
      | val hv hc =>
        cases hK with
        | «let» hu hK' =>
          refine ⟨Γ.cons _, _, .cons hσ hv, .tm (Typed.alloc hu hc), ?_⟩
          rw [← initRen_weaken]
          exact ContTy.weaken hK' _
  | letRef =>
    cases ht with
    | tm h =>
      cases h with
      | ref hc =>
        cases hK with
        | «let» hu hK' => exact ⟨Γ, _, hσ, .tm (Typed.letRef hu hc), hK'⟩
  | beta hl =>
    cases ht with
    | app hev he =>
      cases hev with
      | ret hv =>
        rcases VTy.canon_all wf hv with ⟨_, hl'⟩ | ⟨_, _, _, _, _, hws, _⟩
        · obtain ⟨t', hσf, htt⟩ := hσ.lam hl'
          rw [hl] at hσf
          cases hσf
          exact ⟨Γ, _, hσ, .tm (Typed.inst htt he), hK⟩
        · cases hws
  | select hl hlt =>
    cases ht with
    | sel hev =>
      cases hev with
      | ret hv =>
        rcases VTy.canon_fld wf hv with ⟨_, T0, hl0, hc⟩ | ⟨_, _, _, hws, _⟩
        · obtain ⟨d', t', hd', ht', htt⟩ := hσ.field hl0 hc
          rw [hl] at hd'
          cases hd'
          rw [hlt] at ht'
          cases ht'
          exact ⟨Γ, _, hσ, .tm htt, hK⟩
        · cases hws
  | castPush =>
    cases ht with
    | tm h =>
      cases h with
      | cast h1 hc => exact ⟨Γ, _, hσ, .tm h1, .co hc hK⟩
  | coRef =>
    cases ht with
    | tm h =>
      cases h with
      | ref he =>
        cases hK with
        | co hc hK' => exact ⟨Γ, _, hσ, .tm (.ref (.seq he (hc.anySubject _))), hK'⟩
  | coVal =>
    cases ht with
    | tm h =>
      cases h with
      | val hv he =>
        cases hK with
        | co hc hK' => exact ⟨Γ, _, hσ, .tm (.val hv (.seq he hc)), hK'⟩
  | focusSel =>
    cases ht with
    | tm h =>
      cases h with
      | proj hc => exact ⟨Γ, _, hσ, .sel (.app (.ret (.self .refl)) hc), hK⟩
  | focusApp =>
    cases ht with
    | tm h =>
      cases h with
      | app hc hd => exact ⟨Γ, _, hσ, .app (.app (.ret (.self .refl)) hc) hd, hK⟩
  | evSel hst =>
    cases ht with
    | sel hev => exact ⟨Γ, _, hσ, .sel (Step.preservation wf hev hst).1, hK⟩
  | evApp hst =>
    cases ht with
    | app hev hd => exact ⟨Γ, _, hσ, .app (Step.preservation wf hev hst).1 hd, hK⟩
  | peelSel =>
    cases ht with
    | sel hev =>
      cases hev with
      | ret hv =>
        obtain ⟨T1, hv', hc⟩ := sel_step_wrapper wf hv
        exact ⟨Γ, _, hσ, .sel (.ret hv'), .co hc hK⟩
  | peelApp =>
    cases ht with
    | app hev he =>
      cases hev with
      | ret hv =>
        obtain ⟨S1, T1, hv', he', hd'⟩ := app_step_wrapper wf hv he
        exact ⟨Γ, _, hσ, .app (.ret hv') he', .co hd' hK⟩

/-- Progress. -/
theorem State.Ok.progress {A : Ty []} {st : State s} (h : st.Ok A) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), MStep st st' := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := h
  have wf := StoreTy.wf hσ
  obtain ⟨σ, K, r⟩ := st
  cases r with
  | tm t =>
    cases t with
    | ref y c =>
      cases K with
      | nil => exact .inl ⟨rfl, .inl ⟨y, c, rfl⟩⟩
      | cons f K =>
        cases f with
        | «let» u => exact .inr ⟨_, _, .letRef⟩
        | co c' => exact .inr ⟨_, _, .coRef⟩
    | val v c =>
      cases K with
      | nil => exact .inl ⟨rfl, .inr ⟨v, c, rfl⟩⟩
      | cons f K =>
        cases f with
        | «let» u => exact .inr ⟨_, _, .alloc⟩
        | co c' => exact .inr ⟨_, _, .coVal⟩
    | app => exact .inr ⟨_, _, .focusApp⟩
    | proj => exact .inr ⟨_, _, .focusSel⟩
    | «let» => exact .inr ⟨_, _, .letPush⟩
    | cast => exact .inr ⟨_, _, .castPush⟩
  | sel e a =>
    right
    cases ht with
    | sel hev =>
      rcases EvTy.progress wf (fun _ _ hd => StoreTy.defines hσ hd) hev with ⟨⟨x, ws⟩, rfl⟩ | ⟨e', hst⟩
      · cases hev with
        | ret hv =>
          rcases VTy.canon_fld wf hv with ⟨rfl, T0, hl0, hc⟩ | ⟨_, _, _, rfl, _⟩
          · obtain ⟨d, t, hd, ht', _⟩ := hσ.field hl0 hc
            exact ⟨_, _, .select hd ht'⟩
          · exact ⟨_, _, .peelSel⟩
      · exact ⟨_, _, .evSel hst⟩
  | app e z d =>
    right
    cases ht with
    | app hev _ =>
      rcases EvTy.progress wf (fun _ _ hd => StoreTy.defines hσ hd) hev with ⟨⟨f, ws⟩, rfl⟩ | ⟨e', hst⟩
      · cases hev with
        | ret hv =>
          rcases VTy.canon_all wf hv with ⟨rfl, hl⟩ | ⟨_, _, _, _, _, rfl, _⟩
          · obtain ⟨t, hf, _⟩ := hσ.lam hl
            exact ⟨_, _, .beta hf⟩
          · exact ⟨_, _, .peelApp⟩
      · exact ⟨_, _, .evApp hst⟩

/-- Safety: every state reachable from a closed well-typed program is final
or takes a step. -/
theorem safety {t : Tm []} {A : Ty []} (h : Typed Ctx.nil (.tm t A))
    {st : State s} (hs : MSteps (⟨.nil, [], .tm t⟩ : State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), MStep st st' := by
  have hok : ∀ {s0 s'} {st0 : State s0} {st' : State s'}, MSteps st0 st' → st0.Ok A → st'.Ok A := by
    intro s0 s' st0 st' hs' h0
    induction hs' with
    | refl => exact h0
    | tail _ h2 ih => exact (ih h0).step h2
  exact (hok hs (State.Ok.init h)).progress

end CoDot
