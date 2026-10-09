import Coercions.Frontend.Look

/-!
# Subtyping in the compiler's case order

The algorithm decides two goals.  `sub S T` asks for `S <: T` and is answered by
a `DotMNF.Sub` derivation.  `var x V T` asks that the variable `x`, already seen
at the type `V`, have the type `T`.  It is answered by a map from a derivation
of `x : V` to one of `x : T`.  This is the compiler's singleton on the left: it
keeps `x` while it widens, so a recursive type is opened at `x` (the `RecType`
case of `TypeComparer.thirdTry` and `TypeComparer.fixRecs`).  DOT-MNF opens `μ`
only at a variable and introduces `∧` only at a variable, so the second goal is
needed.

Each goal tries its alternatives in the order of core/TypeComparer.scala.  First
identity (`recur`), then `firstTry` on the right, `secondTry` on the left,
`thirdTry` on the right and `fourthTry` on the left.  An intersection on the
right is final, as in `firstTry`.  Each alternative is a function of its own and
emits a DOT-MNF derivation.  The middle of every transitivity step is a bound of
a member or an operand of an intersection, read off a type the algorithm already
holds.  No middle is chosen from the context.  Where the compiler tries two
alternatives with `either`, each is tried in turn.

DOT-MNF forces these differences from the compiler.

* The compiler compares `μ <: μ` through the parents (`thirdTry`) and a `μ` on
  the left by its parent (`fourthTry`).  DOT-MNF has no `μ` rule in `Sub`, so a
  `μ` is opened only at a variable.
* The compiler merges two members of one name (`TypeBounds.&` in
  core/Types.scala, and `hasMatchingMember`).  DOT-MNF has no union, so each
  member is tried.
* `matchAbstractTypeMember` has no rule in DOT-MNF and is left out.
* The compiler gives up after a failed alias (`compareNamed` in `firstTry`).
  Here every alternative is tried, which only adds successes.

A selection on the right skips a member whose lower bound is `⊥`, as
`isSubApproxHi` fails at once there.  A left side that is `⊥` has already
succeeded by the rule for `⊥`.

Member lookups go through `look` of `Look.lean`.  Its structural index is the
fuel left in the tank.  Each lookup level draws at least one unit, so the index
never runs out before the tank does.

The run is the generic one of `Fuel.lean`, at the cost `cost`.  It has one tank
for the whole run and the goals pending along the branch, and a goal that
repeats exactly fails.  A goal holds its context, so a goal under a new binder
is never cut by a goal outside it.  `sub?` and `var?` start a run from a full
tank and return the answer with the tank left.  `subF` and `varF` run on a tank
they are handed, for a caller that threads one tank through many goals.

The step is framed and dominated (`step_frame`, `step_dom`), so the facts of
`Fuel.lean` hold for the run.  `subF` and `varF` are framed, and `sub?` and
`var?` keep an answer at any larger fuel (`sub?_mono`, `var?_mono`).

Every definition is structural, so the kernel evaluates the algorithm.  The
checks at the end of the module run it on the examples by `decide +kernel`.
-/

namespace Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Defs Ctx Sub HasTy)

deriving instance DecidableEq for DotMNF.Ctx

/-! ## Goals and answers -/

/-- The two goals of the algorithm. -/
inductive Q (s : Sig) where
  /-- `S <: T`. -/
  | sub (S T : Ty s)
  /-- The variable `x`, seen at `V`, has the type `T`. -/
  | var (x : BVar s .var) (V T : Ty s)
deriving DecidableEq

/-- A goal in its context.  Two goals are equal only if their contexts are. -/
structure G where
  s : Sig
  Γ : Ctx s
  q : Q s
deriving DecidableEq

/-- The answer to a goal: a derivation of `S <: T`, or a map from a
derivation of `x : V` to one of `x : T`. -/
def RQ {s : Sig} (Γ : Ctx s) : Q s → Type
  | .sub S T => Sub Γ S T
  | .var x V T => Var Γ x V → Var Γ x T

/-- The answer to a goal in its context. -/
def R (g : G) : Type := RQ g.Γ g.q

/-- The oracle an alternative asks: goals in the same context. -/
abbrev Rec {s : Sig} (Γ : Ctx s) := (q : Q s) → Fu (Option (RQ Γ q))

/-- The oracle for the codomains of two function types, under the new
binder at the second domain. -/
abbrev RecAll {s : Sig} (Γ : Ctx s) :=
  (S2 : Ty s) → (T1 T2 : Ty (s,x)) → Fu (Option (Sub (Γ.cons S2) T1 T2))

/-- A type member of `p` at `A`: its bounds, and the premise of
`Sub.selUpper` and `Sub.selLower`. -/
abbrev TyMem {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Type :=
  (lo : Ty s) × (hi : Ty s) × Var Γ p (.typ A lo hi)

/-! ## Combinators on optional answers -/

/-- Run `c`, and map an answer through `f`. -/
def mapO {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (Option β) :=
  Fu.bind c fun o => Fu.ret (o.map f)

/-- Run `c`, and on an answer run `f` on it.  No answer stops here. -/
def bindO {α β : Type} (c : Fu (Option α)) (f : α → Fu (Option β)) : Fu (Option β) :=
  Fu.bind c fun
    | some a => f a
    | none => Fu.ret none

/-- The type members of `p` at `A`, looked up on the tank.  The index of the
lookup is the fuel left. -/
def declsAt {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) : Fu (List (TyMem Γ p A)) :=
  fun t => decls Γ t.left p A t

/-- The type is an intersection. -/
def isAnd {s : Sig} : Ty s → Bool
  | .and _ _ => true
  | _ => false

/-- The type is an atom of a widening: not `μ`, `∧` or a selection. -/
def isAtom {s : Sig} : Ty s → Bool
  | .mu _ => false
  | .and _ _ => false
  | .sel _ _ => false
  | _ => true

/-- `Sub.fld` across a decided label equality. -/
def subFld {s : Sig} {Γ : Ctx s} {a b : Label} {S T : Ty s} (h : a = b) (e : Sub Γ S T) :
    Sub Γ (.fld a S) (.fld b T) := by
  cases h
  exact Sub.fld e

/-- `Sub.typ` across a decided label equality. -/
def subTyp {s : Sig} {Γ : Ctx s} {A B : Label} {S1 S2 T1 T2 : Ty s} (h : A = B)
    (e1 : Sub Γ S2 S1) (e2 : Sub Γ T1 T2) : Sub Γ (.typ A S1 T1) (.typ B S2 T2) := by
  cases h
  exact Sub.typ e1 e2

/-! ## The `sub` goal, one alternative per compiler case -/

section SubAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, as in `TypeComparer.recur`. -/
def sRefl (S T : Ty s) : Option (Sub Γ S T) :=
  if h : S = T then some (h ▸ Sub.refl) else none

/-- `Any` on the right, as in `thirdTryNamed`. -/
def sTop (S T : Ty s) : Option (Sub Γ S T) :=
  if h : T = .top then some (h ▸ Sub.top) else none

/-- `Nothing` on the left, as in `secondTry`. -/
def sBot (S T : Ty s) : Option (Sub Γ S T) :=
  if h : S = .bot then some (h ▸ Sub.bot) else none

/-- An intersection on the right, as in `firstTry`.  Both operands must hold. -/
def sAndR (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))
  | .and T1 T2 =>
      bindO (r (.sub S T1)) fun e1 =>
        mapO (r (.sub S T2)) fun e2 => Sub.and e1 e2
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, as in
`thirdTryNamed`.  Each member is tried.  A member whose lower bound is `⊥` is
skipped, as `isSubApproxHi` fails at once there. -/
def sSelLo (r : Rec Γ) (S : Ty s) : (T : Ty s) → Fu (Option (Sub Γ S T))
  | .sel (.var p) A =>
      Fu.bind (declsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TyMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.sub S d.1)) fun e => Sub.trans e (Sub.selLower d.2.2)) ds
  | _ => Fu.ret none

/-- Two fields, two type members or two function types of one shape, as in
`thirdTry`.  Fields follow `compareRefinedSlow` and `hasMatchingMember`, type
members follow `compareTypeBounds`, and functions with contravariant parameters
follow `isSubInfo`.  The codomains are compared under the new binder at the
second domain. -/
def sStruct (r : Rec Γ) (rAll : RecAll Γ) : (S T : Ty s) → Fu (Option (Sub Γ S T))
  | .fld a S', .fld b T' =>
      if h : a = b then mapO (r (.sub S' T')) (subFld h) else Fu.ret none
  | .typ A S1 T1, .typ B S2 T2 =>
      if h : A = B then
        bindO (r (.sub S2 S1)) fun e1 =>
          mapO (r (.sub T1 T2)) fun e2 => subTyp h e1 e2
      else Fu.ret none
  | .all S1 T1, .all S2 T2 =>
      bindO (r (.sub S2 S1)) fun e1 =>
        mapO (rAll S2 T1 T2) fun e2 => Sub.all e1 e2
  | _, _ => Fu.ret none

/-- A selection on the left, through the upper bound of a member, as in
`fourthTry`.  Each member is tried. -/
def sSelHi (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))
  | .sel (.var q) B =>
      Fu.bind (declsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TyMem Γ q B =>
          mapO (r (.sub d.2.1 T)) fun e => Sub.trans (Sub.selUpper d.2.2) e) ds
  | _ => Fu.ret none

/-- An intersection on the left, as in `fourthTry`.  The left operand comes
first, then the right one, as in `either`. -/
def sAndL (r : Rec Γ) (T : Ty s) : (S : Ty s) → Fu (Option (Sub Γ S T))
  | .and S1 S2 =>
      Fu.orElse (mapO (r (.sub S1 T)) fun e => Sub.trans Sub.and1 e) fun _ =>
        mapO (r (.sub S2 T)) fun e => Sub.trans Sub.and2 e
  | _ => Fu.ret none

end SubAlts

/-- The `sub` goal: the alternatives in the compiler's order.  An
intersection on the right is final: when `T` is one, nothing after `sAndR` is
tried. -/
def subStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (rAll : RecAll Γ) (S T : Ty s) :
    Fu (Option (Sub Γ S T)) :=
  Fu.orElse (Fu.ret (sRefl S T)) fun _ =>
  Fu.orElse (Fu.ret (sTop S T)) fun _ =>
  Fu.orElse (Fu.ret (sBot S T)) fun _ =>
  if isAnd T then sAndR r S T else
  Fu.orElse (sSelLo r S T) fun _ =>
  Fu.orElse (sStruct r rAll S T) fun _ =>
  Fu.orElse (sSelHi r T S) fun _ =>
  sAndL r T S

/-! ## The `var` goal, one alternative per compiler case -/

/-- A map from a derivation of `x : V` to one of `x : T`. -/
abbrev VarFn {s : Sig} (Γ : Ctx s) (x : BVar s .var) (V T : Ty s) : Type :=
  Var Γ x V → Var Γ x T

section VarAlts

variable {s : Sig} {Γ : Ctx s}

/-- Identity, as in `TypeComparer.recur`. -/
def vRefl (x : BVar s .var) (V T : Ty s) : Option (VarFn Γ x V T) :=
  if h : V = T then some (fun d => h ▸ d) else none

/-- An intersection on the right, as in `firstTry`, by `HasTy.andI`. -/
def vAndR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .and T1 T2 =>
      bindO (r (.var x V T1)) fun f1 =>
        mapO (r (.var x V T2)) fun f2 d => HasTy.andI (f1 d) (f2 d)
  | _ => Fu.ret none

/-- A recursive type on the right with a singleton on the left, as in
`thirdTry`.  `fixRecs` opens the body at the variable, and so does
`HasTy.recI`. -/
def vMuR (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .mu B => mapO (r (.var x V (B.substVar x))) fun f d => HasTy.recI (f d)
  | _ => Fu.ret none

/-- A selection on the right, through the lower bound of a member, with the
variable kept, as in `thirdTryNamed`.  Each member is tried.  A member whose
lower bound is `⊥` is skipped, as in `sSelLo`. -/
def vSelLo (r : Rec Γ) (x : BVar s .var) (V : Ty s) : (T : Ty s) → Fu (Option (VarFn Γ x V T))
  | .sel (.var p) A =>
      Fu.bind (declsAt Γ p A) fun ds =>
        Fu.firstSome (fun d : TyMem Γ p A =>
          if d.1 = .bot then Fu.ret none
          else mapO (r (.var x V d.1)) fun f e => HasTy.sub (f e) (Sub.selLower d.2.2)) ds
  | _ => Fu.ret none

/-- A recursive type in the view, opened at the variable by `HasTy.recE`.  The
compiler widens the singleton in `fourthTry` and then opens the recursive type
as `goRec` in `Type.findMember` does. -/
def vMuL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .mu B => mapO (r (.var x (B.substVar x) T)) fun f d => f (HasTy.recE d)
  | _ => Fu.ret none

/-- An intersection in the view, as in `fourthTry`.  The left operand comes
first, then the right one, as in `either`. -/
def vAndL (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .and V1 V2 =>
      Fu.orElse (mapO (r (.var x V1 T)) fun f d => f (HasTy.sub d Sub.and1)) fun _ =>
        mapO (r (.var x V2 T)) fun f d => f (HasTy.sub d Sub.and2)
  | _ => Fu.ret none

/-- A selection in the view, through the upper bound of a member, as in
`fourthTry`.  Each member is tried. -/
def vSelHi (r : Rec Γ) (x : BVar s .var) (T : Ty s) : (V : Ty s) → Fu (Option (VarFn Γ x V T))
  | .sel (.var q) B =>
      Fu.bind (declsAt Γ q B) fun ds =>
        Fu.firstSome (fun d : TyMem Γ q B =>
          mapO (r (.var x d.2.1 T)) fun f e => f (HasTy.sub e (Sub.selUpper d.2.2))) ds
  | _ => Fu.ret none

/-- An atom of the view against the goal, by subsumption.  The compiler
compares the widened singleton as a type in `fourthTry`. -/
def vAtom (r : Rec Γ) (x : BVar s .var) (V T : Ty s) : Fu (Option (VarFn Γ x V T)) :=
  if isAtom V then mapO (r (.sub V T)) fun e d => HasTy.sub d e else Fu.ret none

end VarAlts

/-- The `var` goal: the variable `x`, seen at `V`, must be shown at `T`.  The
alternatives in the compiler's order.  An intersection on the right is final. -/
def varStep {s : Sig} (Γ : Ctx s) (r : Rec Γ) (x : BVar s .var) (V T : Ty s) :
    Fu (Option (VarFn Γ x V T)) :=
  Fu.orElse (Fu.ret (vRefl x V T)) fun _ =>
  if isAnd T then vAndR r x V T else
  Fu.orElse (vMuR r x V T) fun _ =>
  Fu.orElse (vSelLo r x V T) fun _ =>
  Fu.orElse (vMuL r x T V) fun _ =>
  Fu.orElse (vAndL r x T V) fun _ =>
  Fu.orElse (vSelHi r x T V) fun _ =>
  vAtom r x V T

/-! ## The step and the entry points -/

/-- One step of the algorithm.  A goal in `Γ` asks goals in `Γ`, and the
codomains of two function types are asked in `Γ.cons S2`. -/
def step : Step G R := fun o g =>
  match g with
  | ⟨s, Γ, .sub S T⟩ =>
      subStep Γ (fun q => o ⟨s, Γ, q⟩) (fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | ⟨s, Γ, .var x V T⟩ => varStep Γ (fun q => o ⟨s, Γ, q⟩) x V T

/-- `S <: T` on the tank it is handed.  The run's index is the fuel left. -/
def subF {s : Sig} (Γ : Ctx s) (S T : Ty s) : Fu (Option (Sub Γ S T)) := fun t =>
  run cost step t.left [] ⟨s, Γ, .sub S T⟩ t

/-- `x : T` on the tank it is handed, from the type `x` is declared at. -/
def varF {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Fu (Option (Var Γ x T)) :=
  mapO (fun t => run cost step t.left [] ⟨s, Γ, .var x (Γ.lookup x) T⟩ t) fun f => f .var

/-- `S <: T` from a full tank of `n` units, with the tank left. -/
def sub? {s : Sig} (Γ : Ctx s) (S T : Ty s) (n : Nat := defaultFuel) : Option (Sub Γ S T) × Tank :=
  subF Γ S T ⟨n, false⟩

/-- `x : T` from a full tank of `n` units, with the tank left. -/
def var? {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) (n : Nat := defaultFuel) :
    Option (Var Γ x T) × Tank :=
  varF Γ x T ⟨n, false⟩

/-! ## The lookup at the tank's own index

`declsAt` runs a lookup whose index is the fuel left.  With more fuel the
index is larger.  A lookup that ends unmarked never reached index zero, so it
gives the same answers at any larger index.  So `declsAt` is framed, as every
computation of a step must be. -/

/-- Either branch of a test agrees with its partner, so the tests agree. -/
theorem ite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' b b' : Fu α} (ha : Agree a a')
    (hb : Agree b b') : Agree (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- A lookup at a larger index does what the lookup at a smaller one does. -/
theorem look_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ (P : List (LKey s)) (x : BVar s .var) (V : Ty s) (k : Key),
      Agree (look Γ d P x V k) (look Γ d' P x V k)
  | 0, d', _, P, x, V, k => by
    refine ⟨look_framed Γ 0 P x V k, look_framed Γ d' P x V k, ?_⟩
    intro t r t' h ho _
    simp only [look, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, x, V, k => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := look_agree Γ d e (by omega)
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · apply ite_agree (ret_agree _)
      apply ite_agree (ret_agree _)
      cases V with
      | mu B => exact bind_agree (ih _ _ _ _) fun _ => ret_agree _
      | and V1 V2 =>
        exact bind_agree (ih _ _ _ _) fun _ => bind_agree (ih _ _ _ _) fun _ => ret_agree _
      | sel p B =>
        cases p with
        | var q =>
          refine bind_agree (ih _ _ _ _) fun es => flatMapL_agree ?_ es
          intro e
          split
          · exact bind_agree (ih _ _ _ _) fun _ => ret_agree _
          · exact ret_agree _
      | top => exact ret_agree _
      | bot => exact ret_agree _
      | typ _ _ _ => exact ret_agree _
      | fld _ _ => exact ret_agree _
      | all _ _ => exact ret_agree _

/-- A lookup that ends unmarked gives the same answers at a larger index. -/
theorem decls_index {s : Sig} {Γ : Ctx s} {d d' : Nat} {p : BVar s .var} {A : Label} {t : Tank}
    (h : (decls Γ d p A t).2.out = false) (hd : d ≤ d') : decls Γ d' p A t = decls Γ d p A t := by
  have hag : Agree (decls Γ d p A) (decls Γ d' p A) :=
    bind_agree (look_agree Γ d d' hd _ _ _ _) fun _ => ret_agree _
  have := hag.sim t _ _ rfl h 0
  simpa using this

theorem declsAt_framed {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) :
    Framed (declsAt Γ p A) where
  absorbs t ht := (decls_framed Γ t.left p A).absorbs t ht
  spends t := (decls_framed Γ t.left p A).spends t
  shift := by
    intro t r t' h ho k
    have h1 := decls_frame h ho k
    have h2 : (decls Γ t.left p A (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change decls Γ (t.left + k) p A (t.add k) = _
    rw [decls_index h2 (Nat.le_add_right _ _), h1]

/-! ## The step is framed and dominated

`FrameF step` says that oracles which agree give answers which agree.
`DomF step` says that an oracle which dominates another gives answers which
dominate.  `run_frame`, `run_index` and `cut_complete` of `Fuel.lean` ask for
both.  Each alternative is built from `Fu.ret`, `Fu.bind`, `Fu.orElse`,
`Fu.firstSome`, `mapO`, `bindO`, `declsAt` and tests.  So each has an
agreement lemma and a dominance lemma, each a composition of the combinator
lemmas.  An alternative at one oracle agrees with itself, so it is framed.
The two facts of the step follow by cases on the goal. -/

section Tests

variable {α : Type}

/-- Either branch of a test dominates its partner, so the tests do. -/
theorem ite_dom {p : Prop} [hp : Decidable p] {m : Nat} {a a' b b' : Fu α} (ha : Dom m a a')
    (hb : Dom m b b') : Dom m (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha

/-- A test whose branches read its proof agrees with its partner when the
branches do. -/
theorem dite_agree {p : Prop} [hp : Decidable p] {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Agree (a h) (a' h)) (hb : ∀ h, Agree (b h) (b' h)) :
    Agree (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-- A test whose branches read its proof dominates its partner when the
branches do. -/
theorem dite_dom {p : Prop} [hp : Decidable p] {m : Nat} {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Dom m (a h) (a' h)) (hb : ∀ h, Dom m (b h) (b' h)) :
    Dom m (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

end Tests

section OptionFrames

variable {α β : Type} {m : Nat}

theorem mapO_framed {c : Fu (Option α)} (f : α → β) (hc : Framed c) : Framed (mapO c f) :=
  bind_framed hc fun _ => ret_framed _

theorem mapO_agree {c c' : Fu (Option α)} (f : α → β) (hc : Agree c c') :
    Agree (mapO c f) (mapO c' f) :=
  bind_agree hc fun _ => ret_agree _

theorem mapO_dom {c c' : Fu (Option α)} (f : α → β) (hc : Framed c) (hd : Dom m c c') :
    Dom m (mapO c f) (mapO c' f) :=
  bind_dom hc (fun _ => ret_framed _) hd fun _ => ret_dom _ m

theorem bindO_agree {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Agree c c')
    (hf : ∀ a, Agree (f a) (f' a)) : Agree (bindO c f) (bindO c' f') :=
  bind_agree hc fun
    | some a => hf a
    | none => ret_agree _

theorem bindO_dom {c c' : Fu (Option α)} {f f' : α → Fu (Option β)} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) (hd : Dom m c c') (hfd : ∀ a, Dom m (f a) (f' a)) :
    Dom m (bindO c f) (bindO c' f') :=
  bind_dom hc (fun | some a => hf a | none => ret_framed _) hd fun
    | some a => hfd a
    | none => ret_dom _ m

end OptionFrames

/-! ### The alternatives of the `sub` goal

The agreement lemmas take oracles `r` and `r'` that agree on every goal.  The
dominance lemmas take a framed `r` that dominates `r'` below `m`.  The lemmas
of `sStruct` and `subStep` take the same of the oracles for codomains. -/

section SubFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {rAll rAll' : RecAll Γ} {m : Nat}

theorem sAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty s) :
    Dom m (sAndR r S T) (sAndR r' S T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem sSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (S T : Ty s) :
    Agree (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      exact bind_agree (Agree.refl (declsAt_framed Γ p A)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
  | _ => exact ret_agree _

theorem sSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (S T : Ty s) :
    Dom m (sSelLo r S T) (sSelLo r' S T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      have hf : ∀ d : TyMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
          else mapO (r (.sub S d.1)) fun e => Sub.trans e (Sub.selLower d.2.2)) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (declsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
        ((declsAt_framed Γ p A).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
  | _ => exact ret_dom _ m

theorem sStruct_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Agree (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_agree _
    | exact dite_agree (fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact dite_agree (fun _ => bindO_agree (hr _) fun _ => mapO_agree _ (hr _)) fun _ => ret_agree _
    | exact bindO_agree (hr _) fun _ => mapO_agree _ (hA _ _ _)

theorem sStruct_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ S2 T1 T2, Framed (rAll S2 T1 T2))
    (hAd : ∀ S2 T1 T2, Dom m (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Dom m (sStruct r rAll S T) (sStruct r' rAll' S T) := by
  cases S <;> cases T
  all_goals first
    | exact ret_dom _ m
    | exact dite_dom (fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact dite_dom (fun _ => bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _)
        fun _ => mapO_dom _ (hF _) (hd _)) fun _ => ret_dom _ m
    | exact bindO_dom (hF _) (fun _ => mapO_framed _ (hAF _ _ _)) (hd _)
        fun _ => mapO_dom _ (hAF _ _ _) (hAd _ _ _)

theorem sSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) :
    Agree (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_agree (Agree.refl (declsAt_framed Γ q B)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | _ => exact ret_agree _

theorem sSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty s) :
    Dom m (sSelHi r T S) (sSelHi r' T S) := by
  cases S with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_dom (declsAt_framed Γ q B)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((declsAt_framed Γ q B).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | _ => exact ret_dom _ m

theorem sAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (T S : Ty s) :
    Agree (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem sAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (T S : Ty s) :
    Dom m (sAndL r T S) (sAndL r' T S) := by
  cases S with
  | and S1 S2 =>
    dsimp only [sAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem subStep_agree (hr : ∀ q, Agree (r q) (r' q))
    (hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Agree (subStep Γ r rAll S T) (subStep Γ r' rAll' S T) :=
  orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <| orElse_agree (ret_agree _) <|
    ite_agree (sAndR_agree hr S T) <|
    orElse_agree (sSelLo_agree hr S T) <| orElse_agree (sStruct_agree hr hA S T) <|
    orElse_agree (sSelHi_agree hr T S) (sAndL_agree hr T S)

theorem subStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q))
    (hAF : ∀ S2 T1 T2, Framed (rAll S2 T1 T2))
    (hAd : ∀ S2 T1 T2, Dom m (rAll S2 T1 T2) (rAll' S2 T1 T2)) (S T : Ty s) :
    Dom m (subStep Γ r rAll S T) (subStep Γ r' rAll' S T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  have hA : ∀ S2 T1 T2, Agree (rAll S2 T1 T2) (rAll S2 T1 T2) := fun _ _ _ => Agree.refl (hAF _ _ _)
  orElse_dom (ret_framed _) (ret_dom _ m) <| orElse_dom (ret_framed _) (ret_dom _ m) <|
    orElse_dom (ret_framed _) (ret_dom _ m) <|
    ite_dom (sAndR_dom hF hd S T) <|
    orElse_dom (sSelLo_agree hr S T).left (sSelLo_dom hF hd S T) <|
    orElse_dom (sStruct_agree hr hA S T).left (sStruct_dom hF hd hAF hAd S T) <|
    orElse_dom (sSelHi_agree hr T S).left (sSelHi_dom hF hd T S) (sAndL_dom hF hd T S)

end SubFrames

/-! ### The alternatives of the `var` goal -/

section VarFrames

variable {s : Sig} {Γ : Ctx s} {r r' : Rec Γ} {m : Nat}

theorem vAndR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 => exact bindO_agree (hr _) fun _ => mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vAndR r x V T) (vAndR r' x V T) := by
  cases T with
  | and T1 T2 =>
    exact bindO_dom (hF _) (fun _ => mapO_framed _ (hF _)) (hd _) fun _ => mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vMuR_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vMuR_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vMuR r x V T) (vMuR r' x V T) := by
  cases T with
  | mu B => exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelLo_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      exact bind_agree (Agree.refl (declsAt_framed Γ p A)) fun ds =>
        firstSome_agree (fun _ => ite_agree (ret_agree _) (mapO_agree _ (hr _))) ds
  | _ => exact ret_agree _

theorem vSelLo_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vSelLo r x V T) (vSelLo r' x V T) := by
  cases T with
  | sel p A =>
    cases p with
    | var p =>
      have hf : ∀ d : TyMem Γ p A, Framed (if d.1 = .bot then Fu.ret none
          else mapO (r (.var x V d.1)) fun f e => HasTy.sub (f e) (Sub.selLower d.2.2)) :=
        fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))
      exact bind_dom (declsAt_framed Γ p A) (fun ds => firstSome_framed hf ds)
        ((declsAt_framed Γ p A).dom m) fun ds =>
          firstSome_dom hf (fun _ => ite_dom (ret_dom _ m) (mapO_dom _ (hF _) (hd _))) ds
  | _ => exact ret_dom _ m

theorem vMuL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vMuL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vMuL r x T V) (vMuL r' x T V) := by
  cases V with
  | mu B => exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vAndL_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_agree ?_ ?_ <;> exact mapO_agree _ (hr _)
  | _ => exact ret_agree _

theorem vAndL_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vAndL r x T V) (vAndL r' x T V) := by
  cases V with
  | and V1 V2 =>
    dsimp only [vAndL]
    refine orElse_dom (mapO_framed _ (hF _)) ?_ ?_ <;> exact mapO_dom _ (hF _) (hd _)
  | _ => exact ret_dom _ m

theorem vSelHi_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (T V : Ty s) :
    Agree (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_agree (Agree.refl (declsAt_framed Γ q B)) fun ds =>
        firstSome_agree (fun _ => mapO_agree _ (hr _)) ds
  | _ => exact ret_agree _

theorem vSelHi_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (T V : Ty s) : Dom m (vSelHi r x T V) (vSelHi r' x T V) := by
  cases V with
  | sel p B =>
    cases p with
    | var q =>
      exact bind_dom (declsAt_framed Γ q B)
        (fun ds => firstSome_framed (fun _ => mapO_framed _ (hF _)) ds)
        ((declsAt_framed Γ q B).dom m) fun ds =>
          firstSome_dom (fun _ => mapO_framed _ (hF _)) (fun _ => mapO_dom _ (hF _) (hd _)) ds
  | _ => exact ret_dom _ m

theorem vAtom_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (vAtom r x V T) (vAtom r' x V T) :=
  ite_agree (mapO_agree _ (hr _)) (ret_agree _)

theorem vAtom_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (vAtom r x V T) (vAtom r' x V T) :=
  ite_dom (mapO_dom _ (hF _) (hd _)) (ret_dom _ m)

theorem varStep_agree (hr : ∀ q, Agree (r q) (r' q)) (x : BVar s .var) (V T : Ty s) :
    Agree (varStep Γ r x V T) (varStep Γ r' x V T) :=
  orElse_agree (ret_agree _) <| ite_agree (vAndR_agree hr x V T) <|
    orElse_agree (vMuR_agree hr x V T) <| orElse_agree (vSelLo_agree hr x V T) <|
    orElse_agree (vMuL_agree hr x T V) <| orElse_agree (vAndL_agree hr x T V) <|
    orElse_agree (vSelHi_agree hr x T V) (vAtom_agree hr x V T)

theorem varStep_dom (hF : ∀ q, Framed (r q)) (hd : ∀ q, Dom m (r q) (r' q)) (x : BVar s .var)
    (V T : Ty s) : Dom m (varStep Γ r x V T) (varStep Γ r' x V T) :=
  have hr : ∀ q, Agree (r q) (r q) := fun q => Agree.refl (hF q)
  orElse_dom (ret_framed _) (ret_dom _ m) <| ite_dom (vAndR_dom hF hd x V T) <|
    orElse_dom (vMuR_agree hr x V T).left (vMuR_dom hF hd x V T) <|
    orElse_dom (vSelLo_agree hr x V T).left (vSelLo_dom hF hd x V T) <|
    orElse_dom (vMuL_agree hr x T V).left (vMuL_dom hF hd x T V) <|
    orElse_dom (vAndL_agree hr x T V).left (vAndL_dom hF hd x T V) <|
    orElse_dom (vSelHi_agree hr x T V).left (vSelHi_dom hF hd x T V) (vAtom_dom hF hd x V T)

end VarFrames

/-! ### The step -/

theorem step_frame : FrameF step := by
  intro o o' ho g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (rAll' := fun S2 T1 T2 => o' ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun q => ho ⟨s, Γ, q⟩) (fun S2 T1 T2 => ho ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | var x V T =>
    exact varStep_agree (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => ho ⟨s, Γ, q⟩) x V T

theorem step_dom : DomF step := by
  intro m o o' hF _ hd g
  obtain ⟨s, Γ, q⟩ := g
  cases q with
  | sub S T =>
    exact subStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (rAll := fun S2 T1 T2 => o ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (rAll' := fun S2 T1 T2 => o' ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩)
      (fun S2 T1 T2 => hF ⟨_, Γ.cons S2, .sub T1 T2⟩)
      (fun S2 T1 T2 => hd ⟨_, Γ.cons S2, .sub T1 T2⟩) S T
  | var x V T =>
    exact varStep_dom (r := fun q => o ⟨s, Γ, q⟩) (r' := fun q => o' ⟨s, Γ, q⟩)
      (fun q => hF ⟨s, Γ, q⟩) (fun q => hd ⟨s, Γ, q⟩) x V T

/-! ## The entry points keep an answer with more fuel

A run whose index is the fuel left is framed, as `declsAt` is.  A run that
ends unmarked never reached index zero, so it does the same at any larger
index.  So `subF` and `varF` are framed, and `sub?` and `var?` keep an answer
at any larger fuel. -/

section RunLeft

variable {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat} {F : Step G R}

/-- An answer of the run leaves the tank unmarked. -/
theorem run_some {d : Nat} {P : List G} {g : G} {t : Tank} {x : R g}
    (h : (run cost F d P g t).1 = some x) : (run cost F d P g t).2.out = false := by
  cases d with
  | zero => simp [run] at h
  | succ d =>
    rw [run_succ] at h ⊢
    exact node_some (k := F (run cost F d (g :: P)) g) (Prod.ext h rfl)

/-- The run at the index of the fuel left is framed. -/
theorem runLeft_framed (hF : FrameF F) (P : List G) (g : G) :
    Framed (fun t => run cost F t.left P g t) where
  absorbs t ht := (run_framed hF t.left P g).absorbs t ht
  spends t := (run_framed hF t.left P g).spends t
  shift := by
    intro t r t' h ho k
    have h1 := run_frame hF h ho k
    have h2 : (run cost F t.left P g (t.add k)).2.out = false := by
      rw [h1]
      exact ho
    change run cost F (t.left + k) P g (t.add k) = _
    rw [run_index hF h2 (Nat.le_add_right _ _), h1]

end RunLeft

theorem subF_framed {s : Sig} (Γ : Ctx s) (S T : Ty s) : Framed (subF Γ S T) :=
  runLeft_framed step_frame [] ⟨s, Γ, .sub S T⟩

theorem varF_framed {s : Sig} (Γ : Ctx s) (x : BVar s .var) (T : Ty s) : Framed (varF Γ x T) :=
  mapO_framed _ (runLeft_framed step_frame [] ⟨s, Γ, .var x (Γ.lookup x) T⟩)

/-- A full tank of `n` units with `m - n` more is a full tank of `m` units. -/
theorem full_add {n m : Nat} (h : n ≤ m) : (⟨n, false⟩ : Tank).add (m - n) = ⟨m, false⟩ := by
  simp only [Tank.add, Tank.mk.injEq, and_true]
  omega

theorem sub?_mono {s : Sig} {Γ : Ctx s} {S T : Ty s} {n m : Nat} {e : Sub Γ S T}
    (h : (sub? Γ S T n).1 = some e) (hnm : n ≤ m) : (sub? Γ S T m).1 = some e := by
  have ho : (sub? Γ S T n).2.out = false := run_some (cost := cost) (P := []) h
  have := (subF_framed Γ S T).shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  change (subF Γ S T ⟨m, false⟩).1 = some e
  rw [this]

theorem var?_mono {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n m : Nat} {e : Var Γ x T}
    (h : (var? Γ x T n).1 = some e) (hnm : n ≤ m) : (var? Γ x T m).1 = some e := by
  have ho : (var? Γ x T n).2.out = false := by
    simp only [var?, varF, mapO, Fu.bind, Fu.ret] at h ⊢
    cases hr : run cost step n [] ⟨s, Γ, .var x (Γ.lookup x) T⟩ ⟨n, false⟩ with
    | mk o t1 =>
      rw [hr] at h
      cases o with
      | none => simp at h
      | some f =>
        have := run_some (cost := cost) (F := step) (d := n) (P := [])
          (g := ⟨s, Γ, .var x (Γ.lookup x) T⟩) (t := ⟨n, false⟩) (x := f) (by rw [hr])
        rw [hr] at this
        exact this
  have := (varF_framed Γ x T).shift ⟨n, false⟩ (some e) _ (Prod.ext h rfl) ho (m - n)
  rw [full_add hnm] at this
  change (varF Γ x T ⟨m, false⟩).1 = some e
  rw [this]

/-! ## Reading a run

`answers` and `rejects` read the result of a run from a full tank.  Each
says whether the run answered, that it ended with the tank unmarked, and how
many units it used.  So one kernel check evaluates the run once.  A run that
ends unmarked uses the same units at every larger fuel. -/

/-- The run from a full tank of `n` units answered, ended unmarked and used
`k` units. -/
def answers {α : Type} (r : Option α × Tank) (k : Nat) (n : Nat := defaultFuel) : Bool :=
  match r with
  | (some _, t) => !t.out && n - t.left == k
  | (none, _) => false

/-- The run from a full tank of `n` units gave no answer, ended unmarked and
used `k` units. -/
def rejects {α : Type} (r : Option α × Tank) (k : Nat) (n : Nat := defaultFuel) : Bool :=
  match r with
  | (none, t) => !t.out && n - t.left == k
  | (some _, _) => false

theorem answers_isSome {α : Type} {r : Option α × Tank} {k n : Nat} (h : answers r k n = true) :
    r.1.isSome = true ∧ r.2.out = false := by
  obtain ⟨o, t⟩ := r
  cases o with
  | none => simp [answers] at h
  | some _ =>
    simp only [answers, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨rfl, h.1⟩

/-- A rejection read off a run is a run that ends with no answer and the tank
unmarked. -/
theorem rejects_eq {α : Type} {r : Option α × Tank} {k n : Nat} (h : rejects r k n = true) :
    r = (none, ⟨r.2.left, false⟩) := by
  obtain ⟨o, t⟩ := r
  cases o with
  | some _ => simp [rejects] at h
  | none =>
    simp only [rejects, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨left, out⟩ := t
    simp only at h
    rw [h.1]

/-! ## Checks

Each check runs in the kernel at the default fuel. -/

section SubChecks

open DotMNF.Examples

/-- After `let t : ⊤ = x` in E1: `x : {A : ⊤..⊥}`, `t : ⊤`. -/
def E1sCtx1 : Ctx ([],x,x) := .cons E1Ctx .top

/-- After `let u : x.A = t` in E1. -/
def E1sCtx2 : Ctx ([],x,x,x) := .cons E1sCtx1 (.sel (.var (.there .here)) lA)

/-- `μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥..{a : ⊤}}))`. -/
def P1M {s : Sig} : Ty s := .mu (.and (.fld lb .top) (.and (.fld lv .top) (.typ lA .bot (.fld la .top))))

/-- `∀(y : P1M) y.A`. -/
def P1S : Ty [] := .all P1M (.sel (.var .here) lA)

/-- `∀(y : P1M) {a : ⊤}`. -/
def P1T : Ty [] := .all P1M (.fld la .top)

/-- `n` variables. -/
def chainBase : Nat → Sig
  | 0 => []
  | n + 1 => Sig.extend (chainBase n) .var

/-- The signature of an alias chain of `n` links: `n + 1` variables. -/
def chainSig (n : Nat) : Sig := Sig.extend (chainBase n) .var

/-- `x0 : {A : ⊥..⊤}` and `xk : {A : x(k-1).A .. x(k-1).A}` for `k = 1..n`. -/
def chainCtx : (n : Nat) → Ctx (chainSig n)
  | 0 => Ctx.nil.cons (.typ lA .bot .top)
  | n + 1 => (chainCtx n).cons (.typ lA (.sel (.var .here) lA) (.sel (.var .here) lA))

/-- `x0`, seen from the end of a chain of `n` links. -/
def chainFirst : (n : Nat) → BVar (chainSig n) .var
  | 0 => .here
  | n + 1 => .there (chainFirst n)

/-- `xn.A`, the last selection of the chain. -/
def chainTop (n : Nat) : Ty (chainSig n) := .sel (.var .here) lA

/-- `x0.A`, the first selection of the chain. -/
def chainBot (n : Nat) : Ty (chainSig n) := .sel (.var (chainFirst n)) lA

/-- R1's context at the projection: `x : {A : ⊥..{a : ⊤}}`,
`y : x.A ∧ {a : {b : ⊤}}`. -/
def R1Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.typ lA .bot (.fld la .top))).cons (.and (.sel (.var .here) lA) (.fld la (.fld lb .top)))

-- E6: `Int <: x.T` at the self binder, the member read on demand.
example : answers (sub? E6Ctxz E6Int (.sel (.var .here) lT)) 12 = true := by decide +kernel
example : answers (var? E6Ctxz (.there .here) (.sel (.var .here) lT)) 12 = true := by decide +kernel

-- E8: `x.A <: {a : ⊤}` through the upper bound.
example : answers (sub? E8Ctx2 (.sel (.var (.there .here)) lA) (.fld la .top)) 4 = true := by
  decide +kernel
-- The converse of E8 fails: the lower bound of `x.A` is `⊥`.
example : rejects (sub? E8Ctx2 (.fld la .top) (.sel (.var (.there .here)) lA)) 2 = true := by
  decide +kernel

-- E1s: `t : ⊤` is shown at `x.A` through the lower bound `⊤`.
example : answers (var? E1sCtx1 .here (.sel (.var (.there .here)) lA)) 4 = true := by decide +kernel
-- E1s: `u : x.A` is shown at `{B : {a : ⊤}..{a : ⊤}}` through the upper bound `⊥`.
example : answers (var? E1sCtx2 .here E1Res) 7 = true := by decide +kernel

-- E3s: `{b : ⊤} <: x.A` through the second member's lower bound.
example : answers (sub? E3Ctx2 E3T2 (.sel (.var (.there .here)) lA)) 8 = true := by decide +kernel
-- E3s: `x.A <: {a : ⊤}` through the first member's upper bound.
example : answers (sub? E3Ctx2 (.sel (.var (.there .here)) lA) E3T1) 8 = true := by decide +kernel

-- P1: a member three levels down a recursive binder, under a `∀`.
example : answers (sub? .nil P1S P1T) 25 = true := by decide +kernel

-- P2: an alias chain of seven links, both ways.
example : answers (sub? (chainCtx 7) (chainTop 7) (chainBot 7)) 50 = true := by decide +kernel
example : answers (sub? (chainCtx 7) (chainBot 7) (chainTop 7)) 43 = true := by decide +kernel

-- Alias chains of 16 and 32 links.
example : answers (sub? (chainCtx 16) (chainTop 16) (chainBot 16)) 185 = true := by decide +kernel
example : answers (sub? (chainCtx 32) (chainTop 32) (chainBot 32)) 625 = true := by decide +kernel

-- E7: the alias cycle `x.A = x.B`, `x.B = x.A`.  The cut ends the search for a
-- field, with the tank unmarked.  The two aliases are related.
example : rejects (sub? E7Ctx (.sel (.var .here) lA) (.fld la .top)) 24 = true := by decide +kernel
example : answers (sub? E7Ctx (.sel (.var .here) lA) (.sel (.var .here) lB)) 12 = true := by
  decide +kernel

-- R1: `y : x.A ∧ {a : {b : ⊤}}` has the field `{a : {b : ⊤}}`, by the right operand.
example : answers (var? R1Ctx .here (.fld la (.fld lb .top))) 18 = true := by decide +kernel

-- E1, E3 and E4 as written are rejected with the tank unmarked, as the compiler rejects them.
example : rejects (sub? E1Ctx E1Dom E1Res) 1 = true := by decide +kernel
example : rejects (var? E1Ctx .here E1Res) 3 = true := by decide +kernel
example : rejects (sub? E3Ctx2 E3T2 E3T1) 1 = true := by decide +kernel
example : rejects (sub? E4Ctx4 E4Int (.sel (.var (.there (.there .here))) lA)) 2 = true := by
  decide +kernel
example : rejects (var? E4Ctx4 (.there .here) (.sel (.var (.there (.there .here))) lA)) 5 = true := by
  decide +kernel

end SubChecks

end Frontend.Core
