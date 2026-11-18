import Coercions.DotMNF.Structural

/-!
# CoDot core: coercions, views and coercion evaluation

Types are those of `DotMNF`. New here: coercions, their static typing, views
(a store location under a list of structural wrappers), coercion evaluation
on views, and the typing of views and of evaluation states.

The store holds real values only. A reference is a location together with a
coercion; no proxy is allocated, so a type never mentions anything but a
location. Coercion evaluation reads one thing from the store: which type
members an object defines (the parameter `D` of `Step`). Typing takes the
store as a context `Γ` (location ↦ precise type) with the invariant `Ctx.WF`.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Coercions -/

/-- Coercions. `unfold`/`fold` act on the subject of the judgment. In
`all c d` the codomain coercion `d` binds the argument. In `up x A k` and
`down x A k` the evidence `k` is a coercion on the type of `x`. -/
inductive Co : Sig → Type where
  | id : Co s
  | top : Co s
  | bot : Co s
  | seq : Co s → Co s → Co s
  | unfold : Co s
  | fold : Co s
  | andL : Co s → Co s
  | andR : Co s → Co s
  | pair : Co s → Co s → Co s
  | fld : Label → Co s → Co s
  | typ : Label → Co s → Co s → Co s
  | all : Co s → Co (s,x) → Co s
  | up : BVar s .var → Label → Co s → Co s
  | down : BVar s .var → Label → Co s → Co s

def Co.rename : Co s1 → Rename s1 s2 → Co s2
  | .id, _ => .id
  | .top, _ => .top
  | .bot, _ => .bot
  | .seq c d, ρ => .seq (c.rename ρ) (d.rename ρ)
  | .unfold, _ => .unfold
  | .fold, _ => .fold
  | .andL c, ρ => .andL (c.rename ρ)
  | .andR c, ρ => .andR (c.rename ρ)
  | .pair c d, ρ => .pair (c.rename ρ) (d.rename ρ)
  | .fld a c, ρ => .fld a (c.rename ρ)
  | .typ A c d, ρ => .typ A (c.rename ρ) (d.rename ρ)
  | .all c d, ρ => .all (c.rename ρ) (d.rename ρ.lift)
  | .up x A k, ρ => .up (ρ.var x) A (k.rename ρ)
  | .down x A k, ρ => .down (ρ.var x) A (k.rename ρ)

def Co.weaken (c : Co s) : Co (s,x) := c.rename Rename.succ

/-! ## Contexts -/

/-- A context, extensionally: the type of each variable in the current scope. -/
structure Ctx (s : Sig) where
  lookup : BVar s .var → Ty s

def Ctx.cons (Γ : Ctx s) (T : Ty s) : Ctx (s,x) where
  lookup
    | .here => T.weaken
    | .there y => (Γ.lookup y).weaken

/-! ## Static typing of coercions

`CoTy Γ o c S T`: `c` takes `S` to `T` for a subject that denotes `o`
(`some x`), or for any subject (`none`). Only `unfold`/`fold` need a subject.
The coercions stored inside `fld`, `typ`, `all` act on other values and are
typed for no subject. The evidence of `up`/`down` is a coercion on the context
type of the receiver `x`, with subject `x`; the subject `o` of the conclusion
is unrelated to `x`. -/
inductive CoTy : {s : Sig} → Ctx s → Option (BVar s .var) → Co s → Ty s → Ty s → Prop where
  | id : CoTy Γ o .id S S
  | top : CoTy Γ o .top S .top
  | bot : CoTy Γ o .bot .bot T
  | seq : CoTy Γ o c S T → CoTy Γ o d T U → CoTy Γ o (.seq c d) S U
  | unfold : CoTy Γ (some x) .unfold (.mu T) (T.substVar x)
  | fold : CoTy Γ (some x) .fold (T.substVar x) (.mu T)
  | andL : CoTy Γ o c S T → CoTy Γ o (.andL c) (.and S U) T
  | andR : CoTy Γ o c U T → CoTy Γ o (.andR c) (.and S U) T
  | pair : CoTy Γ o c S T → CoTy Γ o d S U → CoTy Γ o (.pair c d) S (.and T U)
  | fld : CoTy Γ none c T U → CoTy Γ o (.fld a c) (.fld a T) (.fld a U)
  | typ : CoTy Γ none c S2 S1 → CoTy Γ none d T1 T2 →
      CoTy Γ o (.typ A c d) (.typ A S1 T1) (.typ A S2 T2)
  | all : CoTy Γ none c S2 S1 → CoTy (Γ.cons S2) none d T1 T2 →
      CoTy Γ o (.all c d) (.all S1 T1) (.all S2 T2)
  | up : CoTy Γ (some x) k (Γ.lookup x) (.typ A S T) →
      CoTy Γ o (.up x A k) (.sel (.var x) A) T
  | down : CoTy Γ (some x) k (Γ.lookup x) (.typ A S T) →
      CoTy Γ o (.down x A k) S (.sel (.var x) A)

/-! ## Store shape: precise types of locations -/

/-- The labels declared by a record type. -/
def labels : Ty s → List Label
  | .typ A _ _ => [A]
  | .fld a _ => [a]
  | .and S T => labels S ++ labels T
  | _ => []

/-- The type of an object literal: an intersection tree of declarations with
precise type members and pairwise distinct labels. This is what definition
typing (`DefsTy`, with `Defs.Distinct`) assigns. -/
inductive Record : {s : Sig} → Ty s → Prop where
  | typ : Record (.typ A U U)
  | fld : Record (.fld a T)
  | and : Record S → Record T → (∀ ℓ, ℓ ∈ labels S → ℓ ∉ labels T) → Record (.and S T)

/-- The type member `A` of a record type. -/
def member : Ty s → Label → Option (Ty s)
  | .typ B _ T, A => if A = B then some T else none
  | .and S T, A => (member T A).or (member S A)
  | _, _ => none

/-- A store context: every location is an object at `μ(T0)` with `T0` a
record type, or a function at `∀(S)T`. -/
def Ctx.WF (Γ : Ctx s) : Prop :=
  ∀ x, (∃ T0, Γ.lookup x = .mu T0 ∧ Record T0) ∨ (∃ S T, Γ.lookup x = .all S T)

/-- The type members that the context's object types define. Progress of
coercion evaluation needs the store predicate `D` to contain it. -/
def Ctx.Defines (Γ : Ctx s) (y : BVar s .var) (A : Label) : Prop :=
  ∃ T0 U, Γ.lookup y = .mu T0 ∧ member T0 A = some U

/-- Intersection components, reflexively. -/
inductive Comp : {s : Sig} → Ty s → Ty s → Prop where
  | refl : Comp T T
  | left : Comp S C → Comp (.and S T) C
  | right : Comp T C → Comp (.and S T) C

/-! ## Views and evaluation states -/

/-- Structural wrappers: the coercions that are kept on a reference. -/
inductive Wrap : Sig → Type where
  | fld : Label → Co s → Wrap s
  | typ : Label → Co s → Co s → Wrap s
  | all : Co s → Co (s,x) → Wrap s
  | pair : Co s → Co s → Wrap s

/-- A view: a location under wrappers, outermost first. -/
structure View (s : Sig) where
  loc : BVar s .var
  ws : List (Wrap s)

/-- Coercion evaluation states. `app e c` applies `c` to the result of `e`;
`up e A ev` and `down e A ev` are bound steps on the result of `e` whose
evidence `ev` (a view of the receiver) is being evaluated. -/
inductive Ev : Sig → Type where
  | ret : View s → Ev s
  | app : Ev s → Co s → Ev s
  | up : Ev s → Label → Ev s → Ev s
  | down : Ev s → Label → Ev s → Ev s

/-- The location an evaluation state is a view of. -/
def Ev.loc : Ev s → BVar s .var
  | .ret w => w.loc
  | .app e _ => e.loc
  | .up e _ _ => e.loc
  | .down e _ _ => e.loc

/-- One step of coercion evaluation. `D y A` says that the object stored at
`y` defines the type member `A`; the store is read only through `D`, in
`upObj` and `downObj`. The relation does not depend on any typing. Nothing is
allocated. -/
inductive Step (D : BVar s .var → Label → Prop) : Ev s → Ev s → Prop where
  | appCtx : Step D e e' → Step D (.app e c) (.app e' c)
  | upSubj : Step D e e' → Step D (.up e A ev) (.up e' A ev)
  | upEv : Step D ev ev' → Step D (.up (.ret w) A ev) (.up (.ret w) A ev')
  | downSubj : Step D e e' → Step D (.down e A ev) (.down e' A ev)
  | downEv : Step D ev ev' → Step D (.down (.ret w) A ev) (.down (.ret w) A ev')
  | id : Step D (.app (.ret w) .id) (.ret w)
  | top : Step D (.app (.ret w) .top) (.ret w)
  | unfold : Step D (.app (.ret w) .unfold) (.ret w)
  | fold : Step D (.app (.ret w) .fold) (.ret w)
  | seq : Step D (.app (.ret w) (.seq c d)) (.app (.app (.ret w) c) d)
  | andLPair :
      Step D (.app (.ret ⟨x, .pair c1 c2 :: ws⟩) (.andL c)) (.app (.app (.ret ⟨x, ws⟩) c1) c)
  | andLOther : (∀ c1 c2 ws', w.ws ≠ .pair c1 c2 :: ws') →
      Step D (.app (.ret w) (.andL c)) (.app (.ret w) c)
  | andRPair :
      Step D (.app (.ret ⟨x, .pair c1 c2 :: ws⟩) (.andR c)) (.app (.app (.ret ⟨x, ws⟩) c2) c)
  | andROther : (∀ c1 c2 ws', w.ws ≠ .pair c1 c2 :: ws') →
      Step D (.app (.ret w) (.andR c)) (.app (.ret w) c)
  | pair : Step D (.app (.ret ⟨x, ws⟩) (.pair c d)) (.ret ⟨x, .pair c d :: ws⟩)
  | fld : Step D (.app (.ret ⟨x, ws⟩) (.fld a c)) (.ret ⟨x, .fld a c :: ws⟩)
  | typ : Step D (.app (.ret ⟨x, ws⟩) (.typ A c d)) (.ret ⟨x, .typ A c d :: ws⟩)
  | all : Step D (.app (.ret ⟨x, ws⟩) (.all c d)) (.ret ⟨x, .all c d :: ws⟩)
  | upStart : Step D (.app (.ret w) (.up y A k)) (.up (.ret w) A (.app (.ret ⟨y, []⟩) k))
  | downStart : Step D (.app (.ret w) (.down y A k)) (.down (.ret w) A (.app (.ret ⟨y, []⟩) k))
  | upObj : D y A → Step D (.up (.ret w) A (.ret ⟨y, []⟩)) (.ret w)
  | upTyp :
      Step D (.up (.ret w) A (.ret ⟨y, .typ A c d :: ws⟩)) (.app (.up (.ret w) A (.ret ⟨y, ws⟩)) d)
  | downObj : D y A → Step D (.down (.ret w) A (.ret ⟨y, []⟩)) (.ret w)
  | downTyp :
      Step D (.down (.ret w) A (.ret ⟨y, .typ A c d :: ws⟩))
        (.down (.app (.ret w) c) A (.ret ⟨y, ws⟩))

/-! ## Typing of views and evaluation states -/

/-- One resolution step for a view of `x`: unfold a recursive type at `x`, or
replace `y.A` by the type member the object at `y` defines. Deterministic. -/
inductive Res (Γ : Ctx s) (x : BVar s .var) : Ty s → Ty s → Prop where
  | mu : Res Γ x (.mu T) (T.substVar x)
  | sel : Γ.lookup y = .mu T0 → member T0 A = some U →
      Res Γ x (.sel (.var y) A) (U.substVar y)

inductive ResStar (Γ : Ctx s) (x : BVar s .var) : Ty s → Ty s → Prop where
  | refl : ResStar Γ x T T
  | head : Res Γ x S M → ResStar Γ x M T → ResStar Γ x S T

/-- Typing of a wrapper on a view of `x`. -/
inductive WrapTy (Γ : Ctx s) (x : BVar s .var) : Wrap s → Ty s → Ty s → Prop where
  | fld : CoTy Γ none c T U → WrapTy Γ x (.fld a c) (.fld a T) (.fld a U)
  | typ : CoTy Γ none c S2 S1 → CoTy Γ none d T1 T2 →
      WrapTy Γ x (.typ A c d) (.typ A S1 T1) (.typ A S2 T2)
  | all : CoTy Γ none c S2 S1 → CoTy (Γ.cons S2) none d T1 T2 →
      WrapTy Γ x (.all c d) (.all S1 T1) (.all S2 T2)
  | pair : CoTy Γ (some x) c S T → CoTy Γ (some x) d S U →
      WrapTy Γ x (.pair c d) S (.and T U)

/-- Typing of views. A view has the types that resolve to one of its core
types: the precise type of a bare location; the intersection components of a
bare object's opened record type; the target of the outermost wrapper; `⊤`.
No rule gives a component of a `pair` wrapper's target. -/
inductive VTy (Γ : Ctx s) : View s → Ty s → Prop where
  | self : ResStar Γ x T (Γ.lookup x) → VTy Γ ⟨x, []⟩ T
  | comp : Γ.lookup x = .mu T0 → Comp (T0.substVar x) C → ResStar Γ x T C →
      VTy Γ ⟨x, []⟩ T
  | wrap : VTy Γ ⟨x, ws⟩ S → WrapTy Γ x k S N → ResStar Γ x T N →
      VTy Γ ⟨x, k :: ws⟩ T
  | top : ResStar Γ w.loc T .top → VTy Γ w T

/-- Typing of evaluation states. In a bound step the evidence is a view of
the receiver `y`, which need not be the location of the subject. -/
inductive EvTy (Γ : Ctx s) : Ev s → Ty s → Prop where
  | ret : VTy Γ w T → EvTy Γ (.ret w) T
  | app : EvTy Γ e S → CoTy Γ (some e.loc) c S T → EvTy Γ (.app e c) T
  | up : EvTy Γ e (.sel (.var y) A) → EvTy Γ ev (.typ A S T) → ev.loc = y →
      EvTy Γ (.up e A ev) T
  | down : EvTy Γ e S → EvTy Γ ev (.typ A S T) → ev.loc = y →
      EvTy Γ (.down e A ev) (.sel (.var y) A)

/-! ## Coerced substitution -/

/-- A coerced renaming: each variable goes to a variable under a coercion. -/
structure CoSub (s1 s2 : Sig) where
  ρ : Rename s1 s2
  η : BVar s1 .var → Co s2

def CoSub.lift (σ : CoSub s1 s2) : CoSub (s1,x) (s2,x) where
  ρ := σ.ρ.lift
  η
    | .here => .id
    | .there y => (σ.η y).weaken

/-- Apply a coerced renaming to a coercion. Variables occur in coercions only
as the receivers of bound steps; the coercion of the receiver is put in front
of the evidence. -/
def Co.csubst : Co s1 → CoSub s1 s2 → Co s2
  | .id, _ => .id
  | .top, _ => .top
  | .bot, _ => .bot
  | .seq c d, σ => .seq (c.csubst σ) (d.csubst σ)
  | .unfold, _ => .unfold
  | .fold, _ => .fold
  | .andL c, σ => .andL (c.csubst σ)
  | .andR c, σ => .andR (c.csubst σ)
  | .pair c d, σ => .pair (c.csubst σ) (d.csubst σ)
  | .fld a c, σ => .fld a (c.csubst σ)
  | .typ A c d, σ => .typ A (c.csubst σ) (d.csubst σ)
  | .all c d, σ => .all (c.csubst σ) (d.csubst σ.lift)
  | .up x A k, σ => .up (σ.ρ.var x) A (.seq (σ.η x) (k.csubst σ))
  | .down x A k, σ => .down (σ.ρ.var x) A (.seq (σ.η x) (k.csubst σ))

/-- `σ` is typed from `Γ1` to `Γ2`: the coercion of `x` takes the context
type of its image to the renamed context type of `x`, with that image as
subject. -/
def CoSub.Ok (Γ1 : Ctx s1) (Γ2 : Ctx s2) (σ : CoSub s1 s2) : Prop :=
  ∀ x, CoTy Γ2 (some (σ.ρ.var x)) (σ.η x) (Γ2.lookup (σ.ρ.var x)) ((Γ1.lookup x).rename σ.ρ)

/-- Replace the innermost variable by the reference `z ▷ e`. -/
def CoSub.inst (z : BVar s .var) (e : Co s) : CoSub (s,x) s where
  ρ := Rename.subst z
  η
    | .here => e
    | .there _ => .id

end CoDot
