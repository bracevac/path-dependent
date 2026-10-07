import Coercions.Oopsla16.Frontend.Decide

/-!
# Views and the subtyping search

The typer asks two questions of a context that this module answers, each
with a derivation of the version's own judgments.

* A *view* of a context variable `x` is a type of `x`'s own prefix scope with
  an `Oopsla16.Htp` derivation.  `Htp` is the judgment the two selection rules
  `stp_sel1` and `stp_sel2` consult.  It types `x` in the context truncated at
  `x`, and it has no packing rule.  `hviews` computes the views a fixed number
  of rounds deep.
* `sub?` searches for an `Oopsla16.Stp` derivation between two types, at a
  fuel.

Everything returns the derivation, so there is no soundness theorem: the
result type is the statement.  Subtyping in this calculus is undecidable, so
nothing here is complete and no completeness theorem is claimed.

## The view closure

The closure starts at `htp_var`, the recorded type of `x`, and every round
adds one step from every view it has.

| view | new view | rule |
|---|---|---|
| `μ T` | `T` opened at `x` | `htp_unpack` |
| `A ∧ B` | `A` and `B` | `htp_sub` with `stp_and11`, `stp_and12` |
| `y.L` | the upper bound `U` of a member `{type L : _..U}` of a view of `y` | `htp_sub` with `stp_sel1` |

The selection step reads the bound off the views of `y` in the context
truncated at `x`, one round shallower.  So the closure recurses on the round
count and nothing else, and needs no subtyping search.  The truncation is
the one `htp_sub` demands: a hypothesis younger than `x`, such as the self
assumption of an enclosing `stp_bindx`, is out of scope there.  The front end
therefore cannot build the packing derivation that would make the calculus
unsound (`Oopsla16.PackingCounterexample`), by the types of its functions.

A type member's bounds are not moved by a closure step.  A rule that wants
`{type L : ⊥..U}` from a view `{type L : S..U}` builds the move itself
(`lowerBot`, `upperTop`), so one view serves both selection rules.

Duplicates are dropped by type after every round.  Without that the views of
a variable whose type repeats a selection multiply with every round, and a
failing branch of the search pays for each copy.

## The search

`sub? b n Γ S T` tries the rules below in order and returns the first
derivation found.  Each recursive premise is a call at fuel `n - 1`.

1. `S = T`: reflexivity, derived by `Oopsla16.Stp.refl`.
2. `T = ⊤`: `stp_top`.  `S = ⊥`: `stp_bot`.
3. `T = T₁ ∧ T₂`: `stp_and2`.
4. `S = μ T₁` and `T = μ T₂`: `stp_bindx`, the bodies under the self assumed
   at the left body.
5. Two method types at one label: `stp_fun`, the codomains under the new
   domain.
6. Two type members at one label: `stp_typ`.
7. `S = S₁ ∧ S₂`: `stp_and11`, then `stp_and12`.
8. `S = S₁ ∨ S₂`: `stp_or1`.  `T = T₁ ∨ T₂`: `stp_or21`, then `stp_or22`.
9. `S = μ T₁`: `stp_bind1`, the body against `T` weakened past the self.
10. `S = x.L`: `stp_sel1` at a view of `x`, then `stp_trans` to `T` unless the
    upper bound is `T`.
11. `T = x.L`: `stp_sel2` at a view of `x`, after `stp_trans` from `S` unless
    the lower bound is `S`.

Rules 10 and 11 are the one place where `stp_trans` is tried, with a middle
read off a view.  Rule 4 comes before rule 9, so two recursive types are
compared body to body before the left self is forgotten.

## Fuel and rounds

`Budget` holds three counters: rounds of the view closure, fuel of the
search, fuel of the typer.  Both `hviews` and `sub?` are structural, on the
round count and on the fuel, so the kernel reduces them, and every check at
the end of this module is decided by `decide +kernel`.  Their monotonicity is stated below: more rounds
never lose the type of a view, and more fuel never loses an answer.  The
second is proved rule by rule, each rule being monotone in the search it
calls.

Nothing in this module is part of the metatheory and no definition here
lives in the `Oopsla16` namespace.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Ty Ctx Store Stp Htp scopeUpTo renameUpTo varUpTo)

/-! ## The budget -/

/-- The three counters of the front end.  The defaults are a starting
point, and the budget each probe is found at is stated beside it. -/
structure Budget where
  /-- Rounds of the view closure. -/
  views : Nat := 4
  /-- Fuel of the subtyping search. -/
  sub : Nat := 8
  /-- Fuel of the typer. -/
  typer : Nat := 12
deriving Repr, Inhabited, DecidableEq

/-! ## Two list and option helpers -/

/-- The first success of `f` along a list. -/
def firstSome {α β : Type} (f : α → Option β) (l : List α) : Option β :=
  match l with
  | [] => none
  | a :: as =>
      match f a with
      | some b => some b
      | none => firstSome f as
termination_by structural l

/-- `firstSome` succeeds when some element succeeds. -/
theorem firstSome_isSome {α β : Type} {f : α → Option β} :
    {l : List α} → (firstSome f l).isSome = true ↔ ∃ a ∈ l, (f a).isSome = true
  | [] => by simp [firstSome]
  | a :: as => by
      unfold firstSome
      cases h : f a with
      | some b => simp [h]
      | none =>
          simp only [List.mem_cons, exists_eq_or_imp, h]
          rw [firstSome_isSome]
          simp

/-- `firstSome` is monotone in the function it walks with. -/
theorem firstSome_mono {α β γ : Type} {f : α → Option β} {g : α → Option γ}
    (h : ∀ a, (f a).isSome = true → (g a).isSome = true) {l : List α}
    (hf : (firstSome f l).isSome = true) : (firstSome g l).isSome = true := by
  obtain ⟨a, ha, hfa⟩ := firstSome_isSome.mp hf
  exact firstSome_isSome.mpr ⟨a, ha, h a hfa⟩

/-- An alternative succeeds when either side does, so it is monotone in
both. -/
theorem orElse_mono {α : Type} {a a' : Option α} {b b' : Option α}
    (ha : a.isSome = true → a'.isSome = true) (hb : b.isSome = true → b'.isSome = true) :
    (a <|> b).isSome = true → (a' <|> b').isSome = true := by
  cases a with
  | some x =>
      intro _
      cases a' with
      | some y => rfl
      | none => cases ha rfl
  | none =>
      intro h
      cases a' with
      | some y => rfl
      | none => exact hb h

/-- Two premises in sequence succeed when both do, so the pair is monotone
in each. -/
theorem bindMap_mono {α β γ : Type} {a a' : Option α} {b b' : Option β} {f g : α → β → γ}
    (ha : a.isSome = true → a'.isSome = true) (hb : b.isSome = true → b'.isSome = true) :
    (a.bind fun x => b.map (f x)).isSome = true →
      (a'.bind fun x => b'.map (g x)).isSome = true := by
  cases a with
  | none => intro h; cases h
  | some x =>
      cases b with
      | none => intro h; cases h
      | some y =>
          intro _
          cases a' with
          | none => cases ha rfl
          | some x' =>
              cases b' with
              | none => cases hb rfl
              | some y' => rfl

/-- One premise, mapped to a conclusion, is monotone in the premise. -/
theorem map_mono {α β γ : Type} {a : Option α} {a' : Option β} {f : α → γ} {g : β → γ}
    (ha : a.isSome = true → a'.isSome = true) :
    (a.map f).isSome = true → (a'.map g).isSome = true := by
  simpa using ha

/-! ## Views -/

/-- A type a context variable has in its own prefix scope, with the `Htp`
derivation. -/
structure HView {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) where
  /-- The type, in the scope of `x` and the binders older than `x`. -/
  ty : Ty [] (scopeUpTo x)
  /-- The derivation. -/
  deriv : Htp Store.nil Γ x ty

/-- Membership of a type in a list of types, as a decision. -/
def tyMem? {s : Sig} (T : Ty [] s) (l : List (Ty [] s)) : Bool :=
  match l with
  | [] => false
  | U :: Us => if U = T then true else tyMem? T Us
termination_by structural l

theorem tyMem?_cons {s : Sig} (T U : Ty [] s) (Us : List (Ty [] s)) :
    tyMem? T (U :: Us) = true ↔ (U = T ∨ tyMem? T Us = true) := by
  by_cases h : U = T
  · simp [tyMem?, h]
  · simp [tyMem?, h]

/-- Views whose type is already in `seen` are dropped, and the first view of
every other type is kept. -/
def dedupViewsFrom {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (seen : List (Ty [] (scopeUpTo x)))
    (l : List (HView Γ x)) : List (HView Γ x) :=
  match l with
  | [] => []
  | v :: vs =>
      if tyMem? v.ty seen then dedupViewsFrom seen vs
      else v :: dedupViewsFrom (v.ty :: seen) vs
termination_by structural l

/-- Keep the first view of each type. -/
def dedupViews {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (l : List (HView Γ x)) :
    List (HView Γ x) :=
  dedupViewsFrom [] l

/-- A type member with its lower bound moved to `⊥`.  When the bound is
already `⊥` the derivation is the one given. -/
def lowerBot {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {l : Lb} {lo hi : Ty [] (scopeUpTo x)}
    (d : Htp Store.nil Γ x (.TTyp l lo hi)) : Htp Store.nil Γ x (.TTyp l .TBot hi) :=
  if h : lo = .TBot then h ▸ d else .htp_sub d (.stp_typ .stp_bot (Oopsla16.Stp.refl hi))

/-- A type member with its upper bound moved to `⊤`.  When the bound is
already `⊤` the derivation is the one given. -/
def upperTop {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {l : Lb} {lo hi : Ty [] (scopeUpTo x)}
    (d : Htp Store.nil Γ x (.TTyp l lo hi)) : Htp Store.nil Γ x (.TTyp l lo .TTop) :=
  if h : hi = .TTop then h ▸ d else .htp_sub d (.stp_typ (Oopsla16.Stp.refl lo) .stp_top)

/-- The selection step: a view `y.L` of `x`, and a view of `y` in the
context truncated at `x` with a member `L`, give `x` the member's upper
bound. -/
def widenAt {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {y : BVar (scopeUpTo x) .var} {l : Lb}
    (d : Htp Store.nil Γ x (.TSel (.abs y) l)) (w : HView (Γ.upTo x) y) : Option (HView Γ x) :=
  match w with
  | ⟨.TTyp l' lo hi, e⟩ =>
      if hl : l' = l then
        some ⟨hi.rename (renameUpTo y), .htp_sub d (.stp_sel1 (hl ▸ lowerBot (lo := lo) e))⟩
      else none
  | _ => none

/-- The views one step from a view.  `pre y` are the views of a variable `y`
of `x`'s prefix, in the context truncated at `x`. -/
def hstep {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    (pre : (y : BVar (scopeUpTo x) .var) → List (HView (Γ.upTo x) y)) (v : HView Γ x) :
    List (HView Γ x) :=
  match v with
  | ⟨.TBind _, d⟩ => [⟨_, .htp_unpack d⟩]
  | ⟨.TAnd A B, d⟩ =>
      [⟨A, .htp_sub d (.stp_and11 (Oopsla16.Stp.refl A))⟩,
       ⟨B, .htp_sub d (.stp_and12 (Oopsla16.Stp.refl B))⟩]
  | ⟨.TSel (.abs _) _, d⟩ => (pre _).filterMap (widenAt d)
  | _ => []

/-- One round of the closure: every view of the list, one step from each,
and the duplicates by type dropped. -/
def hround {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    (pre : (y : BVar (scopeUpTo x) .var) → List (HView (Γ.upTo x) y)) (vs : List (HView Γ x)) :
    List (HView Γ x) :=
  dedupViews (vs ++ vs.flatMap (hstep pre))

/-- The views of `x` after `k` rounds of the closure.  The selection step of
round `k + 1` reads the views of round `k` of the variables in the prefix. -/
def hviews (k : Nat) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) : List (HView Γ x) :=
  match k with
  | 0 => [⟨Γ.lookupAt x, .htp_var⟩]
  | k + 1 => hround (fun y => hviews k (Γ.upTo x) y) (hviews k Γ x)
termination_by structural k

/-! ## The subtyping search -/

/-- A subtyping search at one fuel, the form in which the rules receive their
recursive calls. -/
abbrev Search : Type :=
  ∀ {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s), Option (Stp Store.nil Γ S T)

/-- Every answer of the first search is found by the second. -/
def SearchLe (r r' : Search) : Prop :=
  ∀ {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s), (r Γ S T).isSome = true → (r' Γ S T).isSome = true

/-- Rule 1, reflexivity at equal types. -/
def ruleEq {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Option (Stp Store.nil Γ S T) :=
  if h : S = T then some (h ▸ Oopsla16.Stp.refl S) else none

/-- Rule 2, `stp_top`. -/
def ruleTop {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Option (Stp Store.nil Γ S T) :=
  match T with
  | .TTop => some .stp_top
  | _ => none

/-- Rule 2, `stp_bot`. -/
def ruleBot {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) : Option (Stp Store.nil Γ S T) :=
  match S with
  | .TBot => some .stp_bot
  | _ => none

/-- Rule 3, `stp_and2`. -/
def ruleAndR (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match T with
  | .TAnd T1 T2 => (rec Γ S T1).bind fun a => (rec Γ S T2).map (.stp_and2 a)
  | _ => none

/-- Rule 4, `stp_bindx`: the bodies, under the self assumed at the left
body. -/
def ruleBindx (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S, T with
  | .TBind T1, .TBind T2 => (rec (Γ.cons T1) T1 T2).map .stp_bindx
  | _, _ => none

/-- Rule 5, `stp_fun`: the domains contravariantly, the codomains under the
new domain. -/
def ruleFun (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S, T with
  | .TFun l1 T1 T2, .TFun l2 T3 T4 =>
      if h : l1 = l2 then
        (rec Γ T3 T1).bind fun a => (rec (Γ.cons T3.weaken) T2 T4).map fun b => h ▸ .stp_fun a b
      else none
  | _, _ => none

/-- Rule 6, `stp_typ`. -/
def ruleTyp (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S, T with
  | .TTyp l1 T1 T2, .TTyp l2 T3 T4 =>
      if h : l1 = l2 then
        (rec Γ T3 T1).bind fun a => (rec Γ T2 T4).map fun b => h ▸ .stp_typ a b
      else none
  | _, _ => none

/-- Rule 7, `stp_and11`, then `stp_and12`. -/
def ruleAndL (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S with
  | .TAnd S1 S2 => (rec Γ S1 T).map .stp_and11 <|> (rec Γ S2 T).map .stp_and12
  | _ => none

/-- Rule 8, `stp_or1`. -/
def ruleOrL (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S with
  | .TOr S1 S2 => (rec Γ S1 T).bind fun a => (rec Γ S2 T).map (.stp_or1 a)
  | _ => none

/-- Rule 8, `stp_or21`, then `stp_or22`. -/
def ruleOrR (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match T with
  | .TOr T1 T2 => (rec Γ S T1).map .stp_or21 <|> (rec Γ S T2).map .stp_or22
  | _ => none

/-- Rule 9, `stp_bind1`: forget a self the right side does not mention. -/
def ruleBind1 (rec : Search) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S with
  | .TBind T1 => (rec (Γ.cons T1) T1 T.weaken).map .stp_bind1
  | _ => none

/-- Rule 10 at one view of the receiver `x`: `stp_sel1` at the view's member
`L`, then `stp_trans` to `T` unless the upper bound is `T`. -/
def sel1At (rec : Search) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (l : Lb) (T : Ty [] s)
    (v : HView Γ x) : Option (Stp Store.nil Γ (.TSel (.abs x) l) T) :=
  match v with
  | ⟨.TTyp l' lo hi, d⟩ =>
      if hl : l' = l then
        if h : hi.rename (renameUpTo x) = T then
          some (h ▸ .stp_sel1 (hl ▸ lowerBot (lo := lo) d))
        else (rec Γ (hi.rename (renameUpTo x)) T).map (.stp_trans (.stp_sel1 (hl ▸ lowerBot (lo := lo) d)))
      else none
  | _ => none

/-- Rule 11 at one view of the receiver `x`: `stp_sel2` at the view's member
`L`, after `stp_trans` from `S` unless the lower bound is `S`. -/
def sel2At (rec : Search) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (l : Lb) (S : Ty [] s)
    (v : HView Γ x) : Option (Stp Store.nil Γ S (.TSel (.abs x) l)) :=
  match v with
  | ⟨.TTyp l' lo hi, d⟩ =>
      if hl : l' = l then
        if h : S = lo.rename (renameUpTo x) then
          some (h ▸ .stp_sel2 (hl ▸ upperTop (hi := hi) d))
        else (rec Γ S (lo.rename (renameUpTo x))).map fun e =>
          .stp_trans e (.stp_sel2 (hl ▸ upperTop (hi := hi) d))
      else none
  | _ => none

/-- Rule 10, `stp_sel1` through the views of the receiver. -/
def ruleSel1 (rec : Search) (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match S with
  | .TSel (.abs x) l => firstSome (sel1At rec Γ x l T) (hviews k Γ x)
  | _ => none

/-- Rule 11, `stp_sel2` through the views of the receiver. -/
def ruleSel2 (rec : Search) (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match T with
  | .TSel (.abs x) l => firstSome (sel2At rec Γ x l S) (hviews k Γ x)
  | _ => none

/-- The eleven rules in order, at a search `rec` for the premises and `k`
rounds of the view closure. -/
def subRules (rec : Search) (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  ruleEq Γ S T <|> ruleTop Γ S T <|> ruleBot Γ S T <|> ruleAndR rec Γ S T
    <|> ruleBindx rec Γ S T <|> ruleFun rec Γ S T <|> ruleTyp rec Γ S T
    <|> ruleAndL rec Γ S T <|> ruleOrL rec Γ S T <|> ruleOrR rec Γ S T
    <|> ruleBind1 rec Γ S T <|> ruleSel1 rec k Γ S T <|> ruleSel2 rec k Γ S T

/-- The subtyping search at fuel `n`.  Fuel `0` finds nothing.  Fuel `n + 1`
tries the rules with the search at fuel `n` for every premise. -/
def sub? (b : Budget) (n : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    Option (Stp Store.nil Γ S T) :=
  match n with
  | 0 => none
  | n + 1 => subRules (fun Γ' S' T' => sub? b n Γ' S' T') b.views Γ S T
termination_by structural n

/-! ## Monotonicity

More rounds of the closure never lose the type of a view, and more fuel never
loses an answer of the search.  Both statements speak of types and of
`isSome`, not of derivations: deduplication keeps the first derivation of a
type, and more fuel may find another derivation of the same judgment.

The search has no retry clause at the end of its `n + 1` case.  Such a clause
would make monotonicity a one line induction, but it repeats the whole search
at fuel `n` whenever fuel `n + 1` fails, and a failing branch then costs a
factor of about six per two units of fuel where it costs two without it.  So
monotonicity is proved rule by rule instead: every rule is monotone in the
search it receives, and so is their chain. -/

/-- Every type of `l` is the type of a view in `l'`. -/
def ViewsLe {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (l l' : List (HView Γ x)) : Prop :=
  ∀ v ∈ l, ∃ w ∈ l', w.ty = v.ty

theorem viewsLe_refl {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} (l : List (HView Γ x)) :
    ViewsLe l l := fun v hv => ⟨v, hv, rfl⟩

theorem viewsLe_trans {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    {l l' l'' : List (HView Γ x)} (h1 : ViewsLe l l') (h2 : ViewsLe l' l'') : ViewsLe l l'' := by
  intro v hv
  obtain ⟨w, hw, hwty⟩ := h1 v hv
  obtain ⟨u, hu, huty⟩ := h2 w hw
  exact ⟨u, hu, huty.trans hwty⟩

/-- A view dropped by deduplication has its type in `seen` or kept. -/
theorem dedupViewsFrom_covers {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    (l : List (HView Γ x)) :
    ∀ (seen : List (Ty [] (scopeUpTo x))) (v : HView Γ x), v ∈ l →
      tyMem? v.ty seen = true ∨ ∃ w ∈ dedupViewsFrom seen l, w.ty = v.ty := by
  induction l with
  | nil => intro seen v hv; cases hv
  | cons u l ih =>
      intro seen v hv
      by_cases hs : tyMem? u.ty seen = true
      · have heq : dedupViewsFrom seen (u :: l) = dedupViewsFrom seen l := by
          simp [dedupViewsFrom, hs]
        cases List.mem_cons.mp hv with
        | inl he => exact Or.inl (he ▸ hs)
        | inr hv' => rw [heq]; exact ih seen v hv'
      · have heq : dedupViewsFrom seen (u :: l) = u :: dedupViewsFrom (u.ty :: seen) l := by
          simp [dedupViewsFrom, hs]
        cases List.mem_cons.mp hv with
        | inl he => exact Or.inr ⟨u, by rw [heq]; simp, by rw [he]⟩
        | inr hv' =>
            cases ih (u.ty :: seen) v hv' with
            | inl h =>
                cases (tyMem?_cons v.ty u.ty seen).mp h with
                | inl h' => exact Or.inr ⟨u, by rw [heq]; simp, h'⟩
                | inr h' => exact Or.inl h'
            | inr h =>
                obtain ⟨w, hw, hwty⟩ := h
                exact Or.inr ⟨w, by rw [heq]; exact List.mem_cons_of_mem _ hw, hwty⟩

/-- Deduplication keeps one view of each type. -/
theorem dedupViews_covers {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    (l : List (HView Γ x)) : ViewsLe l (dedupViews l) := by
  intro v hv
  cases dedupViewsFrom_covers l [] v hv with
  | inl h => exact absurd h (by simp [tyMem?])
  | inr h => exact h

/-- A round only adds. -/
theorem hround_covers {s : Sig} {Γ : Ctx [] s} {x : BVar s .var}
    (pre : (y : BVar (scopeUpTo x) .var) → List (HView (Γ.upTo x) y)) (vs : List (HView Γ x)) :
    ViewsLe vs (hround pre vs) := fun v hv =>
  dedupViews_covers _ v (List.mem_append_left _ hv)

/-- One more round never loses a type. -/
theorem hviews_succ (k : Nat) {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) :
    ViewsLe (hviews k Γ x) (hviews (k + 1) Γ x) := by
  rw [hviews.eq_2]
  exact hround_covers _ _

/-- **More rounds of the view closure never lose the type of a view.** -/
theorem hviews_mono {k k' : Nat} (h : k ≤ k') {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) :
    ∀ v ∈ hviews k Γ x, ∃ w ∈ hviews k' Γ x, w.ty = v.ty := by
  induction k' with
  | zero =>
      have hk : k = 0 := Nat.le_zero.mp h
      subst hk
      exact viewsLe_refl _
  | succ m ih =>
      cases Nat.lt_or_ge k (m + 1) with
      | inl hlt => exact viewsLe_trans (ih (Nat.lt_succ_iff.mp hlt)) (hviews_succ m Γ x)
      | inr hge =>
          have hk : k = m + 1 := Nat.le_antisymm h hge
          subst hk
          exact viewsLe_refl _

section RuleMono
variable {rec rec' : Search} (hr : SearchLe rec rec')
include hr

theorem ruleAndR_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleAndR rec Γ S T).isSome = true → (ruleAndR rec' Γ S T).isSome = true := by
  intro hs
  cases T <;> simp only [ruleAndR] at hs ⊢
  all_goals first
    | exact bindMap_mono (hr _ _ _) (hr _ _ _) hs
    | exact hs

theorem ruleBindx_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleBindx rec Γ S T).isSome = true → (ruleBindx rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> cases T <;> simp only [ruleBindx] at hs ⊢
  all_goals first
    | exact map_mono (hr _ _ _) hs
    | exact hs

theorem ruleFun_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleFun rec Γ S T).isSome = true → (ruleFun rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> cases T <;> simp only [ruleFun] at hs ⊢
  all_goals first
    | exact hs
    | (rename_i l1 _ _ l2 _ _
       by_cases hl : l1 = l2
       · rw [dif_pos hl] at hs ⊢; exact bindMap_mono (hr _ _ _) (hr _ _ _) hs
       · rw [dif_neg hl] at hs; simp at hs)

theorem ruleTyp_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleTyp rec Γ S T).isSome = true → (ruleTyp rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> cases T <;> simp only [ruleTyp] at hs ⊢
  all_goals first
    | exact hs
    | (rename_i l1 _ _ l2 _ _
       by_cases hl : l1 = l2
       · rw [dif_pos hl] at hs ⊢; exact bindMap_mono (hr _ _ _) (hr _ _ _) hs
       · rw [dif_neg hl] at hs; simp at hs)

theorem ruleAndL_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleAndL rec Γ S T).isSome = true → (ruleAndL rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> simp only [ruleAndL] at hs ⊢
  all_goals first
    | exact orElse_mono (map_mono (hr _ _ _)) (map_mono (hr _ _ _)) hs
    | exact hs

theorem ruleOrL_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleOrL rec Γ S T).isSome = true → (ruleOrL rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> simp only [ruleOrL] at hs ⊢
  all_goals first
    | exact bindMap_mono (hr _ _ _) (hr _ _ _) hs
    | exact hs

theorem ruleOrR_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleOrR rec Γ S T).isSome = true → (ruleOrR rec' Γ S T).isSome = true := by
  intro hs
  cases T <;> simp only [ruleOrR] at hs ⊢
  all_goals first
    | exact orElse_mono (map_mono (hr _ _ _)) (map_mono (hr _ _ _)) hs
    | exact hs

theorem ruleBind1_mono {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleBind1 rec Γ S T).isSome = true → (ruleBind1 rec' Γ S T).isSome = true := by
  intro hs
  cases S <;> simp only [ruleBind1] at hs ⊢
  all_goals first
    | exact map_mono (hr _ _ _) hs
    | exact hs

theorem sel1At_mono {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (l : Lb) (T : Ty [] s)
    (v : HView Γ x) :
    (sel1At rec Γ x l T v).isSome = true → (sel1At rec' Γ x l T v).isSome = true := by
  intro hs
  obtain ⟨ty, d⟩ := v
  cases ty <;> simp only [sel1At] at hs ⊢
  all_goals first
    | exact hs
    | (rename_i l' lo hi
       by_cases hl : l' = l
       · rw [dif_pos hl] at hs ⊢
         by_cases he : hi.rename (renameUpTo x) = T
         · rw [dif_pos he]; rfl
         · rw [dif_neg he] at hs ⊢; exact map_mono (hr _ _ _) hs
       · rw [dif_neg hl] at hs; simp at hs)

theorem sel2At_mono {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (l : Lb) (S : Ty [] s)
    (v : HView Γ x) :
    (sel2At rec Γ x l S v).isSome = true → (sel2At rec' Γ x l S v).isSome = true := by
  intro hs
  obtain ⟨ty, d⟩ := v
  cases ty <;> simp only [sel2At] at hs ⊢
  all_goals first
    | exact hs
    | (rename_i l' lo hi
       by_cases hl : l' = l
       · rw [dif_pos hl] at hs ⊢
         by_cases he : S = lo.rename (renameUpTo x)
         · rw [dif_pos he]; rfl
         · rw [dif_neg he] at hs ⊢; exact map_mono (hr _ _ _) hs
       · rw [dif_neg hl] at hs; simp at hs)

theorem ruleSel1_mono (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleSel1 rec k Γ S T).isSome = true → (ruleSel1 rec' k Γ S T).isSome = true := by
  intro hs
  cases S with
  | TSel v l =>
      cases v with
      | abs x => exact firstSome_mono (sel1At_mono hr Γ x l T) hs
      | conc y => exact hs
  | _ => exact hs

theorem ruleSel2_mono (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (ruleSel2 rec k Γ S T).isSome = true → (ruleSel2 rec' k Γ S T).isSome = true := by
  intro hs
  cases T with
  | TSel v l =>
      cases v with
      | abs x => exact firstSome_mono (sel2At_mono hr Γ x l S) hs
      | conc y => exact hs
  | _ => exact hs

/-- The chain of rules is monotone in the search it receives. -/
theorem subRules_mono (k : Nat) {s : Sig} (Γ : Ctx [] s) (S T : Ty [] s) :
    (subRules rec k Γ S T).isSome = true → (subRules rec' k Γ S T).isSome = true := by
  unfold subRules
  refine orElse_mono id (orElse_mono id (orElse_mono id ?_))
  refine orElse_mono (ruleAndR_mono hr Γ S T) (orElse_mono (ruleBindx_mono hr Γ S T) ?_)
  refine orElse_mono (ruleFun_mono hr Γ S T) (orElse_mono (ruleTyp_mono hr Γ S T) ?_)
  refine orElse_mono (ruleAndL_mono hr Γ S T) (orElse_mono (ruleOrL_mono hr Γ S T) ?_)
  refine orElse_mono (ruleOrR_mono hr Γ S T) (orElse_mono (ruleBind1_mono hr Γ S T) ?_)
  exact orElse_mono (ruleSel1_mono hr k Γ S T) (ruleSel2_mono hr k Γ S T)

end RuleMono

/-- The search at a smaller fuel is below the search at a larger one. -/
theorem sub?_searchLe (b : Budget) : ∀ {n n' : Nat}, n ≤ n' →
    SearchLe (fun Γ S T => sub? b n Γ S T) (fun Γ S T => sub? b n' Γ S T)
  | 0, _, _ => fun _ _ _ hs => by simp [sub?] at hs
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, n' + 1, h => fun Γ S T hs => by
      simp only [sub?] at hs ⊢
      exact subRules_mono (sub?_searchLe b (Nat.le_of_succ_le_succ h)) b.views Γ S T hs

/-- **More fuel never loses an answer of the search.** -/
theorem sub?_le {b : Budget} {n n' : Nat} (h : n ≤ n') {s : Sig} {Γ : Ctx [] s}
    {S T : Ty [] s} : (sub? b n Γ S T).isSome = true → (sub? b n' Γ S T).isSome = true :=
  sub?_searchLe b h Γ S T

/-! ## Checks

Every check below runs in the kernel.  A budget is written as the fields it
sets: `{ views := k }` is `k` rounds of the view closure, and the second
argument of `sub?` is the fuel.  Each positive check states the budget the
answer is found at.  A negative check states a budget it is not found at,
and says nothing about other budgets. -/

namespace SearchChecks

/-! ### Recursive subtyping and the open examples of `FunctionField`

`Oopsla16.Examples.FunctionField`: `μz. S(z) <: μz. T(z)` by `stp_bindx`,
and the steps of its premise in the context `Γz` of the self. -/

section FunctionField
open Oopsla16.Examples.FunctionField (Sbody Tbody Γz A B f)

/-- `recursive` is found at one round and fuel 5. -/
example : (sub? { views := 1 } 5 (Ctx.nil : Ctx [] []) (.TBind Sbody) (.TBind Tbody)).isSome
    = true := by
  decide +kernel

/-- The converse is not found at four rounds and fuel 8.  The left self
assumption `z : T(z)` gives no member `A`. -/
example : (sub? { views := 4 } 8 (Ctx.nil : Ctx [] []) (.TBind Tbody) (.TBind Sbody)).isSome
    = false := by
  decide +kernel

/-- The derivation of `recursive` the search returns. -/
def recursiveFound : Stp Store.nil Ctx.nil (.TBind Sbody) (.TBind Tbody) :=
  (sub? { views := 1 } 5 (Ctx.nil : Ctx [] []) (.TBind Sbody) (.TBind Tbody)).get
    (by decide +kernel)

/-- The checker of the target accepts the elaboration of the found
derivation at the source types. -/
example : FCdotR.checkLe Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabStp FCdotR.emptyStoreTy recursiveFound).1 (.TBind Sbody) (.TBind Tbody) = true := by
  decide +kernel

/-- `sBound`: `S(z) <: {A : ⊥..z.B}` in `Γz`, found at no rounds and fuel 3. -/
example : (sub? { views := 0 } 3 Γz Sbody (.TTyp A .TBot (.TSel (.abs .here) B))).isSome
    = true := by
  decide +kernel

/-- `selMember`: the self has the member `{A : ⊥..z.B}` under the method's
parameter, a view after one round. -/
example : ((hviews 1 (Γz.cons .TTop) (.there .here)).any
    fun v => decide (v.ty = .TTyp A .TBot (.TSel (.abs .here) B))) = true := by
  decide +kernel

/-- `selUnder`: `z.A <: z.B` under the parameter, found at one round and
fuel 2. -/
example : (sub? { views := 1 } 2 (Γz.cons .TTop) (.TSel (.abs (.there .here)) A)
    (.TSel (.abs (.there .here)) B)).isSome = true := by
  decide +kernel

/-- `methodCovariant`, found at one round and fuel 3. -/
example : (sub? { views := 1 } 3 Γz (.TFun f .TTop (.TSel (.abs (.there .here)) A)) Tbody).isSome
    = true := by
  decide +kernel

/-- `premise`: `S(z) <: T(z)` in `Γz`, found at one round and fuel 5. -/
example : (sub? { views := 1 } 5 Γz Sbody Tbody).isSome = true := by
  decide +kernel

end FunctionField

/-- `forgetSelf`, by `stp_bind1`: found at no rounds and fuel 3. -/
example : (sub? { views := 0 } 3 (Ctx.nil : Ctx [] [])
    (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop))) (.TAnd .TTop (.TTyp 1 .TBot .TTop))).isSome
    = true := by
  decide +kernel

/-- `⊤ <: z.A` in the body of `FCdotR.SourceSafety.RecursiveArg`'s method,
`⊤ <: z.B <: z.A` by `stp_sel2` twice: found at two rounds and fuel 2. -/
example : (sub? { views := 2 } 2 FCdotR.SourceSafety.RecursiveArg.Γf .TTop
    FCdotR.SourceSafety.RecursiveArg.zA).isSome = true := by
  decide +kernel

/-! ### The list cells of `paper_lst` below `m.List`

A cell is below `TLst m ⊥ ⊤` by `stp_bindx`, and below `m.List` by `stp_sel2`
at the module self's member `{List : TLst m ⊥ ⊤..⊤}`, which is a view of the
module self after three rounds. -/

section PaperLst
open FCdotR.CheckerExamples.PaperLst (Γn PNil Γ2t P3)

/-- The `nil` cell, found at three rounds and fuel 9. -/
example : (sub? { views := 3 } 9 Γn (.TBind PNil) (.TSel (.abs (.there .here)) 0)).isSome
    = true := by
  decide +kernel

/-- The derivation the search returns for the `cons` cell. -/
def consCellFound : Stp Store.nil Γ2t (.TBind P3)
    (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0) :=
  (sub? { views := 3 } 11 Γ2t (.TBind P3)
    (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)).get (by decide +kernel)

/-- The `cons` cell is found at three rounds and fuel 11, and the checker of
the target accepts the elaboration of the found derivation. -/
example : FCdotR.checkLe Store.nil FCdotR.emptyStoreTy Γ2t
    (FCdotR.elabStp FCdotR.emptyStoreTy consCellFound).1 (.TBind P3)
    (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0) = true := by
  decide +kernel

/-- The parameter `tl : m.List ∧ {Elem : ⊥..t.T}` of `cons` reaches the
method `head` of the list type: and-elimination, then the selection step
through the module self, then `htp_unpack`, then and-elimination again.
Six rounds. -/
example : ((hviews 6 Γ2t .here).any fun v => match v.ty with
    | .TFun 2 _ _ => true
    | _ => false) = true := by
  decide +kernel

end PaperLst

/-! ### Unions and `⊥`

A method type of a receiver at a union or at `⊥` is reached by the search,
through `stp_or1` and `stp_bot`. -/

/-- The method type `{def 0(y : ⊤) : ⊤}`. -/
abbrev F {s : Sig} : Ty [] s := .TFun 0 .TTop .TTop

/-- A method parameter at the union `F ∨ F`, under a self. -/
abbrev Γu : Ctx [] (([],x),x) :=
  ((Ctx.nil : Ctx [] []).cons (.TAnd (.TFun 0 (.TOr F F) .TTop) .TTop)).cons
    (Ty.TOr F F : Ty [] ([],x)).weaken

/-- `stp_or1`: the union below `F`, found at fuel 2. -/
example : (sub? {} 2 Γu (Γu.lookup .here) F).isSome = true := by decide +kernel

/-- A method parameter at `⊥`, under a self. -/
abbrev Γbot : Ctx [] (([],x),x) :=
  ((Ctx.nil : Ctx [] []).cons (.TAnd (.TFun 0 .TBot .TTop) .TTop)).cons
    (Ty.TBot : Ty [] ([],x)).weaken

/-- `stp_bot`: `⊥` below `F`, found at fuel 1. -/
example : (sub? {} 1 Γbot (Γbot.lookup .here) F).isSome = true := by decide +kernel

/-- `stp_or21`: a type below the left side of a union and not below the
right, found at fuel 2. -/
example : (sub? {} 2 (Ctx.nil : Ctx [] []) (.TTyp 0 .TBot .TTop)
    (.TOr (.TTyp 0 .TBot .TTop) .TBot)).isSome = true := by
  decide +kernel

/-- `stp_or22`: a type below the right side of a union and not below the
left, found at fuel 2. -/
example : (sub? {} 2 (Ctx.nil : Ctx [] []) (.TTyp 0 .TBot .TTop)
    (.TOr .TBot (.TTyp 0 .TBot .TTop))).isSome = true := by
  decide +kernel

/-! ### Selections on the receiver

A receiver typed by a selection reaches a method type by `stp_sel1`, and a
recursive type reaches a selection by `stp_sel2` at its lower bound. -/

/-- `c`'s self: `{L : F..F} ∧ {def 0(x : c.L) : ⊤} ∧ ⊤`. -/
abbrev selfC : Ty [] ([],x) :=
  .TAnd (.TTyp 1 F F) (.TAnd (.TFun 0 (.TSel (.abs .here) 1) .TTop) .TTop)

/-- The method's parameter `x : c.L`, under the self `c`. -/
abbrev Γc : Ctx [] (([],x),x) :=
  ((Ctx.nil : Ctx [] []).cons selfC).cons (Ty.TSel (.abs .here) 1 : Ty [] ([],x)).weaken

/-- `c.L <: F` by `stp_sel1`, found at one round and fuel 1. -/
example : (sub? { views := 1 } 1 Γc (Γc.lookup .here) F).isSome = true := by decide +kernel

/-- `F` is a view of `x : c.L` after two rounds, by the selection step. -/
example : ((hviews 2 Γc .here).any fun v => decide (v.ty = F)) = true := by decide +kernel

/-- `m`'s self: `{L : μ(w. {A : ⊤..⊤})..μ(w. {A : ⊤..⊤})} ∧ {def 0(x : {A : ⊤..⊤}) : m.L} ∧ ⊤`. -/
abbrev selfP : Ty [] ([],x) :=
  .TAnd (.TTyp 1 (.TBind (.TTyp 0 .TTop .TTop)) (.TBind (.TTyp 0 .TTop .TTop)))
    (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TSel (.abs (.there .here)) 1)) .TTop)

/-- The method's parameter `x : {A : ⊤..⊤}`, under the self `m`. -/
abbrev Γp : Ctx [] (([],x),x) :=
  ((Ctx.nil : Ctx [] []).cons selfP).cons (Ty.TTyp 0 .TTop .TTop : Ty [] ([],x)).weaken

/-- `μ(w. {A : ⊤..⊤}) <: m.L` by `stp_sel2` at the lower bound, found at one
round and fuel 1.  This is the step after packing `x` in the method body. -/
example : (sub? { views := 1 } 1 Γp (.TBind (.TTyp 0 .TTop .TTop))
    (.TSel (.abs (.there .here)) 1)).isSome = true := by
  decide +kernel

/-! ### A failing branch with a repeated selection

`new {z ⇒ type A = z.A ∧ z.A   def g(x : z.A) : {type C : ⊥..⊤} ∨ ⊤ = x}`.
The body's goal is `z.A <: {C : ⊥..⊤} ∨ ⊤`.  The search tries `stp_or21`
first, and that branch unfolds `z.A` through `stp_sel1` and the
and-eliminations until the fuel runs out.  Then `stp_or22` closes the goal
by `stp_top`.  With deduplication the self `z` has five views after four
rounds, and the kernel decides the goal at fuel 16. -/

/-- `z.A`. -/
abbrev zA : Ty [] ([],x) := .TSel (.abs .here) 1
/-- `{C : ⊥..⊤} ∨ ⊤`. -/
abbrev Cod {s : Sig} : Ty [] s := .TOr (.TTyp 0 .TBot .TTop) .TTop
/-- `z`'s self: `{A : z.A ∧ z.A..z.A ∧ z.A} ∧ {def 0(x : z.A) : Cod} ∧ ⊤`. -/
abbrev selfZ : Ty [] ([],x) :=
  .TAnd (.TTyp 1 (.TAnd zA zA) (.TAnd zA zA)) (.TAnd (.TFun 0 zA Cod) .TTop)
/-- The method's parameter `x : z.A`, under the self `z`. -/
abbrev Γz2 : Ctx [] (([],x),x) := ((Ctx.nil : Ctx [] []).cons selfZ).cons zA.weaken

/-- Five views of the self after four rounds. -/
example : (hviews 4 Γz2 (.there .here)).length = 5 := by decide +kernel

/-- The body's goal, found at four rounds and fuel 16. -/
example : (sub? { views := 4 } 16 Γz2 (Γz2.lookup .here) Cod).isSome = true := by
  decide +kernel

end SearchChecks

end Oopsla16Frontend
