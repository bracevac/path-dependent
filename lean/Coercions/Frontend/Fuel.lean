/-!
# The tank

Every typer of the front ends runs on one fuel, the tank.  The tank is passed
from each goal to the next, through the whole run, and not down a branch.  So
it counts the work of a run, not the depth of one branch.  A goal that finds
the tank short marks it.  A marked tank stays marked, so every later goal
fails and the run ends.  A run that ends with the tank marked hit the
recursion limit, which is what the compiler reports as a `RecursionOverflow`
(`TypeErrors.scala:88,133-149`).  It is never a rejection by the rules.

The run keeps the goals pending along the branch, and a goal that repeats one
of them exactly fails.  This is the compiler's set of pending subtype goals
(`TypeComparer.scala:60,259-298`).  The tank ends the loops that this cut
does not catch, such as a descent that never repeats a goal.

The module imports only Lean core.  It holds the tank, the computations that
draw on it, a few combinators, the run with the cut and the run without it,
and the three facts the front ends use.  A run that ends unmarked gives the
same answer with more fuel (`run_frame`) and with a larger index
(`run_index`).  The cut never loses a success of the run without it
(`cut_complete`).  The last is the argument by a minimal derivation, in tank
form.  A front end proves that its step is framed and dominated, from the
combinator lemmas below, and the three facts follow for its run.

Every definition is structural, so the kernel evaluates a run.
-/

namespace Frontend.Fuel

/-- The fuel left, and whether some goal found it short. -/
structure Tank where
  left : Nat
  out : Bool
deriving DecidableEq, Repr

/-- The same tank with `k` more units. -/
def Tank.add (t : Tank) (k : Nat) : Tank := ⟨t.left + k, t.out⟩

/-- A computation that draws on the tank. -/
abbrev Fu (α : Type) := Tank → α × Tank

/-- Return a value and leave the tank alone. -/
def Fu.ret {α : Type} (a : α) : Fu α := fun t => (a, t)

/-- Run `c`, then `f` on its value, from the tank `c` leaves.  The match
evaluates `c t` once. -/
def Fu.bind {α β : Type} (c : Fu α) (f : α → Fu β) : Fu β := fun t =>
  match c t with
  | (a, t1) => f a t1

/-- Take `c` units.  A marked tank stays marked.  A short tank is marked. -/
def draw (c : Nat) : Fu Bool := fun t =>
  if t.out then (false, t)
  else if c ≤ t.left then (true, ⟨t.left - c, false⟩)
  else (false, ⟨t.left, true⟩)

/-- First success.  The second branch is skipped once the tank is marked. -/
def Fu.orElse {α : Type} (a : Fu (Option α)) (b : Unit → Fu (Option α)) : Fu (Option α) :=
  fun t =>
    match a t with
    | (some x, t1) => (some x, t1)
    | (none, t1) => if t1.out then (none, t1) else b () t1

/-- First success over a list, the compiler's `either` over finitely many
alternatives. -/
def Fu.firstSome {α β : Type} (f : α → Fu (Option β)) : List α → Fu (Option β)
  | [] => Fu.ret none
  | x :: xs => Fu.orElse (f x) (fun _ => Fu.firstSome f xs)
termination_by structural l => l

/-- Every answer over a list, in order. -/
def Fu.flatMapL {α β : Type} (f : α → Fu (List β)) : List α → Fu (List β)
  | [] => Fu.ret []
  | x :: xs =>
      Fu.bind (f x) fun ys => Fu.bind (Fu.flatMapL f xs) fun zs => Fu.ret (ys ++ zs)
termination_by structural l => l

/-- An answer for every goal, drawn on the tank. -/
abbrev Oracle (G : Type) (R : G → Type) := (g : G) → Fu (Option (R g))

/-- The step of an algorithm, given the run one level down as an oracle. -/
abbrev Step (G : Type) (R : G → Type) := Oracle G R → Oracle G R

section Run

variable {G : Type} [DecidableEq G] {R : G → Type}

/-- The run.  `d` is the structural index, `P` the goals pending along the
branch.  A goal costs `cost P.length`.  A goal that repeats exactly fails.  A
step that ends with the tank marked answers `none`. -/
def run (cost : Nat → Nat) (F : Step G R) : Nat → List G → Oracle G R
  | 0, _, _ => fun t => (none, { t with out := true })
  | d + 1, P, g => fun t =>
      match draw (cost P.length) t with
      | (false, t1) => (none, t1)
      | (true, t1) =>
          if g ∈ P then (none, t1)
          else
            match F (run cost F d (g :: P)) g t1 with
            | (r, t2) => if t2.out then (none, t2) else (r, t2)
termination_by structural d _ _ => d

/-- The run without the cut, at depth `k`. -/
def run' (cost : Nat → Nat) (F : Step G R) : Nat → Nat → Oracle G R
  | 0, _, _ => fun t => (none, { t with out := true })
  | d + 1, k, g => fun t =>
      match draw (cost k) t with
      | (false, t1) => (none, t1)
      | (true, t1) =>
          match F (run' cost F d (k + 1)) g t1 with
          | (r, t2) => if t2.out then (none, t2) else (r, t2)
termination_by structural d _ _ => d

end Run

/-! ## Frames and dominance

`Sim c c'` says that whenever `c` ends unmarked, `c'` gives the same answer
from any tank with more fuel, and spends exactly as much.  `Framed c` adds that
`c` keeps a marked tank and never adds fuel.  `Agree c c'` is the pair of
frames with the relation between them.  `Dom m c c'` is the inexact relation:
from a tank of at most `m` units on which `c` ends unmarked, `c'` gives the
same answer from any tank with at least as much fuel, and leaves at least as
much extra.  The run with the cut dominates the run without it, since a cut
goal stops at once. -/

section Frames

variable {α β : Type}

/-- From a tank on which `c` ends unmarked, `c'` gives the same answer with `k`
more units, and leaves `k` more. -/
def Sim (c c' : Fu α) : Prop :=
  ∀ t r t', c t = (r, t') → t'.out = false → ∀ k, c' (t.add k) = (r, t'.add k)

/-- `c` keeps a marked tank, never adds fuel, and does the same with more
fuel. -/
structure Framed (c : Fu α) : Prop where
  absorbs : ∀ t, t.out = true → (c t).2 = t
  spends : ∀ t, (c t).2.left ≤ t.left
  shift : Sim c c

/-- Two framed computations, the second doing what the first does. -/
structure Agree (c c' : Fu α) : Prop where
  left : Framed c
  right : Framed c'
  sim : Sim c c'

/-- From a tank of at most `m` units on which `c` ends unmarked, `c'` gives the
same answer from any unmarked tank with at least as much fuel, and leaves at
least as much extra. -/
def Dom (m : Nat) (c c' : Fu α) : Prop :=
  ∀ t r t', t.left ≤ m → c t = (r, t') → t'.out = false →
    ∀ u : Tank, u.out = false → t.left ≤ u.left →
      (c' u).1 = r ∧ (c' u).2.out = false ∧ t'.left + (u.left - t.left) ≤ (c' u).2.left

end Frames

section Steps

variable {G : Type} {R : G → Type}

/-- A step is framed when oracles that agree give answers that agree. -/
def FrameF (F : Step G R) : Prop :=
  ∀ o o' : Oracle G R, (∀ g, Agree (o g) (o' g)) → ∀ g, Agree (F o g) (F o' g)

/-- A step is dominated when a framed oracle that dominates another below `m`
gives answers that dominate below `m`. -/
def DomF (F : Step G R) : Prop :=
  ∀ (m : Nat) (o o' : Oracle G R), (∀ g, Framed (o g)) → (∀ g, Framed (o' g)) →
    (∀ g, Dom m (o g) (o' g)) → ∀ g, Dom m (F o g) (F o' g)

/-- `p` fails without the cut, at every index, at every depth of at least `k`,
from every unmarked tank of at most `m` units. -/
def FailsBelow (cost : Nat → Nat) (F : Step G R) (p : G) (k m : Nat) : Prop :=
  ∀ (d j : Nat) (u : Tank), k ≤ j → u.out = false → u.left ≤ m → (run' cost F d j p u).1 = none

end Steps

/-- Every goal costs at least one unit, and a deeper goal costs at least as
much. -/
structure CostOk (cost : Nat → Nat) : Prop where
  pos : ∀ k, 1 ≤ cost k
  mono : ∀ j k, j ≤ k → cost j ≤ cost k

theorem costOk_succ : CostOk (fun k => k + 1) :=
  ⟨fun _ => Nat.le_add_left 1 _, fun _ _ h => Nat.add_le_add_right h 1⟩

theorem costOk_one : CostOk (fun _ => 1) :=
  ⟨fun _ => Nat.le_refl 1, fun _ _ _ => Nat.le_refl 1⟩

/-! ## Tanks -/

@[simp] theorem Tank.add_left (t : Tank) (k : Nat) : (t.add k).left = t.left + k := rfl

@[simp] theorem Tank.add_out (t : Tank) (k : Nat) : (t.add k).out = t.out := rfl

@[simp] theorem Tank.add_zero (t : Tank) : t.add 0 = t := by
  cases t; rfl

/-- An unmarked tank with more fuel is the smaller one with units added. -/
theorem Tank.eq_add {t u : Tank} (ht : t.out = false) (hu : u.out = false) (h : t.left ≤ u.left) :
    u = t.add (u.left - t.left) := by
  cases t with
  | mk a b =>
    cases u with
    | mk c e =>
      simp only at ht hu h
      subst ht; subst hu
      simp only [Tank.add, Tank.mk.injEq, and_true]
      omega

/-! ## The combinators -/

section Combinators

variable {α β : Type}

theorem draw_out {c : Nat} {t : Tank} (h : t.out = true) : draw c t = (false, t) := by
  simp [draw, h]

theorem draw_ok {c : Nat} {t : Tank} (h : t.out = false) (hc : c ≤ t.left) :
    draw c t = (true, ⟨t.left - c, false⟩) := by
  simp [draw, h, hc]

theorem draw_short {c : Nat} {t : Tank} (h : t.out = false) (hc : t.left < c) :
    draw c t = (false, ⟨t.left, true⟩) := by
  simp [draw, h, Nat.not_le.mpr hc]

/-- A framed computation ends marked from a marked tank, so an unmarked end
had an unmarked start. -/
theorem Framed.start {c : Fu α} (hc : Framed c) {t : Tank} {r : α} {t' : Tank}
    (h : c t = (r, t')) (ho : t'.out = false) : t.out = false := by
  cases hto : t.out
  · rfl
  · have := hc.absorbs t hto
    rw [h] at this
    subst this
    simp_all

theorem Framed.le {c : Fu α} (hc : Framed c) {t : Tank} {r : α} {t' : Tank}
    (h : c t = (r, t')) : t'.left ≤ t.left := by
  have := hc.spends t
  rw [h] at this
  exact this

theorem Agree.refl {c : Fu α} (hc : Framed c) : Agree c c := ⟨hc, hc, hc.shift⟩

/-- A framed computation dominates itself below any bound. -/
theorem Framed.dom {c : Fu α} (hc : Framed c) (m : Nat) : Dom m c c := by
  intro t r t' _ h ho u hu htu
  have ht := hc.start h ho
  rw [Tank.eq_add ht hu htu, hc.shift t r t' h ho]
  simp [ho]

theorem ret_framed (a : α) : Framed (Fu.ret a) where
  absorbs _ _ := rfl
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h _ k
    simp only [Fu.ret, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem ret_agree (a : α) : Agree (Fu.ret a) (Fu.ret a) := Agree.refl (ret_framed a)

theorem ret_dom (a : α) (m : Nat) : Dom m (Fu.ret a) (Fu.ret a) := (ret_framed a).dom m

theorem bind_sim {c c' : Fu α} {f f' : α → Fu β} (hs : Sim c c') (hf : ∀ a, Framed (f a))
    (hfs : ∀ a, Sim (f a) (f' a)) : Sim (Fu.bind c f) (Fu.bind c' f') := by
  intro t r t' h ho k
  simp only [Fu.bind] at h ⊢
  cases hct : c t with
  | mk a t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf a).start h ho
    rw [hs t a t1 hct ht1 k]
    exact hfs a t1 r t' h ho k

theorem bind_framed {c : Fu α} {f : α → Fu β} (hc : Framed c) (hf : ∀ a, Framed (f a)) :
    Framed (Fu.bind c f) where
  absorbs t ht := by
    simp only [Fu.bind]
    cases hct : c t with
    | mk a t1 =>
      have := hc.absorbs t ht
      rw [hct] at this
      simp only at this
      subst this
      exact (hf a).absorbs _ ht
  spends t := by
    simp only [Fu.bind]
    cases hct : c t with
    | mk a t1 =>
      exact Nat.le_trans ((hf a).spends t1) (hc.le hct)
  shift := bind_sim hc.shift hf (fun a => (hf a).shift)

theorem bind_agree {c c' : Fu α} {f f' : α → Fu β} (hc : Agree c c')
    (hf : ∀ a, Agree (f a) (f' a)) : Agree (Fu.bind c f) (Fu.bind c' f') :=
  ⟨bind_framed hc.left (fun a => (hf a).left), bind_framed hc.right (fun a => (hf a).right),
    bind_sim hc.sim (fun a => (hf a).left) (fun a => (hf a).sim)⟩

theorem bind_dom {m : Nat} {c c' : Fu α} {f f' : α → Fu β} (hc : Framed c)
    (hf : ∀ a, Framed (f a)) (hd : Dom m c c') (hfd : ∀ a, Dom m (f a) (f' a)) :
    Dom m (Fu.bind c f) (Fu.bind c' f') := by
  intro t r t' htm h ho u hu htu
  simp only [Fu.bind] at h ⊢
  cases hct : c t with
  | mk a t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf a).start h ho
    have h1m : t1.left ≤ t.left := hc.le hct
    obtain ⟨e1, e2, e3⟩ := hd t a t1 htm hct ht1 u hu htu
    cases hcu : c' u with
    | mk a' u1 =>
      rw [hcu] at e1 e2 e3
      simp only at e1 e2 e3
      subst a'
      simp only
      obtain ⟨g1, g2, g3⟩ := hfd a t1 r t' (Nat.le_trans h1m htm) h ho u1 e2 (by omega)
      refine ⟨g1, g2, ?_⟩
      have := (hf a).le h
      omega

theorem draw_framed (c : Nat) : Framed (draw c) where
  absorbs t ht := by rw [draw_out ht]
  spends t := by
    cases hto : t.out
    · by_cases hc : c ≤ t.left
      · rw [draw_ok hto hc]; simp only; omega
      · rw [draw_short hto (Nat.not_le.mp hc)]; exact Nat.le_refl _
    · rw [draw_out hto]; exact Nat.le_refl _
  shift := by
    intro t r t' h ho k
    cases hto : t.out
    · by_cases hc : c ≤ t.left
      · rw [draw_ok hto hc] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [draw_ok (by simp [hto]) (by simp; omega)]
        simp only [Tank.add, Prod.mk.injEq, Tank.mk.injEq, and_true, true_and]
        omega
      · rw [draw_short hto (Nat.not_le.mp hc)] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp at ho
    · rw [draw_out hto] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hto] at ho

theorem draw_agree (c : Nat) : Agree (draw c) (draw c) := Agree.refl (draw_framed c)

/-- A draw dominates a draw of fewer units. -/
theorem draw_dom {c c' : Nat} (hcc : c' ≤ c) (m : Nat) : Dom m (draw c) (draw c') := by
  intro t r t' _ h ho u hu htu
  cases hto : t.out
  · by_cases hc : c ≤ t.left
    · rw [draw_ok hto hc] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [draw_ok hu (by omega)]
      simp only [true_and]
      omega
    · rw [draw_short hto (Nat.not_le.mp hc)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at ho
  · rw [draw_out hto] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hto] at ho

theorem orElse_sim {a a' : Fu (Option α)} {b b' : Unit → Fu (Option α)} (hs : Sim a a')
    (hbs : Sim (b ()) (b' ())) : Sim (Fu.orElse a b) (Fu.orElse a' b') := by
  intro t r t' h ho k
  simp only [Fu.orElse] at h ⊢
  cases hat : a t with
  | mk x t1 =>
    rw [hat] at h
    cases x with
    | some x =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hs t (some x) t1 hat ho k]
    | none =>
      cases ht1 : t1.out
      · simp only [ht1] at h
        rw [hs t none t1 hat ht1 k]
        simp only [Tank.add_out, ht1]
        exact hbs t1 r t' h ho k
      · simp only [ht1, if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ht1] at ho

theorem orElse_framed {a : Fu (Option α)} {b : Unit → Fu (Option α)} (ha : Framed a)
    (hb : Framed (b ())) : Framed (Fu.orElse a b) where
  absorbs t ht := by
    simp only [Fu.orElse]
    cases hat : a t with
    | mk x t1 =>
      have := ha.absorbs t ht
      rw [hat] at this
      simp only at this
      subst this
      cases x <;> simp [ht]
  spends t := by
    simp only [Fu.orElse]
    cases hat : a t with
    | mk x t1 =>
      have h1 := ha.le hat
      cases x with
      | some x => exact h1
      | none =>
        cases ht1 : t1.out
        · simp only [ht1, Bool.false_eq_true, if_false]
          exact Nat.le_trans (hb.spends t1) h1
        · simp only [ht1, if_true]
          exact h1
  shift := orElse_sim ha.shift hb.shift

theorem orElse_agree {a a' : Fu (Option α)} {b b' : Unit → Fu (Option α)} (ha : Agree a a')
    (hb : Agree (b ()) (b' ())) : Agree (Fu.orElse a b) (Fu.orElse a' b') :=
  ⟨orElse_framed ha.left hb.left, orElse_framed ha.right hb.right, orElse_sim ha.sim hb.sim⟩

theorem orElse_dom {m : Nat} {a a' : Fu (Option α)} {b b' : Unit → Fu (Option α)}
    (ha : Framed a) (hd : Dom m a a') (hbd : Dom m (b ()) (b' ())) :
    Dom m (Fu.orElse a b) (Fu.orElse a' b') := by
  intro t r t' htm h ho u hu htu
  simp only [Fu.orElse] at h ⊢
  cases hat : a t with
  | mk x t1 =>
    rw [hat] at h
    have h1t := ha.le hat
    cases x with
    | some x =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e1, e2, e3⟩ := hd t (some x) t1 htm hat ho u hu htu
      cases hau : a' u with
      | mk x' u1 =>
        rw [hau] at e1 e2 e3
        simp only at e1 e2 e3
        subst x'
        exact ⟨rfl, e2, e3⟩
    | none =>
      cases ht1 : t1.out
      · simp only [ht1, Bool.false_eq_true, if_false] at h
        obtain ⟨e1, e2, e3⟩ := hd t none t1 htm hat ht1 u hu htu
        cases hau : a' u with
        | mk x' u1 =>
          rw [hau] at e1 e2 e3
          simp only at e1 e2 e3
          subst x'
          simp only [e2, Bool.false_eq_true, if_false]
          obtain ⟨g1, g2, g3⟩ := hbd t1 r t' (Nat.le_trans h1t htm) h ho u1 e2 (by omega)
          refine ⟨g1, g2, ?_⟩
          omega
      · simp only [ht1, if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ht1] at ho

theorem firstSome_framed {f : α → Fu (Option β)} (hf : ∀ x, Framed (f x)) :
    ∀ l, Framed (Fu.firstSome f l)
  | [] => by simpa [Fu.firstSome] using ret_framed (none : Option β)
  | x :: xs => by
    simp only [Fu.firstSome]
    exact orElse_framed (hf x) (firstSome_framed hf xs)

theorem firstSome_agree {f f' : α → Fu (Option β)} (hf : ∀ x, Agree (f x) (f' x)) :
    ∀ l, Agree (Fu.firstSome f l) (Fu.firstSome f' l)
  | [] => by simpa [Fu.firstSome] using ret_agree (none : Option β)
  | x :: xs => by
    simp only [Fu.firstSome]
    exact orElse_agree (hf x) (firstSome_agree hf xs)

theorem firstSome_dom {m : Nat} {f f' : α → Fu (Option β)} (hf : ∀ x, Framed (f x))
    (hd : ∀ x, Dom m (f x) (f' x)) : ∀ l, Dom m (Fu.firstSome f l) (Fu.firstSome f' l)
  | [] => by simpa [Fu.firstSome] using ret_dom (none : Option β) m
  | x :: xs => by
    simp only [Fu.firstSome]
    exact orElse_dom (hf x) (hd x) (firstSome_dom hf hd xs)

theorem flatMapL_framed {f : α → Fu (List β)} (hf : ∀ x, Framed (f x)) :
    ∀ l, Framed (Fu.flatMapL f l)
  | [] => by simpa [Fu.flatMapL] using ret_framed ([] : List β)
  | x :: xs => by
    simp only [Fu.flatMapL]
    exact bind_framed (hf x) fun _ => bind_framed (flatMapL_framed hf xs) fun _ => ret_framed _

theorem flatMapL_agree {f f' : α → Fu (List β)} (hf : ∀ x, Agree (f x) (f' x)) :
    ∀ l, Agree (Fu.flatMapL f l) (Fu.flatMapL f' l)
  | [] => by simpa [Fu.flatMapL] using ret_agree ([] : List β)
  | x :: xs => by
    simp only [Fu.flatMapL]
    exact bind_agree (hf x) fun _ => bind_agree (flatMapL_agree hf xs) fun _ => ret_agree _

theorem flatMapL_dom {m : Nat} {f f' : α → Fu (List β)} (hf : ∀ x, Framed (f x))
    (hd : ∀ x, Dom m (f x) (f' x)) : ∀ l, Dom m (Fu.flatMapL f l) (Fu.flatMapL f' l)
  | [] => by simpa [Fu.flatMapL] using ret_dom ([] : List β) m
  | x :: xs => by
    simp only [Fu.flatMapL]
    exact bind_dom (hf x) (fun _ => bind_framed (flatMapL_framed hf xs) fun _ => ret_framed _)
      (hd x) fun _ => bind_dom (flatMapL_framed hf xs) (fun _ => ret_framed _)
        (flatMapL_dom hf hd xs) fun _ => ret_dom _ m

end Combinators

/-! ## One level of a run

A level of either run draws, stops at a cut, and otherwise runs the step and
answers `none` if the step ends with the tank marked.  The lemmas about a
level are the lemmas about both runs. -/

section Node

variable {α : Type}

/-- One level of a run.  Draw `c` units, answer `none` at a cut, and otherwise
run `k`, whose answer counts only if it ends with the tank unmarked. -/
def node (c : Nat) (cut : Prop) [Decidable cut] (k : Fu (Option α)) : Fu (Option α) := fun t =>
  match draw c t with
  | (false, t1) => (none, t1)
  | (true, t1) =>
      if cut then (none, t1)
      else
        match k t1 with
        | (r, t2) => if t2.out then (none, t2) else (r, t2)

variable {c : Nat} {cut : Prop} [Decidable cut] {k : Fu (Option α)}

theorem node_out {t : Tank} (ht : t.out = true) : node c cut k t = (none, t) := by
  simp [node, draw_out ht]

theorem node_short {t : Tank} (ht : t.out = false) (hc : t.left < c) :
    node c cut k t = (none, ⟨t.left, true⟩) := by
  simp [node, draw_short ht hc]

theorem node_cut {t : Tank} (ht : t.out = false) (hc : c ≤ t.left) (hcut : cut) :
    node c cut k t = (none, ⟨t.left - c, false⟩) := by
  simp [node, draw_ok ht hc, hcut]

theorem node_go {t : Tank} (ht : t.out = false) (hc : c ≤ t.left) (hcut : ¬cut)
    (hk : (k ⟨t.left - c, false⟩).2.out = false) : node c cut k t = k ⟨t.left - c, false⟩ := by
  simp only [node, draw_ok ht hc, hcut, if_false]
  cases hx : k ⟨t.left - c, false⟩ with
  | mk r t2 =>
    rw [hx] at hk
    simp only at hk
    simp [hk]

/-- A level that ends unmarked drew its units and either cut or ran its step to
an unmarked end. -/
theorem node_inv {t : Tank} {r : Option α} {t' : Tank} (h : node c cut k t = (r, t'))
    (ho : t'.out = false) :
    t.out = false ∧ c ≤ t.left ∧
      ((cut ∧ r = none ∧ t' = ⟨t.left - c, false⟩) ∨ (¬cut ∧ k ⟨t.left - c, false⟩ = (r, t'))) := by
  cases hto : t.out
  · by_cases hc : c ≤ t.left
    · refine ⟨rfl, hc, ?_⟩
      by_cases hcut : cut
      · rw [node_cut hto hc hcut] at h
        simp only [Prod.mk.injEq] at h
        exact Or.inl ⟨hcut, h.1.symm, h.2.symm⟩
      · refine Or.inr ⟨hcut, ?_⟩
        simp only [node, draw_ok hto hc, hcut, if_false] at h
        cases hx : k ⟨t.left - c, false⟩ with
        | mk r2 t2 =>
          rw [hx] at h
          cases h2 : t2.out
          · simp only [h2, Bool.false_eq_true, if_false] at h
            exact h
          · simp only [h2, if_true, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            simp [h2] at ho
    · rw [node_short hto (Nat.not_le.mp hc)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp at ho
  · rw [node_out hto] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp [hto] at ho

/-- A level that answers leaves the tank unmarked. -/
theorem node_some {t : Tank} {x : α} {t' : Tank} (h : node c cut k t = (some x, t')) :
    t'.out = false := by
  cases hto : t.out
  · by_cases hc : c ≤ t.left
    · by_cases hcut : cut
      · rw [node_cut hto hc hcut] at h
        simp at h
      · simp only [node, draw_ok hto hc, hcut, if_false] at h
        cases hx : k ⟨t.left - c, false⟩ with
        | mk r2 t2 =>
          rw [hx] at h
          cases h2 : t2.out
          · simp only [h2, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
            rw [← h.2]
            exact h2
          · simp [h2] at h
    · rw [node_short hto (Nat.not_le.mp hc)] at h
      simp at h
  · rw [node_out hto] at h
    simp at h

theorem node_sim {k' : Fu (Option α)} (hs : Sim k k') : Sim (node c cut k) (node c cut k') := by
  intro t r t' h ho j
  obtain ⟨ht, hc, hcase⟩ := node_inv h ho
  have ht' : (t.add j).out = false := by simp [ht]
  have hc' : c ≤ (t.add j).left := by simp; omega
  have e : (⟨(t.add j).left - c, false⟩ : Tank) = (⟨t.left - c, false⟩ : Tank).add j := by
    simp only [Tank.add, Tank.mk.injEq, and_true]
    omega
  rcases hcase with ⟨hcut, rfl, rfl⟩ | ⟨hcut, hk⟩
  · rw [node_cut ht' hc' hcut, e]
  · have hk' := hs _ r t' hk ho j
    rw [node_go ht' hc' hcut (by rw [e, hk']; simp [ho]), e, hk']

theorem node_framed (hk : Framed k) : Framed (node c cut k) where
  absorbs t ht := by rw [node_out ht]
  spends t := by
    cases hto : t.out
    · by_cases hc : c ≤ t.left
      · by_cases hcut : cut
        · rw [node_cut hto hc hcut]; simp only; omega
        · simp only [node, draw_ok hto hc, hcut, if_false]
          cases hx : k ⟨t.left - c, false⟩ with
          | mk r2 t2 =>
            have := hk.le hx
            simp only at this
            cases t2.out <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
      · rw [node_short hto (Nat.not_le.mp hc)]; exact Nat.le_refl _
    · rw [node_out hto]; exact Nat.le_refl _
  shift := node_sim hk.shift

theorem node_agree {k' : Fu (Option α)} (hk : Agree k k') : Agree (node c cut k) (node c cut k') :=
  ⟨node_framed hk.left, node_framed hk.right, node_sim hk.sim⟩

/-- A level dominates a level that draws fewer units, when the steps do. -/
theorem node_dom {m c' : Nat} {k' : Fu (Option α)} (hcc : c' ≤ c) (hk : Framed k)
    (hd : Dom m k k') : Dom m (node c cut k) (node c' cut k') := by
  intro t r t' htm h ho u hu htu
  obtain ⟨ht, hc, hcase⟩ := node_inv h ho
  have hc' : c' ≤ u.left := by omega
  rcases hcase with ⟨hcut, rfl, rfl⟩ | ⟨hcut, hk1⟩
  · rw [node_cut hu hc' hcut]
    simp only [true_and]
    omega
  · have hle := hk.le hk1
    simp only at hle
    obtain ⟨e1, e2, e3⟩ := hd _ r t' (by simp only; omega) hk1 ho ⟨u.left - c', false⟩ rfl
      (by simp only; omega)
    rw [node_go hu hc' hcut e2]
    refine ⟨e1, e2, ?_⟩
    simp only at e3
    omega

end Node

/-! ## The run without the cut -/

section RunPrime

variable {G : Type} {R : G → Type} {cost : Nat → Nat} {F : Step G R}

/-- At index zero both runs mark the tank. -/
theorem zero_framed {α : Type} : Framed (fun t : Tank => ((none : Option α), { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho

theorem run'_succ (d k : Nat) (g : G) :
    run' cost F (d + 1) k g = node (cost k) False (F (run' cost F d (k + 1)) g) := rfl

theorem run'_framed (hF : FrameF F) : ∀ d k g, Framed (run' cost F d k g)
  | 0, _, _ => zero_framed
  | d + 1, k, g => by
    rw [run'_succ]
    exact node_framed (hF _ _ (fun g' => Agree.refl (run'_framed hF d (k + 1) g')) g).left

theorem run'_agree (hF : FrameF F) :
    ∀ d d', d ≤ d' → ∀ k g, Agree (run' cost F d k g) (run' cost F d' k g)
  | 0, d', _, k, g => by
    refine ⟨zero_framed, run'_framed hF d' k g, ?_⟩
    intro t r t' h ho _
    simp only [run', Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, k, g => by
    obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    rw [run'_succ, run'_succ]
    exact node_agree (hF _ _ (fun g' => run'_agree hF d d'' (by omega) (k + 1) g') g)

theorem run'_frame {cost : Nat → Nat} {F : Step G R} (hF : FrameF F) {d k : Nat} {g : G}
    {t t' : Tank} {r : Option (R g)} (h : run' cost F d k g t = (r, t')) (ho : t'.out = false) (j : Nat) :
    run' cost F d k g (t.add j) = (r, t'.add j) :=
  (run'_framed hF d k g).shift t r t' h ho j

theorem run'_index {cost : Nat → Nat} {F : Step G R} (hF : FrameF F) {d d' k : Nat} {g : G}
    {t : Tank} (h : (run' cost F d k g t).2.out = false) (hd : d ≤ d') :
    run' cost F d' k g t = run' cost F d k g t := by
  have := (run'_agree hF d d' hd k g).sim t _ _ rfl h 0
  simpa using this

/-- An answer of the run without the cut leaves the tank unmarked. -/
theorem run'_some {d k : Nat} {g : G} {t : Tank} {x : R g} (h : (run' cost F d k g t).1 = some x) :
    (run' cost F d k g t).2.out = false := by
  cases d with
  | zero => simp [run'] at h
  | succ d =>
    rw [run'_succ] at h ⊢
    exact node_some (k := F (run' cost F d (k + 1)) g) (Prod.ext h rfl)

/-- A goal at a shallower depth costs no more, so the run there dominates. -/
theorem run'_depth_dom (hc : CostOk cost) (hF : FrameF F) (hD : DomF F) :
    ∀ d k k' g m, k ≤ k' → Dom m (run' cost F d k' g) (run' cost F d k g)
  | 0, _, _, _, _, _ => by
    intro t r t' _ h ho
    simp only [run', Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, k, k', g, m, hk => by
    rw [run'_succ, run'_succ]
    exact node_dom (hc.mono _ _ hk)
      (hF _ _ (fun g' => Agree.refl (run'_framed hF d (k' + 1) g')) g).left
      (hD m _ _ (fun g' => run'_framed hF d (k' + 1) g') (fun g' => run'_framed hF d (k + 1) g')
        (fun g' => run'_depth_dom hc hF hD d (k + 1) (k' + 1) g' m (by omega)) g)

theorem run'_depth {cost : Nat → Nat} (hc : CostOk cost) {F : Step G R} (hF : FrameF F) (hD : DomF F)
    {d k k' : Nat} {g : G} {t : Tank} {r : R g} (hk : k ≤ k')
    (h : (run' cost F d k' g t).1 = some r) (ho : (run' cost F d k' g t).2.out = false) :
    (run' cost F d k g t).1 = some r := by
  have ht : t.out = false := (run'_framed hF d k' g).start rfl ho
  have := run'_depth_dom hc hF hD d k k' g t.left hk t _ _ (Nat.le_refl _) rfl ho t ht
    (Nat.le_refl _)
  rw [this.1, h]

/-- `p` fails without the cut at every index up to `D`, at every depth of at
least `k`, from every unmarked tank of at most `m` units. -/
def FailsUpTo (cost : Nat → Nat) (F : Step G R) (D : Nat) (p : G) (k m : Nat) : Prop :=
  ∀ d, d ≤ D → ∀ (j : Nat) (u : Tank), k ≤ j → u.out = false → u.left ≤ m →
    (run' cost F d j p u).1 = none

theorem FailsUpTo.mono {D D' k k' m m' : Nat} {p : G} (h : FailsUpTo cost F D p k m) (hD : D' ≤ D)
    (hk : k ≤ k') (hm : m' ≤ m) : FailsUpTo cost F D' p k' m' :=
  fun d hd j u hj hu hum => h d (Nat.le_trans hd hD) j u (Nat.le_trans hk hj) hu (Nat.le_trans hum hm)

end RunPrime

/-! ## The run with the cut -/

section RunCut

variable {G : Type} [DecidableEq G] {R : G → Type} {cost : Nat → Nat} {F : Step G R}

theorem run_succ (d : Nat) (P : List G) (g : G) :
    run cost F (d + 1) P g = node (cost P.length) (g ∈ P) (F (run cost F d (g :: P)) g) := rfl

theorem run_framed (hF : FrameF F) : ∀ d P g, Framed (run cost F d P g)
  | 0, _, _ => zero_framed
  | d + 1, P, g => by
    rw [run_succ]
    exact node_framed (hF _ _ (fun g' => Agree.refl (run_framed hF d (g :: P) g')) g).left

/-- The run at a larger index does what the run at a smaller one does. -/
theorem run_agree (hF : FrameF F) :
    ∀ d d', d ≤ d' → ∀ P g, Agree (run cost F d P g) (run cost F d' P g)
  | 0, d', _, P, g => by
    refine ⟨zero_framed, run_framed hF d' P g, ?_⟩
    intro t r t' h ho _
    simp only [run, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, g => by
    obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    rw [run_succ, run_succ]
    exact node_agree (hF _ _ (fun g' => run_agree hF d d'' (by omega) (g :: P) g') g)

theorem run_absorbs (cost : Nat → Nat) (F : Step G R) (d : Nat) (P : List G) (g : G) {t : Tank}
    (h : t.out = true) : run cost F d P g t = (none, t) := by
  cases d with
  | zero =>
    cases t
    simp_all [run]
  | succ d => rw [run_succ, node_out h]

theorem run_frame {cost : Nat → Nat} {F : Step G R} (hF : FrameF F) {d : Nat} {P : List G} {g : G}
    {t t' : Tank} {r : Option (R g)} (h : run cost F d P g t = (r, t')) (ho : t'.out = false) (k : Nat) :
    run cost F d P g (t.add k) = (r, t'.add k) :=
  (run_framed hF d P g).shift t r t' h ho k

theorem run_index {cost : Nat → Nat} {F : Step G R} (hF : FrameF F) {d d' : Nat} {P : List G} {g : G}
    {t : Tank} (h : (run cost F d P g t).2.out = false) (hd : d ≤ d') :
    run cost F d' P g t = run cost F d P g t := by
  have := (run_agree hF d d' hd P g).sim t _ _ rfl h 0
  simpa using this

/-- A pending goal that fails without the cut: the cut answers at once and
spends less. -/
theorem cut_hit (hF : FrameF F) {d k m : Nat} {Q : List G} {p : G} (hp : p ∈ Q)
    (hQ : Q.length = k) (hf : FailsUpTo cost F d p k m) :
    Dom m (run' cost F d k p) (run cost F d Q p) := by
  intro v r v' hvm h ho w hw hvw
  have hv : v.out = false := (run'_framed hF d k p).start h ho
  have hr : r = none := by
    have := hf d (Nat.le_refl _) k v (Nat.le_refl _) hv hvm
    rw [h] at this
    exact this
  cases d with
  | zero =>
    simp only [run', Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | succ d =>
    rw [run'_succ] at h
    obtain ⟨_, hcv, hcase⟩ := node_inv h ho
    rcases hcase with ⟨hfalse, _⟩ | ⟨_, hk⟩
    · exact absurd hfalse id
    · have hle := (hF _ _ (fun g' => Agree.refl (run'_framed hF d (k + 1) g')) p).left.le hk
      simp only at hle
      rw [run_succ, hQ, node_cut hw (by omega) hp]
      simp only [true_and]
      exact ⟨hr.symm, by omega⟩

/-- The cut never loses an answer, in dominance form.  The proof is strong
induction on the fuel.  At a goal `g` the step receives a smaller tank `t1`.
If `g` already answers without the cut from `t1`, one level deeper, the
induction hypothesis at `t1` gives the answer with the cut, and the frame and
the index lift it to `t`.  If not, `g` fails without the cut from every tank of
at most `t1` units, so the cut at `g` loses nothing below `t1`, and the step
carries the dominance over.  The case split is on an `Option`, so the proof
makes no choice. -/
theorem cut_dom (hc : CostOk cost) (hF : FrameF F) (hD : DomF F) :
    ∀ n d (P : List G) g m, m < n → (∀ p ∈ P, FailsUpTo cost F d p P.length m) →
      Dom m (run' cost F d P.length g) (run cost F d P g) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro d P g m hmn hP t r t' htm h ho u hu htu
    cases d with
    | zero =>
      simp only [run', Prod.mk.injEq] at h
      rw [← h.2] at ho
      simp at ho
    | succ d =>
      have hFr' : ∀ k g, Framed (F (run' cost F d k) g) := fun k g =>
        (hF _ _ (fun g' => Agree.refl (run'_framed hF d k g')) g).left
      have h0 := h
      rw [run'_succ] at h
      obtain ⟨ht, hct, hcase⟩ := node_inv h ho
      have hpos := hc.pos P.length
      rcases hcase with ⟨hfalse, _⟩ | ⟨_, hk⟩
      · exact absurd hfalse id
      · have hle := (hFr' _ g).le hk
        simp only at hle
        rcases Decidable.em (g ∈ P) with hgP | hgP
        · have hr : r = none := by
            have := hP g hgP (d + 1) (Nat.le_refl _) P.length t (Nat.le_refl _) ht htm
            rw [h0] at this
            exact this
          rw [run_succ, node_cut hu (by omega) hgP]
          simp only [true_and]
          exact ⟨hr.symm, by omega⟩
        · cases hx : (run' cost F d (P.length + 1) g ⟨t.left - cost P.length, false⟩).1 with
          | some x =>
            -- `g` already answers from the smaller tank
            have hx2 := run'_depth hc hF hD (Nat.le_succ P.length) hx (run'_some hx)
            have hw2 := run'_some hx2
            have e2 : run' cost F d P.length g ⟨t.left - cost P.length, false⟩ =
                (some x, (run' cost F d P.length g ⟨t.left - cost P.length, false⟩).2) := by
              rw [← hx2]
            have hIH := ih d P g (t.left - cost P.length) (by omega)
              (fun p hp => (hP p hp).mono (Nat.le_succ d) (Nat.le_refl _) (by omega))
              ⟨t.left - cost P.length, false⟩ _ _ (Nat.le_refl _) e2 hw2 u hu (by simp only; omega)
            obtain ⟨i1, i2, i3⟩ := hIH
            rw [run_index hF i2 (Nat.le_succ d)]
            -- the answer at `t` is the answer at `t1`, framed and lifted
            have ef := run'_frame hF e2 hw2 (cost P.length)
            have et : (⟨t.left - cost P.length, false⟩ : Tank).add (cost P.length) = t := by
              cases t
              simp only at ht
              subst ht
              simp only [Tank.add, Tank.mk.injEq, and_true]
              simp only at hct
              omega
            rw [et] at ef
            rw [run'_index hF (by rw [ef]; simpa using hw2) (Nat.le_succ d), ef] at h0
            simp only [Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            refine ⟨i1, i2, ?_⟩
            dsimp only at i3
            rw [Tank.add_left]
            omega
          | none =>
            -- `g` fails without the cut below the smaller tank
            have hfg : FailsUpTo cost F d g (P.length + 1) (t.left - cost P.length) := by
              intro d'' hd'' j v hj hv hvm
              cases hy : (run' cost F d'' j g v).1 with
              | none => rfl
              | some y =>
                exfalso
                have hy2 := run'_some hy
                have e1 := run'_index hF hy2 hd''
                have hy4 := run'_depth hc hF hD hj (by rw [e1]; exact hy) (by rw [e1]; exact hy2)
                have e3 := run'_frame hF (Prod.ext (α := Option (R g)) (β := Tank) hy4 rfl)
                  (run'_some hy4) (t.left - cost P.length - v.left)
                have ev : v.add (t.left - cost P.length - v.left) =
                    ⟨t.left - cost P.length, false⟩ := by
                  cases v
                  simp only at hv
                  subst hv
                  simp only [Tank.add, Tank.mk.injEq, and_true]
                  simp only at hvm
                  omega
                rw [ev] at e3
                rw [e3] at hx
                simp at hx
            have hO : ∀ g', Dom (t.left - cost P.length) (run' cost F d (P.length + 1) g')
                (run cost F d (g :: P) g') := by
              intro g'
              rcases Decidable.em (g' ∈ g :: P) with hg' | hg'
              · apply cut_hit hF hg' (by simp)
                rcases List.mem_cons.mp hg' with rfl | hp
                · exact hfg
                · exact (hP g' hp).mono (Nat.le_succ d) (Nat.le_succ _) (by omega)
              · have := ih d (g :: P) g' (t.left - cost P.length) (by omega) (by
                  intro p hp
                  rcases List.mem_cons.mp hp with rfl | hp
                  · simpa using hfg
                  · simpa using (hP p hp).mono (Nat.le_succ d) (Nat.le_succ _) (by omega))
                simpa using this
            have hDF := hD (t.left - cost P.length) _ _ (fun g' => run'_framed hF d (P.length + 1) g')
              (fun g' => run_framed hF d (g :: P) g') hO g
            obtain ⟨e1, e2, e3⟩ := hDF ⟨t.left - cost P.length, false⟩ r t' (Nat.le_refl _) hk ho
              ⟨u.left - cost P.length, false⟩ rfl (by simp only; omega)
            rw [run_succ, node_go hu (by omega) hgP e2]
            refine ⟨e1, e2, ?_⟩
            simp only at e3
            omega

theorem cut_complete {cost : Nat → Nat} (hc : CostOk cost) {F : Step G R} (hF : FrameF F) (hD : DomF F)
    {d : Nat} {P : List G} {g : G} {t : Tank}
    (h : (run' cost F d P.length g t).1.isSome = true) (ho : (run' cost F d P.length g t).2.out = false)
    (hP : ∀ p ∈ P, FailsBelow cost F p P.length t.left) :
    (run cost F d P g t).1.isSome = true := by
  have ht : t.out = false := (run'_framed hF d P.length g).start rfl ho
  have := cut_dom hc hF hD (t.left + 1) d P g t.left (Nat.lt_succ_self _)
    (fun p hp d' _ j u hj hu hum => hP p hp d' j u hj hu hum) t _ _ (Nat.le_refl _) rfl ho t ht
    (Nat.le_refl _)
  rw [this.1]
  exact h

theorem cut_complete_nil {cost : Nat → Nat} (hc : CostOk cost) {F : Step G R} (hF : FrameF F) (hD : DomF F)
    {d : Nat} {g : G} {t : Tank}
    (h : (run' cost F d 0 g t).1.isSome = true) (ho : (run' cost F d 0 g t).2.out = false) :
    (run cost F d [] g t).1.isSome = true :=
  cut_complete (P := []) hc hF hD h ho (fun _ hp => by cases hp)

end RunCut

end Frontend.Fuel
