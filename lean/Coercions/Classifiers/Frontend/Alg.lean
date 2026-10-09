import Coercions.Classifiers.Frontend.Sub

/-!
# The algorithmic judgment and completeness

`Alg` states the rules of the algorithm of `Sub.lean`, one constructor per
alternative, with no fuel and no pending goals.  There are five goal kinds:
`shp S T`, `cap C D`, `kind C φ`, `var x V T` and `esub E F`.

Some constructors carry side conditions.  After an intersection on the right,
`isAnd T = false`, since that alternative is final.  A selection on the right
through a lower bound carries `lo ≠ ⊥`, as the algorithm skips such a member.
A recursive shape opened at a variable carries `Shape.Decl B`, as `Rec-I` and
`Rec-E` ask.  A capture binder, an instance binder, a capture member or a
projected atom on the right carries the inclusion of its atom in the right set.
A member premise is phrased through the lookup (`Member`, `CapMember`,
`KindMember`): the lookup finds that member within its fuel.  A projected atom
is taken apart by the test the algorithm runs, `unprojSetW?` (`UnprojAt`).

Two types compare by a set goal and a shape goal, so a constructor that
compares two types has a `cap` and a `shp` premise for each pair.  The domains
of two function shapes and the bodies of two existentials are premises in
`Γ.scope`, the codomains in `Γ.body T2`, and the residual of a pack in
`Γ.scopeInst W`.  The witness `W` of a pack is the answer's own capture set or
the bound.  A set below a projected atom also has a `kind` premise.

Completeness holds up to the recursion limit.  If `Alg` derives a goal, the
algorithm answers it at every fuel at which its run ends with the tank
(the shared fuel of `Fuel.lean`) unmarked (`shp?_complete`, `cap?_complete`,
`kind?_complete`, `esub?_complete`, `var?_complete`).  Two types compare by two runs on one tank, so
`sub?_complete` takes one derivation per half.  A run that ends unmarked with
no answer is a rejection by the rules (`shp?_reject`, `cap?_reject`,
`kind?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`).

Completeness cannot say that some fuel suffices.  The tank is shared by all
the alternatives of a goal, and a marked tank stays marked.  So an alternative
that never ends, tried before the one an `Alg` derivation uses, exhausts every
tank.  `p.A ∧ ⊥ <: ∀(y : ⊤) q.B` is such a goal.  `Alg` derives it by the right
operand, and the left operand, tried first, descends under a new binder at each
level.

The proof needs no minimal derivation.  A derivation in which no goal repeats
along a branch exists whenever a derivation does (`Deriv.pruneNil`), because a
repeat is cut out by using the inner derivation of the goal at the outer place.
The run never cuts such a derivation.  At each goal it either answers by an
alternative tried before or reaches the one the derivation uses, since the tank
is unmarked at the end and so at every point before (`run_ans`).  Both facts
are generic in the goals and the step.

`Alg.sound` is the soundness of `Alg`: each constructor builds the derivation
its alternative emits.

The checks at the end derive goals of each kind by `Alg`, read E1, E3, E4, CE5,
a subcapturing goal of C2 and three kinding goals as rejections by the rules,
and show the goal above whose run hits the recursion limit.
-/

namespace ClassifiersFrontend.Core

open Frontend.Fuel
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy CapKind)
open Classifiers
open scoped Classifiers.DotMNF

/-! ## Derivations without a repeated goal

`Deriv Rule g` is a derivation of `g` by one-step rules: `Rule g ps` says that
`g` follows from the premises `ps`.  `DerivP Rule P g` is a derivation whose
goals never repeat one of `P` or one below them on the branch, so the run with
the pending goals `P` never cuts it. -/

section Prune

variable {Goal : Type} (Rule : Goal → List Goal → Prop)

/-- Derivations by `Rule`. -/
inductive Deriv : Goal → Prop
  | mk {g : Goal} {ps : List Goal} : Rule g ps → (∀ p ∈ ps, Deriv p) → Deriv g

/-- Derivations by `Rule` that avoid the pending goals `P`, and in which no goal
repeats along a branch. -/
inductive DerivP : List Goal → Goal → Prop
  | mk {P : List Goal} {g : Goal} {ps : List Goal} :
      g ∉ P → Rule g ps → (∀ p ∈ ps, DerivP (g :: P) p) → DerivP P g

/-- What pruning a derivation gives under the pending goals `P`: a derivation
that avoids them, or a derivation of one of them that avoids those below it. -/
def Pruned (P : List Goal) (g : Goal) : Prop :=
  DerivP Rule P g ∨ ∃ Q1 p Q2, P = Q1 ++ p :: Q2 ∧ DerivP Rule Q2 p

variable {Rule}

/-- Each member of a list gives a fact or a common fact, so either all give
the first or one gives the second. -/
theorem all_or {α : Type} {A : α → Prop} {B : Prop} :
    ∀ l : List α, (∀ a ∈ l, A a ∨ B) → (∀ a ∈ l, A a) ∨ B
  | [], _ => Or.inl fun _ h => by cases h
  | a :: l, h => by
    rcases h a (List.mem_cons.mpr (Or.inl rfl)) with ha | hb
    · rcases all_or l (fun b hb => h b (List.mem_cons.mpr (Or.inr hb))) with hl | hb
      · refine Or.inl fun b hb => ?_
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hl b hb
      · exact Or.inr hb
    · exact Or.inr hb

/-- A derivation can be pruned under any pending goals.  At a goal outside
`P`, the premises are pruned under `g :: P`.  If one of them repeats `g`, its
derivation of `g` replaces this one.  At a goal inside `P`, the derivation is
pruned under the goals below that place in `P`. -/
theorem Deriv.prune [DecidableEq Goal] {g : Goal} (h : Deriv Rule g) :
    ∀ P, Pruned Rule P g := by
  induction h with
  | @mk g ps hr _ ih =>
    have hcomb : ∀ P, g ∉ P → Pruned Rule P g := by
      intro P hg
      have hps : ∀ p ∈ ps, DerivP Rule (g :: P) p ∨ Pruned Rule P g := by
        intro p hp
        rcases ih p hp (g :: P) with h1 | ⟨Q1, p', Q2, hQ, h2⟩
        · exact Or.inl h1
        · right
          cases Q1 with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hQ
            obtain ⟨rfl, rfl⟩ := hQ
            exact Or.inl h2
          | cons a Q1 =>
            simp only [List.cons_append, List.cons.injEq] at hQ
            exact Or.inr ⟨Q1, p', Q2, hQ.2, h2⟩
      rcases all_or ps hps with hall | hpr
      · exact Or.inl (DerivP.mk hg hr hall)
      · exact hpr
    suffices H : ∀ n (P : List Goal), P.length ≤ n → Pruned Rule P g from
      fun P => H _ P (Nat.le_refl _)
    intro n
    induction n with
    | zero =>
      intro P hP
      cases P with
      | nil => exact hcomb [] (fun h => by cases h)
      | cons _ _ => simp at hP
    | succ n ihn =>
      intro P hP
      rcases Decidable.em (g ∈ P) with hg | hg
      · obtain ⟨Q1, Q2, rfl⟩ := List.append_of_mem hg
        have hlen : Q2.length ≤ n := by
          simp only [List.length_append, List.length_cons] at hP
          omega
        rcases ihn Q2 hlen with h1 | ⟨Q1', p, Q2', rfl, h2⟩
        · exact Or.inr ⟨Q1, g, Q2, rfl, h1⟩
        · exact Or.inr ⟨Q1 ++ g :: Q1', p, Q2', by simp, h2⟩
      · exact hcomb P hg

/-- A derivation gives one in which no goal repeats along a branch. -/
theorem Deriv.pruneNil [DecidableEq Goal] {g : Goal} (h : Deriv Rule g) : DerivP Rule [] g := by
  rcases h.prune [] with h | ⟨Q1, p, Q2, hQ, _⟩
  · exact h
  · simp at hQ

end Prune

/-! ## Computations that answer when they end unmarked -/

section Ans

variable {α β : Type}

/-- From every tank on which `c` ends unmarked, it answers. -/
def Ans (c : Fu (Option α)) : Prop :=
  ∀ t, (c t).2.out = false → (c t).1.isSome = true

theorem ans_ret {o : Option α} (h : o.isSome = true) : Ans (Fu.ret o) := fun _ _ => h

theorem ans_orElse_left {a : Fu (Option α)} {b : Unit → Fu (Option α)} (ha : Ans a) :
    Ans (Fu.orElse a b) := by
  intro t ho
  have hd : Fu.orElse a b t = match a t with
      | (some x, t1) => (some x, t1)
      | (none, t1) => if t1.out then (none, t1) else b () t1 := rfl
  have hat := ha t
  revert ho hat
  rw [hd]
  rcases a t with ⟨x, t1⟩
  cases x with
  | some x => intro _ _; rfl
  | none =>
    intro ho h
    have ht1 : t1.out = false := by
      cases h1 : t1.out
      · rfl
      · simp [h1] at ho
    simpa using h ht1

/-- The second branch answers, so the choice does: the first branch either
answers, or fails with the tank unmarked and hands over, or marks the tank. -/
theorem ans_orElse_right {a : Fu (Option α)} {b : Unit → Fu (Option α)} (hb : Ans (b ())) :
    Ans (Fu.orElse a b) := by
  intro t ho
  have hd : Fu.orElse a b t = match a t with
      | (some x, t1) => (some x, t1)
      | (none, t1) => if t1.out then (none, t1) else b () t1 := rfl
  revert ho
  rw [hd]
  rcases a t with ⟨x, t1⟩
  cases x with
  | some x => intro _; rfl
  | none =>
    intro ho
    have ht1 : t1.out = false := by
      cases h1 : t1.out
      · rfl
      · simp [h1] at ho
    simp only [ht1, Bool.false_eq_true, if_false] at ho ⊢
    exact hb t1 ho

theorem ans_bindO {c : Fu (Option α)} {f : α → Fu (Option β)} (hc : Ans c) (hf : ∀ a, Ans (f a)) :
    Ans (bindO c f) := by
  intro t ho
  have hd : bindO c f t = match c t with
      | (some a, t1) => f a t1
      | (none, t1) => (none, t1) := by
    simp only [bindO, Fu.bind]
    rcases c t with ⟨o, t1⟩
    cases o <;> rfl
  have hct := hc t
  revert ho hct
  rw [hd]
  rcases c t with ⟨o, t1⟩
  cases o with
  | some a => intro ho _; exact hf a t1 ho
  | none => intro ho h; simpa using h ho

theorem ans_mapO {c : Fu (Option α)} {f : α → β} (hc : Ans c) : Ans (mapO c f) := by
  intro t ho
  have hd : mapO c f t = ((c t).1.map f, (c t).2) := rfl
  rw [hd] at ho ⊢
  simpa using hc t ho

theorem ans_firstSome {f : α → Fu (Option β)} {x : α} (hx : Ans (f x)) :
    ∀ l, x ∈ l → Ans (Fu.firstSome f l)
  | [], h => by cases h
  | y :: ys, h => by
    simp only [Fu.firstSome]
    rcases List.mem_cons.mp h with rfl | h
    · exact ans_orElse_left hx
    · exact ans_orElse_right (ans_firstSome hx ys h)

theorem ans_ite_pos {p : Prop} [Decidable p] {a b : Fu (Option α)} (hp : p) (ha : Ans a) :
    Ans (if p then a else b) := by
  rw [if_pos hp]
  exact ha

theorem ans_ite_neg {p : Prop} [Decidable p] {a b : Fu (Option α)} (hp : ¬p) (hb : Ans b) :
    Ans (if p then a else b) := by
  rw [if_neg hp]
  exact hb

theorem ans_dite_pos {p : Prop} [Decidable p] {a : p → Fu (Option α)} {b : ¬p → Fu (Option α)}
    (hp : p) (ha : Ans (a hp)) : Ans (dite p a b) := by
  rw [dif_pos hp]
  exact ha

/-- A level of a run that does not cut answers when its step does. -/
theorem node_ans {c : Nat} {cut : Prop} [Decidable cut] {k : Fu (Option α)} (hcut : ¬cut)
    (hk : Ans k) : Ans (node c cut k) := by
  intro t ho
  obtain ⟨_, _, hcase⟩ := node_inv (r := (node c cut k t).1) (t' := (node c cut k t).2) rfl ho
  rcases hcase with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd h hcut
  · have := hk _ (by rw [h]; exact ho)
    rw [h] at this
    exact this

end Ans

/-! ## The run answers a derivation without repeats -/

section RunAns

variable {Goal : Type} [DecidableEq Goal] {Res : Goal → Type} {cost : Nat → Nat}
  {F : Step Goal Res} {Rule : Goal → List Goal → Prop}

/-- If each rule's step answers whenever the oracle answers its premises, the
run answers every derivation without repeats that avoids its pending goals,
whenever it ends unmarked. -/
theorem run_ans (hF : FrameF F)
    (hR : ∀ g ps, Rule g ps → ∀ o : Oracle Goal Res, (∀ g', Framed (o g')) →
      (∀ p ∈ ps, Ans (o p)) → Ans (F o g))
    {P : List Goal} {g : Goal} (h : DerivP Rule P g) : ∀ d, Ans (run cost F d P g) := by
  induction h with
  | mk hgP hr _ ih =>
    intro d
    cases d with
    | zero =>
      intro t ho
      simp [run] at ho
    | succ d =>
      rw [run_succ]
      exact node_ans hgP (hR _ _ hr _ (fun g' => run_framed hF d _ g') (fun p hp => ih p hp d))

end RunAns

/-! ## Member premises -/

/-- `p` has the type member `A : lo..hi`: the lookup of `p`'s type members at
`A` finds it, from some full tank, and ends with the tank unmarked. -/
def Member {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (lo hi : Shape s) : Prop :=
  ∃ n, (typs Γ n p A ⟨n, false⟩).2.out = false ∧
    ∃ d ∈ (typs Γ n p A ⟨n, false⟩).1, d.1 = lo ∧ d.2.1 = hi

/-- `p` has the capture member `A : c1..c2` bounded by sets: the lookup of
`p`'s capture members at `A` finds it, from some full tank, and ends with the
tank unmarked. -/
def CapMember {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (c1 c2 : CaptureSet s) : Prop :=
  ∃ n, (caps Γ n p A ⟨n, false⟩).2.out = false ∧
    ∃ d ∈ (caps Γ n p A ⟨n, false⟩).1, d.1 = c1 ∧ d.2.1 = c2

/-- `p` has the capture member `A` bounded by the kind `ψ`: the lookup of
`p`'s capture members bounded by a kind at `A` finds it, from some full tank,
and ends with the tank unmarked. -/
def KindMember {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (ψ : Cls.Kind) : Prop :=
  ∃ n, (capks Γ n p A ⟨n, false⟩).2.out = false ∧
    ∃ d ∈ (capks Γ n p A ⟨n, false⟩).1, d.1 = ψ

/-- A type member premise read off one lookup.  Both hypotheses are
decidable, so the kernel checks them on an example. -/
theorem Member.of_mem {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Shape s}
    (n : Nat) (ho : (typs Γ n p A ⟨n, false⟩).2.out = false)
    (h : (lo, hi) ∈ (typs Γ n p A ⟨n, false⟩).1.map fun d => (d.1, d.2.1)) :
    Member Γ p A lo hi := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, d, hd, (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩

/-- A capture member premise read off one lookup. -/
theorem CapMember.of_mem {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label}
    {c1 c2 : CaptureSet s} (n : Nat) (ho : (caps Γ n p A ⟨n, false⟩).2.out = false)
    (h : (c1, c2) ∈ (caps Γ n p A ⟨n, false⟩).1.map fun d => (d.1, d.2.1)) :
    CapMember Γ p A c1 c2 := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, d, hd, (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩

/-- A kind member premise read off one lookup. -/
theorem KindMember.of_mem {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {ψ : Cls.Kind}
    (n : Nat) (ho : (capks Γ n p A ⟨n, false⟩).2.out = false)
    (h : ψ ∈ (capks Γ n p A ⟨n, false⟩).1.map (·.1)) : KindMember Γ p A ψ := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, d, hd, he⟩

/-- Two full tanks with a common larger tank: `⟨n, false⟩` grown by the fuel
left in `t`, and `t` grown by `n`. -/
theorem tank_meet {n : Nat} {t : Tank} (ht : t.out = false) :
    (⟨n, false⟩ : Tank).add t.left = t.add n := by
  obtain ⟨l, o⟩ := t
  simp only at ht
  subst ht
  simp only [Tank.add, Tank.mk.injEq, and_true]
  omega

/-- Two member lookups that end unmarked find the same members, for every
reader. -/
theorem members_same {s : Sig} {β : Type} {Γ : Ctx s} {p : BVar s .var} {k : Key}
    {pick : Found Γ p (Γ.lookup p).shape → Option β} {n : Nat} {t : Tank}
    (h1 : (members Γ n p k pick ⟨n, false⟩).2.out = false)
    (h2 : (members Γ t.left p k pick t).2.out = false) :
    (members Γ t.left p k pick t).1 = (members Γ n p k pick ⟨n, false⟩).1 := by
  have ht : t.out = false := (members_framed Γ t.left p k pick).start rfl h2
  have hu := tank_meet (n := n) ht
  have e1 := members_frame (pick := pick) (Prod.ext rfl rfl) h1 t.left
  have e2 := members_frame (pick := pick) (Prod.ext rfl rfl) h2 n
  rw [hu] at e1
  have i1 := members_index (pick := pick) (d' := n + t.left) (by rw [e1]; exact h1)
    (Nat.le_add_right _ _)
  have i2 := members_index (pick := pick) (d' := n + t.left) (by rw [e2]; exact h2)
    (Nat.le_add_left _ _)
  have := i1.symm.trans i2
  rw [e1, e2] at this
  exact (Prod.mk.inj this).1.symm

/-- A member lookup at the tank's own index, then a computation on the
members found, answers when the computation answers on the members that one
lookup from a full tank finds, provided that lookup ends unmarked. -/
theorem membersAt_ans {s : Sig} {β γ : Type} {Γ : Ctx s} {p : BVar s .var} {k : Key}
    {pick : Found Γ p (Γ.lookup p).shape → Option β} {n : Nat}
    {c : List β → Fu (Option γ)} (hn : (members Γ n p k pick ⟨n, false⟩).2.out = false)
    (hk : ∀ ds, Framed (c ds)) (hans : Ans (c (members Γ n p k pick ⟨n, false⟩).1)) :
    Ans (Fu.bind (fun t => members Γ t.left p k pick t) c) := by
  intro t ho
  have hd : Fu.bind (fun t => members Γ t.left p k pick t) c t =
      c (members Γ t.left p k pick t).1 (members Γ t.left p k pick t).2 := rfl
  rw [hd] at ho ⊢
  have ht1 : (members Γ t.left p k pick t).2.out = false := (hk _).start rfl ho
  have hds := members_same hn ht1
  revert ho
  rw [hds]
  exact hans _

/-- A lookup of a type member, then a computation on the members found,
answers when the computation does on every list that holds the member. -/
theorem typsAt_ans {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Shape s} {β : Type}
    {k : List (TMem Γ p A) → Fu (Option β)} (hm : Member Γ p A lo hi) (hk : ∀ ds, Framed (k ds))
    (hans : ∀ ds, (∃ d ∈ ds, d.1 = lo ∧ d.2.1 = hi) → Ans (k ds)) :
    Ans (Fu.bind (typsAt Γ p A) k) := by
  obtain ⟨n, hn, hmem⟩ := hm
  exact membersAt_ans hn hk (hans _ hmem)

/-- A lookup of a capture member bounded by sets, then a computation on the
members found, answers when the computation does on every list that holds the
member. -/
theorem capsAt_ans {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {c1 c2 : CaptureSet s}
    {β : Type} {k : List (CMem Γ p A) → Fu (Option β)} (hm : CapMember Γ p A c1 c2)
    (hk : ∀ ds, Framed (k ds)) (hans : ∀ ds, (∃ d ∈ ds, d.1 = c1 ∧ d.2.1 = c2) → Ans (k ds)) :
    Ans (Fu.bind (capsAt Γ p A) k) := by
  obtain ⟨n, hn, hmem⟩ := hm
  exact membersAt_ans hn hk (hans _ hmem)

/-- A lookup of a capture member bounded by a kind, then a computation on the
members found, answers when the computation does on every list that holds the
member. -/
theorem capksAt_ans {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {ψ : Cls.Kind}
    {β : Type} {k : List (KMem Γ p A) → Fu (Option β)} (hm : KindMember Γ p A ψ)
    (hk : ∀ ds, Framed (k ds)) (hans : ∀ ds, (∃ d ∈ ds, d.1 = ψ) → Ans (k ds)) :
    Ans (Fu.bind (capksAt Γ p A) k) := by
  obtain ⟨n, hn, hmem⟩ := hm
  exact membersAt_ans hn hk (hans _ hmem)

/-! ## Projected atoms -/

/-- The test the algorithm runs, `unprojSetW?`, reads the set `L` as
`C₀ ↾ φ`.  An `abbrev`, so `Decidable` is synthesised and an example
discharges it by `decide`. -/
abbrev UnprojAt {s : Sig} (L C₀ : CaptureSet s) (φ : Cls.Kind) : Prop :=
  (unprojSetW? L).map Subtype.val = some (C₀, φ)

/-- The test answers with the pair the premise names. -/
theorem UnprojAt.of_eq {s : Sig} {L C₀ : CaptureSet s} {φ : Cls.Kind}
    {p : CaptureSet s × Cls.Kind} {h : CaptureSet.proj p.1 p.2 = L} (hu : UnprojAt L C₀ φ)
    (he : unprojSetW? L = some ⟨p, h⟩) : p = (C₀, φ) := by
  unfold UnprojAt at hu
  rw [he] at hu
  exact Option.some.inj hu

/-- The test does not refuse a set the premise reads. -/
theorem UnprojAt.not_none {s : Sig} {L C₀ : CaptureSet s} {φ : Cls.Kind} (hu : UnprojAt L C₀ φ)
    (he : unprojSetW? L = none) : False := by
  unfold UnprojAt at hu
  rw [he] at hu
  cases hu

/-- The set the premise reads is the projection it names. -/
theorem UnprojAt.eq {s : Sig} {L C₀ : CaptureSet s} {φ : Cls.Kind} (hu : UnprojAt L C₀ φ) :
    CaptureSet.proj C₀ φ = L := by
  cases he : unprojSetW? L with
  | none => exact (hu.not_none he).elim
  | some w =>
    obtain ⟨p, h⟩ := w
    have := hu.of_eq he
    subst this
    exact h

/-! ## The judgment -/

/-- The algorithm's rules, one constructor per alternative of `shpStep`,
`capStep`, `kindStep`, `varStep` and `esubStep`, with no fuel and no pending
goals.  An alternative that reads two forms of its goal has one constructor
per form. -/
inductive Alg : G → Prop
  | refl {s : Sig} {Γ : Ctx s} {T : Shape s} : Alg ⟨s, Γ, .shp T T⟩
  | top {s : Sig} {Γ : Ctx s} {S : Shape s} : Alg ⟨s, Γ, .shp S .top⟩
  | bot {s : Sig} {Γ : Ctx s} {T : Shape s} : Alg ⟨s, Γ, .shp .bot T⟩
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Shape s} :
      Alg ⟨s, Γ, .shp S T1⟩ → Alg ⟨s, Γ, .shp S T2⟩ → Alg ⟨s, Γ, .shp S (.and T1 T2)⟩
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Shape s} {p : BVar s .var} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .shp S lo⟩ →
      Alg ⟨s, Γ, .shp S (.sel (.var p) A)⟩
  | fld {s : Sig} {Γ : Ctx s} {a : Label} {S S' : Shape s} {C C' : CaptureSet s} :
      Alg ⟨s, Γ, .cap C C'⟩ → Alg ⟨s, Γ, .shp S S'⟩ →
      Alg ⟨s, Γ, .shp (.fld a (S ^ C)) (.fld a (S' ^ C'))⟩
  | typ {s : Sig} {Γ : Ctx s} {A : Label} {S1 S2 T1 T2 : Shape s} :
      Alg ⟨s, Γ, .shp S2 S1⟩ → Alg ⟨s, Γ, .shp T1 T2⟩ →
      Alg ⟨s, Γ, .shp (.typ A S1 T1) (.typ A S2 T2)⟩
  | cap {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 c1' c2' : CaptureSet s} :
      Alg ⟨s, Γ, .cap c1' c1⟩ → Alg ⟨s, Γ, .cap c2 c2'⟩ →
      Alg ⟨s, Γ, .shp (.cap A c1 c2) (.cap A c1' c2')⟩
  | capkI {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 : CaptureSet s} {φ : Cls.Kind} :
      Alg ⟨s, Γ, .kind c2 φ⟩ → Alg ⟨s, Γ, .shp (.cap A c1 c2) (.capk A φ)⟩
  | capk {s : Sig} {Γ : Ctx s} {A : Label} {φ1 φ2 : Cls.Kind} :
      φ1.subkindB φ2 = true → Alg ⟨s, Γ, .shp (.capk A φ1) (.capk A φ2)⟩
  | box {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} :
      Alg ⟨s, Γ, .cap C C'⟩ → Alg ⟨s, Γ, .shp S S'⟩ →
      Alg ⟨s, Γ, .shp (.box (S ^ C)) (.box (S' ^ C'))⟩
  | all {s : Sig} {Γ : Ctx s} {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Alg ⟨_, Γ.scope, .cap (Dom.underRoot T2).captureSet (Dom.underRoot T1).captureSet⟩ →
      Alg ⟨_, Γ.scope, .shp (Dom.underRoot T2).shape (Dom.underRoot T1).shape⟩ →
      Alg ⟨_, Γ.body T2, .esub (Cod.underRoot U1) (Cod.underRoot U2)⟩ →
      Alg ⟨s, Γ, .shp (.all T1 U1) (.all T2 U2)⟩
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Shape s} {q : BVar s .var} {B : Label} :
      Member Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .shp hi T⟩ →
      Alg ⟨s, Γ, .shp (.sel (.var q) B) T⟩
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Shape s} :
      isAnd T = false → Alg ⟨s, Γ, .shp S1 T⟩ → Alg ⟨s, Γ, .shp (.and S1 S2) T⟩
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Shape s} :
      isAnd T = false → Alg ⟨s, Γ, .shp S2 T⟩ → Alg ⟨s, Γ, .shp (.and S1 S2) T⟩
  | cElem {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} :
      CaptureSet.Subset C D → Alg ⟨s, Γ, .cap C D⟩
  | cUnion {s : Sig} {Γ : Ctx s} {a b : CapAtom s} {C D : CaptureSet s} :
      Alg ⟨s, Γ, .cap [a] D⟩ → Alg ⟨s, Γ, .cap (b :: C) D⟩ → Alg ⟨s, Γ, .cap (a :: b :: C) D⟩
  | cLevel {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {D : CaptureSet s} :
      CaptureSet.Subset [CapAtom.cvar κ] D → Γ.IsRoot (.cvar κ) → Γ.LvlLe a (.cvar κ) →
      Alg ⟨s, Γ, .cap [a] D⟩
  | cProjMono {s : Sig} {Γ : Ctx s} {a x : CapAtom s} {C₀ C₀' D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [a] C₀ φ → UnprojAt [x] C₀' φ → CaptureSet.Subset [x] D →
      Alg ⟨s, Γ, .cap C₀ C₀'⟩ → Alg ⟨s, Γ, .cap [a] D⟩
  | cProjL {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C₀ D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [a] C₀ φ → Alg ⟨s, Γ, .cap C₀ D⟩ → Alg ⟨s, Γ, .cap [a] D⟩
  | cSelHi {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 → Alg ⟨s, Γ, .cap c2 D⟩ → Alg ⟨s, Γ, .cap [CapAtom.sel y A] D⟩
  | cProjR {s : Sig} {Γ : Ctx s} {a x : CapAtom s} {X D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [x] X φ → CaptureSet.Subset [x] D → Alg ⟨s, Γ, .kind [a] φ⟩ →
      Alg ⟨s, Γ, .cap [a] X⟩ → Alg ⟨s, Γ, .cap [a] D⟩
  | cSelLo {s : Sig} {Γ : Ctx s} {a : CapAtom s} {y : BVar s .var} {A : Label}
      {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 → CaptureSet.Subset [CapAtom.sel y A] D →
      Alg ⟨s, Γ, .cap [a] c1⟩ → Alg ⟨s, Γ, .cap [a] D⟩
  | cInst {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {W D : CaptureSet s} :
      CaptureSet.Subset [CapAtom.cvar κ] D → Γ.instSet? κ = some W → Alg ⟨s, Γ, .cap [a] W⟩ →
      Alg ⟨s, Γ, .cap [a] D⟩
  | cVar {s : Sig} {Γ : Ctx s} {x : BVar s .var} {D : CaptureSet s} :
      Alg ⟨s, Γ, .cap (Γ.lookup x).captureSet D⟩ → Alg ⟨s, Γ, .cap [CapAtom.var x] D⟩
  | cProjVar {s : Sig} {Γ : Ctx s} {y : BVar s .var} {φ : Cls.Kind} {D : CaptureSet s} :
      Alg ⟨s, Γ, .cap (CaptureSet.proj (Γ.lookup y).captureSet φ) D⟩ →
      Alg ⟨s, Γ, .cap [CapAtom.proj (.var y) φ] D⟩
  | cProjSel {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} {φ : Cls.Kind}
      {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 → Alg ⟨s, Γ, .cap (CaptureSet.proj c2 φ) D⟩ →
      Alg ⟨s, Γ, .cap [CapAtom.proj (.sel y A) φ] D⟩
  | kNil {s : Sig} {Γ : Ctx s} {φ : Cls.Kind} : Alg ⟨s, Γ, .kind [] φ⟩
  | kCons {s : Sig} {Γ : Ctx s} {a b : CapAtom s} {C : CaptureSet s} {φ : Cls.Kind} :
      Alg ⟨s, Γ, .kind [a] φ⟩ → Alg ⟨s, Γ, .kind (b :: C) φ⟩ → Alg ⟨s, Γ, .kind (a :: b :: C) φ⟩
  | kProj {s : Sig} {Γ : Ctx s} {a : CapAtom s} {φ : Cls.Kind} :
      a.kindOf.subkindB φ = true → Alg ⟨s, Γ, .kind [a] φ⟩
  | kCls {s : Sig} {Γ : Ctx s} {a : CapAtom s} {c : Cls.Classifier} {φ : Cls.Kind} :
      Γ.clsOf? a.base = some c → (a.kindOf.containsB c = true → φ.containsB c = true) →
      Alg ⟨s, Γ, .kind [a] φ⟩
  | kSel {s : Sig} {Γ : Ctx s} {x : BVar s .var} {A : Label} {ψ φ : Cls.Kind} :
      KindMember Γ x A ψ → ψ = φ ∨ ψ.subkindB φ = true →
      Alg ⟨s, Γ, .kind [CapAtom.sel x A] φ⟩
  | kVar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {x : BVar s .var} {φ : Cls.Kind} :
      a.base = CapAtom.var x →
      Alg ⟨s, Γ, .kind (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ⟩ →
      Alg ⟨s, Γ, .kind [a] φ⟩
  | kInst {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {C : CaptureSet s}
      {φ : Cls.Kind} :
      a.base = CapAtom.cvar κ → Γ.instSet? κ = some C →
      Alg ⟨s, Γ, .kind (CaptureSet.proj C a.kindOf) φ⟩ → Alg ⟨s, Γ, .kind [a] φ⟩
  | kSelUp {s : Sig} {Γ : Ctx s} {x : BVar s .var} {A : Label} {c1 c2 : CaptureSet s}
      {φ : Cls.Kind} :
      CapMember Γ x A c1 c2 → Alg ⟨s, Γ, .kind c2 φ⟩ → Alg ⟨s, Γ, .kind [CapAtom.sel x A] φ⟩
  | kProjS {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C₀ : CaptureSet s} {ψ φ : Cls.Kind} :
      UnprojAt [a] C₀ ψ → Alg ⟨s, Γ, .kind C₀ φ⟩ → Alg ⟨s, Γ, .kind [a] φ⟩
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Alg ⟨s, Γ, .var x T T⟩
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {C : CaptureSet s} {T1 T2 : Shape s} :
      Alg ⟨s, Γ, .var x V (T1 ^ C)⟩ → Alg ⟨s, Γ, .var x V (T2 ^ C)⟩ →
      Alg ⟨s, Γ, .var x V ((Shape.and T1 T2) ^ C)⟩
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {C : CaptureSet s} {B : Shape (s,x)} :
      Shape.Decl B → Alg ⟨s, Γ, .var x V ((B.substVar x) ^ C)⟩ →
      Alg ⟨s, Γ, .var x V ((Shape.mu B) ^ C)⟩
  | vSelLo {s : Sig} {Γ : Ctx s} {x p : BVar s .var} {V : Ty s} {C : CaptureSet s}
      {lo hi : Shape s} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .var x V (lo ^ C)⟩ →
      Alg ⟨s, Γ, .var x V ((Shape.sel (.var p) A) ^ C)⟩
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {B : Shape (s,x)} :
      isAnd T.shape = false → Shape.Decl B → Alg ⟨s, Γ, .var x ((B.substVar x) ^ C) T⟩ →
      Alg ⟨s, Γ, .var x ((Shape.mu B) ^ C) T⟩
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {V1 V2 : Shape s} :
      isAnd T.shape = false → Alg ⟨s, Γ, .var x (V1 ^ C) T⟩ →
      Alg ⟨s, Γ, .var x ((Shape.and V1 V2) ^ C) T⟩
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {V1 V2 : Shape s} :
      isAnd T.shape = false → Alg ⟨s, Γ, .var x (V2 ^ C) T⟩ →
      Alg ⟨s, Γ, .var x ((Shape.and V1 V2) ^ C) T⟩
  | vSelHi {s : Sig} {Γ : Ctx s} {x q : BVar s .var} {T : Ty s} {C : CaptureSet s}
      {lo hi : Shape s} {B : Label} :
      Member Γ q B lo hi → isAnd T.shape = false → Alg ⟨s, Γ, .var x (hi ^ C) T⟩ →
      Alg ⟨s, Γ, .var x ((Shape.sel (.var q) B) ^ C) T⟩
  | vWiden {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isAnd T.shape = false → Alg ⟨s, Γ, .cap V.captureSet T.captureSet⟩ →
      Alg ⟨s, Γ, .shp V.shape T.shape⟩ → Alg ⟨s, Γ, .var x V T⟩
  | eTy {s : Sig} {Γ : Ctx s} {T T' : Ty s} :
      Alg ⟨s, Γ, .cap T.captureSet T'.captureSet⟩ → Alg ⟨s, Γ, .shp T.shape T'.shape⟩ →
      Alg ⟨s, Γ, .esub (.ty T) (.ty T')⟩
  | ePack {s : Sig} {Γ : Ctx s} {T' : Ty s} {C₀ W : CaptureSet s} {T : Ty (s,c)} :
      W ∈ [T'.captureSet, C₀] → Alg ⟨s, Γ, .cap W C₀⟩ →
      Alg ⟨_, Γ.scopeInst W, .cap ((T'.weaken (k := .cap)).weaken (k := .cap)).captureSet
        (Dom.underRoot (s := s) T).captureSet⟩ →
      Alg ⟨_, Γ.scopeInst W, .shp ((T'.weaken (k := .cap)).weaken (k := .cap)).shape
        (Dom.underRoot (s := s) T).shape⟩ →
      Alg ⟨s, Γ, .esub (.ty T') (∃ᶜ[C₀] T)⟩
  | eExist {s : Sig} {Γ : Ctx s} {C₀ C₀' : CaptureSet s} {T T' : Ty (s,c)} :
      Alg ⟨s, Γ, .cap C₀ C₀'⟩ →
      Alg ⟨_, Γ.scope, .cap (Dom.underRoot (s := s) T).captureSet
        (Dom.underRoot (s := s) T').captureSet⟩ →
      Alg ⟨_, Γ.scope, .shp (Dom.underRoot (s := s) T).shape (Dom.underRoot (s := s) T').shape⟩ →
      Alg ⟨s, Γ, .esub (∃ᶜ[C₀] T) (∃ᶜ[C₀'] T')⟩

/-- One step of `Alg`: the goal follows from the premises listed by one
alternative.  The constructors are those of `Alg`, and the premises are listed
in the order the alternative asks them. -/
inductive Rule : G → List G → Prop
  | refl {s : Sig} {Γ : Ctx s} {T : Shape s} : Rule ⟨s, Γ, .shp T T⟩ []
  | top {s : Sig} {Γ : Ctx s} {S : Shape s} : Rule ⟨s, Γ, .shp S .top⟩ []
  | bot {s : Sig} {Γ : Ctx s} {T : Shape s} : Rule ⟨s, Γ, .shp .bot T⟩ []
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Shape s} :
      Rule ⟨s, Γ, .shp S (.and T1 T2)⟩ [⟨s, Γ, .shp S T1⟩, ⟨s, Γ, .shp S T2⟩]
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Shape s} {p : BVar s .var} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot →
      Rule ⟨s, Γ, .shp S (.sel (.var p) A)⟩ [⟨s, Γ, .shp S lo⟩]
  | fld {s : Sig} {Γ : Ctx s} {a : Label} {S S' : Shape s} {C C' : CaptureSet s} :
      Rule ⟨s, Γ, .shp (.fld a (S ^ C)) (.fld a (S' ^ C'))⟩
        [⟨s, Γ, .cap C C'⟩, ⟨s, Γ, .shp S S'⟩]
  | typ {s : Sig} {Γ : Ctx s} {A : Label} {S1 S2 T1 T2 : Shape s} :
      Rule ⟨s, Γ, .shp (.typ A S1 T1) (.typ A S2 T2)⟩ [⟨s, Γ, .shp S2 S1⟩, ⟨s, Γ, .shp T1 T2⟩]
  | cap {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 c1' c2' : CaptureSet s} :
      Rule ⟨s, Γ, .shp (.cap A c1 c2) (.cap A c1' c2')⟩ [⟨s, Γ, .cap c1' c1⟩, ⟨s, Γ, .cap c2 c2'⟩]
  | capkI {s : Sig} {Γ : Ctx s} {A : Label} {c1 c2 : CaptureSet s} {φ : Cls.Kind} :
      Rule ⟨s, Γ, .shp (.cap A c1 c2) (.capk A φ)⟩ [⟨s, Γ, .kind c2 φ⟩]
  | capk {s : Sig} {Γ : Ctx s} {A : Label} {φ1 φ2 : Cls.Kind} :
      φ1.subkindB φ2 = true → Rule ⟨s, Γ, .shp (.capk A φ1) (.capk A φ2)⟩ []
  | box {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} :
      Rule ⟨s, Γ, .shp (.box (S ^ C)) (.box (S' ^ C'))⟩ [⟨s, Γ, .cap C C'⟩, ⟨s, Γ, .shp S S'⟩]
  | all {s : Sig} {Γ : Ctx s} {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Rule ⟨s, Γ, .shp (.all T1 U1) (.all T2 U2)⟩
        [⟨_, Γ.scope, .cap (Dom.underRoot T2).captureSet (Dom.underRoot T1).captureSet⟩,
         ⟨_, Γ.scope, .shp (Dom.underRoot T2).shape (Dom.underRoot T1).shape⟩,
         ⟨_, Γ.body T2, .esub (Cod.underRoot U1) (Cod.underRoot U2)⟩]
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Shape s} {q : BVar s .var} {B : Label} :
      Member Γ q B lo hi → isAnd T = false →
      Rule ⟨s, Γ, .shp (.sel (.var q) B) T⟩ [⟨s, Γ, .shp hi T⟩]
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Shape s} :
      isAnd T = false → Rule ⟨s, Γ, .shp (.and S1 S2) T⟩ [⟨s, Γ, .shp S1 T⟩]
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Shape s} :
      isAnd T = false → Rule ⟨s, Γ, .shp (.and S1 S2) T⟩ [⟨s, Γ, .shp S2 T⟩]
  | cElem {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} :
      CaptureSet.Subset C D → Rule ⟨s, Γ, .cap C D⟩ []
  | cUnion {s : Sig} {Γ : Ctx s} {a b : CapAtom s} {C D : CaptureSet s} :
      Rule ⟨s, Γ, .cap (a :: b :: C) D⟩ [⟨s, Γ, .cap [a] D⟩, ⟨s, Γ, .cap (b :: C) D⟩]
  | cLevel {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {D : CaptureSet s} :
      CaptureSet.Subset [CapAtom.cvar κ] D → Γ.IsRoot (.cvar κ) → Γ.LvlLe a (.cvar κ) →
      Rule ⟨s, Γ, .cap [a] D⟩ []
  | cProjMono {s : Sig} {Γ : Ctx s} {a x : CapAtom s} {C₀ C₀' D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [a] C₀ φ → UnprojAt [x] C₀' φ → CaptureSet.Subset [x] D →
      Rule ⟨s, Γ, .cap [a] D⟩ [⟨s, Γ, .cap C₀ C₀'⟩]
  | cProjL {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C₀ D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [a] C₀ φ → Rule ⟨s, Γ, .cap [a] D⟩ [⟨s, Γ, .cap C₀ D⟩]
  | cSelHi {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 → Rule ⟨s, Γ, .cap [CapAtom.sel y A] D⟩ [⟨s, Γ, .cap c2 D⟩]
  | cProjR {s : Sig} {Γ : Ctx s} {a x : CapAtom s} {X D : CaptureSet s} {φ : Cls.Kind} :
      UnprojAt [x] X φ → CaptureSet.Subset [x] D →
      Rule ⟨s, Γ, .cap [a] D⟩ [⟨s, Γ, .kind [a] φ⟩, ⟨s, Γ, .cap [a] X⟩]
  | cSelLo {s : Sig} {Γ : Ctx s} {a : CapAtom s} {y : BVar s .var} {A : Label}
      {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 → CaptureSet.Subset [CapAtom.sel y A] D →
      Rule ⟨s, Γ, .cap [a] D⟩ [⟨s, Γ, .cap [a] c1⟩]
  | cInst {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {W D : CaptureSet s} :
      CaptureSet.Subset [CapAtom.cvar κ] D → Γ.instSet? κ = some W →
      Rule ⟨s, Γ, .cap [a] D⟩ [⟨s, Γ, .cap [a] W⟩]
  | cVar {s : Sig} {Γ : Ctx s} {x : BVar s .var} {D : CaptureSet s} :
      Rule ⟨s, Γ, .cap [CapAtom.var x] D⟩ [⟨s, Γ, .cap (Γ.lookup x).captureSet D⟩]
  | cProjVar {s : Sig} {Γ : Ctx s} {y : BVar s .var} {φ : Cls.Kind} {D : CaptureSet s} :
      Rule ⟨s, Γ, .cap [CapAtom.proj (.var y) φ] D⟩
        [⟨s, Γ, .cap (CaptureSet.proj (Γ.lookup y).captureSet φ) D⟩]
  | cProjSel {s : Sig} {Γ : Ctx s} {y : BVar s .var} {A : Label} {φ : Cls.Kind}
      {c1 c2 D : CaptureSet s} :
      CapMember Γ y A c1 c2 →
      Rule ⟨s, Γ, .cap [CapAtom.proj (.sel y A) φ] D⟩ [⟨s, Γ, .cap (CaptureSet.proj c2 φ) D⟩]
  | kNil {s : Sig} {Γ : Ctx s} {φ : Cls.Kind} : Rule ⟨s, Γ, .kind [] φ⟩ []
  | kCons {s : Sig} {Γ : Ctx s} {a b : CapAtom s} {C : CaptureSet s} {φ : Cls.Kind} :
      Rule ⟨s, Γ, .kind (a :: b :: C) φ⟩ [⟨s, Γ, .kind [a] φ⟩, ⟨s, Γ, .kind (b :: C) φ⟩]
  | kProj {s : Sig} {Γ : Ctx s} {a : CapAtom s} {φ : Cls.Kind} :
      a.kindOf.subkindB φ = true → Rule ⟨s, Γ, .kind [a] φ⟩ []
  | kCls {s : Sig} {Γ : Ctx s} {a : CapAtom s} {c : Cls.Classifier} {φ : Cls.Kind} :
      Γ.clsOf? a.base = some c → (a.kindOf.containsB c = true → φ.containsB c = true) →
      Rule ⟨s, Γ, .kind [a] φ⟩ []
  | kSel {s : Sig} {Γ : Ctx s} {x : BVar s .var} {A : Label} {ψ φ : Cls.Kind} :
      KindMember Γ x A ψ → ψ = φ ∨ ψ.subkindB φ = true →
      Rule ⟨s, Γ, .kind [CapAtom.sel x A] φ⟩ []
  | kVar {s : Sig} {Γ : Ctx s} {a : CapAtom s} {x : BVar s .var} {φ : Cls.Kind} :
      a.base = CapAtom.var x →
      Rule ⟨s, Γ, .kind [a] φ⟩ [⟨s, Γ, .kind (CaptureSet.proj (Γ.lookup x).captureSet a.kindOf) φ⟩]
  | kInst {s : Sig} {Γ : Ctx s} {a : CapAtom s} {κ : BVar s .cap} {C : CaptureSet s}
      {φ : Cls.Kind} :
      a.base = CapAtom.cvar κ → Γ.instSet? κ = some C →
      Rule ⟨s, Γ, .kind [a] φ⟩ [⟨s, Γ, .kind (CaptureSet.proj C a.kindOf) φ⟩]
  | kSelUp {s : Sig} {Γ : Ctx s} {x : BVar s .var} {A : Label} {c1 c2 : CaptureSet s}
      {φ : Cls.Kind} :
      CapMember Γ x A c1 c2 → Rule ⟨s, Γ, .kind [CapAtom.sel x A] φ⟩ [⟨s, Γ, .kind c2 φ⟩]
  | kProjS {s : Sig} {Γ : Ctx s} {a : CapAtom s} {C₀ : CaptureSet s} {ψ φ : Cls.Kind} :
      UnprojAt [a] C₀ ψ → Rule ⟨s, Γ, .kind [a] φ⟩ [⟨s, Γ, .kind C₀ φ⟩]
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Rule ⟨s, Γ, .var x T T⟩ []
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {C : CaptureSet s} {T1 T2 : Shape s} :
      Rule ⟨s, Γ, .var x V ((Shape.and T1 T2) ^ C)⟩
        [⟨s, Γ, .var x V (T1 ^ C)⟩, ⟨s, Γ, .var x V (T2 ^ C)⟩]
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {C : CaptureSet s} {B : Shape (s,x)} :
      Shape.Decl B →
      Rule ⟨s, Γ, .var x V ((Shape.mu B) ^ C)⟩ [⟨s, Γ, .var x V ((B.substVar x) ^ C)⟩]
  | vSelLo {s : Sig} {Γ : Ctx s} {x p : BVar s .var} {V : Ty s} {C : CaptureSet s}
      {lo hi : Shape s} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot →
      Rule ⟨s, Γ, .var x V ((Shape.sel (.var p) A) ^ C)⟩ [⟨s, Γ, .var x V (lo ^ C)⟩]
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {B : Shape (s,x)} :
      isAnd T.shape = false → Shape.Decl B →
      Rule ⟨s, Γ, .var x ((Shape.mu B) ^ C) T⟩ [⟨s, Γ, .var x ((B.substVar x) ^ C) T⟩]
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {V1 V2 : Shape s} :
      isAnd T.shape = false →
      Rule ⟨s, Γ, .var x ((Shape.and V1 V2) ^ C) T⟩ [⟨s, Γ, .var x (V1 ^ C) T⟩]
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {C : CaptureSet s} {V1 V2 : Shape s} :
      isAnd T.shape = false →
      Rule ⟨s, Γ, .var x ((Shape.and V1 V2) ^ C) T⟩ [⟨s, Γ, .var x (V2 ^ C) T⟩]
  | vSelHi {s : Sig} {Γ : Ctx s} {x q : BVar s .var} {T : Ty s} {C : CaptureSet s}
      {lo hi : Shape s} {B : Label} :
      Member Γ q B lo hi → isAnd T.shape = false →
      Rule ⟨s, Γ, .var x ((Shape.sel (.var q) B) ^ C) T⟩ [⟨s, Γ, .var x (hi ^ C) T⟩]
  | vWiden {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isAnd T.shape = false →
      Rule ⟨s, Γ, .var x V T⟩
        [⟨s, Γ, .cap V.captureSet T.captureSet⟩, ⟨s, Γ, .shp V.shape T.shape⟩]
  | eTy {s : Sig} {Γ : Ctx s} {T T' : Ty s} :
      Rule ⟨s, Γ, .esub (.ty T) (.ty T')⟩
        [⟨s, Γ, .cap T.captureSet T'.captureSet⟩, ⟨s, Γ, .shp T.shape T'.shape⟩]
  | ePack {s : Sig} {Γ : Ctx s} {T' : Ty s} {C₀ W : CaptureSet s} {T : Ty (s,c)} :
      W ∈ [T'.captureSet, C₀] →
      Rule ⟨s, Γ, .esub (.ty T') (∃ᶜ[C₀] T)⟩
        [⟨s, Γ, .cap W C₀⟩,
         ⟨_, Γ.scopeInst W, .cap ((T'.weaken (k := .cap)).weaken (k := .cap)).captureSet
           (Dom.underRoot (s := s) T).captureSet⟩,
         ⟨_, Γ.scopeInst W, .shp ((T'.weaken (k := .cap)).weaken (k := .cap)).shape
           (Dom.underRoot (s := s) T).shape⟩]
  | eExist {s : Sig} {Γ : Ctx s} {C₀ C₀' : CaptureSet s} {T T' : Ty (s,c)} :
      Rule ⟨s, Γ, .esub (∃ᶜ[C₀] T) (∃ᶜ[C₀'] T')⟩
        [⟨s, Γ, .cap C₀ C₀'⟩,
         ⟨_, Γ.scope, .cap (Dom.underRoot (s := s) T).captureSet
           (Dom.underRoot (s := s) T').captureSet⟩,
         ⟨_, Γ.scope, .shp (Dom.underRoot (s := s) T).shape (Dom.underRoot (s := s) T').shape⟩]

section Lists

variable {α : Type} {P : α → Prop}

theorem forall_mem_one {a : α} (h : P a) : ∀ p ∈ [a], P p := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

theorem forall_mem_two {a b : α} (ha : P a) (hb : P b) : ∀ p ∈ [a, b], P p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ha
  · exact hb

theorem forall_mem_three {a b c : α} (ha : P a) (hb : P b) (hc : P c) :
    ∀ p ∈ [a, b, c], P p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem forall_mem_nil : ∀ p ∈ ([] : List α), P p := fun _ h => by cases h

end Lists

/-- An `Alg` derivation is a derivation by `Rule`. -/
theorem Alg.deriv {g : G} (h : Alg g) : Deriv Rule g := by
  induction h with
  | refl => exact .mk .refl forall_mem_nil
  | top => exact .mk .top forall_mem_nil
  | bot => exact .mk .bot forall_mem_nil
  | andR _ _ ih1 ih2 => exact .mk .andR (forall_mem_two ih1 ih2)
  | selLo hm hlo _ ih => exact .mk (.selLo hm hlo) (forall_mem_one ih)
  | fld _ _ ih1 ih2 => exact .mk .fld (forall_mem_two ih1 ih2)
  | typ _ _ ih1 ih2 => exact .mk .typ (forall_mem_two ih1 ih2)
  | cap _ _ ih1 ih2 => exact .mk .cap (forall_mem_two ih1 ih2)
  | capkI _ ih => exact .mk .capkI (forall_mem_one ih)
  | capk hs => exact .mk (.capk hs) forall_mem_nil
  | box _ _ ih1 ih2 => exact .mk .box (forall_mem_two ih1 ih2)
  | all _ _ _ ih1 ih2 ih3 => exact .mk .all (forall_mem_three ih1 ih2 ih3)
  | selHi hm hT _ ih => exact .mk (.selHi hm hT) (forall_mem_one ih)
  | and1 hT _ ih => exact .mk (.and1 hT) (forall_mem_one ih)
  | and2 hT _ ih => exact .mk (.and2 hT) (forall_mem_one ih)
  | cElem h => exact .mk (.cElem h) forall_mem_nil
  | cUnion _ _ ih1 ih2 => exact .mk .cUnion (forall_mem_two ih1 ih2)
  | cLevel hm hr hl => exact .mk (.cLevel hm hr hl) forall_mem_nil
  | cProjMono hu1 hu2 hm _ ih => exact .mk (.cProjMono hu1 hu2 hm) (forall_mem_one ih)
  | cProjL hu _ ih => exact .mk (.cProjL hu) (forall_mem_one ih)
  | cSelHi hm _ ih => exact .mk (.cSelHi hm) (forall_mem_one ih)
  | cProjR hu hm _ _ ih1 ih2 => exact .mk (.cProjR hu hm) (forall_mem_two ih1 ih2)
  | cSelLo hm hsub _ ih => exact .mk (.cSelLo hm hsub) (forall_mem_one ih)
  | cInst hm hi _ ih => exact .mk (.cInst hm hi) (forall_mem_one ih)
  | cVar _ ih => exact .mk .cVar (forall_mem_one ih)
  | cProjVar _ ih => exact .mk .cProjVar (forall_mem_one ih)
  | cProjSel hm _ ih => exact .mk (.cProjSel hm) (forall_mem_one ih)
  | kNil => exact .mk .kNil forall_mem_nil
  | kCons _ _ ih1 ih2 => exact .mk .kCons (forall_mem_two ih1 ih2)
  | kProj h => exact .mk (.kProj h) forall_mem_nil
  | kCls hc h2 => exact .mk (.kCls hc h2) forall_mem_nil
  | kSel hm hk => exact .mk (.kSel hm hk) forall_mem_nil
  | kVar hb _ ih => exact .mk (.kVar hb) (forall_mem_one ih)
  | kInst hb hi _ ih => exact .mk (.kInst hb hi) (forall_mem_one ih)
  | kSelUp hm _ ih => exact .mk (.kSelUp hm) (forall_mem_one ih)
  | kProjS hu _ ih => exact .mk (.kProjS hu) (forall_mem_one ih)
  | vRefl => exact .mk .vRefl forall_mem_nil
  | vAndR _ _ ih1 ih2 => exact .mk .vAndR (forall_mem_two ih1 ih2)
  | vMuR hB _ ih => exact .mk (.vMuR hB) (forall_mem_one ih)
  | vSelLo hm hlo _ ih => exact .mk (.vSelLo hm hlo) (forall_mem_one ih)
  | vMuL hT hB _ ih => exact .mk (.vMuL hT hB) (forall_mem_one ih)
  | vAnd1 hT _ ih => exact .mk (.vAnd1 hT) (forall_mem_one ih)
  | vAnd2 hT _ ih => exact .mk (.vAnd2 hT) (forall_mem_one ih)
  | vSelHi hm hT _ ih => exact .mk (.vSelHi hm hT) (forall_mem_one ih)
  | vWiden hT _ _ ih1 ih2 => exact .mk (.vWiden hT) (forall_mem_two ih1 ih2)
  | eTy _ _ ih1 ih2 => exact .mk .eTy (forall_mem_two ih1 ih2)
  | ePack hW _ _ _ ih1 ih2 ih3 => exact .mk (.ePack hW) (forall_mem_three ih1 ih2 ih3)
  | eExist _ _ _ ih1 ih2 ih3 => exact .mk .eExist (forall_mem_three ih1 ih2 ih3)

/-! ## Each rule's alternative answers

The step at the conclusion of a rule answers whenever the oracle answers the
rule's premises and the tank is unmarked at the end.  The alternatives tried
before the rule's own one either answer or end unmarked, since a marked tank
stays marked. -/

theorem not_isAnd {s : Sig} {T : Shape s} (h : isAnd T = false) : ¬(isAnd T = true) := by
  rw [h]
  exact Bool.false_ne_true

/-- A selection that a set includes is among the selections the set names. -/
theorem mem_selAtoms {s : Sig} {y : BVar s .var} {A : Label} {D : CaptureSet s}
    (h : CaptureSet.Subset [CapAtom.sel y A] D) : (y, A) ∈ selAtoms D := by
  have hm : CapAtom.sel y A ∈ D := h _ (List.mem_singleton.mpr rfl)
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- A capture binder that a set includes is among the binders the set names. -/
theorem mem_capVars {s : Sig} {κ : BVar s .cap} {D : CaptureSet s}
    (h : CaptureSet.Subset [CapAtom.cvar κ] D) : κ ∈ capVars D := by
  have hm : CapAtom.cvar κ ∈ D := h _ (List.mem_singleton.mpr rfl)
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- An atom that a set includes is an atom of the set. -/
theorem mem_of_subset {s : Sig} {x : CapAtom s} {D : CaptureSet s}
    (h : CaptureSet.Subset [x] D) : x ∈ D :=
  h _ (List.mem_singleton.mpr rfl)

/-- Two types compare by their set goal and their shape goal. -/
theorem ans_tySub {s : Sig} {Γ : Ctx s} {r : Rec Γ} {T U : Ty s}
    (h1 : Ans (r (.cap T.captureSet U.captureSet))) (h2 : Ans (r (.shp T.shape U.shape))) :
    Ans (tySub r T U) := by
  cases T
  cases U
  exact ans_bindO h1 fun _ => ans_mapO h2

theorem rule_ans {g : G} {ps : List G} (h : Rule g ps) (o : Oracle G R) (hF : ∀ g', Framed (o g'))
    (hp : ∀ p ∈ ps, Ans (o p)) : Ans (step o g) := by
  cases h with
  | refl =>
    exact ans_orElse_left (ans_ret (by simp [sRefl]))
  | top =>
    exact ans_orElse_right (ans_orElse_left (ans_ret (by simp [sTop])))
  | bot =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_ret (by simp [sBot]))))
  | @andR s Γ S T1 T2 =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_ite_pos rfl ?_)))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @selLo s Γ S lo hi p A hm hlo =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_left ?_))))
    refine typsAt_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @fld s Γ a S S' C C' =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl
      (ans_mapO (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))))
  | @typ s Γ A S1 S2 T1 T2 =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @cap s Γ A c1 c2 c1' c2' =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @capkI s Γ A c1 c2 φ =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_mapO (hp _ (by simp)))
  | @capk s Γ A φ1 φ2 hs =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_dite_pos hs (ans_ret rfl))
  | @box s Γ S S' C C' =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_mapO (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @all s Γ T1 T2 U1 U2 =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_bindO (ans_tySub (hp _ (by simp)) (hp _ (by simp))) fun _ =>
      ans_mapO (hp _ (by simp))
  | @selHi s Γ T lo hi q B hm hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine typsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @and1 s Γ S1 S2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @and2 s Γ S1 S2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | @cElem s Γ C D hsub =>
    exact ans_orElse_left (ans_ret (by simp [cElem, hsub]))
  | @cUnion s Γ a b C D =>
    refine ans_orElse_right (ans_orElse_left ?_)
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @cLevel s Γ a κ D hm hr hl =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_ret ?_)))
    show ((capVars D).findSome? _).isSome = true
    refine List.findSome?_isSome_iff.mpr ⟨κ, mem_capVars hm, ?_⟩
    dsimp only
    rw [dif_pos hr, dif_pos hl, dif_pos hm]
    rfl
  | @cProjMono s Γ a x C₀ C₀' D φ hu1 hu2 hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))
    dsimp only [cProjMono]
    split
    · rename_i p h1 he1
      obtain rfl := hu1.of_eq he1
      refine ans_firstSome ?_ D (mem_of_subset hm)
      dsimp only
      split
      · rename_i q h2 he2
        obtain rfl := hu2.of_eq he2
        exact ans_dite_pos rfl (ans_dite_pos hm (ans_mapO (hp _ (by simp))))
      · rename_i he2
        exact (hu2.not_none he2).elim
    · rename_i he1
      exact (hu1.not_none he1).elim
  | @cProjL s Γ a C₀ D φ hu =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_left ?_))))
    dsimp only [cProjL]
    split
    · rename_i p h1 he1
      obtain rfl := hu.of_eq he1
      exact ans_mapO (hp _ (by simp))
    · rename_i he1
      exact (hu.not_none he1).elim
  | @cSelHi s Γ y A c1 c2 D hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_left ?_)))))
    refine capsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨c1', c2', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @cProjR s Γ a x X D φ hu hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine ans_firstSome ?_ D (mem_of_subset hm)
    dsimp only
    split
    · rename_i p h1 he1
      obtain rfl := hu.of_eq he1
      exact ans_dite_pos hm (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
    · rename_i he1
      exact (hu.not_none he1).elim
  | @cSelLo s Γ a y A c1 c2 D hm hsub =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))))
    refine ans_firstSome ?_ (selAtoms D) (mem_selAtoms hsub)
    refine ans_dite_pos hsub ?_
    refine capsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨c1', c2', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @cInst s Γ a κ W D hm hi =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_left ?_))))))))
    refine ans_firstSome ?_ (capVars D) (mem_capVars hm)
    dsimp only
    split
    · rename_i W' h'
      rw [hi] at h'
      cases h'
      exact ans_dite_pos hm (ans_mapO (hp _ (by simp)))
    · rename_i h'
      rw [hi] at h'
      cases h'
  | @cVar s Γ x D =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_left ?_)))))))))
    exact ans_mapO (hp _ (by simp))
  | @cProjVar s Γ y φ D =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right ?_)))))))))
    exact ans_mapO (hp _ (by simp))
  | @cProjSel s Γ y A φ c1 c2 D hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right ?_)))))))))
    refine capsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨c1', c2', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | kNil =>
    exact ans_orElse_left (ans_ret rfl)
  | @kCons s Γ a b C φ =>
    refine ans_orElse_right (ans_orElse_left ?_)
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @kProj s Γ a φ hk =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_ret ?_)))
    simp [kProj, hk]
  | @kCls s Γ a c φ hc h2 =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_ret ?_))))
    dsimp only [kCls]
    split
    · rename_i c' hc'
      obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
      rw [dif_pos h2]
      rfl
    · rename_i hc'
      cases hc.symm.trans hc'
  | @kSel s Γ x A ψ φ hm hk =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_left ?_))))
    refine capksAt_ans hm (fun _ => firstSome_framed (fun _ => ret_framed _) _) ?_
    rintro ds ⟨⟨ψ', v⟩, hd, rfl⟩
    refine ans_firstSome ?_ ds hd
    refine ans_ret ?_
    unfold kselOf
    split
    · rfl
    · rename_i hne
      rw [dif_pos (hk.resolve_left hne)]
      rfl
  | @kVar s Γ a x φ hb =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_left ?_)))))
    dsimp only [kVar]
    split
    · rename_i x' hb'
      obtain rfl : x = x' := CapAtom.var.inj (hb.symm.trans hb')
      exact ans_mapO (hp _ (by simp))
    · rename_i κ hb'
      cases hb.symm.trans hb'
    · rename_i hv _
      exact (hv x hb).elim
  | @kInst s Γ a κ C φ hb hi =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_left ?_)))))
    dsimp only [kVar]
    split
    · rename_i x' hb'
      cases hb.symm.trans hb'
    · rename_i κ' hb'
      obtain rfl : κ = κ' := CapAtom.cvar.inj (hb.symm.trans hb')
      split
      · rename_i C' hi'
        obtain rfl : C = C' := Option.some.inj (hi.symm.trans hi')
        exact ans_mapO (hp _ (by simp))
      · rename_i hi'
        cases hi.symm.trans hi'
    · rename_i _ hc
      exact (hc κ hb).elim
  | @kSelUp s Γ x A c1 c2 φ hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine capsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨c1', c2', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @kProjS s Γ a C₀ ψ φ hu =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    dsimp only [kProjS]
    split
    · rename_i p h1 he1
      obtain rfl := hu.of_eq he1
      exact ans_mapO (hp _ (by simp))
    · rename_i he1
      exact (hu.not_none he1).elim
  | vRefl =>
    exact ans_orElse_left (ans_ret (by simp [vRefl]))
  | @vAndR s Γ x V C T1 T2 =>
    refine ans_orElse_right (ans_ite_pos rfl ?_)
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @vMuR s Γ x V C B hB =>
    refine ans_orElse_right (ans_ite_neg (by simp [isAnd]) (ans_orElse_left ?_))
    exact ans_dite_pos hB (ans_mapO (hp _ (by simp)))
  | @vSelLo s Γ x p V C lo hi A hm hlo =>
    refine ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_left ?_)))
    refine typsAt_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @vMuL s Γ x T C B hT hB =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))
    exact ans_dite_pos hB (ans_mapO (hp _ (by simp)))
  | @vAnd1 s Γ x T C V1 V2 hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @vAnd2 s Γ x T C V1 V2 hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | @vSelHi s Γ x q T C lo hi B hm hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine typsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @vWiden s Γ x V T hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_mapO (ans_tySub (hp _ (by simp)) (hp _ (by simp)))
  | @eTy s Γ T T' =>
    refine ans_orElse_left ?_
    exact ans_mapO (ans_tySub (hp _ (by simp)) (hp _ (by simp)))
  | @ePack s Γ T' C₀ W T hW =>
    refine ans_orElse_right (ans_orElse_left ?_)
    refine ans_firstSome ?_ _ hW
    exact ans_bindO (hp _ (by simp)) fun _ =>
      ans_mapO (ans_tySub (hp _ (by simp)) (hp _ (by simp)))
  | @eExist s Γ C₀ C₀' T T' =>
    refine ans_orElse_right (ans_orElse_right ?_)
    exact ans_bindO (hp _ (by simp)) fun _ =>
      ans_mapO (ans_tySub (hp _ (by simp)) (hp _ (by simp)))

/-! ## Completeness up to the recursion limit -/

/-- An `Alg` derivation is answered by the run, at every index and from every
tank on which the run ends unmarked. -/
theorem alg_run {g : G} (h : Alg g) (d : Nat) : Ans (run cost step d [] g) :=
  run_ans step_frame (fun _ _ hr o hF hp => rule_ans hr o hF hp) h.deriv.pruneNil d

theorem shpF_complete {s : Sig} {Γ : Ctx s} {S T : Shape s} (h : Alg ⟨s, Γ, .shp S T⟩) :
    Ans (shpF Γ S T) :=
  fun t ho => alg_run h t.left t ho

theorem capF_complete {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (h : Alg ⟨s, Γ, .cap C D⟩) :
    Ans (capF Γ C D) :=
  fun t ho => alg_run h t.left t ho

theorem kindF_complete {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (h : Alg ⟨s, Γ, .kind C φ⟩) : Ans (kindF Γ C φ) :=
  fun t ho => alg_run h t.left t ho

theorem varTyF_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s}
    (h : Alg ⟨s, Γ, .var x V T⟩) : Ans (varTyF Γ x V T) :=
  fun t ho => alg_run h t.left t ho

theorem esubF_complete {s : Sig} {Γ : Ctx s} {E F : ETy s} (h : Alg ⟨s, Γ, .esub E F⟩) :
    Ans (esubF Γ E F) :=
  fun t ho => alg_run h t.left t ho

/-- Two types: the set goal, then the shape goal, each answered by its own
derivation. -/
theorem subF_complete {s : Sig} {Γ : Ctx s} {T U : Ty s}
    (h1 : Alg ⟨s, Γ, .shp T.shape U.shape⟩) (h2 : Alg ⟨s, Γ, .cap T.captureSet U.captureSet⟩) :
    Ans (subF Γ T U) := by
  cases T
  cases U
  exact ans_bindO (capF_complete h2) fun _ => ans_mapO (shpF_complete h1)

/-- A variable at a view: the `var` goal from the view. -/
theorem varFrom_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {U : CaptureSet s} {V : Ty s}
    {d : HasTy U Γ (.path (.var x)) (.ty V)} {T : Ty s} (h : Alg ⟨s, Γ, .var x V T⟩) :
    Ans (varFrom Γ x U V d T) :=
  ans_mapO (varTyF_complete h)

theorem varF_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Alg ⟨s, Γ, .var x (varView Γ x).ty T⟩) : Ans (varF Γ x T) :=
  varFrom_complete h

theorem shp?_complete {s : Sig} {Γ : Ctx s} {S T : Shape s} {n : Nat}
    (h : Alg ⟨s, Γ, .shp S T⟩) (ho : (shp? Γ S T n).2.out = false) :
    (shp? Γ S T n).1.isSome = true :=
  shpF_complete h _ ho

theorem cap?_complete {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {n : Nat}
    (h : Alg ⟨s, Γ, .cap C D⟩) (ho : (cap? Γ C D n).2.out = false) :
    (cap? Γ C D n).1.isSome = true :=
  capF_complete h _ ho

theorem kind?_complete {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} {n : Nat}
    (h : Alg ⟨s, Γ, .kind C φ⟩) (ho : (kind? Γ C φ n).2.out = false) :
    (kind? Γ C φ n).1.isSome = true :=
  kindF_complete h _ ho

theorem esub?_complete {s : Sig} {Γ : Ctx s} {E F : ETy s} {n : Nat}
    (h : Alg ⟨s, Γ, .esub E F⟩) (ho : (esub? Γ E F n).2.out = false) :
    (esub? Γ E F n).1.isSome = true :=
  esubF_complete h _ ho

theorem sub?_complete {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} {n : Nat}
    (h1 : Alg ⟨s, Γ, .shp S S'⟩) (h2 : Alg ⟨s, Γ, .cap C C'⟩)
    (ho : (sub? Γ (S ^ C) (S' ^ C') n).2.out = false) :
    (sub? Γ (S ^ C) (S' ^ C') n).1.isSome = true :=
  subF_complete (T := S ^ C) (U := S' ^ C') h1 h2 _ ho

/-- A variable starts from its first view, `varView`: its declared type at
`{}` for a variable declared at `{}`, its declared shape at `{x}` for any
other. -/
theorem var?_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n : Nat}
    (h : Alg ⟨s, Γ, .var x (varView Γ x).ty T⟩) (ho : (var? Γ x T n).2.out = false) :
    (var? Γ x T n).1.isSome = true :=
  varF_complete h _ ho

/-- From the first fuel at which the run ends unmarked, an `Alg` derivation is
answered at every larger fuel. -/
theorem shp?_complete_from {s : Sig} {Γ : Ctx s} {S T : Shape s} {n m : Nat}
    (h : Alg ⟨s, Γ, .shp S T⟩) (ho : (shp? Γ S T n).2.out = false) (hnm : n ≤ m) :
    (shp? Γ S T m).1.isSome = true := by
  have hs := shp?_complete h ho
  cases he : (shp? Γ S T n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [shp?_mono he hnm]; rfl

/-- The same for kinding. -/
theorem kind?_complete_from {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} {n m : Nat}
    (h : Alg ⟨s, Γ, .kind C φ⟩) (ho : (kind? Γ C φ n).2.out = false) (hnm : n ≤ m) :
    (kind? Γ C φ m).1.isSome = true := by
  have hs := kind?_complete h ho
  cases he : (kind? Γ C φ n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [kind?_mono he hnm]; rfl

/-- The same for answers. -/
theorem esub?_complete_from {s : Sig} {Γ : Ctx s} {E F : ETy s} {n m : Nat}
    (h : Alg ⟨s, Γ, .esub E F⟩) (ho : (esub? Γ E F n).2.out = false) (hnm : n ≤ m) :
    (esub? Γ E F m).1.isSome = true := by
  have hs := esub?_complete h ho
  cases he : (esub? Γ E F n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [esub?_mono he hnm]; rfl

/-! ## Rejections

A run that ends unmarked with no answer rejects by the rules: no `Alg`
derivation exists, at any fuel.  Two types are two runs, so their rejection
says that the two halves do not both hold. -/

theorem shp?_reject {s : Sig} {Γ : Ctx s} {S T : Shape s} {n k : Nat}
    (h : shp? Γ S T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .shp S T⟩ := fun ha => by
  have := shp?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem cap?_reject {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} {n k : Nat}
    (h : cap? Γ C D n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .cap C D⟩ := fun ha => by
  have := cap?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem kind?_reject {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind} {n k : Nat}
    (h : kind? Γ C φ n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .kind C φ⟩ := fun ha => by
  have := kind?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem esub?_reject {s : Sig} {Γ : Ctx s} {E F : ETy s} {n k : Nat}
    (h : esub? Γ E F n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .esub E F⟩ := fun ha => by
  have := esub?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem sub?_reject {s : Sig} {Γ : Ctx s} {S S' : Shape s} {C C' : CaptureSet s} {n k : Nat}
    (h : sub? Γ (S ^ C) (S' ^ C') n = (none, ⟨k, false⟩)) :
    ¬ (Alg ⟨s, Γ, .shp S S'⟩ ∧ Alg ⟨s, Γ, .cap C C'⟩) := fun ⟨h1, h2⟩ => by
  have := sub?_complete h1 h2 (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem var?_reject {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n k : Nat}
    (h : var? Γ x T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .var x (varView Γ x).ty T⟩ :=
  fun ha => by
  have := var?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

/-! ## Soundness -/

/-- A type member premise gives the typing of the variable at the member. -/
theorem Member.var {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Shape s}
    (h : Member Γ p A lo hi) : Nonempty (Var Γ p [.var p] [.var p] (.typ A lo hi)) := by
  obtain ⟨_, _, ⟨lo', hi', v⟩, _, rfl, rfl⟩ := h
  exact ⟨v⟩

/-- A capture member premise gives the typing of the variable at the member. -/
theorem CapMember.var {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {c1 c2 : CaptureSet s}
    (h : CapMember Γ p A c1 c2) : Nonempty (Var Γ p [.var p] [.var p] (.cap A c1 c2)) := by
  obtain ⟨_, _, ⟨c1', c2', v⟩, _, rfl, rfl⟩ := h
  exact ⟨v⟩

/-- A kind member premise gives the typing of the variable at the member. -/
theorem KindMember.var {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {ψ : Cls.Kind}
    (h : KindMember Γ p A ψ) : Nonempty (Var Γ p [.var p] [.var p] (.capk A ψ)) := by
  obtain ⟨_, _, ⟨ψ', v⟩, _, rfl⟩ := h
  exact ⟨v⟩

/-- Two types by `Sub.capt`, from a shape derivation and a set derivation on
their parts. -/
def subOf {s : Sig} {Γ : Ctx s} : {T U : Ty s} → SubShape Γ T.shape U.shape →
    Subcap Γ T.captureSet U.captureSet → Sub Γ T U
  | .capt _ _, .capt _ _, e1, e2 => Sub.capt e1 e2

/-- Every goal `Alg` derives has an answer: a `SubShape`, `Subcap`, `CapKind`
or `ESub` derivation, or a map from the variable at one type to the variable
at another.  Each case builds what its alternative emits. -/
theorem Alg.sound {g : G} (h : Alg g) : Nonempty (R g) := by
  induction h with
  | refl => exact ⟨SubShape.refl⟩
  | top => exact ⟨SubShape.top⟩
  | bot => exact ⟨SubShape.bot⟩
  | andR _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨SubShape.and e1 e2⟩
  | selLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨SubShape.trans e (SubShape.selLower v)⟩
  | fld _ _ ih1 ih2 =>
    obtain ⟨e2⟩ := ih1
    obtain ⟨e1⟩ := ih2
    exact ⟨SubShape.fld (Sub.capt e1 e2)⟩
  | typ _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨SubShape.typ e1 e2⟩
  | cap _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨SubShape.cap e1 e2⟩
  | capkI _ ih =>
    obtain ⟨g⟩ := ih
    exact ⟨SubShape.capkI g⟩
  | capk hs => exact ⟨SubShape.capk hs⟩
  | box _ _ ih1 ih2 =>
    obtain ⟨e2⟩ := ih1
    obtain ⟨e1⟩ := ih2
    exact ⟨SubShape.box (Sub.capt e1 e2)⟩
  | all _ _ _ ih1 ih2 ih3 =>
    obtain ⟨e2⟩ := ih1
    obtain ⟨e1⟩ := ih2
    obtain ⟨e3⟩ := ih3
    exact ⟨SubShape.all (subOf e1 e2) e3⟩
  | selHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨SubShape.trans (SubShape.selUpper v) e⟩
  | and1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨SubShape.trans SubShape.and1 e⟩
  | and2 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨SubShape.trans SubShape.and2 e⟩
  | cElem h => exact ⟨Subcap.elem h⟩
  | @cUnion s Γ a b C D _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Subcap.union (C1 := [a]) (C2 := b :: C) e1 e2⟩
  | cLevel hm hr hl => exact ⟨Subcap.trans (Subcap.level hr hl) (Subcap.elem hm)⟩
  | cProjMono hu1 hu2 hm _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans (projMonoTo hu1.eq hu2.eq rfl e) (Subcap.elem hm)⟩
  | cProjL hu _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨unprojTo hu.eq e⟩
  | cSelHi hm _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans (Subcap.selUpper v) e⟩
  | cProjR hu hm _ _ ih1 ih2 =>
    obtain ⟨g⟩ := ih1
    obtain ⟨e⟩ := ih2
    exact ⟨Subcap.trans (projThrough hu.eq g e) (Subcap.elem hm)⟩
  | cSelLo hm hsub _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans e (Subcap.trans (Subcap.selLower v) (Subcap.elem hsub))⟩
  | cInst hm hi _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans e (Subcap.trans (Subcap.inst hi) (Subcap.elem hm))⟩
  | cVar _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans Subcap.var e⟩
  | @cProjVar s Γ y φ D _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans (Subcap.projMono (C := [.var y]) (ψ := φ) Subcap.var) e⟩
  | @cProjSel s Γ y A φ c1 c2 D hm _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨Subcap.trans (Subcap.projMono (C := [.sel y A]) (ψ := φ) (Subcap.selUpper v)) e⟩
  | kNil => exact ⟨CapKind.nil⟩
  | kCons _ _ ih1 ih2 =>
    obtain ⟨g⟩ := ih1
    obtain ⟨g'⟩ := ih2
    exact ⟨CapKind.cons g g'⟩
  | kProj hk => exact ⟨CapKind.kproj hk⟩
  | kCls hc h2 => exact ⟨CapKind.kcls hc h2⟩
  | kSel hm hk =>
    obtain ⟨v⟩ := hm.var
    rcases hk with rfl | hs
    · exact ⟨CapKind.ksel v⟩
    · exact ⟨CapKind.ksub (CapKind.ksel v) hs⟩
  | kVar hb _ ih =>
    obtain ⟨g⟩ := ih
    exact ⟨CapKind.kvar hb g⟩
  | kInst hb hi _ ih =>
    obtain ⟨g⟩ := ih
    exact ⟨CapKind.kcvar hb hi g⟩
  | kSelUp hm _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨g⟩ := ih
    exact ⟨CapKind.kle (Subcap.selUpper v) g⟩
  | kProjS hu _ ih =>
    obtain ⟨g⟩ := ih
    exact ⟨kprojSTo hu.eq g⟩
  | vRefl => exact ⟨fun _ d => d⟩
  | vAndR _ _ ih1 ih2 =>
    obtain ⟨f1⟩ := ih1
    obtain ⟨f2⟩ := ih2
    exact ⟨fun U d => HasTy.andI (f1 U d) (f2 U d)⟩
  | vMuR hB _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun U d => HasTy.recI (f U d) hB⟩
  | vSelLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨f⟩ := ih
    exact ⟨fun U e =>
      HasTy.sub (f U e) (ESub.ty (Sub.capt (SubShape.selLower v) Subcap.refl)) Subcap.refl⟩
  | vMuL _ hB _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun U d => f U (HasTy.recE d hB)⟩
  | vAnd1 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun U d => f U (HasTy.sub d (ESub.ty (Sub.capt SubShape.and1 Subcap.refl)) Subcap.refl)⟩
  | vAnd2 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun U d => f U (HasTy.sub d (ESub.ty (Sub.capt SubShape.and2 Subcap.refl)) Subcap.refl)⟩
  | vSelHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨f⟩ := ih
    exact ⟨fun U e =>
      f U (HasTy.sub e (ESub.ty (Sub.capt (SubShape.selUpper v) Subcap.refl)) Subcap.refl)⟩
  | vWiden _ _ _ ih1 ih2 =>
    obtain ⟨e2⟩ := ih1
    obtain ⟨e1⟩ := ih2
    exact ⟨fun _ d => HasTy.sub d (ESub.ty (subOf e1 e2)) Subcap.refl⟩
  | eTy _ _ ih1 ih2 =>
    obtain ⟨e2⟩ := ih1
    obtain ⟨e1⟩ := ih2
    exact ⟨ESub.ty (subOf e1 e2)⟩
  | ePack _ _ _ _ ih1 ih2 ih3 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e3⟩ := ih2
    obtain ⟨e2⟩ := ih3
    exact ⟨ESub.pack e1 (subOf e2 e3)⟩
  | eExist _ _ _ ih1 ih2 ih3 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e3⟩ := ih2
    obtain ⟨e2⟩ := ih3
    exact ⟨ESub.exist e1 (subOf e2 e3)⟩

theorem Alg.sound_shp {s : Sig} {Γ : Ctx s} {S T : Shape s} (h : Alg ⟨s, Γ, .shp S T⟩) :
    Nonempty (SubShape Γ S T) :=
  h.sound

theorem Alg.sound_cap {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (h : Alg ⟨s, Γ, .cap C D⟩) :
    Nonempty (Subcap Γ C D) :=
  h.sound

theorem Alg.sound_kind {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {φ : Cls.Kind}
    (h : Alg ⟨s, Γ, .kind C φ⟩) : Nonempty (CapKind Γ C φ) :=
  h.sound

theorem Alg.sound_esub {s : Sig} {Γ : Ctx s} {E F : ETy s} (h : Alg ⟨s, Γ, .esub E F⟩) :
    Nonempty (ESub Γ E F) :=
  h.sound

theorem Alg.sound_var {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s}
    (h : Alg ⟨s, Γ, .var x V T⟩) : Nonempty (VarTy Γ x V T) :=
  h.sound

/-! ## Checks -/

section AlgChecks

open Classifiers.DotMNF.Examples

-- E8: `x.A <: {a : ⊤}` by the upper bound of `x`'s one member, read off the lookup.
theorem E8_alg : Alg ⟨_, E8Ctx2, .shp (.sel (.var (up .here)) lA) (.fld la (.top ^ []))⟩ :=
  Alg.selHi (Member.of_mem (lo := .bot) 8 (by decide +kernel) (by decide +kernel)) rfl Alg.refl

-- S1: `{fs} <: {cp.C}` through the lower bound of `cp`'s capture member, read off the lookup.
theorem S1_alg : Alg ⟨_, S1Ctx2, .cap [CapAtom.cvar fs2] [CapAtom.sel .here lC]⟩ :=
  Alg.cSelLo (c1 := [CapAtom.cvar fs2]) (c2 := [CapAtom.cvar fs2])
    (CapMember.of_mem 8 (by decide +kernel) (by decide +kernel)) (fun _ h => h)
    (Alg.cElem fun _ h => h)

-- W5: `f` below the root of its own scope, by its level.
theorem W5_alg : Alg ⟨_, W5Ctx, .cap [CapAtom.var W5f] [CapAtom.cvar W5kb]⟩ :=
  Alg.cLevel (κ := W5kb) (fun _ h => h) (by decide +kernel) (by decide +kernel)

-- CE4: the closure's set `{x.C}` at `only[Control]`, by the kind bound of `x`'s
-- capture member, read off the lookup.
theorem CE4_kind_alg : Alg ⟨_, E3ClientCtx, .kind E3ClosureSet (Cls.only Cls.Control)⟩ :=
  Alg.kSel (ψ := Cls.only Cls.Control) (KindMember.of_mem 16 (by decide +kernel)
    (by decide +kernel)) (Or.inl rfl)

-- CE4's call: `{g} <: {g ↾ only[Control]}` through the projected atom on the
-- right.  Its kinding premise goes to `g`'s declared set, `{x.C}` under the
-- restriction `⊤`, then to the kind bound above.
theorem CE4_call_alg : Alg ⟨_, E3ClientCtx, .cap [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.only Cls.Control))⟩ :=
  Alg.cProjR (x := CapAtom.proj (.var .here) (Cls.only Cls.Control)) (X := [CapAtom.var .here])
    (by decide +kernel) (fun _ h => h)
    (Alg.kVar (x := .here) rfl (Alg.kProjS (C₀ := E3ClosureSet) (ψ := Cls.Kind.top)
      (by decide +kernel) CE4_kind_alg))
    (Alg.cElem fun _ h => h)

-- R2: a capture member bounded by sets, kinded through its upper bound, whose
-- two binders declare `Control`.
theorem R2_alg : Alg ⟨_, C2CtxG E3PlatCtx E3k1 E3k2, .kind [CapAtom.sel (.there (up .here)) lC]
    (Cls.only Cls.Control)⟩ :=
  Alg.kSelUp (c1 := [])
    (c2 := [CapAtom.cvar (.there (up (up E3k1))), CapAtom.cvar (.there (up (up E3k2)))])
    (CapMember.of_mem 16 (by decide +kernel) (by decide +kernel))
    (Alg.kCons (Alg.kCls (c := Cls.Control) (by decide +kernel) (by decide +kernel))
      (Alg.kCls (c := Cls.Control) (by decide +kernel) (by decide +kernel)))

-- W: `{f ↾ only[Control]}` below `f`'s declared set restricted to `only[Control]`.
theorem W_alg : Alg ⟨_, WCtx1, .cap WL WR⟩ := Alg.cProjVar (Alg.cElem fun _ h => h)

/-- The empty set is below itself. -/
theorem alg_nil {s : Sig} {Γ : Ctx s} : Alg ⟨s, Γ, .cap [] []⟩ := Alg.cElem fun _ h => h

-- E1, E3 and E4 as written.  The run ends unmarked with no answer.  For two
-- types the set goal `{} <: {}` holds, so the shape goal has no `Alg`
-- derivation.  The variables are declared at `{}`, so their view is their
-- declared type, and the `var` goal is the whole verdict.
theorem E1_shp_not_alg : ¬ Alg ⟨_, E1Ctx, .shp E1DomS E1ResS⟩ := fun h =>
  sub?_reject (S := E1DomS) (S' := E1ResS) (C := []) (C' := [])
    (rejects_eq (by decide +kernel : rejects (sub? E1Ctx E1Dom E1Res) 2 = true)) ⟨h, alg_nil⟩

theorem E1_var_not_alg : ¬ Alg ⟨_, E1Ctx, .var .here E1Dom E1Res⟩ := by
  have hr := var?_reject
    (rejects_eq (by decide +kernel : rejects (var? E1Ctx .here E1Res) 5 = true))
  have hv : (varView E1Ctx .here).ty = E1Dom := by decide +kernel
  rw [hv] at hr
  exact hr

theorem E3_shp_not_alg : ¬ Alg ⟨_, E3Ctx2, .shp E3T2S E3T1S⟩ :=
  shp?_reject (rejects_eq (by decide +kernel : rejects (shp? E3Ctx2 E3T2S E3T1S) 1 = true))

theorem E4_shp_not_alg :
    ¬ Alg ⟨_, E4Ctx4, .shp E4IntS (.sel (.var (.there (up .here))) lA)⟩ := fun h =>
  sub?_reject (C := []) (C' := [])
    (rejects_eq (by decide +kernel :
      rejects (sub? E4Ctx4 E4Int ((Shape.sel (.var (.there (up .here))) lA) ^ [])) 3 = true))
    ⟨h, alg_nil⟩

theorem E4_var_not_alg :
    ¬ Alg ⟨_, E4Ctx4,
      .var (.there .here) E4Int ((Shape.sel (.var (.there (up .here))) lA) ^ [])⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? E4Ctx4 (.there .here) ((Shape.sel (.var (.there (up .here))) lA) ^ [])) 7
      = true))
  have hv : (varView E4Ctx4 (.there .here)).ty = E4Int := by decide +kernel
  rw [hv] at hr
  exact hr

-- C2: the upper bound of the capture member is `{κ₁, κ₂}`, so `{g}` is not
-- below `{κ₁}`.
theorem C2_cap_not_alg : ¬ Alg ⟨_, C2CtxG platCtx k1 k2, .cap [CapAtom.var .here]
    [CapAtom.cvar (.there (up (up k1)))]⟩ :=
  cap?_reject (rejects_eq (by decide +kernel : rejects (cap? (C2CtxG platCtx k1 k2)
    [CapAtom.var .here] [CapAtom.cvar (.there (up (up k1)))]) 23 = true))

-- CE5: the thread-local argument is not below its own set restricted to
-- `except[ThreadLocal]`.
theorem CE5_cap_not_alg : ¬ Alg ⟨_, E2TlCtx, .cap [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))⟩ :=
  cap?_reject (rejects_eq (by decide +kernel : rejects (cap? E2TlCtx [CapAtom.var .here]
    (CaptureSet.proj [CapAtom.var .here] (Cls.except Cls.ThreadLocal))) 15 = true))

-- CE4 at the unrelated classifier `IO`: the closure's set is not of that kind.
theorem CE4_io_kind_not_alg :
    ¬ Alg ⟨_, E3ClientCtx, .kind E3ClosureSet (Cls.only Cls.IO)⟩ :=
  kind?_reject (rejects_eq (by decide +kernel :
    rejects (kind? E3ClientCtx E3ClosureSet (Cls.only Cls.IO)) 19 = true))

-- A capture member bounded by itself has no kind.
theorem Cyc_kind_not_alg : ¬ Alg ⟨_, CycCtx, .kind [CapAtom.sel .here lC] ctlK⟩ :=
  kind?_reject (rejects_eq (by decide +kernel :
    rejects (kind? CycCtx [CapAtom.sel .here lC] ctlK) 9 = true))

-- W: `io` is not of kind `only[Control]`.
theorem W_io_kind_not_alg : ¬ Alg ⟨_, WCtx1, .kind [CapAtom.cvar (.there E1io)] ctlK⟩ :=
  kind?_reject (rejects_eq (by decide +kernel :
    rejects (kind? WCtx1 [CapAtom.cvar (.there E1io)] ctlK) 1 = true))

/-- `p.A ∧ ⊥`, in the context of the loop `LPCtx`. -/
def LPLeft : Shape ([],x,x,x) := .and (.sel (.var (.there (.there .here))) lA) .bot

/-- `∀(y : ⊤) q.B`, in the context of the loop `LPCtx`. -/
def LPRight : Shape ([],x,x,x) :=
  .all (.top ^ []) (.ty ((Shape.sel (.var (.there (.there (.there .here)))) lB) ^ []))

-- `Alg` derives `p.A ∧ ⊥ <: ∀(y : ⊤) q.B` by the right operand.
theorem LP_alg : Alg ⟨_, LPCtx, .shp LPLeft LPRight⟩ := Alg.and2 rfl Alg.bot

-- The left operand, tried first, descends under a new binder at each level and
-- exhausts the tank, so the run hits the recursion limit.
example : (shp? LPCtx LPLeft LPRight).2.out = true := by decide +kernel

end AlgChecks

end ClassifiersFrontend.Core
