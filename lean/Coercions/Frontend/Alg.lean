import Coercions.Frontend.Sub

/-!
# The algorithmic judgment and completeness

`Alg` states the rules of the algorithm of `Sub.lean`, one constructor per
alternative, with no fuel and no pending goals.  A constructor tried after an
intersection on the right carries `isAnd T = false`, since that alternative
is final.  A selection on the right through a lower bound carries `lo ≠ ⊥`,
as the algorithm skips such a member.  A member premise is phrased through
the lookup (`Member`): the lookup finds that member and ends within its fuel.

Completeness holds up to the recursion limit.  If `Alg` derives a goal, the
algorithm answers it at every fuel at which its run ends with the tank
unmarked (`sub?_complete`, `var?_complete`).  So a run that ends unmarked with
no answer is a rejection by the rules (`sub?_reject`, `var?_reject`).  The
tank is shared by all the alternatives of a goal, and a marked tank stays
marked.  So an alternative that never ends, tried before the one an `Alg`
derivation uses, exhausts every tank.  `p.A ∧ ⊥ <: ∀(y : ⊤) q.B` below is such
a goal: `Alg` derives it by the right operand, and the left operand, tried
first, descends under a new binder at each level.  So completeness cannot say
that some fuel suffices.

The proof needs no minimal derivation.  A derivation in which no goal repeats
along a branch exists whenever a derivation does (`Deriv.pruneNil`): a repeat
is cut out by using the inner derivation of the goal at the outer place.  A
derivation without repeats is never cut by the run.  At each goal the run
either answers by an earlier alternative or reaches the one the derivation
uses, since the tank is unmarked at the end and so at every point before
(`run_ans`).  Both facts are generic in the goals and the step.

`Alg.sound` is the soundness of `Alg` for DOT-MNF.  Each constructor builds
the derivation its alternative emits.
-/

namespace Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Defs Ctx Sub HasTy)

/-! ## Derivations without a repeated goal

`Deriv Rule g` is a derivation of `g` by one-step rules: `Rule g ps` says that
`g` follows from the premises `ps`.  `DerivP Rule P g` is a derivation whose
goals never repeat one of `P` or one below them on the branch.  So the run with
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

/-- `p` has the member `A : lo..hi`: the lookup of `p`'s members at `A` finds
it, from some full tank, and ends with the tank unmarked. -/
def Member {s : Sig} (Γ : Ctx s) (p : BVar s .var) (A : Label) (lo hi : Ty s) : Prop :=
  ∃ n, (decls Γ n p A ⟨n, false⟩).2.out = false ∧
    ∃ d ∈ (decls Γ n p A ⟨n, false⟩).1, d.1 = lo ∧ d.2.1 = hi

/-- A member premise read off one lookup.  Both hypotheses are decidable, so
the kernel checks them on an example. -/
theorem Member.of_mem {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Ty s} (n : Nat)
    (ho : (decls Γ n p A ⟨n, false⟩).2.out = false)
    (h : (lo, hi) ∈ (decls Γ n p A ⟨n, false⟩).1.map fun d => (d.1, d.2.1)) :
    Member Γ p A lo hi := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, d, hd, (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩

/-- Two lookups that end unmarked find the same members. -/
theorem decls_same {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {n : Nat} {t : Tank}
    (h1 : (decls Γ n p A ⟨n, false⟩).2.out = false) (h2 : (decls Γ t.left p A t).2.out = false) :
    (decls Γ t.left p A t).1 = (decls Γ n p A ⟨n, false⟩).1 := by
  have ht : t.out = false := (decls_framed Γ t.left p A).start rfl h2
  let u : Tank := ⟨n + t.left, false⟩
  have hu1 : u = (⟨n, false⟩ : Tank).add t.left := rfl
  have hu2 : u = t.add n := by
    obtain ⟨l, o⟩ := t
    simp only at ht
    subst ht
    simp only [u, Tank.add, Tank.mk.injEq, and_true]
    omega
  have e1 := decls_frame (Prod.ext rfl rfl) h1 t.left
  have e2 := decls_frame (Prod.ext rfl rfl) h2 n
  rw [← hu1] at e1
  rw [← hu2] at e2
  have i1 := decls_index (d' := n + t.left) (by rw [e1]; exact h1) (Nat.le_add_right _ _)
  have i2 := decls_index (d' := n + t.left) (by rw [e2]; exact h2) (Nat.le_add_left _ _)
  have := i1.symm.trans i2
  rw [e1, e2] at this
  exact (Prod.mk.inj this).1.symm

/-- A lookup of a member, then a computation on the members found, answers
when the computation does on every list that holds the member. -/
theorem declsAt_ans {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Ty s} {β : Type}
    {k : List (TyMem Γ p A) → Fu (Option β)} (hm : Member Γ p A lo hi) (hk : ∀ ds, Framed (k ds))
    (hans : ∀ ds, (∃ d ∈ ds, d.1 = lo ∧ d.2.1 = hi) → Ans (k ds)) :
    Ans (Fu.bind (declsAt Γ p A) k) := by
  obtain ⟨n, hn, hmem⟩ := hm
  intro t ho
  have hd : Fu.bind (declsAt Γ p A) k t = k (declsAt Γ p A t).1 (declsAt Γ p A t).2 := rfl
  rw [hd] at ho ⊢
  have ht1 : (declsAt Γ p A t).2.out = false := (hk _).start rfl ho
  have hds : (declsAt Γ p A t).1 = (decls Γ n p A ⟨n, false⟩).1 := decls_same hn ht1
  revert ho
  rw [hds]
  exact hans _ hmem _

/-! ## The judgment -/

/-- The algorithm's rules, one constructor per alternative of `subStep` and
`varStep`, with no fuel and no pending goals. -/
inductive Alg : G → Prop
  | refl {s : Sig} {Γ : Ctx s} {T : Ty s} : Alg ⟨s, Γ, .sub T T⟩
  | top {s : Sig} {Γ : Ctx s} {S : Ty s} : Alg ⟨s, Γ, .sub S .top⟩
  | bot {s : Sig} {Γ : Ctx s} {T : Ty s} : Alg ⟨s, Γ, .sub .bot T⟩
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Ty s} :
      Alg ⟨s, Γ, .sub S T1⟩ → Alg ⟨s, Γ, .sub S T2⟩ → Alg ⟨s, Γ, .sub S (.and T1 T2)⟩
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Ty s} {p : BVar s .var} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .sub S lo⟩ →
      Alg ⟨s, Γ, .sub S (.sel (.var p) A)⟩
  | fld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Alg ⟨s, Γ, .sub S T⟩ → Alg ⟨s, Γ, .sub (.fld a S) (.fld a T)⟩
  | typ {s : Sig} {Γ : Ctx s} {S1 S2 T1 T2 : Ty s} {A : Label} :
      Alg ⟨s, Γ, .sub S2 S1⟩ → Alg ⟨s, Γ, .sub T1 T2⟩ →
      Alg ⟨s, Γ, .sub (.typ A S1 T1) (.typ A S2 T2)⟩
  | all {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T1 T2 : Ty (s,x)} :
      Alg ⟨s, Γ, .sub S2 S1⟩ → Alg ⟨_, Γ.cons S2, .sub T1 T2⟩ →
      Alg ⟨s, Γ, .sub (.all S1 T1) (.all S2 T2)⟩
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Ty s} {q : BVar s .var} {B : Label} :
      Member Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .sub hi T⟩ →
      Alg ⟨s, Γ, .sub (.sel (.var q) B) T⟩
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .sub S1 T⟩ → Alg ⟨s, Γ, .sub (.and S1 S2) T⟩
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .sub S2 T⟩ → Alg ⟨s, Γ, .sub (.and S1 S2) T⟩
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Alg ⟨s, Γ, .var x T T⟩
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T1 T2 : Ty s} :
      Alg ⟨s, Γ, .var x V T1⟩ → Alg ⟨s, Γ, .var x V T2⟩ → Alg ⟨s, Γ, .var x V (.and T1 T2)⟩
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {B : Ty (s,x)} :
      Alg ⟨s, Γ, .var x V (B.substVar x)⟩ → Alg ⟨s, Γ, .var x V (.mu B)⟩
  | vSelLo {s : Sig} {Γ : Ctx s} {x p : BVar s .var} {V lo hi : Ty s} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .var x V lo⟩ →
      Alg ⟨s, Γ, .var x V (.sel (.var p) A)⟩
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Alg ⟨s, Γ, .var x (B.substVar x) T⟩ → Alg ⟨s, Γ, .var x (.mu B) T⟩
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .var x V1 T⟩ → Alg ⟨s, Γ, .var x (.and V1 V2) T⟩
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .var x V2 T⟩ → Alg ⟨s, Γ, .var x (.and V1 V2) T⟩
  | vSelHi {s : Sig} {Γ : Ctx s} {x q : BVar s .var} {T lo hi : Ty s} {B : Label} :
      Member Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .var x hi T⟩ →
      Alg ⟨s, Γ, .var x (.sel (.var q) B) T⟩
  | vAtom {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isAtom V = true → isAnd T = false → Alg ⟨s, Γ, .sub V T⟩ → Alg ⟨s, Γ, .var x V T⟩

/-- One step of `Alg`: the goal follows from the premises listed by one
alternative.  The constructors are those of `Alg`. -/
inductive Rule : G → List G → Prop
  | refl {s : Sig} {Γ : Ctx s} {T : Ty s} : Rule ⟨s, Γ, .sub T T⟩ []
  | top {s : Sig} {Γ : Ctx s} {S : Ty s} : Rule ⟨s, Γ, .sub S .top⟩ []
  | bot {s : Sig} {Γ : Ctx s} {T : Ty s} : Rule ⟨s, Γ, .sub .bot T⟩ []
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Ty s} :
      Rule ⟨s, Γ, .sub S (.and T1 T2)⟩ [⟨s, Γ, .sub S T1⟩, ⟨s, Γ, .sub S T2⟩]
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Ty s} {p : BVar s .var} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot →
      Rule ⟨s, Γ, .sub S (.sel (.var p) A)⟩ [⟨s, Γ, .sub S lo⟩]
  | fld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Rule ⟨s, Γ, .sub (.fld a S) (.fld a T)⟩ [⟨s, Γ, .sub S T⟩]
  | typ {s : Sig} {Γ : Ctx s} {S1 S2 T1 T2 : Ty s} {A : Label} :
      Rule ⟨s, Γ, .sub (.typ A S1 T1) (.typ A S2 T2)⟩ [⟨s, Γ, .sub S2 S1⟩, ⟨s, Γ, .sub T1 T2⟩]
  | all {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T1 T2 : Ty (s,x)} :
      Rule ⟨s, Γ, .sub (.all S1 T1) (.all S2 T2)⟩ [⟨s, Γ, .sub S2 S1⟩, ⟨_, Γ.cons S2, .sub T1 T2⟩]
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Ty s} {q : BVar s .var} {B : Label} :
      Member Γ q B lo hi → isAnd T = false →
      Rule ⟨s, Γ, .sub (.sel (.var q) B) T⟩ [⟨s, Γ, .sub hi T⟩]
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.and S1 S2) T⟩ [⟨s, Γ, .sub S1 T⟩]
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.and S1 S2) T⟩ [⟨s, Γ, .sub S2 T⟩]
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Rule ⟨s, Γ, .var x T T⟩ []
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T1 T2 : Ty s} :
      Rule ⟨s, Γ, .var x V (.and T1 T2)⟩ [⟨s, Γ, .var x V T1⟩, ⟨s, Γ, .var x V T2⟩]
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {B : Ty (s,x)} :
      Rule ⟨s, Γ, .var x V (.mu B)⟩ [⟨s, Γ, .var x V (B.substVar x)⟩]
  | vSelLo {s : Sig} {Γ : Ctx s} {x p : BVar s .var} {V lo hi : Ty s} {A : Label} :
      Member Γ p A lo hi → lo ≠ .bot →
      Rule ⟨s, Γ, .var x V (.sel (.var p) A)⟩ [⟨s, Γ, .var x V lo⟩]
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Rule ⟨s, Γ, .var x (.mu B) T⟩ [⟨s, Γ, .var x (B.substVar x) T⟩]
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .var x (.and V1 V2) T⟩ [⟨s, Γ, .var x V1 T⟩]
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .var x (.and V1 V2) T⟩ [⟨s, Γ, .var x V2 T⟩]
  | vSelHi {s : Sig} {Γ : Ctx s} {x q : BVar s .var} {T lo hi : Ty s} {B : Label} :
      Member Γ q B lo hi → isAnd T = false →
      Rule ⟨s, Γ, .var x (.sel (.var q) B) T⟩ [⟨s, Γ, .var x hi T⟩]
  | vAtom {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isAtom V = true → isAnd T = false → Rule ⟨s, Γ, .var x V T⟩ [⟨s, Γ, .sub V T⟩]

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

end Lists

/-- An `Alg` derivation is a derivation by `Rule`. -/
theorem Alg.deriv {g : G} (h : Alg g) : Deriv Rule g := by
  induction h with
  | refl => exact .mk .refl fun _ h => by cases h
  | top => exact .mk .top fun _ h => by cases h
  | bot => exact .mk .bot fun _ h => by cases h
  | andR _ _ ih1 ih2 => exact .mk .andR (forall_mem_two ih1 ih2)
  | selLo hm hlo _ ih => exact .mk (.selLo hm hlo) (forall_mem_one ih)
  | fld _ ih => exact .mk .fld (forall_mem_one ih)
  | typ _ _ ih1 ih2 => exact .mk .typ (forall_mem_two ih1 ih2)
  | all _ _ ih1 ih2 => exact .mk .all (forall_mem_two ih1 ih2)
  | selHi hm hT _ ih => exact .mk (.selHi hm hT) (forall_mem_one ih)
  | and1 hT _ ih => exact .mk (.and1 hT) (forall_mem_one ih)
  | and2 hT _ ih => exact .mk (.and2 hT) (forall_mem_one ih)
  | vRefl => exact .mk .vRefl fun _ h => by cases h
  | vAndR _ _ ih1 ih2 => exact .mk .vAndR (forall_mem_two ih1 ih2)
  | vMuR _ ih => exact .mk .vMuR (forall_mem_one ih)
  | vSelLo hm hlo _ ih => exact .mk (.vSelLo hm hlo) (forall_mem_one ih)
  | vMuL hT _ ih => exact .mk (.vMuL hT) (forall_mem_one ih)
  | vAnd1 hT _ ih => exact .mk (.vAnd1 hT) (forall_mem_one ih)
  | vAnd2 hT _ ih => exact .mk (.vAnd2 hT) (forall_mem_one ih)
  | vSelHi hm hT _ ih => exact .mk (.vSelHi hm hT) (forall_mem_one ih)
  | vAtom ha hT _ ih => exact .mk (.vAtom ha hT) (forall_mem_one ih)

/-! ## Each rule's alternative answers

The step at the conclusion of a rule answers whenever the oracle answers the
rule's premises and the tank is unmarked at the end.  The alternatives tried
before the rule's own one either answer or end unmarked, since a marked tank
stays marked. -/

theorem not_isAnd {s : Sig} {T : Ty s} (h : isAnd T = false) : ¬(isAnd T = true) := by
  rw [h]
  exact Bool.false_ne_true

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
    refine declsAt_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @fld s Γ S T a =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_mapO (hp _ (by simp)))
  | @typ s Γ S1 S2 T1 T2 A =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @all s Γ S1 S2 T1 T2 =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @selHi s Γ T lo hi q B hm hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine declsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
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
  | vRefl =>
    exact ans_orElse_left (ans_ret (by simp [vRefl]))
  | @vAndR s Γ x V T1 T2 =>
    refine ans_orElse_right (ans_ite_pos rfl ?_)
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @vMuR s Γ x V B =>
    refine ans_orElse_right (ans_ite_neg (by simp [isAnd]) (ans_orElse_left ?_))
    exact ans_mapO (hp _ (by simp))
  | @vSelLo s Γ x p V lo hi A hm hlo =>
    refine ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_left ?_)))
    refine declsAt_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @vMuL s Γ x T B hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))
    exact ans_mapO (hp _ (by simp))
  | @vAnd1 s Γ x V1 V2 T hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @vAnd2 s Γ x V1 V2 T hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | @vSelHi s Γ x q T lo hi B hm hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine declsAt_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | @vAtom s Γ x V T ha hT =>
    refine ans_orElse_right (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_ite_pos ha (ans_mapO (hp _ (by simp)))

/-! ## Completeness up to the recursion limit -/

/-- An `Alg` derivation is answered by the run, at every index and from every
tank on which the run ends unmarked. -/
theorem alg_run {g : G} (h : Alg g) (d : Nat) : Ans (run cost step d [] g) :=
  run_ans step_frame (fun _ _ hr o hF hp => rule_ans hr o hF hp) h.deriv.pruneNil d

theorem subF_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Ans (subF Γ S T) :=
  fun t ho => alg_run h t.left t ho

theorem varF_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) : Ans (varF Γ x T) :=
  ans_mapO fun t ho => alg_run h t.left t ho

theorem sub?_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} {n : Nat} (h : Alg ⟨s, Γ, .sub S T⟩)
    (ho : (sub? Γ S T n).2.out = false) : (sub? Γ S T n).1.isSome = true :=
  subF_complete h _ ho

theorem var?_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n : Nat}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) (ho : (var? Γ x T n).2.out = false) :
    (var? Γ x T n).1.isSome = true :=
  varF_complete h _ ho

/-- From the first fuel at which the run ends unmarked, an `Alg` derivation is
answered at every larger fuel. -/
theorem sub?_complete_from {s : Sig} {Γ : Ctx s} {S T : Ty s} {n m : Nat}
    (h : Alg ⟨s, Γ, .sub S T⟩) (ho : (sub? Γ S T n).2.out = false) (hnm : n ≤ m) :
    (sub? Γ S T m).1.isSome = true := by
  have hs := sub?_complete h ho
  cases he : (sub? Γ S T n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [sub?_mono he hnm]; rfl

theorem sub?_reject {s : Sig} {Γ : Ctx s} {S T : Ty s} {n k : Nat}
    (h : sub? Γ S T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .sub S T⟩ := fun ha => by
  have := sub?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem var?_reject {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n k : Nat}
    (h : var? Γ x T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩ := fun ha => by
  have := var?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

/-! ## Soundness -/

/-- A member premise gives the typing of the variable at the member. -/
theorem Member.var {s : Sig} {Γ : Ctx s} {p : BVar s .var} {A : Label} {lo hi : Ty s}
    (h : Member Γ p A lo hi) : Nonempty (Var Γ p (.typ A lo hi)) := by
  obtain ⟨_, _, ⟨lo', hi', v⟩, _, rfl, rfl⟩ := h
  exact ⟨v⟩

/-- Every goal `Alg` derives has an answer: a derivation of `S <: T`, or a map
from a derivation of `x : V` to one of `x : T`. -/
theorem Alg.answer {g : G} (h : Alg g) : Nonempty (R g) := by
  induction h with
  | refl => exact ⟨Sub.refl⟩
  | top => exact ⟨Sub.top⟩
  | bot => exact ⟨Sub.bot⟩
  | andR _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Sub.and e1 e2⟩
  | selLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans e (Sub.selLower v)⟩
  | fld _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.fld e⟩
  | typ _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Sub.typ e1 e2⟩
  | all _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Sub.all e1 e2⟩
  | selHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans (Sub.selUpper v) e⟩
  | and1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans Sub.and1 e⟩
  | and2 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans Sub.and2 e⟩
  | vRefl => exact ⟨fun d => d⟩
  | vAndR _ _ ih1 ih2 =>
    obtain ⟨f1⟩ := ih1
    obtain ⟨f2⟩ := ih2
    exact ⟨fun d => HasTy.andI (f1 d) (f2 d)⟩
  | vMuR _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => HasTy.recI (f d)⟩
  | vSelLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨f⟩ := ih
    exact ⟨fun d => HasTy.sub (f d) (Sub.selLower v)⟩
  | vMuL _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.recE d)⟩
  | vAnd1 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d Sub.and1)⟩
  | vAnd2 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d Sub.and2)⟩
  | vSelHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.var
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d (Sub.selUpper v))⟩
  | vAtom _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨fun d => HasTy.sub d e⟩

theorem Alg.sound {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Nonempty (Sub Γ S T) :=
  h.answer

/-! ## Checks -/

section AlgChecks

open DotMNF.Examples

-- E8: `x.A <: {a : ⊤}` by the upper bound of `x`'s one member, read off the lookup.
theorem E8_alg : Alg ⟨_, E8Ctx2, .sub (.sel (.var (.there .here)) lA) (.fld la .top)⟩ :=
  Alg.selHi (Member.of_mem (lo := .bot) 8 (by decide +kernel) (by decide +kernel)) rfl Alg.refl

-- E1, E3 and E4 as written: no `Alg` derivation, since the run ends unmarked with no answer.
theorem E1_sub_not_alg : ¬ Alg ⟨_, E1Ctx, .sub E1Dom E1Res⟩ :=
  sub?_reject (rejects_eq (by decide +kernel : rejects (sub? E1Ctx E1Dom E1Res) 1 = true))

theorem E1_var_not_alg : ¬ Alg ⟨_, E1Ctx, .var .here (E1Ctx.lookup .here) E1Res⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E1Ctx .here E1Res) 3 = true))

theorem E3_sub_not_alg : ¬ Alg ⟨_, E3Ctx2, .sub E3T2 E3T1⟩ :=
  sub?_reject (rejects_eq (by decide +kernel : rejects (sub? E3Ctx2 E3T2 E3T1) 1 = true))

theorem E4_sub_not_alg : ¬ Alg ⟨_, E4Ctx4, .sub E4Int (.sel (.var (.there (.there .here))) lA)⟩ :=
  sub?_reject (rejects_eq (by decide +kernel :
    rejects (sub? E4Ctx4 E4Int (.sel (.var (.there (.there .here))) lA)) 2 = true))

theorem E4_var_not_alg : ¬ Alg ⟨_, E4Ctx4, .var (.there .here) (E4Ctx4.lookup (.there .here))
    (.sel (.var (.there (.there .here))) lA)⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (var? E4Ctx4 (.there .here) (.sel (.var (.there (.there .here))) lA)) 5 = true))

/-- `p : μ(s. {A : ⊥..∀(y : ⊤) s.A})`, `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`, the
declarations of the loop through `∀` bodies. -/
def LPCtx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.mu (.typ lA .bot (.all .top (.sel (.var (.there .here)) lA))))).cons
    (.mu (.typ lB (.all .top (.sel (.var (.there .here)) lB)) .top))

/-- `p.A ∧ ⊥`. -/
def LPLeft : Ty ([],x,x) := .and (.sel (.var (.there .here)) lA) .bot

/-- `∀(y : ⊤) q.B`. -/
def LPRight : Ty ([],x,x) := .all .top (.sel (.var (.there .here)) lB)

-- `Alg` derives `p.A ∧ ⊥ <: ∀(y : ⊤) q.B` by the right operand.
theorem LP_alg : Alg ⟨_, LPCtx, .sub LPLeft LPRight⟩ := Alg.and2 rfl Alg.bot

-- The left operand, tried first, descends under a new binder at each level and
-- exhausts the tank, so the run hits the recursion limit.
example : (sub? LPCtx LPLeft LPRight).2.out = true := by decide +kernel

end AlgChecks

end Frontend.Core
