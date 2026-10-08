import Coercions.Oopsla16.Frontend.Sub

/-!
# The algorithmic judgment and completeness

`Alg` states the rules of the algorithm of `Sub.lean`, one constructor per
alternative, with no fuel and no pending goals.  Three cases of the `sub` goal
are final: an intersection on the right, a union on the left and two
recursive types.  A constructor tried after them carries what lets the
algorithm pass them.  `orL` carries `isAnd T = false`.  The constructors of
the later alternatives carry `Final S T = false` where their form does not
already decide it.  At two recursive types the algorithm tries `stp_bindx`,
then `stp_bind1`, so `bind1` carries only `isAnd T = false` and holds whether
the right side is recursive or not.  A selection on the right through a lower
bound carries `lo ≠ ⊥`, as the algorithm skips such a member.  The `var` goal
has no final case, so its constructors carry no condition on the order.  A
member premise is phrased through the lookup (`Member`): the lookup finds that
member and ends within its fuel.

Completeness holds up to the recursion limit.  If `Alg` derives a goal, the
algorithm answers it at every fuel at which its run ends with the tank
unmarked (`sub?_complete`, `var?_complete`).  So a run that ends unmarked with
no answer is a rejection by the rules (`sub?_reject`, `var?_reject`).  The
tank is shared by all the alternatives of a goal, and a marked tank stays
marked.  So an alternative that never ends, tried before the one an `Alg`
derivation uses, exhausts every tank.  `p.1 ∧ ⊥ <: q.1` below is such a goal:
`Alg` derives it by the right operand, and the left operand, tried first,
goes under a method's parameter at each level.  So completeness cannot say
that some fuel suffices.

The proof needs no minimal derivation.  A derivation in which no goal repeats
along a branch exists whenever a derivation does (`Deriv.pruneNil`): a repeat
is cut out by using the inner derivation of the goal at the outer place.  A
derivation without repeats is never cut by the run.  At each goal the run
either answers by an alternative tried first or reaches the one the
derivation uses, since the tank is unmarked at the end and so at every point
before (`run_ans`).  Both facts are generic in the goals and the step.  They
are stated here, in the library of this front end, since the library of the
vanilla front end brings in its own calculus.

`Alg.sound` is the soundness of `Alg` for Oopsla16 at the empty store.  Each
constructor builds the derivation its alternative emits.  It says no more
than that derivation does.
-/

namespace Oopsla16Frontend.Core

open Frontend.Fuel
open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Ctx Store Stp Htp HasType scopeUpTo renameUpTo varUpTo)

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

/-- `x` has the type member `L : lo..hi`, with bounds in the prefix of `x`:
the lookup of the type members of `x` at `L` finds it, from some full tank,
and ends with the tank unmarked. -/
def Member {s : Sig} (Γ : Ctx [] s) (x : BVar s .var) (L : Lb) (lo hi : Ty [] (scopeUpTo x)) :
    Prop :=
  ∃ n, (hdecls Γ n x L ⟨n, false⟩).2.out = false ∧
    ∃ d ∈ (hdecls Γ n x L ⟨n, false⟩).1, d.1 = lo ∧ d.2.1 = hi

/-- A member premise read off one lookup.  Both hypotheses are decidable, so
the kernel checks them on an example. -/
theorem Member.of_mem {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {L : Lb}
    {lo hi : Ty [] (scopeUpTo x)} (n : Nat) (ho : (hdecls Γ n x L ⟨n, false⟩).2.out = false)
    (h : (lo, hi) ∈ (hdecls Γ n x L ⟨n, false⟩).1.map fun d => (d.1, d.2.1)) :
    Member Γ x L lo hi := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, d, hd, (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩

/-- Two lookups that end unmarked find the same members. -/
theorem hdecls_same {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {L : Lb} {n : Nat} {t : Tank}
    (h1 : (hdecls Γ n x L ⟨n, false⟩).2.out = false) (h2 : (hdecls Γ t.left x L t).2.out = false) :
    (hdecls Γ t.left x L t).1 = (hdecls Γ n x L ⟨n, false⟩).1 := by
  have ht : t.out = false := (hdecls_framed Γ t.left x L).start rfl h2
  let u : Tank := ⟨n + t.left, false⟩
  have hu1 : u = (⟨n, false⟩ : Tank).add t.left := rfl
  have hu2 : u = t.add n := by
    obtain ⟨l, o⟩ := t
    simp only at ht
    subst ht
    simp only [u, Tank.add, Tank.mk.injEq, and_true]
    omega
  have e1 := hdecls_frame (Prod.ext rfl rfl) h1 t.left
  have e2 := hdecls_frame (Prod.ext rfl rfl) h2 n
  rw [← hu1] at e1
  rw [← hu2] at e2
  have i1 := hdecls_index (d' := n + t.left) (by rw [e1]; exact h1) (Nat.le_add_right _ _)
  have i2 := hdecls_index (d' := n + t.left) (by rw [e2]; exact h2) (Nat.le_add_left _ _)
  have := i1.symm.trans i2
  rw [e1, e2] at this
  exact (Prod.mk.inj this).1.symm

/-- A lookup of a member, then a computation on the members found, answers
when the computation does on every list that holds the member. -/
theorem members_ans {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {L : Lb}
    {lo hi : Ty [] (scopeUpTo x)} {β : Type} {k : List (TyMem Γ x L) → Fu (Option β)}
    (hm : Member Γ x L lo hi) (hk : ∀ ds, Framed (k ds))
    (hans : ∀ ds, (∃ d ∈ ds, d.1 = lo ∧ d.2.1 = hi) → Ans (k ds)) :
    Ans (Fu.bind (members Γ x L) k) := by
  obtain ⟨n, hn, hmem⟩ := hm
  intro t ho
  have hd : Fu.bind (members Γ x L) k t = k (members Γ x L t).1 (members Γ x L t).2 := rfl
  rw [hd] at ho ⊢
  have ht1 : (members Γ x L t).2.out = false := (hk _).start rfl ho
  have hds : (members Γ x L t).1 = (hdecls Γ n x L ⟨n, false⟩).1 := hdecls_same hn ht1
  revert ho
  rw [hds]
  exact hans _ hmem _

/-! ## The judgment -/

/-- The algorithm's rules, one constructor per alternative of `subStep` and
`varStep`, with no fuel and no pending goals.  The method and type member
cases of `sStruct` are two constructors. -/
inductive Alg : G → Prop
  | refl {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : Alg ⟨s, Γ, .sub T T⟩
  | top {s : Sig} {Γ : Ctx [] s} {S : Ty [] s} : Alg ⟨s, Γ, .sub S .TTop⟩
  | bot {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : Alg ⟨s, Γ, .sub .TBot T⟩
  | andR {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Alg ⟨s, Γ, .sub S T1⟩ → Alg ⟨s, Γ, .sub S T2⟩ → Alg ⟨s, Γ, .sub S (.TAnd T1 T2)⟩
  | orL {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      isAnd T = false → Alg ⟨s, Γ, .sub S1 T⟩ → Alg ⟨s, Γ, .sub S2 T⟩ →
      Alg ⟨s, Γ, .sub (.TOr S1 S2) T⟩
  | bindx {s : Sig} {Γ : Ctx [] s} {T1 T2 : Ty [] (s,x)} :
      Alg ⟨_, Γ.cons T1, .sub T1 T2⟩ → Alg ⟨s, Γ, .sub (.TBind T1) (.TBind T2)⟩
  | bind1 {s : Sig} {Γ : Ctx [] s} {T1 : Ty [] (s,x)} {T : Ty [] s} :
      isAnd T = false → Alg ⟨_, Γ.cons T1, .sub T1 T.weaken⟩ → Alg ⟨s, Γ, .sub (.TBind T1) T⟩
  | orR1 {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Final S (.TOr T1 T2) = false → Alg ⟨s, Γ, .sub S T1⟩ → Alg ⟨s, Γ, .sub S (.TOr T1 T2)⟩
  | orR2 {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Final S (.TOr T1 T2) = false → Alg ⟨s, Γ, .sub S T2⟩ → Alg ⟨s, Γ, .sub S (.TOr T1 T2)⟩
  | selLo {s : Sig} {Γ : Ctx [] s} {S : Ty [] s} {x : BVar s .var} {L : Lb}
      {lo hi : Ty [] (scopeUpTo x)} :
      Member Γ x L lo hi → lo ≠ .TBot → Final S (.TSel (.abs x) L) = false →
      Alg ⟨s, Γ, .sub S (lo.rename (renameUpTo x))⟩ → Alg ⟨s, Γ, .sub S (.TSel (.abs x) L)⟩
  | fn {s : Sig} {Γ : Ctx [] s} {l : Lb} {T1 T3 : Ty [] s} {T2 T4 : Ty [] (s,x)} :
      Alg ⟨s, Γ, .sub T3 T1⟩ → Alg ⟨_, Γ.cons T3.weaken, .sub T2 T4⟩ →
      Alg ⟨s, Γ, .sub (.TFun l T1 T2) (.TFun l T3 T4)⟩
  | typ {s : Sig} {Γ : Ctx [] s} {l : Lb} {T1 T2 T3 T4 : Ty [] s} :
      Alg ⟨s, Γ, .sub T3 T1⟩ → Alg ⟨s, Γ, .sub T2 T4⟩ →
      Alg ⟨s, Γ, .sub (.TTyp l T1 T2) (.TTyp l T3 T4)⟩
  | selHi {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} {x : BVar s .var} {L : Lb}
      {lo hi : Ty [] (scopeUpTo x)} :
      Member Γ x L lo hi → Final (.TSel (.abs x) L) T = false →
      Alg ⟨s, Γ, .sub (hi.rename (renameUpTo x)) T⟩ → Alg ⟨s, Γ, .sub (.TSel (.abs x) L) T⟩
  | andL1 {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      Final (.TAnd S1 S2) T = false → Alg ⟨s, Γ, .sub S1 T⟩ → Alg ⟨s, Γ, .sub (.TAnd S1 S2) T⟩
  | andL2 {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      Final (.TAnd S1 S2) T = false → Alg ⟨s, Γ, .sub S2 T⟩ → Alg ⟨s, Γ, .sub (.TAnd S1 S2) T⟩
  | vRefl {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} : Alg ⟨s, Γ, .var x T T⟩
  | vAndPart {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V W T1 T2 : Ty [] s} :
      W ∈ andParts (.TAnd T1 T2) → Alg ⟨s, Γ, .var x V W⟩ → Alg ⟨s, Γ, .sub W (.TAnd T1 T2)⟩ →
      Alg ⟨s, Γ, .var x V (.TAnd T1 T2)⟩
  | vAndPack {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V : Ty [] s} {A B : Ty [] (s,x)} :
      Alg ⟨s, Γ, .var x V ((Ty.TAnd A B).substVr (.abs x))⟩ →
      Alg ⟨s, Γ, .var x V (.TAnd (.TBind A) (.TBind B))⟩
  | vMuR {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V : Ty [] s} {B : Ty [] (s,x)} :
      Alg ⟨s, Γ, .var x V (B.substVr (.abs x))⟩ → Alg ⟨s, Γ, .var x V (.TBind B)⟩
  | vOrR1 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T1 T2 : Ty [] s} :
      Alg ⟨s, Γ, .var x V T1⟩ → Alg ⟨s, Γ, .var x V (.TOr T1 T2)⟩
  | vOrR2 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T1 T2 : Ty [] s} :
      Alg ⟨s, Γ, .var x V T2⟩ → Alg ⟨s, Γ, .var x V (.TOr T1 T2)⟩
  | vSelLo {s : Sig} {Γ : Ctx [] s} {x p : BVar s .var} {V : Ty [] s} {L : Lb}
      {lo hi : Ty [] (scopeUpTo p)} :
      Member Γ p L lo hi → lo ≠ .TBot → Alg ⟨s, Γ, .var x V (lo.rename (renameUpTo p))⟩ →
      Alg ⟨s, Γ, .var x V (.TSel (.abs p) L)⟩
  | vMuL {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {B : Ty [] (s,x)} :
      Alg ⟨s, Γ, .var x (B.substVr (.abs x)) T⟩ → Alg ⟨s, Γ, .var x (.TBind B) T⟩
  | vAndL1 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V1 V2 T : Ty [] s} :
      Alg ⟨s, Γ, .var x V1 T⟩ → Alg ⟨s, Γ, .var x (.TAnd V1 V2) T⟩
  | vAndL2 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V1 V2 T : Ty [] s} :
      Alg ⟨s, Γ, .var x V2 T⟩ → Alg ⟨s, Γ, .var x (.TAnd V1 V2) T⟩
  | vSelHi {s : Sig} {Γ : Ctx [] s} {x q : BVar s .var} {T : Ty [] s} {L : Lb}
      {lo hi : Ty [] (scopeUpTo q)} :
      Member Γ q L lo hi → Alg ⟨s, Γ, .var x (hi.rename (renameUpTo q)) T⟩ →
      Alg ⟨s, Γ, .var x (.TSel (.abs q) L) T⟩
  | vSub {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T : Ty [] s} :
      isMu V = false → isSel V = false → Alg ⟨s, Γ, .sub V T⟩ → Alg ⟨s, Γ, .var x V T⟩

/-- One step of `Alg`: the goal follows from the premises listed by one
alternative.  The constructors are those of `Alg`. -/
inductive Rule : G → List G → Prop
  | refl {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : Rule ⟨s, Γ, .sub T T⟩ []
  | top {s : Sig} {Γ : Ctx [] s} {S : Ty [] s} : Rule ⟨s, Γ, .sub S .TTop⟩ []
  | bot {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} : Rule ⟨s, Γ, .sub .TBot T⟩ []
  | andR {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Rule ⟨s, Γ, .sub S (.TAnd T1 T2)⟩ [⟨s, Γ, .sub S T1⟩, ⟨s, Γ, .sub S T2⟩]
  | orL {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.TOr S1 S2) T⟩ [⟨s, Γ, .sub S1 T⟩, ⟨s, Γ, .sub S2 T⟩]
  | bindx {s : Sig} {Γ : Ctx [] s} {T1 T2 : Ty [] (s,x)} :
      Rule ⟨s, Γ, .sub (.TBind T1) (.TBind T2)⟩ [⟨_, Γ.cons T1, .sub T1 T2⟩]
  | bind1 {s : Sig} {Γ : Ctx [] s} {T1 : Ty [] (s,x)} {T : Ty [] s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.TBind T1) T⟩ [⟨_, Γ.cons T1, .sub T1 T.weaken⟩]
  | orR1 {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Final S (.TOr T1 T2) = false → Rule ⟨s, Γ, .sub S (.TOr T1 T2)⟩ [⟨s, Γ, .sub S T1⟩]
  | orR2 {s : Sig} {Γ : Ctx [] s} {S T1 T2 : Ty [] s} :
      Final S (.TOr T1 T2) = false → Rule ⟨s, Γ, .sub S (.TOr T1 T2)⟩ [⟨s, Γ, .sub S T2⟩]
  | selLo {s : Sig} {Γ : Ctx [] s} {S : Ty [] s} {x : BVar s .var} {L : Lb}
      {lo hi : Ty [] (scopeUpTo x)} :
      Member Γ x L lo hi → lo ≠ .TBot → Final S (.TSel (.abs x) L) = false →
      Rule ⟨s, Γ, .sub S (.TSel (.abs x) L)⟩ [⟨s, Γ, .sub S (lo.rename (renameUpTo x))⟩]
  | fn {s : Sig} {Γ : Ctx [] s} {l : Lb} {T1 T3 : Ty [] s} {T2 T4 : Ty [] (s,x)} :
      Rule ⟨s, Γ, .sub (.TFun l T1 T2) (.TFun l T3 T4)⟩
        [⟨s, Γ, .sub T3 T1⟩, ⟨_, Γ.cons T3.weaken, .sub T2 T4⟩]
  | typ {s : Sig} {Γ : Ctx [] s} {l : Lb} {T1 T2 T3 T4 : Ty [] s} :
      Rule ⟨s, Γ, .sub (.TTyp l T1 T2) (.TTyp l T3 T4)⟩ [⟨s, Γ, .sub T3 T1⟩, ⟨s, Γ, .sub T2 T4⟩]
  | selHi {s : Sig} {Γ : Ctx [] s} {T : Ty [] s} {x : BVar s .var} {L : Lb}
      {lo hi : Ty [] (scopeUpTo x)} :
      Member Γ x L lo hi → Final (.TSel (.abs x) L) T = false →
      Rule ⟨s, Γ, .sub (.TSel (.abs x) L) T⟩ [⟨s, Γ, .sub (hi.rename (renameUpTo x)) T⟩]
  | andL1 {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      Final (.TAnd S1 S2) T = false → Rule ⟨s, Γ, .sub (.TAnd S1 S2) T⟩ [⟨s, Γ, .sub S1 T⟩]
  | andL2 {s : Sig} {Γ : Ctx [] s} {S1 S2 T : Ty [] s} :
      Final (.TAnd S1 S2) T = false → Rule ⟨s, Γ, .sub (.TAnd S1 S2) T⟩ [⟨s, Γ, .sub S2 T⟩]
  | vRefl {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} : Rule ⟨s, Γ, .var x T T⟩ []
  | vAndPart {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V W T1 T2 : Ty [] s} :
      W ∈ andParts (.TAnd T1 T2) →
      Rule ⟨s, Γ, .var x V (.TAnd T1 T2)⟩ [⟨s, Γ, .var x V W⟩, ⟨s, Γ, .sub W (.TAnd T1 T2)⟩]
  | vAndPack {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V : Ty [] s} {A B : Ty [] (s,x)} :
      Rule ⟨s, Γ, .var x V (.TAnd (.TBind A) (.TBind B))⟩
        [⟨s, Γ, .var x V ((Ty.TAnd A B).substVr (.abs x))⟩]
  | vMuR {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V : Ty [] s} {B : Ty [] (s,x)} :
      Rule ⟨s, Γ, .var x V (.TBind B)⟩ [⟨s, Γ, .var x V (B.substVr (.abs x))⟩]
  | vOrR1 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T1 T2 : Ty [] s} :
      Rule ⟨s, Γ, .var x V (.TOr T1 T2)⟩ [⟨s, Γ, .var x V T1⟩]
  | vOrR2 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T1 T2 : Ty [] s} :
      Rule ⟨s, Γ, .var x V (.TOr T1 T2)⟩ [⟨s, Γ, .var x V T2⟩]
  | vSelLo {s : Sig} {Γ : Ctx [] s} {x p : BVar s .var} {V : Ty [] s} {L : Lb}
      {lo hi : Ty [] (scopeUpTo p)} :
      Member Γ p L lo hi → lo ≠ .TBot →
      Rule ⟨s, Γ, .var x V (.TSel (.abs p) L)⟩ [⟨s, Γ, .var x V (lo.rename (renameUpTo p))⟩]
  | vMuL {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {B : Ty [] (s,x)} :
      Rule ⟨s, Γ, .var x (.TBind B) T⟩ [⟨s, Γ, .var x (B.substVr (.abs x)) T⟩]
  | vAndL1 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V1 V2 T : Ty [] s} :
      Rule ⟨s, Γ, .var x (.TAnd V1 V2) T⟩ [⟨s, Γ, .var x V1 T⟩]
  | vAndL2 {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V1 V2 T : Ty [] s} :
      Rule ⟨s, Γ, .var x (.TAnd V1 V2) T⟩ [⟨s, Γ, .var x V2 T⟩]
  | vSelHi {s : Sig} {Γ : Ctx [] s} {x q : BVar s .var} {T : Ty [] s} {L : Lb}
      {lo hi : Ty [] (scopeUpTo q)} :
      Member Γ q L lo hi →
      Rule ⟨s, Γ, .var x (.TSel (.abs q) L) T⟩ [⟨s, Γ, .var x (hi.rename (renameUpTo q)) T⟩]
  | vSub {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {V T : Ty [] s} :
      isMu V = false → isSel V = false → Rule ⟨s, Γ, .var x V T⟩ [⟨s, Γ, .sub V T⟩]

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
  | orL hT _ _ ih1 ih2 => exact .mk (.orL hT) (forall_mem_two ih1 ih2)
  | bindx _ ih => exact .mk .bindx (forall_mem_one ih)
  | bind1 hT _ ih => exact .mk (.bind1 hT) (forall_mem_one ih)
  | orR1 hf _ ih => exact .mk (.orR1 hf) (forall_mem_one ih)
  | orR2 hf _ ih => exact .mk (.orR2 hf) (forall_mem_one ih)
  | selLo hm hlo hf _ ih => exact .mk (.selLo hm hlo hf) (forall_mem_one ih)
  | fn _ _ ih1 ih2 => exact .mk .fn (forall_mem_two ih1 ih2)
  | typ _ _ ih1 ih2 => exact .mk .typ (forall_mem_two ih1 ih2)
  | selHi hm hf _ ih => exact .mk (.selHi hm hf) (forall_mem_one ih)
  | andL1 hf _ ih => exact .mk (.andL1 hf) (forall_mem_one ih)
  | andL2 hf _ ih => exact .mk (.andL2 hf) (forall_mem_one ih)
  | vRefl => exact .mk .vRefl fun _ h => by cases h
  | vAndPart hW _ _ ih1 ih2 => exact .mk (.vAndPart hW) (forall_mem_two ih1 ih2)
  | vAndPack _ ih => exact .mk .vAndPack (forall_mem_one ih)
  | vMuR _ ih => exact .mk .vMuR (forall_mem_one ih)
  | vOrR1 _ ih => exact .mk .vOrR1 (forall_mem_one ih)
  | vOrR2 _ ih => exact .mk .vOrR2 (forall_mem_one ih)
  | vSelLo hm hlo _ ih => exact .mk (.vSelLo hm hlo) (forall_mem_one ih)
  | vMuL _ ih => exact .mk .vMuL (forall_mem_one ih)
  | vAndL1 _ ih => exact .mk .vAndL1 (forall_mem_one ih)
  | vAndL2 _ ih => exact .mk .vAndL2 (forall_mem_one ih)
  | vSelHi hm _ ih => exact .mk (.vSelHi hm) (forall_mem_one ih)
  | vSub hM hS _ ih => exact .mk (.vSub hM hS) (forall_mem_one ih)

/-! ## Each rule's alternative answers

The step at the conclusion of a rule answers whenever the oracle answers the
rule's premises and the tank is unmarked at the end.  The alternatives tried
before the rule's own one either answer or end unmarked, since a marked tank
stays marked. -/

theorem ne_true {b : Bool} (h : b = false) : ¬(b = true) := by
  rw [h]
  exact Bool.false_ne_true

/-- A pair that is not final passes the three tests of `subMain`. -/
theorem final_false {s : Sig} {S T : Ty [] s} (h : Final S T = false) :
    ¬(isAnd T = true) ∧ ¬(isOr S = true) ∧ ¬((isMu S && isMu T) = true) := by
  simp only [Final, Bool.or_eq_false_iff] at h
  exact ⟨ne_true h.1.1, ne_true h.1.2, ne_true h.2⟩

theorem rule_ans {g : G} {ps : List G} (h : Rule g ps) (o : Oracle G R) (hF : ∀ g', Framed (o g'))
    (hp : ∀ p ∈ ps, Ans (o p)) : Ans (step o g) := by
  cases h with
  | refl =>
    exact ans_orElse_left (ans_ret (by simp [sRefl]))
  | top =>
    exact ans_orElse_right (ans_orElse_left (ans_ret rfl))
  | bot =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_ret rfl)))
  | andR =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_ite_pos rfl ?_)))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | orL hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (ne_true hT) (ans_ite_pos rfl ?_))))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | bindx =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_ite_neg (by simp [isOr]) (ans_ite_pos rfl ?_)))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @bind1 s Γ T1 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (ne_true hT) (ans_ite_neg (by simp [isOr]) ?_))))
    cases isMu T with
    | true =>
      refine ans_ite_pos (by simp [isMu]) ?_
      exact ans_orElse_right (ans_mapO (hp _ (by simp)))
    | false =>
      refine ans_ite_neg (by simp [isMu]) ?_
      refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right ?_))))
      exact ans_mapO (hp _ (by simp))
  | orR1 hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM ?_)))))
    exact ans_orElse_left (ans_orElse_left (ans_mapO (hp _ (by simp))))
  | orR2 hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM ?_)))))
    exact ans_orElse_left (ans_orElse_right (ans_mapO (hp _ (by simp))))
  | @selLo s Γ S x L lo hi hm hlo hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM (ans_orElse_right (ans_orElse_left ?_)))))))
    refine members_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @fn s Γ l T1 T3 T2 T4 =>
    obtain ⟨hA, hO, hM⟩ := final_false (S := .TFun l T1 T2) (T := .TFun l T3 T4) rfl
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM
        (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))))
    exact ans_dite_pos rfl (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @typ s Γ l T1 T2 T3 T4 =>
    obtain ⟨hA, hO, hM⟩ := final_false (S := .TTyp l T1 T2) (T := .TTyp l T3 T4) rfl
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM
        (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))))
    exact ans_dite_pos rfl (ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp)))
  | @selHi s Γ T x L lo hi hm hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM
        (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))))))
    refine members_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | andL1 hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | andL2 hf =>
    obtain ⟨hA, hO, hM⟩ := final_false hf
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg hA (ans_ite_neg hO (ans_ite_neg hM (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | vRefl =>
    exact ans_orElse_left (ans_ret (by simp [vRefl]))
  | @vAndPart s Γ x V W T1 T2 hW =>
    refine ans_orElse_right (ans_orElse_left ?_)
    refine ans_firstSome ?_ _ hW
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | vAndPack =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_mapO (hp _ (by simp)))))
  | vMuR =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left
      (ans_mapO (hp _ (by simp))))))
  | vOrR1 =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_left (ans_orElse_left (ans_mapO (hp _ (by simp))))))))
  | vOrR2 =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_left (ans_orElse_right (ans_mapO (hp _ (by simp))))))))
  | @vSelLo s Γ x p V L lo hi hm hlo =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_left ?_)))))
    refine members_ans hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | vMuL =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_left (ans_mapO (hp _ (by simp)))))))))
  | vAndL1 =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left
        (ans_orElse_left (ans_mapO (hp _ (by simp)))))))))))
  | vAndL2 =>
    exact ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left
        (ans_orElse_right (ans_mapO (hp _ (by simp)))))))))))
  | @vSelHi s Γ x q T L lo hi hm =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_left ?_))))))))
    refine members_ans hm (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ds ⟨⟨lo', hi', v⟩, hd, rfl, rfl⟩
    refine ans_firstSome ?_ ds hd
    exact ans_mapO (hp _ (by simp))
  | vSub hM hS =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right ?_))))))))
    exact ans_ite_pos (by simp [hM, hS]) (ans_mapO (hp _ (by simp)))

/-! ## Completeness up to the recursion limit -/

/-- An `Alg` derivation is answered by the run, at every index and from every
tank on which the run ends unmarked. -/
theorem alg_run {g : G} (h : Alg g) (d : Nat) : Ans (run cost step d [] g) :=
  run_ans step_frame (fun _ _ hr o hF hp => rule_ans hr o hF hp) h.deriv.pruneNil d

theorem subF_complete {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Ans (subF Γ S T) :=
  fun t ho => alg_run h t.left t ho

theorem varF_complete {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) : Ans (varF Γ x T) :=
  ans_mapO fun t ho => alg_run h t.left t ho

theorem sub?_complete {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} {n : Nat} (h : Alg ⟨s, Γ, .sub S T⟩)
    (ho : (sub? Γ S T n).2.out = false) : (sub? Γ S T n).1.isSome = true :=
  subF_complete h _ ho

theorem var?_complete {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {n : Nat}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) (ho : (var? Γ x T n).2.out = false) :
    (var? Γ x T n).1.isSome = true :=
  varF_complete h _ ho

/-- From the first fuel at which the run ends unmarked, an `Alg` derivation is
answered at every larger fuel. -/
theorem sub?_complete_from {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} {n m : Nat}
    (h : Alg ⟨s, Γ, .sub S T⟩) (ho : (sub? Γ S T n).2.out = false) (hnm : n ≤ m) :
    (sub? Γ S T m).1.isSome = true := by
  have hs := sub?_complete h ho
  cases he : (sub? Γ S T n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [sub?_mono he hnm]; rfl

/-- The same for the `var` goal. -/
theorem var?_complete_from {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {n m : Nat}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) (ho : (var? Γ x T n).2.out = false) (hnm : n ≤ m) :
    (var? Γ x T m).1.isSome = true := by
  have hs := var?_complete h ho
  cases he : (var? Γ x T n).1 with
  | none => rw [he] at hs; cases hs
  | some e => rw [var?_mono he hnm]; rfl

theorem sub?_reject {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} {n k : Nat}
    (h : sub? Γ S T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .sub S T⟩ := fun ha => by
  have := sub?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem var?_reject {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {T : Ty [] s} {n k : Nat}
    (h : var? Γ x T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩ := fun ha => by
  have := var?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

/-! ## Soundness -/

/-- A member premise gives the `Htp` derivation of the variable at the
member. -/
theorem Member.htp {s : Sig} {Γ : Ctx [] s} {x : BVar s .var} {L : Lb}
    {lo hi : Ty [] (scopeUpTo x)} (h : Member Γ x L lo hi) : Nonempty (SHtp Γ x (.TTyp L lo hi)) := by
  obtain ⟨_, _, ⟨lo', hi', v⟩, _, rfl, rfl⟩ := h
  exact ⟨v⟩

/-- Every goal `Alg` derives has an answer: a derivation of `S <: T`, or a map
from a derivation of `x : V` to one of `x : T`.  Each case builds what its
alternative emits. -/
theorem Alg.answer {g : G} (h : Alg g) : Nonempty (R g) := by
  induction h with
  | refl => exact ⟨Core.refl _⟩
  | top => exact ⟨.stp_top⟩
  | bot => exact ⟨.stp_bot⟩
  | andR _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨.stp_and2 e1 e2⟩
  | orL _ _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨.stp_or1 e1 e2⟩
  | bindx _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_bindx e⟩
  | bind1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_bind1 e⟩
  | orR1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_or21 e⟩
  | orR2 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_or22 e⟩
  | selLo hm _ _ _ ih =>
    obtain ⟨v⟩ := hm.htp
    obtain ⟨e⟩ := ih
    exact ⟨.stp_trans e (.stp_sel2 (upperTop v))⟩
  | fn _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨.stp_fun e1 e2⟩
  | typ _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨.stp_typ e1 e2⟩
  | selHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.htp
    obtain ⟨e⟩ := ih
    exact ⟨.stp_trans (.stp_sel1 (lowerBot v)) e⟩
  | andL1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_and11 e⟩
  | andL2 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨.stp_and12 e⟩
  | vRefl => exact ⟨fun d => d⟩
  | vAndPart _ _ _ ih1 ih2 =>
    obtain ⟨f⟩ := ih1
    obtain ⟨e⟩ := ih2
    exact ⟨fun d => .T_Sub (f d) e⟩
  | @vAndPack s Γ x V A B _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => .T_Sub (.T_VarPack (f d)) (.stp_and2 (.stp_bindx (.stp_and11 (Core.refl A)))
      (.stp_bindx (.stp_and12 (Core.refl B))))⟩
  | vMuR _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => .T_VarPack (f d)⟩
  | @vOrR1 s Γ x V T1 T2 _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => .T_Sub (f d) (.stp_or21 (Core.refl T1))⟩
  | @vOrR2 s Γ x V T1 T2 _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => .T_Sub (f d) (.stp_or22 (Core.refl T2))⟩
  | vSelLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.htp
    obtain ⟨f⟩ := ih
    exact ⟨fun d => .T_Sub (f d) (.stp_sel2 (upperTop v))⟩
  | vMuL _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (.T_VarUnpack d)⟩
  | @vAndL1 s Γ x V1 V2 T _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (.T_Sub d (.stp_and11 (Core.refl V1)))⟩
  | @vAndL2 s Γ x V1 V2 T _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (.T_Sub d (.stp_and12 (Core.refl V2)))⟩
  | vSelHi hm _ ih =>
    obtain ⟨v⟩ := hm.htp
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (.T_Sub d (.stp_sel1 (lowerBot v)))⟩
  | vSub _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨fun d => .T_Sub d e⟩

theorem Alg.sound {s : Sig} {Γ : Ctx [] s} {S T : Ty [] s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Nonempty (Stp Store.nil Γ S T) :=
  h.answer

/-! ## Checks -/

section AlgChecks

-- D1: `z.0 <: {def 9(y : ⊤) : ⊤}` by the upper bound of the member `0` of `z`,
-- read off the lookup.
theorem D1_alg : Alg ⟨_, deepCtx, .sub (.TSel (.abs .here) 0) (fnTop 9)⟩ :=
  Alg.selHi (Member.of_mem (lo := .TBot) (hi := fnTop 9) defaultFuel (by decide +kernel) (by decide +kernel))
    rfl Alg.refl

-- R3: `μ(z. y.0) <: μ(z. {1 : ⊥..z.1})`.  The left self is unused, so the
-- body `y.0` is compared with the whole right side by `stp_bind1`, and `y.0`
-- reaches it by the upper bound of the member of `y`.
theorem R3_alg : Alg ⟨_, r3Ctx, .sub r3S r3T⟩ :=
  Alg.bind1 rfl (Alg.selHi (Member.of_mem (lo := .TBot)
    (hi := .TBind (.TTyp 1 .TBot (.TSel (.abs .here) 1))) defaultFuel (by decide +kernel)
    (by decide +kernel)) rfl Alg.refl)

-- Packing at the recursive type of both bodies: the opened body of
-- `μ(w. {0 : ⊥..⊤} ∧ {1 : ⊥..w.0})` at `x` is the declared type of `x`.
theorem packTwo_alg : Alg ⟨_, packTwoCtx, .var .here (packTwoCtx.lookup .here) packTwoT⟩ :=
  Alg.vAndPack Alg.vRefl

-- The converse of `recursive` and the alias cycle: no `Alg` derivation, since
-- the run ends unmarked with no answer.
section

open Oopsla16.Examples.FunctionField (Sbody Tbody)

theorem recursive_converse_not_alg : ¬ Alg ⟨_, Ctx.nil, .sub (.TBind Tbody) (.TBind Sbody)⟩ :=
  sub?_reject (rejects_eq (by decide +kernel :
    rejects (sub? Ctx.nil (.TBind Tbody) (.TBind Sbody)) 8 = true))

end

theorem cyc_not_alg : ¬ Alg ⟨_, cycCtx, .sub (.TSel (.abs .here) 1) (fnTop 9)⟩ :=
  sub?_reject (rejects_eq (by decide +kernel :
    rejects (sub? cycCtx (.TSel (.abs .here) 1) (fnTop 9)) 28 = true))

/-- `p.1 ∧ ⊥`, in the context of the loop through method binders. -/
def lpLeft : Ty [] ([],x,x) := .TAnd lpP .TBot

-- `Alg` derives `p.1 ∧ ⊥ <: q.1` by the right operand.
theorem lp_alg : Alg ⟨_, lpCtx, .sub lpLeft lpQ⟩ := Alg.andL2 rfl Alg.bot

-- The left operand, tried first, goes under the method's parameter at each
-- level and exhausts the tank, so the run hits the recursion limit.
example : (sub? lpCtx lpLeft lpQ).2.out = true := by decide +kernel

end AlgChecks

end Oopsla16Frontend.Core
