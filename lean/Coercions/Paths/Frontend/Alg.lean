import Coercions.Paths.Frontend.Sub

/-!
# The algorithmic judgment and completeness

`Alg` states the rules of the algorithm of `Sub.lean`, one constructor per
alternative, with no fuel and no pending goals.  A constructor tried after an
intersection on the right carries `isAnd T = false`, since that alternative
is final.  A selection on the right through a lower bound carries `lo ≠ ⊥`,
as the algorithm skips such a member.  An atom of a view carries `isAtom` or
`isVAtom`.  A recursive type opened on either side carries `Ty.Decl`.

A premise that reads a lookup says what the lookup finds (`Found`): run from
some full tank, it ends unmarked and finds an item with the property.  The
member of a path (`MemberP`), a declared type of a path (`StartP`), a stable
field (`VfldP`) and a singleton (`SnglP`) are such premises.  A lookup that
ends unmarked finds the same items at every fuel, so the run finds the item
too.

Two recursive types are related through the walker of the abstract view.  The
walker reads the members of the right body off the left one and asks a
subtyping at each self-free step whose sides do not mention the self.
`DeclAsks L R ps` says that the walker finds the view of `L` at `R` when each
subtyping of the list `ps` holds.  The constructor `mu` asks `Alg` for each.

Completeness holds up to the recursion limit.  If `Alg` derives a goal, the
algorithm answers it at every fuel at which its run ends with the tank
unmarked (`sub?_complete`, `path?_complete`, `var?_complete`).  So a run that
ends unmarked with no answer is a rejection by the rules (`sub?_reject`,
`var?_reject`).  The tank is shared by all the alternatives of a goal, and a
marked tank stays marked.  So an alternative that never ends, tried before the
one an `Alg` derivation uses, exhausts every tank.  `p.A ∧ ⊥ <: ∀(y : ⊤) q.B`
below is such a goal: `Alg` derives it by the right operand, and the left
operand, tried first, descends under a new binder at each level.  So
completeness cannot say that some fuel suffices.

The proof needs no minimal derivation.  A derivation in which no goal repeats
along a branch exists whenever a derivation does (`Deriv.pruneNil`): a repeat
is cut out by using the inner derivation of the goal at the outer place.  A
derivation without repeats is never cut by the run.  At each goal the run
either answers by an alternative tried before or reaches the one the derivation
uses, since the tank is unmarked at the end and so at every point before
(`run_ans`).  Both facts are generic in the goals and the step.

`Alg.sound` is the soundness of `Alg` for the version.  Each constructor builds
the derivation its alternative emits.
-/

namespace PathsFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Ctx Sub PathTy HasTy SelfFree SubDecl)

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
  | some x =>
    intro _ _
    rfl
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
  | some x =>
    intro _
    rfl
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
  | some a =>
    intro ho _
    exact hf a t1 ho
  | none =>
    intro ho h
    simpa using h ho

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
  · have hk2 : (k ⟨t.left - c, false⟩).2.out = false := by
      rw [h]
      exact ho
    have := hk _ hk2
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

/-! ## Lookup premises

A lookup premise names a lookup on the tank and a property of an item.  The
lookup, run from some full tank, ends unmarked and finds such an item.  A
framed lookup that ends unmarked finds the same items from every tank on which
it ends unmarked.  So the step, which runs the lookup on its own tank, finds
the item whenever it ends unmarked. -/

/-- The lookup `c`, run from some full tank, ends unmarked and finds an item
with the property `P`. -/
def Found {α : Type} (c : Fu (List α)) (P : α → Prop) : Prop :=
  ∃ n, (c ⟨n, false⟩).2.out = false ∧ ∃ a ∈ (c ⟨n, false⟩).1, P a

/-- A lookup premise read off one run of the lookup and a test of its items.
Both hypotheses are decidable, so the kernel checks them on an example. -/
theorem Found.of_any {α : Type} {c : Fu (List α)} {P : α → Prop} (n : Nat) (b : α → Bool)
    (ho : (c ⟨n, false⟩).2.out = false) (h : (c ⟨n, false⟩).1.any b = true)
    (hb : ∀ a, b a = true → P a) : Found c P := by
  obtain ⟨a, ha, hba⟩ := List.any_eq_true.mp h
  exact ⟨n, ho, a, ha, hb a hba⟩

/-- A framed computation that ends unmarked from two tanks gives the same
value from both. -/
theorem framed_same {α : Type} {c : Fu α} (hc : Framed c) {n : Nat} {t : Tank}
    (h1 : (c ⟨n, false⟩).2.out = false) (h2 : (c t).2.out = false) :
    (c t).1 = (c ⟨n, false⟩).1 := by
  have ht : t.out = false := hc.start rfl h2
  have e1 := hc.shift ⟨n, false⟩ _ _ rfl h1 t.left
  have e2 := hc.shift t _ _ rfl h2 n
  have hu : (⟨n, false⟩ : Tank).add t.left = t.add n := by
    obtain ⟨l, o⟩ := t
    simp only at ht
    subst ht
    simp only [Tank.add, Tank.mk.injEq, and_true]
    omega
  rw [hu, e2] at e1
  exact (Prod.mk.inj e1).1

/-- A lookup, then a computation on the items found, answers when the
computation does on every list that holds an item with the property. -/
theorem found_ans {α β : Type} {c : Fu (List α)} {P : α → Prop} {k : List α → Fu (Option β)}
    (hc : Framed c) (hP : Found c P) (hk : ∀ l, Framed (k l))
    (hans : ∀ l, (∃ a ∈ l, P a) → Ans (k l)) : Ans (Fu.bind c k) := by
  obtain ⟨n, hn, hmem⟩ := hP
  intro t ho
  have hd : Fu.bind c k t = k (c t).1 (c t).2 := rfl
  rw [hd] at ho ⊢
  have ht1 : (c t).2.out = false := (hk _).start rfl ho
  have hl : (c t).1 = (c ⟨n, false⟩).1 := framed_same hc hn ht1
  revert ho
  rw [hl]
  exact hans _ hmem _

/-- `q` has the member `A : lo..hi`. -/
def MemberP {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) (lo hi : Ty s) : Prop :=
  Found (declsF Γ q A) fun m => m.lo = lo ∧ m.hi = hi

/-- `W` is a declared type of `q`. -/
def StartP {s : Sig} (Γ : Ctx s) (q : Path s) (W : Ty s) : Prop :=
  Found (startF Γ q) fun w => w.ty = W

/-- `p`, seen at `W`, has a stable field `a`. -/
def VfldP {s : Sig} (Γ : Ctx s) (p : Path s) (W : Ty s) (a : Label) : Prop :=
  Found (lookF Γ p W (.vfld a)) fun e => (e.vfld? a).isSome = true

/-- `q`, seen at `W`, has the singleton `r.type`. -/
def SnglP {s : Sig} (Γ : Ctx s) (q : Path s) (W : Ty s) (r : Path s) : Prop :=
  Found (lookF Γ q W .sngl) fun e => e.ty = .sngl r

/-- A member premise read off one lookup, as pairs of bounds. -/
theorem MemberP.of_mem {s : Sig} {Γ : Ctx s} {q : Path s} {A : Label} {lo hi : Ty s} (n : Nat)
    (ho : (declsF Γ q A ⟨n, false⟩).2.out = false)
    (h : (lo, hi) ∈ (declsF Γ q A ⟨n, false⟩).1.map fun m => (m.lo, m.hi)) :
    MemberP Γ q A lo hi := by
  obtain ⟨m, hm, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, m, hm, (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩

/-- A declared type read off one lookup. -/
theorem StartP.of_mem {s : Sig} {Γ : Ctx s} {q : Path s} {W : Ty s} (n : Nat)
    (ho : (startF Γ q ⟨n, false⟩).2.out = false)
    (h : W ∈ (startF Γ q ⟨n, false⟩).1.map (·.ty)) : StartP Γ q W := by
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  exact ⟨n, ho, w, hw, he⟩

/-- A member premise gives the path's typing at the member. -/
theorem MemberP.d {s : Sig} {Γ : Ctx s} {q : Path s} {A : Label} {lo hi : Ty s}
    (h : MemberP Γ q A lo hi) : Nonempty (PathTy Γ q (.typ A lo hi)) := by
  obtain ⟨_, _, ⟨lo', hi', d⟩, _, rfl, rfl⟩ := h
  exact ⟨d⟩

/-- A declared type premise gives the path's typing at it. -/
theorem StartP.d {s : Sig} {Γ : Ctx s} {q : Path s} {W : Ty s} (h : StartP Γ q W) :
    Nonempty (PathTy Γ q W) := by
  obtain ⟨_, _, ⟨W', d⟩, _, rfl⟩ := h
  exact ⟨d⟩

/-- A found singleton reads as one. -/
theorem FoundP.sngl?_of {s : Sig} {Γ : Ctx s} {q : Path s} {W : Ty s} {r : Path s}
    (e : FoundP Γ q W) (h : e.ty = .sngl r) : ∃ g, e.sngl? = some g ∧ g.1 = r := by
  obtain ⟨ty, f⟩ := e
  simp only at h
  subst h
  exact ⟨_, rfl, rfl⟩

/-! ## The walker's questions

The walker of the abstract view asks the subtyping oracle only at a self-free
step whose two sides are weakenings.  `SfAsks X Y ps` says that the step from
`X` to `Y` succeeds when the subtypings `ps` hold.  `DeclAsks L R ps` says the
same of the view of the body `L` at the body `R`, one rule per case of the
walker. -/

/-- The self-free steps, with the subtypings each asks. -/
inductive SfAsks {s : Sig} : Ty (s,x) → Ty (s,x) → List (Ty s × Ty s) → Prop
  | refl {X : Ty (s,x)} : SfAsks X X []
  | bot {Y : Ty (s,x)} : SfAsks .bot Y []
  | top {X : Ty (s,x)} : SfAsks X .top []
  | closed (X Y : Ty s) : SfAsks X.weaken Y.weaken [(X, Y)]

/-- The abstract view of `L` at `R`, with the subtypings it asks. -/
inductive DeclAsks {s : Sig} (L : Ty (s,x)) : Ty (s,x) → List (Ty s × Ty s) → Prop
  | top : DeclAsks L .top []
  | typ {A : Label} {S1 T1 S2 T2 : Ty (s,x)} {ps1 ps2 : List (Ty s × Ty s)} :
      L.lookupTypDecl A = some (S1, T1) → SfAsks S2 S1 ps1 → SfAsks T1 T2 ps2 →
      DeclAsks L (.typ A S2 T2) (ps1 ++ ps2)
  | fld {a : Label} {T1 T2 : Ty (s,x)} {ps : List (Ty s × Ty s)} :
      L.lookupFldDecl a = some T1 → SfAsks T1 T2 ps → DeclAsks L (.fld a T2) ps
  | vfldFld {a : Label} {T1 T2 : Ty (s,x)} {ps : List (Ty s × Ty s)} :
      L.lookupVfldDecl a = some T1 → SfAsks T1 T2 ps → DeclAsks L (.fld a T2) ps
  | vfld {a : Label} {T1 T2 : Ty (s,x)} {ps : List (Ty s × Ty s)} :
      L.lookupVfldDecl a = some T1 → SfAsks T1 T2 ps → DeclAsks L (.vfld a T2) ps
  | and {R1 R2 : Ty (s,x)} {ps1 ps2 : List (Ty s × Ty s)} :
      DeclAsks L R1 ps1 → DeclAsks L R2 ps2 → DeclAsks L (.and R1 R2) (ps1 ++ ps2)

section WalkerAns

variable {s : Sig} {Γ : Ctx s}

/-- A self-free step answers when the oracle answers what it asks. -/
theorem selfFree?_ans {o : SubO Γ} {X Y : Ty (s,x)} {ps : List (Ty s × Ty s)} (h : SfAsks X Y ps)
    (hp : ∀ pr ∈ ps, Ans (o pr.1 pr.2)) : Ans (selfFree? o X Y) := by
  cases h with
  | refl =>
    unfold selfFree?
    rw [dif_pos rfl]
    exact ans_ret rfl
  | bot =>
    unfold selfFree?
    split
    · exact ans_ret rfl
    · rw [dif_pos rfl]
      exact ans_ret rfl
  | top =>
    unfold selfFree?
    split
    · exact ans_ret rfl
    · split
      · exact ans_ret rfl
      · rw [dif_pos rfl]
        exact ans_ret rfl
  | closed X' Y' =>
    unfold selfFree?
    split
    · exact ans_ret rfl
    · split
      · exact ans_ret rfl
      · split
        · exact ans_ret rfl
        · rw [tyStrengthenW?_weaken, tyStrengthenW?_weaken]
          exact ans_mapO (hp _ (List.mem_singleton.mpr rfl))

theorem subDecl?_and {o : SubO Γ} {L R1 R2 : Ty (s,x)} :
    subDecl? o L (.and R1 R2) =
      bindO (subDecl? o L R1) fun e1 => bindO (subDecl? o L R2) fun e2 => Fu.ret (some (.and e1 e2)) := by
  have h1 : andDepth R1 ≤ max (andDepth R1) (andDepth R2) := Nat.le_max_left _ _
  have h2 : andDepth R2 ≤ max (andDepth R1) (andDepth R2) := Nat.le_max_right _ _
  change subDeclAt o L (max (andDepth R1) (andDepth R2) + 1) (.and R1 R2) = _
  simp only [subDeclAt]
  rw [subDeclAt_eq h1, subDeclAt_eq h2]

/-- The walker answers when the oracle answers what the view asks. -/
theorem subDecl?_ans {o : SubO Γ} {L R : Ty (s,x)} {ps : List (Ty s × Ty s)} (h : DeclAsks L R ps)
    (hp : ∀ pr ∈ ps, Ans (o pr.1 pr.2)) : Ans (subDecl? o L R) := by
  induction h with
  | top => exact ans_ret rfl
  | @typ A S1 T1 S2 T2 ps1 ps2 hl h1 h2 =>
    change Ans (subDeclLeaf? o L (.typ A S2 T2))
    simp only [subDeclLeaf?]
    split
    · rename_i S1' T1' hl'
      rw [hl] at hl'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl')
      exact ans_bindO (selfFree?_ans h1 fun pr hpr => hp pr (List.mem_append_left _ hpr))
        fun _ => ans_bindO (selfFree?_ans h2 fun pr hpr => hp pr (List.mem_append_right _ hpr))
          fun _ => ans_ret rfl
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
  | @fld a T1 T2 ps hl h1 =>
    change Ans (subDeclLeaf? o L (.fld a T2))
    simp only [subDeclLeaf?]
    refine ans_orElse_left ?_
    split
    · rename_i T1' hl'
      rw [hl] at hl'
      cases hl'
      exact ans_bindO (selfFree?_ans h1 hp) fun _ => ans_ret rfl
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
  | @vfldFld a T1 T2 ps hl h1 =>
    change Ans (subDeclLeaf? o L (.fld a T2))
    simp only [subDeclLeaf?]
    refine ans_orElse_right ?_
    split
    · rename_i T1' hl'
      rw [hl] at hl'
      cases hl'
      exact ans_bindO (selfFree?_ans h1 hp) fun _ => ans_ret rfl
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
  | @vfld a T1 T2 ps hl h1 =>
    change Ans (subDeclLeaf? o L (.vfld a T2))
    simp only [subDeclLeaf?]
    split
    · rename_i T1' hl'
      rw [hl] at hl'
      cases hl'
      exact ans_bindO (selfFree?_ans h1 hp) fun _ => ans_ret rfl
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
  | and _ _ ih1 ih2 =>
    rw [subDecl?_and]
    exact ans_bindO (ih1 fun pr hpr => hp pr (List.mem_append_left _ hpr))
      fun _ => ans_bindO (ih2 fun pr hpr => hp pr (List.mem_append_right _ hpr)) fun _ => ans_ret rfl

/-- A self-free step holds when the subtypings it asks do. -/
theorem SfAsks.sound {X Y : Ty (s,x)} {ps : List (Ty s × Ty s)} (h : SfAsks X Y ps)
    (hp : ∀ pr ∈ ps, Nonempty (Sub Γ pr.1 pr.2)) : Nonempty (SelfFree Γ X Y) := by
  cases h with
  | refl => exact ⟨.refl⟩
  | bot => exact ⟨.bot⟩
  | top => exact ⟨.top⟩
  | closed X' Y' =>
    obtain ⟨e⟩ := hp _ (List.mem_singleton.mpr rfl)
    exact ⟨.closed e⟩

/-- The abstract view holds when the subtypings it asks do. -/
theorem DeclAsks.sound {L R : Ty (s,x)} {ps : List (Ty s × Ty s)} (h : DeclAsks L R ps)
    (hp : ∀ pr ∈ ps, Nonempty (Sub Γ pr.1 pr.2)) : Nonempty (SubDecl Γ L R) := by
  induction h with
  | top => exact ⟨.top⟩
  | typ hl h1 h2 =>
    obtain ⟨e1⟩ := h1.sound fun pr hpr => hp pr (List.mem_append_left _ hpr)
    obtain ⟨e2⟩ := h2.sound fun pr hpr => hp pr (List.mem_append_right _ hpr)
    exact ⟨.typ hl e1 e2⟩
  | fld hl h1 =>
    obtain ⟨e⟩ := h1.sound hp
    exact ⟨.fld hl e⟩
  | vfldFld hl h1 =>
    obtain ⟨e⟩ := h1.sound hp
    exact ⟨.vfldToFld hl e⟩
  | vfld hl h1 =>
    obtain ⟨e⟩ := h1.sound hp
    exact ⟨.vfld hl e⟩
  | and _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1 fun pr hpr => hp pr (List.mem_append_left _ hpr)
    obtain ⟨e2⟩ := ih2 fun pr hpr => hp pr (List.mem_append_right _ hpr)
    exact ⟨.and e1 e2⟩

end WalkerAns

/-! ## The judgment -/

/-- The algorithm's rules, one constructor per alternative of `subStep`,
`pathStep` and `varStep`, with no fuel and no pending goals. -/
inductive Alg : G → Prop
  -- `sub`
  | refl {s : Sig} {Γ : Ctx s} {T : Ty s} : Alg ⟨s, Γ, .sub T T⟩
  | top {s : Sig} {Γ : Ctx s} {S : Ty s} : Alg ⟨s, Γ, .sub S .top⟩
  | bot {s : Sig} {Γ : Ctx s} {T : Ty s} : Alg ⟨s, Γ, .sub .bot T⟩
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Ty s} :
      Alg ⟨s, Γ, .sub S T1⟩ → Alg ⟨s, Γ, .sub S T2⟩ → Alg ⟨s, Γ, .sub S (.and T1 T2)⟩
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Ty s} {q : Path s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .sub S lo⟩ → Alg ⟨s, Γ, .sub S (.sel q A)⟩
  | fld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Alg ⟨s, Γ, .sub S T⟩ → Alg ⟨s, Γ, .sub (.fld a S) (.fld a T)⟩
  | vfld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Alg ⟨s, Γ, .sub S T⟩ → Alg ⟨s, Γ, .sub (.vfld a S) (.vfld a T)⟩
  | vfldFld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Alg ⟨s, Γ, .sub S T⟩ → Alg ⟨s, Γ, .sub (.vfld a S) (.fld a T)⟩
  | typ {s : Sig} {Γ : Ctx s} {S1 S2 T1 T2 : Ty s} {A : Label} :
      Alg ⟨s, Γ, .sub S2 S1⟩ → Alg ⟨s, Γ, .sub T1 T2⟩ →
      Alg ⟨s, Γ, .sub (.typ A S1 T1) (.typ A S2 T2)⟩
  | all {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T1 T2 : Ty (s,x)} :
      Alg ⟨s, Γ, .sub S2 S1⟩ → Alg ⟨_, Γ.cons S2, .sub T1 T2⟩ →
      Alg ⟨s, Γ, .sub (.all S1 T1) (.all S2 T2)⟩
  | mu {s : Sig} {Γ : Ctx s} {D1 D2 : Ty (s,x)} {ps : List (Ty s × Ty s)} :
      Ty.Decl D1 → Ty.Decl D2 → DeclAsks D1 D2 ps → (∀ pr ∈ ps, Alg ⟨s, Γ, .sub pr.1 pr.2⟩) →
      Alg ⟨s, Γ, .sub (.mu D1) (.mu D2)⟩
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Ty s} {q : Path s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .sub hi T⟩ → Alg ⟨s, Γ, .sub (.sel q B) T⟩
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .sub S1 T⟩ → Alg ⟨s, Γ, .sub (.and S1 S2) T⟩
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .sub S2 T⟩ → Alg ⟨s, Γ, .sub (.and S1 S2) T⟩
  -- `path`
  | pRefl {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} : Alg ⟨s, Γ, .path p T T⟩
  | pSelf {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} : Alg ⟨s, Γ, .path p V (.sngl p)⟩
  | pAndR {s : Sig} {Γ : Ctx s} {p : Path s} {V T1 T2 : Ty s} :
      Alg ⟨s, Γ, .path p V T1⟩ → Alg ⟨s, Γ, .path p V T2⟩ → Alg ⟨s, Γ, .path p V (.and T1 T2)⟩
  | pPre {s : Sig} {Γ : Ctx s} {p q : Path s} {V W : Ty s} {a : Label} :
      StartP Γ p W → VfldP Γ p W a → Alg ⟨s, Γ, .path p W (.sngl q)⟩ →
      Alg ⟨s, Γ, .path (.sel p a) V (.sngl (.sel q a))⟩
  | pAlias {s : Sig} {Γ : Ctx s} {p q r : Path s} {V W : Ty s} :
      StartP Γ q W → SnglP Γ q W r → Alg ⟨s, Γ, .path p V (.sngl r)⟩ →
      Alg ⟨s, Γ, .path p V (.sngl q)⟩
  | pMuR {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} {B : Ty (s,x)} :
      Ty.Decl B → Alg ⟨s, Γ, .path p V (B.substPath p)⟩ → Alg ⟨s, Γ, .path p V (.mu B)⟩
  | pSelLo {s : Sig} {Γ : Ctx s} {p q : Path s} {V lo hi : Ty s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .path p V lo⟩ →
      Alg ⟨s, Γ, .path p V (.sel q A)⟩
  | pMuL {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Ty.Decl B → Alg ⟨s, Γ, .path p (B.substPath p) T⟩ →
      Alg ⟨s, Γ, .path p (.mu B) T⟩
  | pAnd1 {s : Sig} {Γ : Ctx s} {p : Path s} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .path p V1 T⟩ → Alg ⟨s, Γ, .path p (.and V1 V2) T⟩
  | pAnd2 {s : Sig} {Γ : Ctx s} {p : Path s} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .path p V2 T⟩ → Alg ⟨s, Γ, .path p (.and V1 V2) T⟩
  | pSelHi {s : Sig} {Γ : Ctx s} {p q : Path s} {T lo hi : Ty s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .path p hi T⟩ →
      Alg ⟨s, Γ, .path p (.sel q B) T⟩
  | pSnglL {s : Sig} {Γ : Ctx s} {p q : Path s} {T W : Ty s} :
      StartP Γ q W → isAnd T = false → Alg ⟨s, Γ, .path p W T⟩ → Alg ⟨s, Γ, .path p (.sngl q) T⟩
  | pAtom {s : Sig} {Γ : Ctx s} {p : Path s} {V T : Ty s} :
      isAtom V = true → isAnd T = false → Alg ⟨s, Γ, .sub V T⟩ → Alg ⟨s, Γ, .path p V T⟩
  -- `var`
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Alg ⟨s, Γ, .var x T T⟩
  | vSngl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {q : Path s} :
      Alg ⟨s, Γ, .path (.var x) V (.sngl q)⟩ → Alg ⟨s, Γ, .var x V (.sngl q)⟩
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T1 T2 : Ty s} :
      Alg ⟨s, Γ, .var x V T1⟩ → Alg ⟨s, Γ, .var x V T2⟩ → Alg ⟨s, Γ, .var x V (.and T1 T2)⟩
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {B : Ty (s,x)} :
      Ty.Decl B → Alg ⟨s, Γ, .var x V (B.substVar x)⟩ → Alg ⟨s, Γ, .var x V (.mu B)⟩
  | vSelLo {s : Sig} {Γ : Ctx s} {x : BVar s .var} {q : Path s} {V lo hi : Ty s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot → Alg ⟨s, Γ, .var x V lo⟩ → Alg ⟨s, Γ, .var x V (.sel q A)⟩
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Ty.Decl B → Alg ⟨s, Γ, .var x (B.substVar x) T⟩ →
      Alg ⟨s, Γ, .var x (.mu B) T⟩
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .var x V1 T⟩ → Alg ⟨s, Γ, .var x (.and V1 V2) T⟩
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Alg ⟨s, Γ, .var x V2 T⟩ → Alg ⟨s, Γ, .var x (.and V1 V2) T⟩
  | vSelHi {s : Sig} {Γ : Ctx s} {x : BVar s .var} {q : Path s} {T lo hi : Ty s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false → Alg ⟨s, Γ, .var x hi T⟩ →
      Alg ⟨s, Γ, .var x (.sel q B) T⟩
  | vAtom {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isVAtom V = true → isAnd T = false → Alg ⟨s, Γ, .sub V T⟩ → Alg ⟨s, Γ, .var x V T⟩

/-- The subtyping goals a list of pairs asks in `Γ`. -/
def subGoals {s : Sig} (Γ : Ctx s) (ps : List (Ty s × Ty s)) : List G :=
  ps.map fun pr => ⟨s, Γ, .sub pr.1 pr.2⟩

/-- One step of `Alg`: the goal follows from the premises listed by one
alternative.  The constructors are those of `Alg`. -/
inductive Rule : G → List G → Prop
  | refl {s : Sig} {Γ : Ctx s} {T : Ty s} : Rule ⟨s, Γ, .sub T T⟩ []
  | top {s : Sig} {Γ : Ctx s} {S : Ty s} : Rule ⟨s, Γ, .sub S .top⟩ []
  | bot {s : Sig} {Γ : Ctx s} {T : Ty s} : Rule ⟨s, Γ, .sub .bot T⟩ []
  | andR {s : Sig} {Γ : Ctx s} {S T1 T2 : Ty s} :
      Rule ⟨s, Γ, .sub S (.and T1 T2)⟩ [⟨s, Γ, .sub S T1⟩, ⟨s, Γ, .sub S T2⟩]
  | selLo {s : Sig} {Γ : Ctx s} {S lo hi : Ty s} {q : Path s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot → Rule ⟨s, Γ, .sub S (.sel q A)⟩ [⟨s, Γ, .sub S lo⟩]
  | fld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Rule ⟨s, Γ, .sub (.fld a S) (.fld a T)⟩ [⟨s, Γ, .sub S T⟩]
  | vfld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Rule ⟨s, Γ, .sub (.vfld a S) (.vfld a T)⟩ [⟨s, Γ, .sub S T⟩]
  | vfldFld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} :
      Rule ⟨s, Γ, .sub (.vfld a S) (.fld a T)⟩ [⟨s, Γ, .sub S T⟩]
  | typ {s : Sig} {Γ : Ctx s} {S1 S2 T1 T2 : Ty s} {A : Label} :
      Rule ⟨s, Γ, .sub (.typ A S1 T1) (.typ A S2 T2)⟩ [⟨s, Γ, .sub S2 S1⟩, ⟨s, Γ, .sub T1 T2⟩]
  | all {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T1 T2 : Ty (s,x)} :
      Rule ⟨s, Γ, .sub (.all S1 T1) (.all S2 T2)⟩ [⟨s, Γ, .sub S2 S1⟩, ⟨_, Γ.cons S2, .sub T1 T2⟩]
  | mu {s : Sig} {Γ : Ctx s} {D1 D2 : Ty (s,x)} {ps : List (Ty s × Ty s)} :
      Ty.Decl D1 → Ty.Decl D2 → DeclAsks D1 D2 ps →
      Rule ⟨s, Γ, .sub (.mu D1) (.mu D2)⟩ (subGoals Γ ps)
  | selHi {s : Sig} {Γ : Ctx s} {T lo hi : Ty s} {q : Path s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false → Rule ⟨s, Γ, .sub (.sel q B) T⟩ [⟨s, Γ, .sub hi T⟩]
  | and1 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.and S1 S2) T⟩ [⟨s, Γ, .sub S1 T⟩]
  | and2 {s : Sig} {Γ : Ctx s} {S1 S2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .sub (.and S1 S2) T⟩ [⟨s, Γ, .sub S2 T⟩]
  | pRefl {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} : Rule ⟨s, Γ, .path p T T⟩ []
  | pSelf {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} : Rule ⟨s, Γ, .path p V (.sngl p)⟩ []
  | pAndR {s : Sig} {Γ : Ctx s} {p : Path s} {V T1 T2 : Ty s} :
      Rule ⟨s, Γ, .path p V (.and T1 T2)⟩ [⟨s, Γ, .path p V T1⟩, ⟨s, Γ, .path p V T2⟩]
  | pPre {s : Sig} {Γ : Ctx s} {p q : Path s} {V W : Ty s} {a : Label} :
      StartP Γ p W → VfldP Γ p W a →
      Rule ⟨s, Γ, .path (.sel p a) V (.sngl (.sel q a))⟩ [⟨s, Γ, .path p W (.sngl q)⟩]
  | pAlias {s : Sig} {Γ : Ctx s} {p q r : Path s} {V W : Ty s} :
      StartP Γ q W → SnglP Γ q W r →
      Rule ⟨s, Γ, .path p V (.sngl q)⟩ [⟨s, Γ, .path p V (.sngl r)⟩]
  | pMuR {s : Sig} {Γ : Ctx s} {p : Path s} {V : Ty s} {B : Ty (s,x)} :
      Ty.Decl B → Rule ⟨s, Γ, .path p V (.mu B)⟩ [⟨s, Γ, .path p V (B.substPath p)⟩]
  | pSelLo {s : Sig} {Γ : Ctx s} {p q : Path s} {V lo hi : Ty s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot →
      Rule ⟨s, Γ, .path p V (.sel q A)⟩ [⟨s, Γ, .path p V lo⟩]
  | pMuL {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Ty.Decl B →
      Rule ⟨s, Γ, .path p (.mu B) T⟩ [⟨s, Γ, .path p (B.substPath p) T⟩]
  | pAnd1 {s : Sig} {Γ : Ctx s} {p : Path s} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .path p (.and V1 V2) T⟩ [⟨s, Γ, .path p V1 T⟩]
  | pAnd2 {s : Sig} {Γ : Ctx s} {p : Path s} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .path p (.and V1 V2) T⟩ [⟨s, Γ, .path p V2 T⟩]
  | pSelHi {s : Sig} {Γ : Ctx s} {p q : Path s} {T lo hi : Ty s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false →
      Rule ⟨s, Γ, .path p (.sel q B) T⟩ [⟨s, Γ, .path p hi T⟩]
  | pSnglL {s : Sig} {Γ : Ctx s} {p q : Path s} {T W : Ty s} :
      StartP Γ q W → isAnd T = false → Rule ⟨s, Γ, .path p (.sngl q) T⟩ [⟨s, Γ, .path p W T⟩]
  | pAtom {s : Sig} {Γ : Ctx s} {p : Path s} {V T : Ty s} :
      isAtom V = true → isAnd T = false → Rule ⟨s, Γ, .path p V T⟩ [⟨s, Γ, .sub V T⟩]
  | vRefl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} : Rule ⟨s, Γ, .var x T T⟩ []
  | vSngl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {q : Path s} :
      Rule ⟨s, Γ, .var x V (.sngl q)⟩ [⟨s, Γ, .path (.var x) V (.sngl q)⟩]
  | vAndR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T1 T2 : Ty s} :
      Rule ⟨s, Γ, .var x V (.and T1 T2)⟩ [⟨s, Γ, .var x V T1⟩, ⟨s, Γ, .var x V T2⟩]
  | vMuR {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V : Ty s} {B : Ty (s,x)} :
      Ty.Decl B → Rule ⟨s, Γ, .var x V (.mu B)⟩ [⟨s, Γ, .var x V (B.substVar x)⟩]
  | vSelLo {s : Sig} {Γ : Ctx s} {x : BVar s .var} {q : Path s} {V lo hi : Ty s} {A : Label} :
      MemberP Γ q A lo hi → lo ≠ .bot → Rule ⟨s, Γ, .var x V (.sel q A)⟩ [⟨s, Γ, .var x V lo⟩]
  | vMuL {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {B : Ty (s,x)} :
      isAnd T = false → Ty.Decl B →
      Rule ⟨s, Γ, .var x (.mu B) T⟩ [⟨s, Γ, .var x (B.substVar x) T⟩]
  | vAnd1 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .var x (.and V1 V2) T⟩ [⟨s, Γ, .var x V1 T⟩]
  | vAnd2 {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V1 V2 T : Ty s} :
      isAnd T = false → Rule ⟨s, Γ, .var x (.and V1 V2) T⟩ [⟨s, Γ, .var x V2 T⟩]
  | vSelHi {s : Sig} {Γ : Ctx s} {x : BVar s .var} {q : Path s} {T lo hi : Ty s} {B : Label} :
      MemberP Γ q B lo hi → isAnd T = false →
      Rule ⟨s, Γ, .var x (.sel q B) T⟩ [⟨s, Γ, .var x hi T⟩]
  | vAtom {s : Sig} {Γ : Ctx s} {x : BVar s .var} {V T : Ty s} :
      isVAtom V = true → isAnd T = false → Rule ⟨s, Γ, .var x V T⟩ [⟨s, Γ, .sub V T⟩]

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

theorem forall_subGoals {s : Sig} {Γ : Ctx s} {ps : List (Ty s × Ty s)} {P : G → Prop}
    (h : ∀ pr ∈ ps, P ⟨s, Γ, .sub pr.1 pr.2⟩) : ∀ g ∈ subGoals Γ ps, P g := by
  intro g hg
  obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hg
  exact h pr hpr

theorem of_forall_subGoals {s : Sig} {Γ : Ctx s} {ps : List (Ty s × Ty s)} {P : G → Prop}
    (h : ∀ g ∈ subGoals Γ ps, P g) : ∀ pr ∈ ps, P ⟨s, Γ, .sub pr.1 pr.2⟩ :=
  fun pr hpr => h _ (List.mem_map.mpr ⟨pr, hpr, rfl⟩)

/-- A list holds an item on which `f` answers, so `findSome?` answers. -/
theorem findSome?_isSome {β : Type} {f : α → Option β} {a : α} (hf : (f a).isSome = true) :
    ∀ l : List α, a ∈ l → (l.findSome? f).isSome = true
  | [], h => by cases h
  | b :: l, h => by
    simp only [List.findSome?]
    cases hb : f b with
    | some _ => rfl
    | none =>
      rcases List.mem_cons.mp h with rfl | h
      · rw [hb] at hf
        cases hf
      · exact findSome?_isSome hf l h

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
  | vfld _ ih => exact .mk .vfld (forall_mem_one ih)
  | vfldFld _ ih => exact .mk .vfldFld (forall_mem_one ih)
  | typ _ _ ih1 ih2 => exact .mk .typ (forall_mem_two ih1 ih2)
  | all _ _ ih1 ih2 => exact .mk .all (forall_mem_two ih1 ih2)
  | mu h1 h2 hw _ ih => exact .mk (.mu h1 h2 hw) (forall_subGoals ih)
  | selHi hm hT _ ih => exact .mk (.selHi hm hT) (forall_mem_one ih)
  | and1 hT _ ih => exact .mk (.and1 hT) (forall_mem_one ih)
  | and2 hT _ ih => exact .mk (.and2 hT) (forall_mem_one ih)
  | pRefl => exact .mk .pRefl fun _ h => by cases h
  | pSelf => exact .mk .pSelf fun _ h => by cases h
  | pAndR _ _ ih1 ih2 => exact .mk .pAndR (forall_mem_two ih1 ih2)
  | pPre hw hv _ ih => exact .mk (.pPre hw hv) (forall_mem_one ih)
  | pAlias hw he _ ih => exact .mk (.pAlias hw he) (forall_mem_one ih)
  | pMuR hd _ ih => exact .mk (.pMuR hd) (forall_mem_one ih)
  | pSelLo hm hlo _ ih => exact .mk (.pSelLo hm hlo) (forall_mem_one ih)
  | pMuL hT hd _ ih => exact .mk (.pMuL hT hd) (forall_mem_one ih)
  | pAnd1 hT _ ih => exact .mk (.pAnd1 hT) (forall_mem_one ih)
  | pAnd2 hT _ ih => exact .mk (.pAnd2 hT) (forall_mem_one ih)
  | pSelHi hm hT _ ih => exact .mk (.pSelHi hm hT) (forall_mem_one ih)
  | pSnglL hw hT _ ih => exact .mk (.pSnglL hw hT) (forall_mem_one ih)
  | pAtom ha hT _ ih => exact .mk (.pAtom ha hT) (forall_mem_one ih)
  | vRefl => exact .mk .vRefl fun _ h => by cases h
  | vSngl _ ih => exact .mk .vSngl (forall_mem_one ih)
  | vAndR _ _ ih1 ih2 => exact .mk .vAndR (forall_mem_two ih1 ih2)
  | vMuR hd _ ih => exact .mk (.vMuR hd) (forall_mem_one ih)
  | vSelLo hm hlo _ ih => exact .mk (.vSelLo hm hlo) (forall_mem_one ih)
  | vMuL hT hd _ ih => exact .mk (.vMuL hT hd) (forall_mem_one ih)
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
  | @selLo s Γ S lo hi q A hm hlo =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_left ?_))))
    refine found_ans (declsF_framed Γ q A) hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @fld s Γ S T a =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_mapO (hp _ (by simp)))
  | @vfld s Γ S T a =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos rfl (ans_mapO (hp _ (by simp)))
  | @vfldFld s Γ S T a =>
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
  | @mu s Γ D1 D2 ps h1 h2 hw =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (by simp [isAnd]) (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos h1 (ans_dite_pos h2 (ans_mapO (subDecl?_ans hw (of_forall_subGoals hp))))
  | @selHi s Γ T lo hi q B hm hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine found_ans (declsF_framed Γ q B) hm
      (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_mapO (hp _ (by simp))
  | @and1 s Γ S1 S2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @and2 s Γ S1 S2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_orElse_right
      (ans_ite_neg (not_isAnd hT) (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | pRefl =>
    exact ans_orElse_left (ans_ret (by simp [pRefl]))
  | pSelf =>
    exact ans_orElse_right (ans_orElse_left (ans_ret (by simp [pSelf])))
  | @pAndR s Γ p V T1 T2 =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_pos rfl ?_))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @pPre s Γ p q V W a hw hv =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_left ?_)))
    refine ans_dite_pos rfl ?_
    refine found_ans (startF_framed Γ p) hw (fun _ => firstSome_framed (fun _ =>
      bindO_framed (hF _) fun _ => bind_framed (lookF_framed _ _ _ _) fun _ => ret_framed _) _) ?_
    rintro ws ⟨⟨ty, d⟩, hmem, hty⟩
    simp only at hty
    subst hty
    refine ans_firstSome ?_ ws hmem
    refine ans_bindO (hp _ (by simp)) fun f => ?_
    refine found_ans (lookF_framed Γ p ty (.vfld a)) hv (fun _ => ret_framed _) ?_
    rintro es ⟨e, he, hsome⟩
    refine ans_ret (findSome?_isSome ?_ es he)
    rw [Option.isSome_map]
    exact hsome
  | @pAlias s Γ p q r V W hw hs =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_left ?_))))
    refine found_ans (startF_framed Γ q) hw (fun ws => firstSome_framed (fun w => ?_) ws) ?_
    · refine bind_framed (lookF_framed Γ q w.ty .sngl) fun es => firstSome_framed (fun e => ?_) es
      dsimp only
      split
      · exact mapO_framed _ (hF _)
      · exact ret_framed _
    rintro ws ⟨⟨ty, d⟩, hmem, hty⟩
    simp only at hty
    subst hty
    refine ans_firstSome ?_ ws hmem
    refine found_ans (lookF_framed Γ q ty .sngl) hs (fun es => firstSome_framed (fun e => ?_) es) ?_
    · dsimp only
      split
      · exact mapO_framed _ (hF _)
      · exact ret_framed _
    rintro es ⟨e, he, hty⟩
    refine ans_firstSome ?_ es he
    obtain ⟨g, hg, rfl⟩ := e.sngl?_of hty
    simp only [hg]
    exact ans_mapO (hp _ (by simp))
  | @pMuR s Γ p V B hd =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos hd (ans_mapO (hp _ (by simp)))
  | @pSelLo s Γ p q V lo hi A hm hlo =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    refine found_ans (declsF_framed Γ q A) hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @pMuL s Γ p T B hT hd =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_left ?_)))))))
    exact ans_dite_pos hd (ans_mapO (hp _ (by simp)))
  | @pAnd1 s Γ p V1 V2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_left ?_))))))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @pAnd2 s Γ p V1 V2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_left ?_))))))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | @pSelHi s Γ p q T lo hi B hm hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))))))
    refine found_ans (declsF_framed Γ q B) hm
      (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_mapO (hp _ (by simp))
  | @pSnglL s Γ p q T W hw hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))))))
    refine found_ans (startF_framed Γ q) hw
      (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ws ⟨⟨ty, d⟩, hmem, hty⟩
    simp only at hty
    subst hty
    refine ans_firstSome ?_ ws hmem
    exact ans_mapO (hp _ (by simp))
  | @pAtom s Γ p V T ha hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right ?_))))))))))
    exact ans_ite_pos ha (ans_mapO (hp _ (by simp)))
  | vRefl =>
    exact ans_orElse_left (ans_ret (by simp [vRefl]))
  | @vSngl s Γ x V q =>
    exact ans_orElse_right (ans_orElse_left (ans_mapO (hp _ (by simp))))
  | @vAndR s Γ x V T1 T2 =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_pos rfl ?_))
    exact ans_bindO (hp _ (by simp)) fun _ => ans_mapO (hp _ (by simp))
  | @vMuR s Γ x V B hd =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_left ?_)))
    exact ans_dite_pos hd (ans_mapO (hp _ (by simp)))
  | @vSelLo s Γ x q V lo hi A hm hlo =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (by simp [isAnd])
      (ans_orElse_right (ans_orElse_left ?_))))
    refine found_ans (declsF_framed Γ q A) hm (fun _ => firstSome_framed
      (fun _ => ite_framed (ret_framed _) (mapO_framed _ (hF _))) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_ite_neg hlo (ans_mapO (hp _ (by simp)))
  | @vMuL s Γ x T B hT hd =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_)))))
    exact ans_dite_pos hd (ans_mapO (hp _ (by simp)))
  | @vAnd1 s Γ x V1 V2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    exact ans_orElse_left (ans_mapO (hp _ (by simp)))
  | @vAnd2 s Γ x V1 V2 T hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_left ?_))))))
    exact ans_orElse_right (ans_mapO (hp _ (by simp)))
  | @vSelHi s Γ x q T lo hi B hm hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_left ?_)))))))
    refine found_ans (declsF_framed Γ q B) hm
      (fun _ => firstSome_framed (fun _ => mapO_framed _ (hF _)) _) ?_
    rintro ms ⟨m, hmem, rfl, rfl⟩
    refine ans_firstSome ?_ ms hmem
    exact ans_mapO (hp _ (by simp))
  | @vAtom s Γ x V T ha hT =>
    refine ans_orElse_right (ans_orElse_right (ans_ite_neg (not_isAnd hT)
      (ans_orElse_right (ans_orElse_right (ans_orElse_right (ans_orElse_right
        (ans_orElse_right ?_)))))))
    exact ans_ite_pos ha (ans_mapO (hp _ (by simp)))

/-! ## Completeness up to the recursion limit -/

/-- An `Alg` derivation is answered by the run, at every index and from every
tank on which the run ends unmarked. -/
theorem alg_run {g : G} (h : Alg g) (d : Nat) : Ans (run cost step d [] g) :=
  run_ans step_frame (fun _ _ hr o hF hp => rule_ans hr o hF hp) h.deriv.pruneNil d

theorem runF_complete {g : G} (h : Alg g) : Ans (runF g) :=
  fun t ho => alg_run h t.left t ho

theorem subF_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Ans (subF Γ S T) :=
  runF_complete h

/-- A path goal is answered from a declared type of the path that `Alg` derives
it from. -/
theorem pathF_complete {s : Sig} {Γ : Ctx s} {p : Path s} {W T : Ty s} (hw : StartP Γ p W)
    (h : Alg ⟨s, Γ, .path p W T⟩) : Ans (pathF Γ p T) := by
  refine found_ans (startF_framed Γ p) hw
    (fun _ => firstSome_framed (fun _ => mapO_framed _ (runF_framed _)) _) ?_
  rintro ws ⟨⟨ty, d⟩, hmem, hty⟩
  simp only at hty
  subst hty
  refine ans_firstSome ?_ ws hmem
  exact ans_mapO (runF_complete h)

theorem varF_complete {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩) : Ans (varF Γ x T) :=
  ans_mapO (runF_complete h)

theorem sub?_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} {n : Nat} (h : Alg ⟨s, Γ, .sub S T⟩)
    (ho : (sub? Γ S T n).2.out = false) : (sub? Γ S T n).1.isSome = true :=
  subF_complete h _ ho

theorem path?_complete {s : Sig} {Γ : Ctx s} {p : Path s} {W T : Ty s} {n : Nat}
    (hw : StartP Γ p W) (h : Alg ⟨s, Γ, .path p W T⟩) (ho : (path? Γ p T n).2.out = false) :
    (path? Γ p T n).1.isSome = true :=
  pathF_complete hw h _ ho

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
  | none =>
    rw [he] at hs
    cases hs
  | some e =>
    rw [sub?_mono he hnm]
    rfl

theorem sub?_reject {s : Sig} {Γ : Ctx s} {S T : Ty s} {n k : Nat}
    (h : sub? Γ S T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .sub S T⟩ := fun ha => by
  have := sub?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

theorem path?_reject {s : Sig} {Γ : Ctx s} {p : Path s} {W T : Ty s} {n k : Nat}
    (h : path? Γ p T n = (none, ⟨k, false⟩)) (hw : StartP Γ p W) : ¬ Alg ⟨s, Γ, .path p W T⟩ :=
  fun ha => by
    have := path?_complete hw ha (n := n) (by rw [h])
    rw [h] at this
    cases this

theorem var?_reject {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {n k : Nat}
    (h : var? Γ x T n = (none, ⟨k, false⟩)) : ¬ Alg ⟨s, Γ, .var x (Γ.lookup x) T⟩ := fun ha => by
  have := var?_complete ha (n := n) (by rw [h])
  rw [h] at this
  cases this

/-! ## Soundness -/

/-- Every goal `Alg` derives has an answer: a derivation of `S <: T`, or a map
from a derivation of `p : V` or `x : V` to one at `T`. -/
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
    obtain ⟨v⟩ := hm.d
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans e (Sub.selLower v)⟩
  | fld _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.fld e⟩
  | vfld _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.vfld e⟩
  | vfldFld _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans Sub.vfldToFld (Sub.fld e)⟩
  | typ _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Sub.typ e1 e2⟩
  | all _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨Sub.all e1 e2⟩
  | mu h1 h2 hw _ ih =>
    obtain ⟨e⟩ := hw.sound ih
    exact ⟨Sub.mu e h1 h2⟩
  | selHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.d
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans (Sub.selUpper v) e⟩
  | and1 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans Sub.and1 e⟩
  | and2 _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Sub.trans Sub.and2 e⟩
  | pRefl => exact ⟨fun d => d⟩
  | pSelf => exact ⟨fun d => PathTy.snglRefl d⟩
  | pAndR _ _ ih1 ih2 =>
    obtain ⟨f1⟩ := ih1
    obtain ⟨f2⟩ := ih2
    exact ⟨fun d => PathTy.andI (f1 d) (f2 d)⟩
  | pPre hw hv _ ih =>
    obtain ⟨d⟩ := hw.d
    obtain ⟨f⟩ := ih
    obtain ⟨_, _, e, _, hsome⟩ := hv
    obtain ⟨g, _⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨fun _ => PathTy.snglSel (f d) (g.2 d)⟩
  | pAlias hw hs _ ih =>
    obtain ⟨d⟩ := hw.d
    obtain ⟨f⟩ := ih
    obtain ⟨_, _, e, _, hty⟩ := hs
    obtain ⟨g, _, rfl⟩ := e.sngl?_of hty
    exact ⟨fun dv => PathTy.snglTrans (f dv) (PathTy.snglSym (g.2 d) (PathTy.snglInv (g.2 d)))⟩
  | pMuR hd _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => PathTy.recI (f d) hd⟩
  | pSelLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.d
    obtain ⟨f⟩ := ih
    exact ⟨fun d => PathTy.sub (f d) (Sub.selLower v)⟩
  | pMuL _ hd _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (PathTy.recE d hd)⟩
  | pAnd1 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (PathTy.sub d Sub.and1)⟩
  | pAnd2 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (PathTy.sub d Sub.and2)⟩
  | pSelHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.d
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (PathTy.sub d (Sub.selUpper v))⟩
  | pSnglL hw _ _ ih =>
    obtain ⟨w⟩ := hw.d
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (PathTy.snglTrans d w)⟩
  | pAtom _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨fun d => PathTy.sub d e⟩
  | vRefl => exact ⟨fun d => d⟩
  | vSngl _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => HasTy.sngl (f d.toPathTy)⟩
  | vAndR _ _ ih1 ih2 =>
    obtain ⟨f1⟩ := ih1
    obtain ⟨f2⟩ := ih2
    exact ⟨fun d => HasTy.andI (f1 d) (f2 d)⟩
  | vMuR hd _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => HasTy.recI (f d) hd⟩
  | vSelLo hm _ _ ih =>
    obtain ⟨v⟩ := hm.d
    obtain ⟨f⟩ := ih
    exact ⟨fun d => HasTy.sub (f d) (Sub.selLower v)⟩
  | vMuL _ hd _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.recE d hd)⟩
  | vAnd1 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d Sub.and1)⟩
  | vAnd2 _ _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d Sub.and2)⟩
  | vSelHi hm _ _ ih =>
    obtain ⟨v⟩ := hm.d
    obtain ⟨f⟩ := ih
    exact ⟨fun d => f (HasTy.sub d (Sub.selUpper v))⟩
  | vAtom _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨fun d => HasTy.sub d e⟩

theorem Alg.sound {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Alg ⟨s, Γ, .sub S T⟩) :
    Nonempty (Sub Γ S T) :=
  h.answer

/-! ## Checks

The positive checks build `Alg` derivations whose lookup premises the kernel
reads off one lookup at the default fuel.  The negative checks are rejections
read off one run with the tank unmarked, turned into `¬ Alg` by `sub?_reject`
and `var?_reject`. -/

section AlgChecks

open Paths.DotMNF.Examples

-- E8: `x.A <: {a : ⊤}` by the upper bound of `x`'s one member, read off the lookup.
theorem E8_alg : Alg ⟨_, E8Ctx2, .sub (.sel (.var (.there .here)) lA) (.fld la .top)⟩ :=
  Alg.selHi (MemberP.of_mem (lo := .bot) defaultFuel (by decide +kernel) (by decide +kernel)) rfl
    Alg.refl

-- MuS: `p.A <: {B : p.C .. p.C}` under `p : q.type`.  The member `A` of `p` is read with
-- `q`'s self type opened at `p`.
theorem MuS_alg : Alg ⟨_, MuSCtx, .sub (.sel (.var .here) lA)
    (.typ lB (.sel (.var .here) lC) (.sel (.var .here) lC))⟩ :=
  Alg.selHi (MemberP.of_mem (lo := .bot) defaultFuel (by decide +kernel) (by decide +kernel)) rfl
    Alg.refl

-- MuP: `p : {a : p.A}` under `p : q.type`.  The singleton is widened to `q`'s declared type,
-- the recursive type is opened at `p`, and its right operand is the goal.
theorem MuP_alg : Alg ⟨_, MuPCtx, .path (.var .here) (.sngl (.var (.there .here)))
    (.fld la (.sel (.var .here) lA))⟩ :=
  Alg.pSnglL (W := MuPCtx.lookup (.there .here))
    (StartP.of_mem defaultFuel (by decide +kernel) (by decide +kernel)) rfl
    (Alg.pMuL rfl (.and .typ .fld) (Alg.pAnd2 rfl Alg.pRefl))

-- So the run answers MuP at every fuel at which it ends unmarked, here the default one.
example : (path? MuPCtx (.var .here) (.fld la (.sel (.var .here) lA))).1.isSome = true :=
  path?_complete (StartP.of_mem defaultFuel (by decide +kernel) (by decide +kernel)) MuP_alg
    (by decide +kernel)

-- In `x : {val a : ⊤}`, `y : x.type`: `x : y.type` by the alias of `y`, and
-- `y.a : (x.a).type` by the prefix `y : x.type` and the stable field `a` of `y`.
theorem SgAlias_alg : Alg ⟨_, SgCtx, .path (.var (.there .here)) (SgCtx.lookup (.there .here))
    (.sngl (.var .here))⟩ :=
  Alg.pAlias (W := SgCtx.lookup .here) (StartP.of_mem defaultFuel (by decide +kernel) (by decide +kernel))
    (Found.of_any defaultFuel (fun e => decide (e.ty = .sngl (.var (.there .here))))
      (by decide +kernel) (by decide +kernel) fun _ h => of_decide_eq_true h)
    Alg.pSelf

theorem SgPre_alg : Alg ⟨_, SgCtx, .path (.sel (.var .here) la) (.vfld la .top)
    (.sngl (.sel (.var (.there .here)) la))⟩ :=
  Alg.pPre (W := SgCtx.lookup .here) (StartP.of_mem defaultFuel (by decide +kernel) (by decide +kernel))
    (Found.of_any defaultFuel (fun e => (e.vfld? la).isSome) (by decide +kernel) (by decide +kernel)
      fun _ h => h)
    Alg.pRefl

-- Two recursive types through the abstract view.  The field `a` of the right body is read
-- off the left body, and its self-free step asks `{b : ⊤} ∧ {v : ⊤} <: {b : ⊤}`.
theorem Mu_alg : Alg ⟨_, .nil, .sub MuWide MuNarrow⟩ :=
  Alg.mu (.and .typ .fld) .fld (DeclAsks.fld rfl (SfAsks.closed (.and (.fld lb .top) (.fld lv .top))
    (.fld lb .top))) (forall_mem_one (Alg.and1 rfl Alg.refl))

-- E1, E1p, E3 and E4 as written: no `Alg` derivation, since the run ends unmarked with no
-- answer.
theorem E1_sub_not_alg : ¬ Alg ⟨_, E1Ctx, .sub E1Dom E1Res⟩ :=
  sub?_reject (rejects_eq (by decide +kernel : rejects (sub? E1Ctx E1Dom E1Res) 1 = true))

theorem E1_var_not_alg : ¬ Alg ⟨_, E1Ctx, .var .here (E1Ctx.lookup .here) E1Res⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E1Ctx .here E1Res) 3 = true))

theorem E1p_sub_not_alg : ¬ Alg ⟨_, E1p_Ctx1, .sub E1p_Dom E1p_Res⟩ :=
  sub?_reject (rejects_eq (by decide +kernel : rejects (sub? E1p_Ctx1 E1p_Dom E1p_Res) 1 = true))

theorem E3_sub_not_alg : ¬ Alg ⟨_, E3Ctx2, .sub E3T2 E3T1⟩ :=
  sub?_reject (rejects_eq (by decide +kernel : rejects (sub? E3Ctx2 E3T2 E3T1) 1 = true))

theorem E4_sub_not_alg : ¬ Alg ⟨_, E4Ctx4, .sub E4Int (.sel (.var (.there (.there .here))) lA)⟩ :=
  sub?_reject (rejects_eq (by decide +kernel :
    rejects (sub? E4Ctx4 E4Int (.sel (.var (.there (.there .here))) lA)) 2 = true))

theorem E4_var_not_alg : ¬ Alg ⟨_, E4Ctx4, .var (.there .here) (E4Ctx4.lookup (.there .here))
    (.sel (.var (.there (.there .here))) lA)⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (var? E4Ctx4 (.there .here) (.sel (.var (.there (.there .here))) lA)) 5 = true))

/-- `p.A ∧ ⊥`, in the context of the loop `LPCtx`. -/
def LPAndLeft : Ty ([],x,x) := .and LPLeft .bot

/-- `∀(y : ⊤) q.B`. -/
def LPAllRight : Ty ([],x,x) := .all .top (.sel (.var (.there .here)) lB)

-- `Alg` derives `p.A ∧ ⊥ <: ∀(y : ⊤) q.B` by the right operand.
theorem LP_alg : Alg ⟨_, LPCtx, .sub LPAndLeft LPAllRight⟩ := Alg.and2 rfl Alg.bot

-- The left operand, tried first, descends under a new binder at each level and
-- exhausts the tank, so the run hits the recursion limit.
example : (sub? LPCtx LPAndLeft LPAllRight).2.out = true := by decide +kernel

end AlgChecks

end PathsFrontend.Core
