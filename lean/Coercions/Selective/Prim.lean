import Coercions.DotMNF.Structural

/-!
# The primitive relation `≤₀`

`Prim Γ S T` is a syntax-directed, single-step relation over `DotMNF.Ty` and
`DotMNF.Ctx`.  Its selection rules read the *declared* type of the receiver
(`Γ.lookup x`) through `Exp` (intersections and `μ` opened at the variable);
they never consult term typing, so `Prim` is not mutual with any typing
judgment.  A bound step is a single step: `x.A ≤₀ U` only for the declared
upper bound `U` itself, `L ≤₀ x.A` only for the declared lower bound `L`.

`prim?` decides `Prim` by structural recursion on a fuel equal to the sum of
the sizes of the two types plus one; `prim?_iff` states that the fuel is
sufficient, so this is a decision procedure, not a budgeted search.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Member exposure of a declared type at a variable -/

/-- `Exp x T A L U`: the type `T`, read as the type of the variable `x`,
declares the member `A : L..U`.  Through both operands of an intersection
(members are not merged) and through `μ` opened at `x`.  A selection, `⊥`,
`⊤`, a field or a function exposes nothing. -/
inductive Exp : {s : Sig} → BVar s .var → Ty s → Label → Ty s → Ty s → Prop where
  | typ : Exp x (.typ A L U) A L U
  | andL : Exp x S A L U → Exp x (.and S T) A L U
  | andR : Exp x T A L U → Exp x (.and S T) A L U
  | mu : Exp x (T.substVar x) A L U → Exp x (.mu T) A L U

/-- The exposed members of `T.rename ρ` at the variable `x`, computed by
structural recursion on `T` with a pending renaming (for `μ`). -/
def memR {s2 : Sig} (x : BVar s2 .var) : {s1 : Sig} → Ty s1 → Rename s1 s2 →
    List (Label × Ty s2 × Ty s2)
  | _, .typ A L U, ρ => [(A, L.rename ρ, U.rename ρ)]
  | _, .and S T, ρ => memR x S ρ ++ memR x T ρ
  | _, .mu T, ρ => memR x T (ρ.lift.comp (Rename.subst x))
  | _, .top, _ => []
  | _, .bot, _ => []
  | _, .fld _ _, _ => []
  | _, .sel _ _, _ => []
  | _, .all _ _, _ => []

theorem exp_rename_iff {s2 : Sig} (x : BVar s2 .var) :
    ∀ {s1 : Sig} (T : Ty s1) (ρ : Rename s1 s2) (A : Label) (L U : Ty s2),
    Exp x (T.rename ρ) A L U ↔ (A, L, U) ∈ memR x T ρ
  | _, .typ B L' U', ρ, A, L, U => by
      simp only [Ty.rename, memR, List.mem_singleton, Prod.mk.injEq]
      constructor
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact .typ
  | _, .and S T, ρ, A, L, U => by
      simp only [Ty.rename, memR, List.mem_append]
      rw [← exp_rename_iff x S ρ, ← exp_rename_iff x T ρ]
      constructor
      · intro h; cases h with
        | andL h => exact Or.inl h
        | andR h => exact Or.inr h
      · rintro (h | h)
        · exact .andL h
        · exact .andR h
  | _, .mu T, ρ, A, L, U => by
      simp only [Ty.rename, memR]
      rw [← exp_rename_iff x T (ρ.lift.comp (Rename.subst x))]
      rw [← DotMNF.Ty.rename_comp]
      constructor
      · intro h; cases h with
        | mu h => exact h
      · intro h; exact .mu h
  | _, .top, ρ, A, L, U => by simp only [Ty.rename, memR]; simp; intro h; cases h
  | _, .bot, ρ, A, L, U => by simp only [Ty.rename, memR]; simp; intro h; cases h
  | _, .fld _ _, ρ, A, L, U => by simp only [Ty.rename, memR]; simp; intro h; cases h
  | _, .sel _ _, ρ, A, L, U => by simp only [Ty.rename, memR]; simp; intro h; cases h
  | _, .all _ _, ρ, A, L, U => by simp only [Ty.rename, memR]; simp; intro h; cases h

/-- The exposed members of `T` at `x`. -/
def members {s : Sig} (x : BVar s .var) (T : Ty s) : List (Label × Ty s × Ty s) :=
  memR x T Rename.id

theorem exp_iff_members {s : Sig} (x : BVar s .var) (T : Ty s) (A : Label) (L U : Ty s) :
    Exp x T A L U ↔ (A, L, U) ∈ members x T := by
  have h := exp_rename_iff x T Rename.id A L U
  rwa [DotMNF.Ty.rename_id] at h

/-- Renaming of member exposure. -/
theorem Exp.rename {s1 s2 : Sig} {x : BVar s1 .var} {T : Ty s1} {A : Label} {L U : Ty s1} :
    Exp x T A L U → (ρ : Rename s1 s2) →
    Exp (ρ.var x) (T.rename ρ) A (L.rename ρ) (U.rename ρ)
  | .typ, _ => .typ
  | .andL e, ρ => .andL (e.rename ρ)
  | .andR e, ρ => .andR (e.rename ρ)
  | .mu e, ρ => .mu (by
      have := e.rename ρ
      rwa [DotMNF.Ty.substVar_rename] at this)

/-! ## The primitive relation -/

/-- `Γ ⊢ S ≤₀ T`.  No transitivity; selection rules are single bound steps
read off the declared type of the receiver. -/
inductive Prim : {s : Sig} → Ctx s → Ty s → Ty s → Prop where
  | refl : Prim Γ T T
  | top : Prim Γ S .top
  | bot : Prim Γ .bot T
  | andR : Prim Γ S T → Prim Γ S U → Prim Γ S (.and T U)
  | andL1 : Prim Γ S U → Prim Γ (.and S T) U
  | andL2 : Prim Γ T U → Prim Γ (.and S T) U
  | fld : Prim Γ T U → Prim Γ (.fld a T) (.fld a U)
  | typ : Prim Γ L2 L1 → Prim Γ U1 U2 → Prim Γ (.typ A L1 U1) (.typ A L2 U2)
  | all : Prim Γ S2 S1 → Prim (Γ.cons S2) T1 T2 → Prim Γ (.all S1 T1) (.all S2 T2)
  | selU : Exp x (Γ.lookup x) A L U → Prim Γ (.sel (.var x) A) U
  | selL : Exp x (Γ.lookup x) A L U → Prim Γ L (.sel (.var x) A)

/-! ## Renaming and weakening -/

theorem Prim.rename {s1 s2 : Sig} {Γ : Ctx s1} {S T : Ty s1} (h : Prim Γ S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    Prim Δ (S.rename ρ) (T.rename ρ) :=
  match h with
  | .refl => .refl
  | .top => .top
  | .bot => .bot
  | .andR h1 h2 => .andR (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .andL1 h => .andL1 (h.rename ρ hρ)
  | .andL2 h => .andL2 (h.rename ρ hρ)
  | .fld h => .fld (h.rename ρ hρ)
  | .typ h1 h2 => .typ (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .all h1 h2 => .all (h1.rename ρ hρ) (h2.rename ρ.lift (hρ.cons _))
  | .selU (x := x) e => .selU (x := ρ.var x) (by rw [hρ x]; exact e.rename ρ)
  | .selL (x := x) e => .selL (x := ρ.var x) (by rw [hρ x]; exact e.rename ρ)

theorem Prim.weaken {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Prim Γ S T) (V : Ty s) :
    Prim (Γ.cons V) S.weaken T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

/-! ## Decision procedure -/

def sz {s : Sig} : Ty s → Nat
  | .top => 1
  | .bot => 1
  | .sel _ _ => 1
  | .typ _ L U => sz L + sz U + 1
  | .fld _ T => sz T + 1
  | .mu T => sz T + 1
  | .all S T => sz S + sz T + 1
  | .and S T => sz S + sz T + 1

/-- A recursion oracle: decides `Prim` on smaller goals, in any context. -/
abbrev Oracle := {s : Sig} → Ctx s → Ty s → Ty s → Bool

def isTopB {s : Sig} : Ty s → Bool
  | .top => true
  | _ => false

def isBotB {s : Sig} : Ty s → Bool
  | .bot => true
  | _ => false

def andRB (r : Oracle) {s : Sig} (Γ : Ctx s) (S : Ty s) : Ty s → Bool
  | .and T U => r Γ S T && r Γ S U
  | _ => false

def andLB (r : Oracle) {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Bool
  | .and S T, U => r Γ S U || r Γ T U
  | _, _ => false

def structB (r : Oracle) {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Bool
  | .fld a T, .fld b U => decide (a = b) && r Γ T U
  | .typ A L1 U1, .typ B L2 U2 => decide (A = B) && r Γ L2 L1 && r Γ U1 U2
  | .all S1 T1, .all S2 T2 => r Γ S2 S1 && r (Γ.cons S2) T1 T2
  | _, _ => false

def selUB {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Bool
  | .sel (.var x) A, T => (members x (Γ.lookup x)).any (fun m => decide (m.1 = A) && decide (m.2.2 = T))
  | _, _ => false

def selLB {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Bool
  | S, .sel (.var x) A => (members x (Γ.lookup x)).any (fun m => decide (m.1 = A) && decide (m.2.1 = S))
  | _, _ => false

def stepB (r : Oracle) {s : Sig} (Γ : Ctx s) (S T : Ty s) : Bool :=
  decide (S = T) || isTopB T || isBotB S || andRB r Γ S T || andLB r Γ S T ||
    structB r Γ S T || selUB Γ S T || selLB Γ S T

def primN : Nat → Oracle
  | 0 => fun _ _ _ => false
  | n + 1 => fun Γ S T => stepB (primN n) Γ S T

/-- The decision procedure: fuel is the size of the goal. -/
def prim? {s : Sig} (Γ : Ctx s) (S T : Ty s) : Bool := primN (sz S + sz T + 1) Γ S T

/-! ### Soundness -/

theorem stepB_sound (r : Oracle)
    (hr : ∀ {s : Sig} (Γ : Ctx s) (S T : Ty s), r Γ S T = true → Prim Γ S T)
    {s : Sig} (Γ : Ctx s) (S T : Ty s) (h : stepB r Γ S T = true) : Prim Γ S T := by
  simp only [stepB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · subst h; exact .refl
  · cases T <;> simp [isTopB] at h; exact .top
  · cases S <;> simp [isBotB] at h; exact .bot
  · cases T <;> simp [andRB] at h
    exact .andR (hr _ _ _ h.1) (hr _ _ _ h.2)
  · cases S <;> simp [andLB] at h
    rcases h with h | h
    · exact .andL1 (hr _ _ _ h)
    · exact .andL2 (hr _ _ _ h)
  · cases S <;> cases T <;> simp [structB] at h
    all_goals first
      | (obtain ⟨⟨rfl, h1⟩, h2⟩ := h; exact .typ (hr _ _ _ h1) (hr _ _ _ h2))
      | (obtain ⟨rfl, h⟩ := h; exact .fld (hr _ _ _ h))
      | exact .all (hr _ _ _ h.1) (hr _ _ _ h.2)
  · cases S with
    | sel p A =>
        cases p with
        | var x =>
            simp only [selUB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨B, L, U⟩, hm, rfl, rfl⟩ := h
            exact .selU ((exp_iff_members _ _ _ _ _).mpr hm)
    | _ => simp [selUB] at h
  · cases T with
    | sel p A =>
        cases p with
        | var x =>
            simp only [selLB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨B, L, U⟩, hm, rfl, rfl⟩ := h
            exact .selL ((exp_iff_members _ _ _ _ _).mpr hm)
    | _ => cases S <;> simp [selLB] at h

theorem primN_sound : ∀ (n : Nat) {s : Sig} (Γ : Ctx s) (S T : Ty s),
    primN n Γ S T = true → Prim Γ S T
  | 0, _, _, _, _, h => by simp [primN] at h
  | n + 1, _, Γ, S, T, h => stepB_sound (primN n) (primN_sound n) Γ S T h

theorem prim?_sound {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : prim? Γ S T = true) : Prim Γ S T :=
  primN_sound _ Γ S T h

/-! ### Completeness: the size fuel always suffices -/

theorem sz_pos {s : Sig} (T : Ty s) : 0 < sz T := by cases T <;> simp [sz]

theorem primN_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Prim Γ S T) :
    ∀ n, sz S + sz T < n → primN n Γ S T = true := by
  induction h with
  | refl =>
      intro n hn; cases n with
      | zero => omega
      | succ n => simp [primN, stepB]
  | top =>
      intro n hn; cases n with
      | zero => omega
      | succ n => simp [primN, stepB, isTopB]
  | bot =>
      intro n hn; cases n with
      | zero => omega
      | succ n => simp [primN, stepB, isBotB]
  | andR _ _ ih1 ih2 =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih1 n (by omega); have h2 := ih2 n (by omega)
          simp [primN, stepB, andRB, h1, h2]
  | andL1 _ ih =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih n (by omega)
          simp [primN, stepB, andLB, h1]
  | andL2 _ ih =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih n (by omega)
          simp [primN, stepB, andLB, h1]
  | fld _ ih =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih n (by omega)
          simp [primN, stepB, structB, h1]
  | typ _ _ ih1 ih2 =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih1 n (by omega); have h2 := ih2 n (by omega)
          simp [primN, stepB, structB, h1, h2]
  | all _ _ ih1 ih2 =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          simp only [sz] at hn
          have h1 := ih1 n (by omega); have h2 := ih2 n (by omega)
          simp [primN, stepB, structB, h1, h2]
  | selU e =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          have hm := (exp_iff_members _ _ _ _ _).mp e
          simp only [primN, stepB, Bool.or_eq_true]
          refine Or.inl (Or.inr ?_)
          simp only [selUB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨_, hm, rfl, rfl⟩
  | selL e =>
      intro n hn; cases n with
      | zero => omega
      | succ n =>
          have hm := (exp_iff_members _ _ _ _ _).mp e
          simp only [primN, stepB, Bool.or_eq_true]
          refine Or.inr ?_
          simp only [selLB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨_, hm, rfl, rfl⟩

theorem prim?_complete {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Prim Γ S T) : prim? Γ S T = true :=
  primN_complete h _ (by omega)

/-- `≤₀` is decided by `prim?`: no budget, no exhaustion outcome. -/
theorem prim?_iff {s : Sig} {Γ : Ctx s} {S T : Ty s} : prim? Γ S T = true ↔ Prim Γ S T :=
  ⟨prim?_sound, prim?_complete⟩

instance Prim.decidable {s : Sig} (Γ : Ctx s) (S T : Ty s) : Decidable (Prim Γ S T) :=
  decidable_of_iff _ prim?_iff

/-- A negative judgment from a computed `false`. -/
theorem not_prim_of {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : prim? Γ S T = false) : ¬ Prim Γ S T :=
  fun hp => by rw [prim?_complete hp] at h; cases h

/-! ### Size is invariant under renaming

The term checker's field lookup (`Typer.lean`) unfolds `μ` at a variable and
uses `sz` as its fuel; `sz_substVar` says the fuel suffices. -/

theorem sz_rename {s1 : Sig} (T : Ty s1) : ∀ {s2 : Sig} (ρ : Rename s1 s2), sz (T.rename ρ) = sz T := by
  induction T with
  | top | bot => intro _ _; rfl
  | sel => intro _ _; rfl
  | typ _ _ _ ih1 ih2 => intro _ ρ; simp [Ty.rename, sz, ih1, ih2]
  | fld _ _ ih => intro _ ρ; simp [Ty.rename, sz, ih]
  | mu _ ih => intro _ ρ; simp [Ty.rename, sz, ih]
  | all _ _ ih1 ih2 => intro _ ρ; simp [Ty.rename, sz, ih1, ih2]
  | and _ _ ih1 ih2 => intro _ ρ; simp [Ty.rename, sz, ih1, ih2]

theorem sz_substVar {s : Sig} (T : Ty (s,x)) (y : BVar s .var) : sz (T.substVar y) = sz T :=
  sz_rename T _

/-! ## Chains: the reflexive-transitive closure of `≤₀`

The structural lifts (field, type-member bounds, dependent function,
intersection) are admissible for chains: they are derived forms, not
constructors. -/

inductive Chain {s : Sig} (Γ : Ctx s) : Ty s → Ty s → Prop where
  | refl : Chain Γ T T
  | cons : Prim Γ S M → Chain Γ M T → Chain Γ S T

theorem Chain.single {s : Sig} {Γ : Ctx s} {S T : Ty s} (h : Prim Γ S T) : Chain Γ S T :=
  .cons h .refl

theorem Chain.append {s : Sig} {Γ : Ctx s} {S M T : Ty s} (h1 : Chain Γ S M) (h2 : Chain Γ M T) :
    Chain Γ S T := by
  induction h1 with
  | refl => exact h2
  | cons p _ ih => exact .cons p (ih h2)

theorem Chain.snoc {s : Sig} {Γ : Ctx s} {S M T : Ty s} (h1 : Chain Γ S M) (p : Prim Γ M T) :
    Chain Γ S T := h1.append (.single p)

theorem Chain.rename {s1 s2 : Sig} {Γ : Ctx s1} {S T : Ty s1} (h : Chain Γ S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) : Chain Δ (S.rename ρ) (T.rename ρ) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (p.rename ρ hρ) ih

/-! ## Admissible structural lifts -/

theorem Chain.fld {s : Sig} {Γ : Ctx s} {S T : Ty s} {a : Label} (h : Chain Γ S T) :
    Chain Γ (.fld a S) (.fld a T) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (.fld p) ih

theorem Chain.typU {s : Sig} {Γ : Ctx s} {L U1 U2 : Ty s} {A : Label} (h : Chain Γ U1 U2) :
    Chain Γ (.typ A L U1) (.typ A L U2) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (.typ .refl p) ih

/-- Lower bounds are contravariant: a chain `L2 ⇒* L1` lifts to
`{A : L1..U} ⇒* {A : L2..U}`, steps taken in reverse order. -/
theorem Chain.typL {s : Sig} {Γ : Ctx s} {L1 L2 U : Ty s} {A : Label} (h : Chain Γ L2 L1) :
    Chain Γ (.typ A L1 U) (.typ A L2 U) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact ih.snoc (.typ p .refl)

theorem Chain.typ {s : Sig} {Γ : Ctx s} {L1 L2 U1 U2 : Ty s} {A : Label}
    (hL : Chain Γ L2 L1) (hU : Chain Γ U1 U2) : Chain Γ (.typ A L1 U1) (.typ A L2 U2) :=
  (Chain.typU hU).append (Chain.typL hL)

theorem Chain.allCod {s : Sig} {Γ : Ctx s} {S : Ty s} {T1 T2 : Ty (s,x)}
    (h : Chain (Γ.cons S) T1 T2) : Chain Γ (.all S T1) (.all S T2) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (.all .refl p) ih

theorem Chain.allDom {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T : Ty (s,x)}
    (h : Chain Γ S2 S1) : Chain Γ (.all S1 T) (.all S2 T) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact ih.snoc (.all p .refl)

/-- The dependent-function lift: domain steps first, then codomain steps,
all of them under the *target* domain `S2`, as `Sub.all` prescribes. -/
theorem Chain.all {s : Sig} {Γ : Ctx s} {S1 S2 : Ty s} {T1 T2 : Ty (s,x)}
    (hS : Chain Γ S2 S1) (hT : Chain (Γ.cons S2) T1 T2) :
    Chain Γ (.all S1 T1) (.all S2 T2) :=
  (Chain.allDom hS).append (Chain.allCod hT)

theorem Chain.andCongL {s : Sig} {Γ : Ctx s} {S M U : Ty s} (h : Chain Γ S M) :
    Chain Γ (.and S U) (.and M U) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (.andR (.andL1 p) (.andL2 .refl)) ih

theorem Chain.andCongR {s : Sig} {Γ : Ctx s} {S M U : Ty s} (h : Chain Γ S M) :
    Chain Γ (.and U S) (.and U M) := by
  induction h with
  | refl => exact .refl
  | cons p _ ih => exact .cons (.andR (.andL1 .refl) (.andL2 p)) ih

theorem Chain.and {s : Sig} {Γ : Ctx s} {S T U : Ty s} (h1 : Chain Γ S T) (h2 : Chain Γ S U) :
    Chain Γ S (.and T U) :=
  .cons (.andR .refl .refl) ((Chain.andCongL h1).append (Chain.andCongR h2))

end Selective
