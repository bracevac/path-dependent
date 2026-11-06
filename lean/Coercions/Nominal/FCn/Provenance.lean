import Coercions.Nominal.FCn.Preservation

/-!
# Run-time provenance: the predicate and its preservation (plan XII, stage NR)

Which store variables a reachable state may hold at a class type.  An allocation record
`A : Alloc s` gives each store variable the keys `(q, C)` at which the scope that allocated it seals
it, `q` the owner path and `C` the class label.  `Alloc.consO` admits an owner under a binder only
when it is the weakening of an owner below the binder, so an owner is always older than the variable
it seals.

The predicate `sealsOK ξ` over every family of terms and evidence admits a seal `seal q C` only at
the head of the evidence of a path cast `cast P e` whose path `P.path` is a variable `y` with
`ξ y (q, C)`.  A lambda's parameter, the binder of a `let` of no value and the binder of `pi` admit
no seal.  The binder of a `let` of a value and the self of a literal admit every label at an older
owner.  `State.SealsAtCtors` is the predicate over a state.  The machine with records `AStep` has one
rule per rule of `Step` and records `allocLbl u v` at `MS-LetVal`.  `AStep.sealsAtCtors` keeps the
predicate at every rule, for every application view that meets `AppView.SealsOK`, and
`reachable_sealsAtCtors` reads it at every state a program meeting `Tm.InitSeals` reaches.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Owners, allocation records, the predicate and the seal sites -/

/-- Undo one weakening of a path: `none` when the path mentions the newest variable. -/
def Path.lower : Path (s,x) → Option (Path s)
  | .var .here => none
  | .var (.there y) => some (.var y)
  | .sel p a => (Path.lower p).map (fun q => .sel q a)

theorem Path.lower_weaken : ∀ (q : Path s), Path.lower (q.weaken : Path (s,x)) = some q
  | .var _ => rfl
  | .sel q a => by
      show (Path.lower (q.weaken : Path (s,x))).map (fun r => Path.sel r a) = _
      rw [Path.lower_weaken q]; rfl

theorem Path.lower_some : ∀ {p : Path (s,x)} {q : Path s}, Path.lower p = some q → p = q.weaken
  | .var .here, _, h => by simp [Path.lower] at h
  | .var (.there y), _, h => by simp only [Path.lower, Option.some.injEq] at h; subst h; rfl
  | .sel p a, q, h => by
      simp only [Path.lower, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      rw [Path.lower_some hr]; rfl

/-- A seal key: the owner path and the label of a seal `seal q C`. -/
abbrev Key (s : Sig) := Path s × Label
def Key.weaken (k : Key s) : Key (s,x) := (k.1.weaken, k.2)
def Key.rename (k : Key s₁) (ρ : Rename s₁ s₂) : Key s₂ := (k.1.rename ρ, k.2)
def Key.subst (k : Key s₁) (σ : CoSubst s₁ s₂) : Key s₂ := (k.1.subst σ.paths, k.2)

/-- `A y (q, C)`: the scope that allocated the store variable `y` seals it at the class `q∙C`.  At a
code binder: a seal at `q∙C` may be written at the binder. -/
abbrev Alloc (s : Sig) := BVar s .var → Key s → Bool

/-- Every label: the binder of a `let` of a value, the self of a literal. -/
def Lbl.any : Label → Bool := fun _ => true
/-- No label: a lambda's parameter, the binder of a `let` of no value, the binder of `pi`. -/
def Lbl.none : Label → Bool := fun _ => false

/-- One more variable, with record `b` over keys below it.  Every owner must be a weakening: an owner
that mentions the new variable, or a variable bound after the one it seals, is never admitted. -/
def Alloc.consO (A : Alloc s) (b : Key s → Bool) : Alloc (s,x) := fun y k =>
  match Path.lower k.1 with
  | none => false
  | some q' => match y with
    | .here => b (q', k.2)
    | .there y => A y (q', k.2)
/-- A code binder: its admission reads labels only. -/
def Alloc.cons (A : Alloc s) (b : Label → Bool) : Alloc (s,x) := A.consO (fun k => b k.2)
def Alloc.tail (A : Alloc (s,x)) : Alloc s := fun y k => A (.there y) k.weaken
def Alloc.empty : Alloc s := fun _ _ => false

theorem Alloc.consO_here (A : Alloc s) (b : Key s → Bool) (k : Key s) :
    (A.consO b) .here k.weaken = b k := by
  simp only [Alloc.consO, Key.weaken, Path.lower_weaken]
theorem Alloc.consO_there (A : Alloc s) (b : Key s → Bool) (y : BVar s .var) (k : Key s) :
    (A.consO b) (.there y) k.weaken = A y k := by
  simp only [Alloc.consO, Key.weaken, Path.lower_weaken]
theorem Alloc.consO_true {A : Alloc s} {b : Key s → Bool} {y : BVar (s,x) .var} {k : Key (s,x)}
    (h : (A.consO b) y k = true) : ∃ k₀ : Key s, k = k₀.weaken := by
  simp only [Alloc.consO] at h
  split at h
  · cases h
  · rename_i q₀ e; exact ⟨(q₀, k.2), by rw [Key.weaken, ← Path.lower_some e]⟩
theorem Alloc.cons_here (A : Alloc s) (b : Label → Bool) (k : Key s) :
    (A.cons b) .here k.weaken = b k.2 := Alloc.consO_here _ _ k
theorem Alloc.cons_there (A : Alloc s) (b : Label → Bool) (y : BVar s .var) (k : Key s) :
    (A.cons b) (.there y) k.weaken = A y k := Alloc.consO_there _ _ y k

theorem Alloc.consO_tail (A : Alloc s) (b : Key s → Bool) : (A.consO b).tail = A := by
  funext y k; exact Alloc.consO_there A b y k

/-- A term that reduces to a value with no step through a `let` or an application: `val v` under
casts. -/
def Tm.valShaped : Tm s → Bool
  | .val _ => true
  | .cast t _ => Tm.valShaped t
  | _ => false

/-- The labels admitted at the binder of `let z = t in u`. -/
def letLbl (t : Tm s) : Label → Bool := if Tm.valShaped t then Lbl.any else Lbl.none

mutual
/-- `PEq.sealsOK ξ π`: every seal `seal p C` inside sits at the head of a path cast at a variable `y`
with `ξ y (p, C)`. -/
def PEq.sealsOK : Alloc s → PEq s → Bool
  | _, .refl _ => true
  | ξ, .symm π => PEq.sealsOK ξ π
  | ξ, .trans π π' => PEq.sealsOK ξ π && PEq.sealsOK ξ π'
  | ξ, .sel π _ => PEq.sealsOK ξ π
  | ξ, .member P e _ => PathCo.sealsOK ξ P && LeCo.sealsOK none ξ e
def PathCo.sealsOK : Alloc s → PathCo s → Bool
  | _, .var _ => true
  | ξ, .sel P _ _ => PathCo.sealsOK ξ P
  | ξ, .cast P e => PathCo.sealsOK ξ P && LeCo.sealsOK (some P.path) ξ e
  | ξ, .alias P₀ π Q => PathCo.sealsOK ξ P₀ && PEq.sealsOK ξ π && PathCo.sealsOK ξ Q
  | ξ, .sngl P _ π => PathCo.sealsOK ξ P && PEq.sealsOK ξ π
  | ξ, .fldI _ _ Q => PathCo.sealsOK ξ Q
  | ξ, .fold _ P => PathCo.sealsOK ξ P
  | ξ, .unfold P => PathCo.sealsOK ξ P
  | ξ, .both _ _ P Q => PathCo.sealsOK ξ P && PathCo.sealsOK ξ Q
/-- `LeCo.sealsOK h ξ e`: at `h = some r` the evidence acts on the path `r`, and a seal `seal p C` at
its head is admitted when `r` is a variable `y` with `ξ y (p, C)`.  At `h = none` no seal is at the head. -/
def LeCo.sealsOK : Option (Path s) → Alloc s → LeCo s → Bool
  | _, _, .refl _ => true
  | h, ξ, .trans e f => LeCo.sealsOK h ξ e && LeCo.sealsOK h ξ f
  | _, _, .top _ => true
  | _, _, .bot _ => true
  | _, ξ, .eqToLe φ => EqCo.sealsOK ξ φ
  | _, ξ, .pi e f => LeCo.sealsOK none ξ e && LeCo.sealsOK none (ξ.cons Lbl.none) f
  | h, ξ, .obj _ m => Morphism.sealsOK h ξ m
  | h, ξ, .pair _ _ e f => LeCo.sealsOK h ξ e && LeCo.sealsOK h ξ f
  | _, _, .bound _ _ => true
  | h, ξ, .intoBnd e => LeCo.sealsOK h ξ e
  | _, ξ, .member P e _ => PathCo.sealsOK ξ P && LeCo.sealsOK none ξ e
  | h, ξ, .seal p C => match h with
    | some (.var y) => ξ y (p, C)
    | _ => false
def EqCo.sealsOK : Alloc s → EqCo s → Bool
  | _, .refl _ => true
  | ξ, .symm φ => EqCo.sealsOK ξ φ
  | ξ, .trans φ ψ => EqCo.sealsOK ξ φ && EqCo.sealsOK ξ ψ
  | _, .defP _ _ => true
  | ξ, .lift _ π => PEq.sealsOK ξ π
  | ξ, .dom φ => EqCo.sealsOK ξ φ
  | ξ, .cod φ _ => EqCo.sealsOK ξ φ
def Morphism.sealsOK : Option (Path s) → Alloc s → Morphism s → Bool
  | _, _, .nil => true
  | h, ξ, .le m pre _ post => Morphism.sealsOK h ξ m && Side.sealsOK ξ pre && Side.sealsOK ξ post
  | h, ξ, .fld m _ sd => Morphism.sealsOK h ξ m && Side.sealsOK ξ sd
  | h, ξ, .alias m _ => Morphism.sealsOK h ξ m
  | h, ξ, .is m e => Morphism.sealsOK h ξ m && LeCo.sealsOK h ξ e
def Side.sealsOK : Alloc s → Side s → Bool
  | _, .none => true
  | ξ, .some e => LeCo.sealsOK none ξ e
  | _, .bot _ => true
  | _, .top _ => true
end

mutual
def Tm.sealsOK : Alloc s → Tm s → Bool
  | ξ, .path P => PathCo.sealsOK ξ P
  | ξ, .val v => Value.sealsOK ξ v
  | ξ, .app P Q => PathCo.sealsOK ξ P && PathCo.sealsOK ξ Q
  | ξ, .lett t u => Tm.sealsOK ξ t && Tm.sealsOK (ξ.cons (letLbl t)) u
  | ξ, .cast t e => Tm.sealsOK ξ t && LeCo.sealsOK none ξ e
def Value.sealsOK : Alloc s → Value s → Bool
  | ξ, .lam _ t => Tm.sealsOK (ξ.cons Lbl.none) t
  | ξ, .obj _ ds => Defs.sealsOK (ξ.cons Lbl.any) ds
  | ξ, .cast v e => Value.sealsOK ξ v && LeCo.sealsOK none ξ e
def Defs.sealsOK : Alloc s → Defs s → Bool
  | _, .nil => true
  | ξ, .typ ds _ _ => Defs.sealsOK ξ ds
  | ξ, .fld ds _ rhs => Defs.sealsOK ξ ds && Rhs.sealsOK ξ rhs
  | ξ, .cls ds _ _ => Defs.sealsOK ξ ds
def Rhs.sealsOK : Alloc s → Rhs s → Bool
  | ξ, .path P => PathCo.sealsOK ξ P
  | ξ, .fn v => Value.sealsOK ξ v
  | ξ, .nest _ ds => Defs.sealsOK ξ ds
end

mutual
/-- `PEq.sealSite π x k`: a seal `seal q C` at the head of a path cast whose path is the variable
`x`.  Under a binder the owner is weakened. -/
def PEq.sealSite : PEq s → BVar s .var → Key s → Bool
  | .refl _, _, _ => false
  | .symm π, x, k => PEq.sealSite π x k
  | .trans π π', x, k => PEq.sealSite π x k || PEq.sealSite π' x k
  | .sel π _, x, k => PEq.sealSite π x k
  | .member P e _, x, k => PathCo.sealSite P x k || LeCo.sealSite none e x k
def PathCo.sealSite : PathCo s → BVar s .var → Key s → Bool
  | .var _, _, _ => false
  | .sel P _ _, x, k => PathCo.sealSite P x k
  | .cast P e, x, k => PathCo.sealSite P x k || LeCo.sealSite (some P.path) e x k
  | .alias P₀ π Q, x, k => PathCo.sealSite P₀ x k || PEq.sealSite π x k || PathCo.sealSite Q x k
  | .sngl P _ π, x, k => PathCo.sealSite P x k || PEq.sealSite π x k
  | .fldI _ _ Q, x, k => PathCo.sealSite Q x k
  | .fold _ P, x, k => PathCo.sealSite P x k
  | .unfold P, x, k => PathCo.sealSite P x k
  | .both _ _ P Q, x, k => PathCo.sealSite P x k || PathCo.sealSite Q x k
def LeCo.sealSite : Option (Path s) → LeCo s → BVar s .var → Key s → Bool
  | _, .refl _, _, _ => false
  | h, .trans e f, x, k => LeCo.sealSite h e x k || LeCo.sealSite h f x k
  | _, .top _, _, _ => false
  | _, .bot _, _, _ => false
  | _, .eqToLe φ, x, k => EqCo.sealSite φ x k
  | _, .pi e f, x, k => LeCo.sealSite none e x k || LeCo.sealSite none f (.there x) k.weaken
  | h, .obj _ m, x, k => Morphism.sealSite h m x k
  | h, .pair _ _ e f, x, k => LeCo.sealSite h e x k || LeCo.sealSite h f x k
  | _, .bound _ _, _, _ => false
  | h, .intoBnd e, x, k => LeCo.sealSite h e x k
  | _, .member P e _, x, k => PathCo.sealSite P x k || LeCo.sealSite none e x k
  | h, .seal p D, x, k => match h with
    | some (.var y) => decide (y = x) && decide ((p, D) = k)
    | _ => false
def EqCo.sealSite : EqCo s → BVar s .var → Key s → Bool
  | .refl _, _, _ => false
  | .symm φ, x, k => EqCo.sealSite φ x k
  | .trans φ ψ, x, k => EqCo.sealSite φ x k || EqCo.sealSite ψ x k
  | .defP _ _, _, _ => false
  | .lift _ π, x, k => PEq.sealSite π x k
  | .dom φ, x, k => EqCo.sealSite φ x k
  | .cod φ _, x, k => EqCo.sealSite φ x k
def Morphism.sealSite : Option (Path s) → Morphism s → BVar s .var → Key s → Bool
  | _, .nil, _, _ => false
  | h, .le m pre _ post, x, k => Morphism.sealSite h m x k || Side.sealSite pre x k || Side.sealSite post x k
  | h, .fld m _ sd, x, k => Morphism.sealSite h m x k || Side.sealSite sd x k
  | h, .alias m _, x, k => Morphism.sealSite h m x k
  | h, .is m e, x, k => Morphism.sealSite h m x k || LeCo.sealSite h e x k
def Side.sealSite : Side s → BVar s .var → Key s → Bool
  | .none, _, _ => false
  | .some e, x, k => LeCo.sealSite none e x k
  | .bot _, _, _ => false
  | .top _, _, _ => false
end

mutual
def Tm.sealSite : Tm s → BVar s .var → Key s → Bool
  | .path P, x, k => PathCo.sealSite P x k
  | .val v, x, k => Value.sealSite v x k
  | .app P Q, x, k => PathCo.sealSite P x k || PathCo.sealSite Q x k
  | .lett t u, x, k => Tm.sealSite t x k || Tm.sealSite u (.there x) k.weaken
  | .cast t e, x, k => Tm.sealSite t x k || LeCo.sealSite none e x k
def Value.sealSite : Value s → BVar s .var → Key s → Bool
  | .lam _ t, x, k => Tm.sealSite t (.there x) k.weaken
  | .obj _ ds, x, k => Defs.sealSite ds (.there x) k.weaken
  | .cast v e, x, k => Value.sealSite v x k || LeCo.sealSite none e x k
def Defs.sealSite : Defs s → BVar s .var → Key s → Bool
  | .nil, _, _ => false
  | .typ ds _ _, x, k => Defs.sealSite ds x k
  | .fld ds _ rhs, x, k => Defs.sealSite ds x k || Rhs.sealSite rhs x k
  | .cls ds _ _, x, k => Defs.sealSite ds x k
def Rhs.sealSite : Rhs s → BVar s .var → Key s → Bool
  | .path P, x, k => PathCo.sealSite P x k
  | .fn v, x, k => Value.sealSite v x k
  | .nest _ ds, x, k => Defs.sealSite ds x k
end

/-! ## The state predicate, the machine with allocation records, the application view -/

/-- A literal's self sites, with their owners lowered below the self. -/
def Value.selfLbl : Value s → Key s → Bool
  | .obj _ ds => fun k => Defs.sealSite ds .here k.weaken
  | _ => fun _ => false

/-- The record of the variable that `MS-LetVal` allocates for `let z = val v in u`: the seals `u` puts
at `z` and those the literal's definitions put at its self, each with its owner. -/
def allocLbl (u : Tm (s,x)) (v : Value s) : Key s → Bool :=
  fun k => Tm.sealSite u .here k.weaken || Value.selfLbl v.core k

def Cont.sealsOK (ξ : Alloc s) : Bool → Cont s → Bool
  | _, .nil => true
  | b, .cons K (.lett u) => Tm.sealsOK (ξ.cons (if b then Lbl.any else Lbl.none)) u && Cont.sealsOK ξ false K
  | b, .cons K (.cast e) => LeCo.sealsOK none ξ e && Cont.sealsOK ξ b K

/-- A stored value at the newest variable.  A literal's self is that variable, so its definitions are
read with the self admitting the keys the record gives the variable. -/
def Stored.sealsOK (A : Alloc (s,x)) : Value s → Bool
  | .obj _ ds => Defs.sealsOK (A.tail.consO (fun k => A .here k.weaken)) ds
  | v => Value.sealsOK A.tail v

def Store.sealsOK : Alloc s → Store s → Bool
  | _, .nil => true
  | A, .cons σ v => Store.sealsOK A.tail σ && Stored.sealsOK A v

/-- **The state predicate**: every seal `seal q C` of the store, the frames and the focus sits at the
head of a path cast at a store variable `y` with `A y (q, C)`, or at a code binder that admits it. -/
def State.SealsAtCtors (A : Alloc s) (st : State s) : Bool :=
  Store.sealsOK A st.σ && Cont.sealsOK A (Tm.valShaped st.t) st.K && Tm.sealsOK A st.t

def Tm.InitSeals (t : Tm []) : Bool := Tm.sealsOK Alloc.empty t

def AppHead.sealsOK (A : Alloc s) : AppHead s → Bool
  | .id => true
  | .pi d c => LeCo.sealsOK none A d && LeCo.sealsOK none (A.cons Lbl.none) c
  | .eqv φ => EqCo.sealsOK A φ

def AppView.SealsOK (V : AppView) : Prop :=
  ∀ {s : Sig} {σ : Store s} {P : PathCo s} {S₀ : Ty s} {t₀ : Tm (s,x)} {h : AppHead s} (A : Alloc s),
    V σ P S₀ t₀ h → Store.sealsOK A σ = true → PathCo.sealsOK A P = true →
    Tm.sealsOK (A.cons Lbl.none) t₀ = true ∧ AppHead.sealsOK A h = true

structure AState (s : Sig) where
  st : State s
  A : Alloc s

/-- The machine with allocation records.  One rule per rule of `Step`, the record unchanged but at
`MS-LetVal`, which records `allocLbl u v` at the new variable. -/
inductive AStep (V : AppView) : AState s → AState s' → Prop where
  | lett : AStep V ⟨⟨σ, K, .lett t u⟩, A⟩ ⟨⟨σ, .cons K (.lett u), t⟩, A⟩
  | castPush : AStep V ⟨⟨σ, K, .cast t e⟩, A⟩ ⟨⟨σ, .cons K (.cast e), t⟩, A⟩
  | castVal : AStep V ⟨⟨σ, .cons K (.cast e), .val v⟩, A⟩ ⟨⟨σ, K, .val (.cast v e)⟩, A⟩
  | castPath : AStep V ⟨⟨σ, .cons K (.cast e), .path P⟩, A⟩ ⟨⟨σ, K, .path (.cast P e)⟩, A⟩
  | letVal : AStep V ⟨⟨σ, .cons K (.lett u), .val v⟩, A⟩ ⟨⟨σ.cons v.core, K.weaken, u.adjust v⟩, A.consO (allocLbl u v)⟩
  | letPath : AStep V ⟨⟨σ, .cons K (.lett u), .path P⟩, A⟩ ⟨⟨σ, K, u.substCo P⟩, A⟩
  | appId : V σ P S₀ t₀ .id → AStep V ⟨⟨σ, K, .app P Q⟩, A⟩ ⟨⟨σ, K, t₀.substCo Q⟩, A⟩
  | appPi : V σ P S₀ t₀ (.pi d c) → AStep V ⟨⟨σ, K, .app P Q⟩, A⟩ ⟨⟨σ, K, .cast (t₀.substCo (.cast Q d)) (c.substCo Q)⟩, A⟩
  | appEq : V σ P S₀ t₀ (.eqv φ) → AStep V ⟨⟨σ, K, .app P Q⟩, A⟩
      ⟨⟨σ, K, .cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))⟩, A⟩

inductive ASteps (V : AppView) : AState s → AState s' → Prop where
  | refl : ASteps V g g
  | tail : ASteps V g g' → AStep V g' g'' → ASteps V g g''

theorem AStep.step {V : AppView} {g : AState s} {g' : AState s'} : AStep V g g' → Step V g.st g'.st
  | .lett => .lett
  | .castPush => .castPush
  | .castVal => .castVal
  | .castPath => .castPath
  | .letVal => .letVal
  | .letPath => .letPath
  | .appId h => .appId h
  | .appPi h => .appPi h
  | .appEq h => .appEq h

theorem Step.alloc {V : AppView} {st : State s} {st' : State s'} (h : Step V st st') (A : Alloc s) :
    ∃ A', AStep V ⟨st, A⟩ ⟨st', A'⟩ := by
  cases h with
  | lett => exact ⟨A, .lett⟩
  | castPush => exact ⟨A, .castPush⟩
  | castVal => exact ⟨A, .castVal⟩
  | castPath => exact ⟨A, .castPath⟩
  | letVal => exact ⟨_, .letVal⟩
  | letPath => exact ⟨A, .letPath⟩
  | appId h => exact ⟨A, .appId h⟩
  | appPi h => exact ⟨A, .appPi h⟩
  | appEq h => exact ⟨A, .appEq h⟩

theorem AStep.alloc_det {V : AppView} {g : AState s} {g₁ g₂ : AState s'} (h₁ : AStep V g g₁)
    (h₂ : AStep V g g₂) : g₁.A = g₂.A := by
  cases h₁ <;> cases h₂ <;> rfl

theorem ASteps.steps {V : AppView} {g : AState s} {g' : AState s'} (h : ASteps V g g') : Steps V g.st g'.st := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih h.step

theorem Steps.alloc {V : AppView} {st : State s} {st' : State s'} (h : Steps V st st') (A : Alloc s) :
    ∃ A', ASteps V ⟨st, A⟩ ⟨st', A'⟩ := by
  induction h with
  | refl => exact ⟨A, .refl⟩
  | tail _ h ih =>
      obtain ⟨A₁, h₁⟩ := ih
      obtain ⟨A₂, h₂⟩ := Step.alloc h A₁
      exact ⟨A₂, .tail h₁ h₂⟩

/-- The de Bruijn index of a variable: `0` for the newest. -/
def BVar.dbIdx : BVar s k → Nat
  | .here => 0
  | .there y => BVar.dbIdx y + 1

theorem Path.root_weaken : ∀ (q : Path s), (q.weaken : Path (s,x)).root = .there q.root
  | .var _ => rfl
  | .sel q _ => Path.root_weaken q

/-- An allocation record whose every owner is older than the variable it seals. -/
def Alloc.OwnersOlder (A : Alloc s) : Prop := ∀ y k, A y k = true → BVar.dbIdx y < BVar.dbIdx k.1.root

theorem Alloc.OwnersOlder.consO {A : Alloc s} (hA : A.OwnersOlder) (b : Key s → Bool) :
    (A.consO b).OwnersOlder := by
  unfold Alloc.OwnersOlder
  intro y k h
  obtain ⟨k₀, rfl⟩ := Alloc.consO_true h
  show BVar.dbIdx y < BVar.dbIdx (k₀.1.weaken : Path (s,x)).root
  rw [Path.root_weaken]
  cases y with
  | here => show 0 < BVar.dbIdx k₀.1.root + 1; omega
  | there y =>
      rw [Alloc.consO_there] at h
      show BVar.dbIdx y + 1 < BVar.dbIdx k₀.1.root + 1
      have := hA y k₀ h; omega

theorem AStep.ownersOlder {V : AppView} {g : AState s} {g' : AState s'} (h : AStep V g g')
    (hg : g.A.OwnersOlder) : g'.A.OwnersOlder := by
  cases h with
  | letVal => exact hg.consO _
  | _ => exact hg

/-- **Owners are older.**  Along a run from the empty record, every owner that the record keeps at a
store variable is rooted at a variable allocated before it. -/
theorem ASteps.ownersOlder {V : AppView} {g : AState s} {g' : AState s'} (h : ASteps V g g')
    (hg : g.A.OwnersOlder) : g'.A.OwnersOlder := by
  induction h with
  | refl => exact hg
  | tail _ h ih => exact AStep.ownersOlder h (ih hg)

theorem Alloc.empty_ownersOlder : (Alloc.empty : Alloc s).OwnersOlder := by
  unfold Alloc.OwnersOlder; intro _ _ h; cases h

/-! ## The lemmas: sites are admitted, sites decide, renaming, substitution, the head -/

/-- Split the Boolean connectives of the hypotheses and the goal. -/
local macro "bsplit" : tactic => `(tactic| (simp only [Bool.and_eq_true, Bool.or_eq_true] at *))

/-! ### L0: a seal site is admitted -/

mutual
theorem PEq.sealsOK_site : ∀ {ξ : Alloc s} (π : PEq s) {x : BVar s .var} {C : Key s},
    PEq.sealsOK ξ π = true → PEq.sealSite π x C = true → ξ x C = true
  | _, .refl _, _, _, _, h₂ => by simp [PEq.sealSite] at h₂
  | _, .symm π, _, _, h₁, h₂ => PEq.sealsOK_site π h₁ h₂
  | _, .trans π π', _, _, h₁, h₂ => by
      simp only [PEq.sealsOK, PEq.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PEq.sealsOK_site π h₁.1 h₂
      · exact PEq.sealsOK_site π' h₁.2 h₂
  | _, .sel π _, _, _, h₁, h₂ => PEq.sealsOK_site π h₁ h₂
  | _, .member P e _, _, _, h₁, h₂ => by
      simp only [PEq.sealsOK, PEq.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
theorem PathCo.sealsOK_site : ∀ {ξ : Alloc s} (P : PathCo s) {x : BVar s .var} {C : Key s},
    PathCo.sealsOK ξ P = true → PathCo.sealSite P x C = true → ξ x C = true
  | _, .var _, _, _, _, h₂ => by simp [PathCo.sealSite] at h₂
  | _, .sel P _ _, _, _, h₁, h₂ => PathCo.sealsOK_site P h₁ h₂
  | _, .cast P e, _, _, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
  | _, .alias P₀ π Q, _, _, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with (h₂ | h₂) | h₂
      · exact PathCo.sealsOK_site P₀ h₁.1.1 h₂
      · exact PEq.sealsOK_site π h₁.1.2 h₂
      · exact PathCo.sealsOK_site Q h₁.2 h₂
  | _, .sngl P _ π, _, _, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact PEq.sealsOK_site π h₁.2 h₂
  | _, .fldI _ _ Q, _, _, h₁, h₂ => PathCo.sealsOK_site Q h₁ h₂
  | _, .fold _ P, _, _, h₁, h₂ => PathCo.sealsOK_site P h₁ h₂
  | _, .unfold P, _, _, h₁, h₂ => PathCo.sealsOK_site P h₁ h₂
  | _, .both _ _ P Q, _, _, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact PathCo.sealsOK_site Q h₁.2 h₂
theorem LeCo.sealsOK_site : ∀ {h : Option (Path s)} {ξ : Alloc s} (e : LeCo s) {x : BVar s .var} {C : Key s},
    LeCo.sealsOK h ξ e = true → LeCo.sealSite h e x C = true → ξ x C = true
  | _, _, .refl _, _, _, _, h₂ => by simp [LeCo.sealSite] at h₂
  | _, _, .trans e f, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact LeCo.sealsOK_site e h₁.1 h₂
      · exact LeCo.sealsOK_site f h₁.2 h₂
  | _, _, .top _, _, _, _, h₂ => by simp [LeCo.sealSite] at h₂
  | _, _, .bot _, _, _, _, h₂ => by simp [LeCo.sealSite] at h₂
  | _, _, .eqToLe φ, _, _, h₁, h₂ => EqCo.sealsOK_site φ h₁ h₂
  | _, _, .pi e f, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact LeCo.sealsOK_site e h₁.1 h₂
      · have := LeCo.sealsOK_site f h₁.2 h₂; rwa [Alloc.cons_there] at this
  | _, _, .obj _ m, _, _, h₁, h₂ => Morphism.sealsOK_site m h₁ h₂
  | _, _, .pair _ _ e f, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact LeCo.sealsOK_site e h₁.1 h₂
      · exact LeCo.sealsOK_site f h₁.2 h₂
  | _, _, .bound _ _, _, _, _, h₂ => by simp [LeCo.sealSite] at h₂
  | _, _, .intoBnd e, _, _, h₁, h₂ => LeCo.sealsOK_site e h₁ h₂
  | _, _, .member P e _, _, _, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
  | h, _, .seal p D, x, C, h₁, h₂ => by
      match h, h₁, h₂ with
      | some (.var y), h₁, h₂ =>
          simp only [LeCo.sealsOK, LeCo.sealSite, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
          obtain ⟨rfl, rfl⟩ := h₂
          exact h₁
      | some (.sel _ _), _, h₂ => simp [LeCo.sealSite] at h₂
      | none, _, h₂ => simp [LeCo.sealSite] at h₂
theorem EqCo.sealsOK_site : ∀ {ξ : Alloc s} (φ : EqCo s) {x : BVar s .var} {C : Key s},
    EqCo.sealsOK ξ φ = true → EqCo.sealSite φ x C = true → ξ x C = true
  | _, .refl _, _, _, _, h₂ => by simp [EqCo.sealSite] at h₂
  | _, .symm φ, _, _, h₁, h₂ => EqCo.sealsOK_site φ h₁ h₂
  | _, .trans φ ψ, _, _, h₁, h₂ => by
      simp only [EqCo.sealsOK, EqCo.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact EqCo.sealsOK_site φ h₁.1 h₂
      · exact EqCo.sealsOK_site ψ h₁.2 h₂
  | _, .defP _ _, _, _, _, h₂ => by simp [EqCo.sealSite] at h₂
  | _, .lift _ π, _, _, h₁, h₂ => PEq.sealsOK_site π h₁ h₂
  | _, .dom φ, _, _, h₁, h₂ => EqCo.sealsOK_site φ h₁ h₂
  | _, .cod φ _, _, _, h₁, h₂ => EqCo.sealsOK_site φ h₁ h₂
theorem Morphism.sealsOK_site : ∀ {h : Option (Path s)} {ξ : Alloc s} (m : Morphism s) {x : BVar s .var} {C : Key s},
    Morphism.sealsOK h ξ m = true → Morphism.sealSite h m x C = true → ξ x C = true
  | _, _, .nil, _, _, _, h₂ => by simp [Morphism.sealSite] at h₂
  | _, _, .le m pre _ post, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.sealSite] at h₁ h₂; bsplit
      rcases h₂ with (h₂ | h₂) | h₂
      · exact Morphism.sealsOK_site m h₁.1.1 h₂
      · exact Side.sealsOK_site pre h₁.1.2 h₂
      · exact Side.sealsOK_site post h₁.2 h₂
  | _, _, .fld m _ sd, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Morphism.sealsOK_site m h₁.1 h₂
      · exact Side.sealsOK_site sd h₁.2 h₂
  | _, _, .alias m _, _, _, h₁, h₂ => Morphism.sealsOK_site m h₁ h₂
  | _, _, .is m e, _, _, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Morphism.sealsOK_site m h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
theorem Side.sealsOK_site : ∀ {ξ : Alloc s} (sd : Side s) {x : BVar s .var} {C : Key s},
    Side.sealsOK ξ sd = true → Side.sealSite sd x C = true → ξ x C = true
  | _, .none, _, _, _, h₂ => by simp [Side.sealSite] at h₂
  | _, .some e, _, _, h₁, h₂ => LeCo.sealsOK_site e h₁ h₂
  | _, .bot _, _, _, _, h₂ => by simp [Side.sealSite] at h₂
  | _, .top _, _, _, _, h₂ => by simp [Side.sealSite] at h₂
end

mutual
theorem Tm.sealsOK_site : ∀ {ξ : Alloc s} (t : Tm s) {x : BVar s .var} {C : Key s},
    Tm.sealsOK ξ t = true → Tm.sealSite t x C = true → ξ x C = true
  | _, .path P, _, _, h₁, h₂ => PathCo.sealsOK_site P h₁ h₂
  | _, .val v, _, _, h₁, h₂ => Value.sealsOK_site v h₁ h₂
  | _, .app P Q, _, _, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact PathCo.sealsOK_site P h₁.1 h₂
      · exact PathCo.sealsOK_site Q h₁.2 h₂
  | _, .lett t u, _, _, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Tm.sealsOK_site t h₁.1 h₂
      · have := Tm.sealsOK_site u h₁.2 h₂; rwa [Alloc.cons_there] at this
  | _, .cast t e, _, _, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Tm.sealsOK_site t h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
theorem Value.sealsOK_site : ∀ {ξ : Alloc s} (v : Value s) {x : BVar s .var} {C : Key s},
    Value.sealsOK ξ v = true → Value.sealSite v x C = true → ξ x C = true
  | _, .lam _ t, _, _, h₁, h₂ => by have := Tm.sealsOK_site t h₁ h₂; rwa [Alloc.cons_there] at this
  | _, .obj _ ds, _, _, h₁, h₂ => by have := Defs.sealsOK_site ds h₁ h₂; rwa [Alloc.cons_there] at this
  | _, .cast v e, _, _, h₁, h₂ => by
      simp only [Value.sealsOK, Value.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Value.sealsOK_site v h₁.1 h₂
      · exact LeCo.sealsOK_site e h₁.2 h₂
theorem Defs.sealsOK_site : ∀ {ξ : Alloc s} (ds : Defs s) {x : BVar s .var} {C : Key s},
    Defs.sealsOK ξ ds = true → Defs.sealSite ds x C = true → ξ x C = true
  | _, .nil, _, _, _, h₂ => by simp [Defs.sealSite] at h₂
  | _, .typ ds _ _, _, _, h₁, h₂ => Defs.sealsOK_site ds h₁ h₂
  | _, .fld ds _ rhs, _, _, h₁, h₂ => by
      simp only [Defs.sealsOK, Defs.sealSite] at h₁ h₂; bsplit
      rcases h₂ with h₂ | h₂
      · exact Defs.sealsOK_site ds h₁.1 h₂
      · exact Rhs.sealsOK_site rhs h₁.2 h₂
  | _, .cls ds _ _, _, _, h₁, h₂ => Defs.sealsOK_site ds h₁ h₂
theorem Rhs.sealsOK_site : ∀ {ξ : Alloc s} (rhs : Rhs s) {x : BVar s .var} {C : Key s},
    Rhs.sealsOK ξ rhs = true → Rhs.sealSite rhs x C = true → ξ x C = true
  | _, .path P, _, _, h₁, h₂ => PathCo.sealsOK_site P h₁ h₂
  | _, .fn v, _, _, h₁, h₂ => Value.sealsOK_site v h₁ h₂
  | _, .nest _ ds, _, _, h₁, h₂ => Defs.sealsOK_site ds h₁ h₂
end

/-! ### L1: the predicate reads only its seal sites -/

/-- Sites under a binder: at the binder the admission `b` on both sides, below it `ξ'`. -/
theorem Alloc.cons_of {ξ ξ' : Alloc s} {b : Label → Bool} {f : BVar (s,x) .var → Key (s,x) → Bool}
    (h0 : ∀ x C, f x C = true → (ξ.cons b) x C = true)
    (h1 : ∀ y C, f (.there y) (Key.weaken C) = true → ξ' y C = true) :
    ∀ x C, f x C = true → (ξ'.cons b) x C = true
  | x, C, h => by
      have h' := h0 x C h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      cases x with
      | here => rw [Alloc.cons_here] at h' ⊢; exact h'
      | there y => rw [Alloc.cons_there]; exact h1 y k₀ h

mutual
theorem PEq.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (π : PEq s), PEq.sealsOK ξ π = true →
    (∀ x C, PEq.sealSite π x C = true → ξ' x C = true) → PEq.sealsOK ξ' π = true
  | _, _, .refl _, _, _ => rfl
  | _, _, .symm π, h₁, h₂ => PEq.sealsOK_of_sites π h₁ h₂
  | _, _, .trans π π', h₁, h₂ => by
      simp only [PEq.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PEq.sealsOK_of_sites π h₁.1 (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        PEq.sealsOK_of_sites π' h₁.2 (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
  | _, _, .sel π _, h₁, h₂ => PEq.sealsOK_of_sites π h₁ h₂
  | _, _, .member P e _, h₁, h₂ => by
      simp only [PEq.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
theorem PathCo.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (P : PathCo s), PathCo.sealsOK ξ P = true →
    (∀ x C, PathCo.sealSite P x C = true → ξ' x C = true) → PathCo.sealsOK ξ' P = true
  | _, _, .var _, _, _ => rfl
  | _, _, .sel P _ _, h₁, h₂ => PathCo.sealsOK_of_sites P h₁ h₂
  | _, _, .cast P e, h₁, h₂ => by
      simp only [PathCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .alias P₀ π Q, h₁, h₂ => by
      simp only [PathCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨⟨PathCo.sealsOK_of_sites P₀ h₁.1.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_of_sites π h₁.1.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩,
        PathCo.sealsOK_of_sites Q h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .sngl P _ π, h₁, h₂ => by
      simp only [PathCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_of_sites π h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .fldI _ _ Q, h₁, h₂ => PathCo.sealsOK_of_sites Q h₁ h₂
  | _, _, .fold _ P, h₁, h₂ => PathCo.sealsOK_of_sites P h₁ h₂
  | _, _, .unfold P, h₁, h₂ => PathCo.sealsOK_of_sites P h₁ h₂
  | _, _, .both _ _ P Q, h₁, h₂ => by
      simp only [PathCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PathCo.sealsOK_of_sites Q h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
theorem LeCo.sealsOK_of_sites : ∀ {h : Option (Path s)} {ξ ξ' : Alloc s} (e : LeCo s), LeCo.sealsOK h ξ e = true →
    (∀ x C, LeCo.sealSite h e x C = true → ξ' x C = true) → LeCo.sealsOK h ξ' e = true
  | _, _, _, .refl _, _, _ => rfl
  | _, _, _, .trans e f, h₁, h₂ => by
      simp only [LeCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_of_sites e h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_of_sites f h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .top _, _, _ => rfl
  | _, _, _, .bot _, _, _ => rfl
  | _, _, _, .eqToLe φ, h₁, h₂ => EqCo.sealsOK_of_sites φ h₁ h₂
  | _, ξ, _, .pi e f, h₁, h₂ => by
      simp only [LeCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_of_sites e h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_of_sites f h₁.2 (Alloc.cons_of (fun x C h => LeCo.sealsOK_site (ξ := ξ.cons Lbl.none) f h₁.2 h)
          (fun y C h => h₂ y C (by simp [LeCo.sealSite, h])))⟩
  | _, _, _, .obj _ m, h₁, h₂ => Morphism.sealsOK_of_sites m h₁ h₂
  | _, _, _, .pair _ _ e f, h₁, h₂ => by
      simp only [LeCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_of_sites e h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_of_sites f h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .bound _ _, _, _ => rfl
  | _, _, _, .intoBnd e, h₁, h₂ => LeCo.sealsOK_of_sites e h₁ h₂
  | _, _, _, .member P e _, h₁, h₂ => by
      simp only [LeCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | h, _, _, .seal p D, h₁, h₂ => by
      match h, h₁, h₂ with
      | some (.var y), _, h₂ => exact h₂ y (p, D) (by simp [LeCo.sealSite])
      | some (.sel _ _), h₁, _ => simp [LeCo.sealsOK] at h₁
      | none, h₁, _ => simp [LeCo.sealsOK] at h₁
theorem EqCo.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (φ : EqCo s), EqCo.sealsOK ξ φ = true →
    (∀ x C, EqCo.sealSite φ x C = true → ξ' x C = true) → EqCo.sealsOK ξ' φ = true
  | _, _, .refl _, _, _ => rfl
  | _, _, .symm φ, h₁, h₂ => EqCo.sealsOK_of_sites φ h₁ h₂
  | _, _, .trans φ ψ, h₁, h₂ => by
      simp only [EqCo.sealsOK] at h₁ ⊢; bsplit
      exact ⟨EqCo.sealsOK_of_sites φ h₁.1 (fun x C h => h₂ x C (by simp [EqCo.sealSite, h])),
        EqCo.sealsOK_of_sites ψ h₁.2 (fun x C h => h₂ x C (by simp [EqCo.sealSite, h]))⟩
  | _, _, .defP _ _, _, _ => rfl
  | _, _, .lift _ π, h₁, h₂ => PEq.sealsOK_of_sites π h₁ h₂
  | _, _, .dom φ, h₁, h₂ => EqCo.sealsOK_of_sites φ h₁ h₂
  | _, _, .cod φ _, h₁, h₂ => EqCo.sealsOK_of_sites φ h₁ h₂
theorem Morphism.sealsOK_of_sites : ∀ {h : Option (Path s)} {ξ ξ' : Alloc s} (m : Morphism s),
    Morphism.sealsOK h ξ m = true → (∀ x C, Morphism.sealSite h m x C = true → ξ' x C = true) →
    Morphism.sealsOK h ξ' m = true
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .le m pre _ post, h₁, h₂ => by
      simp only [Morphism.sealsOK] at h₁ ⊢; bsplit
      exact ⟨⟨Morphism.sealsOK_of_sites m h₁.1.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_of_sites pre h₁.1.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩,
        Side.sealsOK_of_sites post h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .fld m _ sd, h₁, h₂ => by
      simp only [Morphism.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_of_sites m h₁.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_of_sites sd h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .alias m _, h₁, h₂ => Morphism.sealsOK_of_sites m h₁ h₂
  | _, _, _, .is m e, h₁, h₂ => by
      simp only [Morphism.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_of_sites m h₁.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
theorem Side.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (sd : Side s), Side.sealsOK ξ sd = true →
    (∀ x C, Side.sealSite sd x C = true → ξ' x C = true) → Side.sealsOK ξ' sd = true
  | _, _, .none, _, _ => rfl
  | _, _, .some e, h₁, h₂ => LeCo.sealsOK_of_sites e h₁ h₂
  | _, _, .bot _, _, _ => rfl
  | _, _, .top _, _, _ => rfl
end

mutual
theorem Tm.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (t : Tm s), Tm.sealsOK ξ t = true →
    (∀ x C, Tm.sealSite t x C = true → ξ' x C = true) → Tm.sealsOK ξ' t = true
  | _, _, .path P, h₁, h₂ => PathCo.sealsOK_of_sites P h₁ h₂
  | _, _, .val v, h₁, h₂ => Value.sealsOK_of_sites v h₁ h₂
  | _, _, .app P Q, h₁, h₂ => by
      simp only [Tm.sealsOK] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_of_sites P h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        PathCo.sealsOK_of_sites Q h₁.2 (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
  | ξ, _, .lett t u, h₁, h₂ => by
      simp only [Tm.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Tm.sealsOK_of_sites t h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        Tm.sealsOK_of_sites u h₁.2 (Alloc.cons_of (fun x C h => Tm.sealsOK_site (ξ := ξ.cons (letLbl t)) u h₁.2 h)
          (fun y C h => h₂ y C (by simp [Tm.sealSite, h])))⟩
  | _, _, .cast t e, h₁, h₂ => by
      simp only [Tm.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Tm.sealsOK_of_sites t h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
theorem Value.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (v : Value s), Value.sealsOK ξ v = true →
    (∀ x C, Value.sealSite v x C = true → ξ' x C = true) → Value.sealsOK ξ' v = true
  | ξ, _, .lam _ t, h₁, h₂ =>
      Tm.sealsOK_of_sites t h₁ (Alloc.cons_of (fun x C h => Tm.sealsOK_site (ξ := ξ.cons Lbl.none) t h₁ h)
        (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | ξ, _, .obj _ ds, h₁, h₂ =>
      Defs.sealsOK_of_sites ds h₁ (Alloc.cons_of (fun x C h => Defs.sealsOK_site (ξ := ξ.cons Lbl.any) ds h₁ h)
        (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | _, _, .cast v e, h₁, h₂ => by
      simp only [Value.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Value.sealsOK_of_sites v h₁.1 (fun x C h => h₂ x C (by simp [Value.sealSite, h])),
        LeCo.sealsOK_of_sites e h₁.2 (fun x C h => h₂ x C (by simp [Value.sealSite, h]))⟩
theorem Defs.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (ds : Defs s), Defs.sealsOK ξ ds = true →
    (∀ x C, Defs.sealSite ds x C = true → ξ' x C = true) → Defs.sealsOK ξ' ds = true
  | _, _, .nil, _, _ => rfl
  | _, _, .typ ds _ _, h₁, h₂ => Defs.sealsOK_of_sites ds h₁ h₂
  | _, _, .fld ds _ rhs, h₁, h₂ => by
      simp only [Defs.sealsOK] at h₁ ⊢; bsplit
      exact ⟨Defs.sealsOK_of_sites ds h₁.1 (fun x C h => h₂ x C (by simp [Defs.sealSite, h])),
        Rhs.sealsOK_of_sites rhs h₁.2 (fun x C h => h₂ x C (by simp [Defs.sealSite, h]))⟩
  | _, _, .cls ds _ _, h₁, h₂ => Defs.sealsOK_of_sites ds h₁ h₂
theorem Rhs.sealsOK_of_sites : ∀ {ξ ξ' : Alloc s} (rhs : Rhs s), Rhs.sealsOK ξ rhs = true →
    (∀ x C, Rhs.sealSite rhs x C = true → ξ' x C = true) → Rhs.sealsOK ξ' rhs = true
  | _, _, .path P, h₁, h₂ => PathCo.sealsOK_of_sites P h₁ h₂
  | _, _, .fn v, h₁, h₂ => Value.sealsOK_of_sites v h₁ h₂
  | _, _, .nest _ ds, h₁, h₂ => Defs.sealsOK_of_sites ds h₁ h₂
end

/-- Monotonicity in the labels, from L0 and L1. -/
theorem Tm.sealsOK_mono {ξ ξ' : Alloc s} {t : Tm s} (h : Tm.sealsOK ξ t = true)
    (hm : ∀ x C, ξ x C = true → ξ' x C = true) : Tm.sealsOK ξ' t = true :=
  Tm.sealsOK_of_sites t h (fun x C hs => hm x C (Tm.sealsOK_site t h hs))
theorem LeCo.sealsOK_mono {hd : Option (Path s)} {ξ ξ' : Alloc s} {e : LeCo s} (h : LeCo.sealsOK hd ξ e = true)
    (hm : ∀ x C, ξ x C = true → ξ' x C = true) : LeCo.sealsOK hd ξ' e = true :=
  LeCo.sealsOK_of_sites e h (fun x C hs => hm x C (LeCo.sealsOK_site e h hs))

/-! ### L4: evidence with no seal at its head may act on any path -/

mutual
theorem LeCo.sealsOK_head : ∀ {ξ : Alloc s} (e : LeCo s) (r : Path s), LeCo.sealsOK none ξ e = true →
    LeCo.sealsOK (some r) ξ e = true
  | _, .refl _, _, h => h
  | _, .trans e f, r, h => by
      simp only [LeCo.sealsOK] at h ⊢; bsplit
      exact ⟨LeCo.sealsOK_head e r h.1, LeCo.sealsOK_head f r h.2⟩
  | _, .top _, _, h => h
  | _, .bot _, _, h => h
  | _, .eqToLe _, _, h => h
  | _, .pi _ _, _, h => h
  | _, .obj _ m, r, h => Morphism.sealsOK_head m r h
  | _, .pair _ _ e f, r, h => by
      simp only [LeCo.sealsOK] at h ⊢; bsplit
      exact ⟨LeCo.sealsOK_head e r h.1, LeCo.sealsOK_head f r h.2⟩
  | _, .bound _ _, _, h => h
  | _, .intoBnd e, r, h => LeCo.sealsOK_head e r h
  | _, .member _ _ _, _, h => h
  | _, .seal _ _, _, h => by simp [LeCo.sealsOK] at h
theorem Morphism.sealsOK_head : ∀ {ξ : Alloc s} (m : Morphism s) (r : Path s), Morphism.sealsOK none ξ m = true →
    Morphism.sealsOK (some r) ξ m = true
  | _, .nil, _, h => h
  | _, .le m _ _ _, r, h => by
      simp only [Morphism.sealsOK] at h ⊢; bsplit
      exact ⟨⟨Morphism.sealsOK_head m r h.1.1, h.1.2⟩, h.2⟩
  | _, .fld m _ _, r, h => by
      simp only [Morphism.sealsOK] at h ⊢; bsplit
      exact ⟨Morphism.sealsOK_head m r h.1, h.2⟩
  | _, .alias m _, r, h => Morphism.sealsOK_head m r h
  | _, .is m e, r, h => by
      simp only [Morphism.sealsOK] at h ⊢; bsplit
      exact ⟨Morphism.sealsOK_head m r h.1, LeCo.sealsOK_head e r h.2⟩
end

/-! ### `valShaped` under renaming and substitution -/

theorem Tm.valShaped_rename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂), Tm.valShaped (t.rename ρ) = Tm.valShaped t
  | .path _, _ => rfl
  | .val _, _ => rfl
  | .app _ _, _ => rfl
  | .lett _ _, _ => rfl
  | .cast t _, ρ => Tm.valShaped_rename t ρ

theorem Tm.valShaped_subst : ∀ (t : Tm s₁) (σ : CoSubst s₁ s₂), Tm.valShaped (t.subst σ) = Tm.valShaped t
  | .path _, _ => rfl
  | .val _, _ => rfl
  | .app _ _, _ => rfl
  | .lett _ _, _ => rfl
  | .cast t _, σ => Tm.valShaped_subst t σ

/-! ### L2: renaming -/

theorem Key.weaken_rename (k : Key s₁) (ρ : Rename s₁ s₂) :
    Key.rename (Key.weaken k : Key (s₁,x)) ρ.lift = Key.weaken (Key.rename k ρ) := by
  simp only [Key.rename, Key.weaken, Path.weaken_rename]

theorem Key.weaken_subst_lift (k : Key s₁) (σ : CoSubst s₁ s₂) :
    Key.subst (Key.weaken k : Key (s₁,x)) σ.lift = Key.weaken (Key.subst k σ) := by
  simp only [Key.subst, Key.weaken, CoSubst.lift_paths, Path.weaken_subst_lift]

theorem Alloc.cons_of_rename {ξ : Alloc s₁} {ξ' : Alloc s₂} {ρ : Rename s₁ s₂} {b : Label → Bool}
    {f : BVar (s₁,x) .var → Key (s₁,x) → Bool}
    (h0 : ∀ x C, f x C = true → (ξ.cons b) x C = true)
    (h1 : ∀ y C, f (.there y) (Key.weaken C) = true → ξ' (ρ.var y) (Key.rename C ρ) = true) :
    ∀ x C, f x C = true → (ξ'.cons b) (ρ.lift.var x) (Key.rename C ρ.lift) = true
  | x, C, h => by
      have h' := h0 x C h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      rw [Key.weaken_rename]
      cases x with
      | here =>
          rw [Alloc.cons_here] at h'
          show (ξ'.cons b) .here (Key.weaken (Key.rename k₀ ρ)) = true
          rw [Alloc.cons_here]; exact h'
      | there y =>
          show (ξ'.cons b) (.there (ρ.var y)) (Key.weaken (Key.rename k₀ ρ)) = true
          rw [Alloc.cons_there]; exact h1 y k₀ h

mutual
theorem PEq.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (π : PEq s₁) (ρ : Rename s₁ s₂), PEq.sealsOK ξ π = true →
    (∀ x C, PEq.sealSite π x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → PEq.sealsOK ξ' (π.rename ρ) = true
  | _, _, .refl _, _, _, _ => rfl
  | _, _, .symm π, ρ, h₁, h₂ => PEq.sealsOK_rename π ρ h₁ h₂
  | _, _, .trans π π', ρ, h₁, h₂ => by
      simp only [PEq.sealsOK, PEq.rename] at h₁ ⊢; bsplit
      exact ⟨PEq.sealsOK_rename π ρ h₁.1 (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        PEq.sealsOK_rename π' ρ h₁.2 (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
  | _, _, .sel π _, ρ, h₁, h₂ => PEq.sealsOK_rename π ρ h₁ h₂
  | _, _, .member P e _, ρ, h₁, h₂ => by
      simp only [PEq.sealsOK, PEq.rename] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        LeCo.sealsOK_rename e ρ h₁.2 (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
theorem PathCo.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (P : PathCo s₁) (ρ : Rename s₁ s₂), PathCo.sealsOK ξ P = true →
    (∀ x C, PathCo.sealSite P x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → PathCo.sealsOK ξ' (P.rename ρ) = true
  | _, _, .var _, _, _, _ => rfl
  | _, _, .sel P _ _, ρ, h₁, h₂ => PathCo.sealsOK_rename P ρ h₁ h₂
  | _, _, .cast P e, ρ, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.rename] at h₁ ⊢; bsplit
      refine ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])), ?_⟩
      rw [PathCo.path_rename]
      exact LeCo.sealsOK_rename e ρ h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))
  | _, _, .alias P₀ π Q, ρ, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.rename] at h₁ ⊢; bsplit
      exact ⟨⟨PathCo.sealsOK_rename P₀ ρ h₁.1.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_rename π ρ h₁.1.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩,
        PathCo.sealsOK_rename Q ρ h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .sngl P _ π, ρ, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.rename] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_rename π ρ h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .fldI _ _ Q, ρ, h₁, h₂ => PathCo.sealsOK_rename Q ρ h₁ h₂
  | _, _, .fold _ P, ρ, h₁, h₂ => PathCo.sealsOK_rename P ρ h₁ h₂
  | _, _, .unfold P, ρ, h₁, h₂ => PathCo.sealsOK_rename P ρ h₁ h₂
  | _, _, .both _ _ P Q, ρ, h₁, h₂ => by
      simp only [PathCo.sealsOK, PathCo.rename] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PathCo.sealsOK_rename Q ρ h₁.2 (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
theorem LeCo.sealsOK_rename : ∀ {h : Option (Path s₁)} {ξ : Alloc s₁} {ξ' : Alloc s₂} (e : LeCo s₁) (ρ : Rename s₁ s₂),
    LeCo.sealsOK h ξ e = true → (∀ x C, LeCo.sealSite h e x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) →
    LeCo.sealsOK (h.map (·.rename ρ)) ξ' (e.rename ρ) = true
  | _, _, _, .refl _, _, _, _ => rfl
  | _, _, _, .trans e f, ρ, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.rename] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_rename e ρ h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_rename f ρ h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .top _, _, _, _ => rfl
  | _, _, _, .bot _, _, _, _ => rfl
  | _, _, _, .eqToLe φ, ρ, h₁, h₂ => EqCo.sealsOK_rename φ ρ h₁ h₂
  | _, ξ, _, .pi e f, ρ, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.rename] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_rename e ρ h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_rename (h := none) f ρ.lift h₁.2
          (Alloc.cons_of_rename (fun x C h => LeCo.sealsOK_site (ξ := ξ.cons Lbl.none) f h₁.2 h)
            (fun y C h => h₂ y C (by simp [LeCo.sealSite, h])))⟩
  | _, _, _, .obj _ m, ρ, h₁, h₂ => Morphism.sealsOK_rename m ρ h₁ h₂
  | _, _, _, .pair _ _ e f, ρ, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.rename] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_rename e ρ h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_rename f ρ h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .bound _ _, _, _, _ => rfl
  | _, _, _, .intoBnd e, ρ, h₁, h₂ => LeCo.sealsOK_rename e ρ h₁ h₂
  | _, _, _, .member P e _, ρ, h₁, h₂ => by
      simp only [LeCo.sealsOK, LeCo.rename] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_rename (h := none) e ρ h₁.2 (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | h, _, _, .seal p D, ρ, h₁, h₂ => by
      match h, h₁, h₂ with
      | some (.var y), _, h₂ => exact h₂ y (p, D) (by simp [LeCo.sealSite])
      | some (.sel _ _), h₁, _ => simp [LeCo.sealsOK] at h₁
      | none, h₁, _ => simp [LeCo.sealsOK] at h₁
theorem EqCo.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (φ : EqCo s₁) (ρ : Rename s₁ s₂), EqCo.sealsOK ξ φ = true →
    (∀ x C, EqCo.sealSite φ x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → EqCo.sealsOK ξ' (φ.rename ρ) = true
  | _, _, .refl _, _, _, _ => rfl
  | _, _, .symm φ, ρ, h₁, h₂ => EqCo.sealsOK_rename φ ρ h₁ h₂
  | _, _, .trans φ ψ, ρ, h₁, h₂ => by
      simp only [EqCo.sealsOK, EqCo.rename] at h₁ ⊢; bsplit
      exact ⟨EqCo.sealsOK_rename φ ρ h₁.1 (fun x C h => h₂ x C (by simp [EqCo.sealSite, h])),
        EqCo.sealsOK_rename ψ ρ h₁.2 (fun x C h => h₂ x C (by simp [EqCo.sealSite, h]))⟩
  | _, _, .defP _ _, _, _, _ => rfl
  | _, _, .lift _ π, ρ, h₁, h₂ => PEq.sealsOK_rename π ρ h₁ h₂
  | _, _, .dom φ, ρ, h₁, h₂ => EqCo.sealsOK_rename φ ρ h₁ h₂
  | _, _, .cod φ _, ρ, h₁, h₂ => EqCo.sealsOK_rename φ ρ h₁ h₂
theorem Morphism.sealsOK_rename : ∀ {h : Option (Path s₁)} {ξ : Alloc s₁} {ξ' : Alloc s₂} (m : Morphism s₁)
    (ρ : Rename s₁ s₂), Morphism.sealsOK h ξ m = true →
    (∀ x C, Morphism.sealSite h m x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) →
    Morphism.sealsOK (h.map (·.rename ρ)) ξ' (m.rename ρ) = true
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .le m pre _ post, ρ, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.rename] at h₁ ⊢; bsplit
      exact ⟨⟨Morphism.sealsOK_rename m ρ h₁.1.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_rename pre ρ h₁.1.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩,
        Side.sealsOK_rename post ρ h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .fld m _ sd, ρ, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.rename] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_rename m ρ h₁.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_rename sd ρ h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .alias m _, ρ, h₁, h₂ => Morphism.sealsOK_rename m ρ h₁ h₂
  | _, _, _, .is m e, ρ, h₁, h₂ => by
      simp only [Morphism.sealsOK, Morphism.rename] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_rename m ρ h₁.1 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        LeCo.sealsOK_rename e ρ h₁.2 (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
theorem Side.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (sd : Side s₁) (ρ : Rename s₁ s₂), Side.sealsOK ξ sd = true →
    (∀ x C, Side.sealSite sd x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → Side.sealsOK ξ' (sd.rename ρ) = true
  | _, _, .none, _, _, _ => rfl
  | _, _, .some e, ρ, h₁, h₂ => LeCo.sealsOK_rename (h := none) e ρ h₁ h₂
  | _, _, .bot _, _, _, _ => rfl
  | _, _, .top _, _, _, _ => rfl
end

mutual
theorem Tm.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (t : Tm s₁) (ρ : Rename s₁ s₂), Tm.sealsOK ξ t = true →
    (∀ x C, Tm.sealSite t x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → Tm.sealsOK ξ' (t.rename ρ) = true
  | _, _, .path P, ρ, h₁, h₂ => PathCo.sealsOK_rename P ρ h₁ h₂
  | _, _, .val v, ρ, h₁, h₂ => Value.sealsOK_rename v ρ h₁ h₂
  | _, _, .app P Q, ρ, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.rename] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_rename P ρ h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        PathCo.sealsOK_rename Q ρ h₁.2 (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
  | ξ, _, .lett t u, ρ, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.rename] at h₁ ⊢; bsplit
      refine ⟨Tm.sealsOK_rename t ρ h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])), ?_⟩
      have e : letLbl (t.rename ρ) = letLbl t := by simp only [letLbl, Tm.valShaped_rename]
      rw [e]
      exact Tm.sealsOK_rename u ρ.lift h₁.2
        (Alloc.cons_of_rename (fun x C h => Tm.sealsOK_site (ξ := ξ.cons (letLbl t)) u h₁.2 h)
          (fun y C h => h₂ y C (by simp [Tm.sealSite, h])))
  | _, _, .cast t e, ρ, h₁, h₂ => by
      simp only [Tm.sealsOK, Tm.rename] at h₁ ⊢; bsplit
      exact ⟨Tm.sealsOK_rename t ρ h₁.1 (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        LeCo.sealsOK_rename (h := none) e ρ h₁.2 (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
theorem Value.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (v : Value s₁) (ρ : Rename s₁ s₂), Value.sealsOK ξ v = true →
    (∀ x C, Value.sealSite v x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → Value.sealsOK ξ' (v.rename ρ) = true
  | ξ, _, .lam _ t, ρ, h₁, h₂ =>
      Tm.sealsOK_rename t ρ.lift h₁ (Alloc.cons_of_rename (fun x C h => Tm.sealsOK_site (ξ := ξ.cons Lbl.none) t h₁ h)
        (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | ξ, _, .obj _ ds, ρ, h₁, h₂ =>
      Defs.sealsOK_rename ds ρ.lift h₁ (Alloc.cons_of_rename (fun x C h => Defs.sealsOK_site (ξ := ξ.cons Lbl.any) ds h₁ h)
        (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | _, _, .cast v e, ρ, h₁, h₂ => by
      simp only [Value.sealsOK, Value.rename] at h₁ ⊢; bsplit
      exact ⟨Value.sealsOK_rename v ρ h₁.1 (fun x C h => h₂ x C (by simp [Value.sealSite, h])),
        LeCo.sealsOK_rename (h := none) e ρ h₁.2 (fun x C h => h₂ x C (by simp [Value.sealSite, h]))⟩
theorem Defs.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (ds : Defs s₁) (ρ : Rename s₁ s₂), Defs.sealsOK ξ ds = true →
    (∀ x C, Defs.sealSite ds x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → Defs.sealsOK ξ' (ds.rename ρ) = true
  | _, _, .nil, _, _, _ => rfl
  | _, _, .typ ds _ _, ρ, h₁, h₂ => Defs.sealsOK_rename ds ρ h₁ h₂
  | _, _, .fld ds _ rhs, ρ, h₁, h₂ => by
      simp only [Defs.sealsOK, Defs.rename] at h₁ ⊢; bsplit
      exact ⟨Defs.sealsOK_rename ds ρ h₁.1 (fun x C h => h₂ x C (by simp [Defs.sealSite, h])),
        Rhs.sealsOK_rename rhs ρ h₁.2 (fun x C h => h₂ x C (by simp [Defs.sealSite, h]))⟩
  | _, _, .cls ds _ _, ρ, h₁, h₂ => Defs.sealsOK_rename ds ρ h₁ h₂
theorem Rhs.sealsOK_rename : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (rhs : Rhs s₁) (ρ : Rename s₁ s₂), Rhs.sealsOK ξ rhs = true →
    (∀ x C, Rhs.sealSite rhs x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) → Rhs.sealsOK ξ' (rhs.rename ρ) = true
  | _, _, .path P, ρ, h₁, h₂ => PathCo.sealsOK_rename P ρ h₁ h₂
  | _, _, .fn v, ρ, h₁, h₂ => Value.sealsOK_rename v ρ h₁ h₂
  | _, _, .nest _ ds, ρ, h₁, h₂ => Defs.sealsOK_rename ds ρ h₁ h₂
end

/-! ### L3: substitution by path evidence -/

/-- The path evidence of a substitution meets the predicate under a binder. -/
theorem CoSubst.lift_ok {ξ' : Alloc s₂} {b : Label → Bool} {σ : CoSubst s₁ s₂}
    (hσ : ∀ x, PathCo.sealsOK ξ' (σ.var x) = true) : ∀ x, PathCo.sealsOK (ξ'.cons b) (σ.lift.var x) = true
  | .here => rfl
  | .there y => PathCo.sealsOK_rename (σ.var y) Rename.succ (hσ y)
      (fun x C h => by
        show (ξ'.cons b) (.there x) (Key.weaken C) = true
        rw [Alloc.cons_there]
        exact PathCo.sealsOK_site (σ.var y) (hσ y) h)

/-- The sites under a binder go to variables admitted at the same keys. -/
theorem CoSubst.lift_sites {ξ : Alloc s₁} {ξ' : Alloc s₂} {b : Label → Bool} {σ : CoSubst s₁ s₂}
    {f : BVar (s₁,x) .var → Key (s₁,x) → Bool}
    (h0 : ∀ x C, f x C = true → (ξ.cons b) x C = true)
    (h1 : ∀ y C, f (.there y) (Key.weaken C) = true → ∃ z, (σ.var y).path = .var z ∧ ξ' z (Key.subst C σ) = true) :
    ∀ x C, f x C = true → ∃ z, (σ.lift.var x).path = .var z ∧ (ξ'.cons b) z (Key.subst C σ.lift) = true
  | x, C, h => by
      have h' := h0 x C h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      rw [Key.weaken_subst_lift]
      cases x with
      | here =>
          rw [Alloc.cons_here] at h'
          refine ⟨.here, rfl, ?_⟩
          rw [Alloc.cons_here]; exact h'
      | there y =>
          obtain ⟨z, hz, hC⟩ := h1 y k₀ h
          refine ⟨.there z, ?_, ?_⟩
          · show ((σ.var y).rename Rename.succ).path = _
            rw [PathCo.path_rename, hz]
            rfl
          · rw [Alloc.cons_there]; exact hC

mutual
theorem PEq.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (π : PEq s₁) (σ : CoSubst s₁ s₂), PEq.sealsOK ξ π = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, PEq.sealSite π x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    PEq.sealsOK ξ' (π.subst σ) = true
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .symm π, σ, h₁, hσ, h₂ => PEq.sealsOK_subst π σ h₁ hσ h₂
  | _, _, .trans π π', σ, h₁, hσ, h₂ => by
      simp only [PEq.sealsOK, PEq.subst] at h₁ ⊢; bsplit
      exact ⟨PEq.sealsOK_subst π σ h₁.1 hσ (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        PEq.sealsOK_subst π' σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
  | _, _, .sel π _, σ, h₁, hσ, h₂ => PEq.sealsOK_subst π σ h₁ hσ h₂
  | _, _, .member P e _, σ, h₁, hσ, h₂ => by
      simp only [PEq.sealsOK, PEq.subst] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [PEq.sealSite, h])),
        LeCo.sealsOK_subst (h := none) e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PEq.sealSite, h]))⟩
theorem PathCo.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (P : PathCo s₁) (σ : CoSubst s₁ s₂), PathCo.sealsOK ξ P = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, PathCo.sealSite P x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    PathCo.sealsOK ξ' (P.subst σ) = true
  | _, _, .var x, _, _, hσ, _ => hσ x
  | _, _, .sel P _ _, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst P σ h₁ hσ h₂
  | _, _, .cast P e, σ, h₁, hσ, h₂ => by
      simp only [PathCo.sealsOK, PathCo.subst] at h₁ ⊢; bsplit
      refine ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])), ?_⟩
      rw [PathCo.path_subst]
      exact LeCo.sealsOK_subst e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))
  | _, _, .alias P₀ π Q, σ, h₁, hσ, h₂ => by
      simp only [PathCo.sealsOK, PathCo.subst] at h₁ ⊢; bsplit
      exact ⟨⟨PathCo.sealsOK_subst P₀ σ h₁.1.1 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_subst π σ h₁.1.2 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩,
        PathCo.sealsOK_subst Q σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .sngl P _ π, σ, h₁, hσ, h₂ => by
      simp only [PathCo.sealsOK, PathCo.subst] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PEq.sealsOK_subst π σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
  | _, _, .fldI _ _ Q, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst Q σ h₁ hσ h₂
  | _, _, .fold _ P, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst P σ h₁ hσ h₂
  | _, _, .unfold P, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst P σ h₁ hσ h₂
  | _, _, .both _ _ P Q, σ, h₁, hσ, h₂ => by
      simp only [PathCo.sealsOK, PathCo.subst] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h])),
        PathCo.sealsOK_subst Q σ h₁.2 hσ (fun x C h => h₂ x C (by simp [PathCo.sealSite, h]))⟩
theorem LeCo.sealsOK_subst : ∀ {h : Option (Path s₁)} {ξ : Alloc s₁} {ξ' : Alloc s₂} (e : LeCo s₁) (σ : CoSubst s₁ s₂),
    LeCo.sealsOK h ξ e = true → (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, LeCo.sealSite h e x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    LeCo.sealsOK (h.map (·.subst σ.paths)) ξ' (e.subst σ) = true
  | _, _, _, .refl _, _, _, _, _ => rfl
  | _, _, _, .trans e f, σ, h₁, hσ, h₂ => by
      simp only [LeCo.sealsOK, LeCo.subst] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_subst e σ h₁.1 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_subst f σ h₁.2 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .top _, _, _, _, _ => rfl
  | _, _, _, .bot _, _, _, _, _ => rfl
  | _, _, _, .eqToLe φ, σ, h₁, hσ, h₂ => EqCo.sealsOK_subst φ σ h₁ hσ h₂
  | _, ξ, _, .pi e f, σ, h₁, hσ, h₂ => by
      simp only [LeCo.sealsOK, LeCo.subst] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_subst (h := none) e σ h₁.1 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_subst (h := none) f σ.lift h₁.2 (CoSubst.lift_ok hσ)
          (CoSubst.lift_sites (fun x C h => LeCo.sealsOK_site (ξ := ξ.cons Lbl.none) f h₁.2 h)
            (fun y C h => h₂ y C (by simp [LeCo.sealSite, h])))⟩
  | _, _, _, .obj _ m, σ, h₁, hσ, h₂ => Morphism.sealsOK_subst m σ h₁ hσ h₂
  | _, _, _, .pair _ _ e f, σ, h₁, hσ, h₂ => by
      simp only [LeCo.sealsOK, LeCo.subst] at h₁ ⊢; bsplit
      exact ⟨LeCo.sealsOK_subst e σ h₁.1 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_subst f σ h₁.2 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | _, _, _, .bound _ _, _, _, _, _ => rfl
  | _, _, _, .intoBnd e, σ, h₁, hσ, h₂ => LeCo.sealsOK_subst e σ h₁ hσ h₂
  | _, _, _, .member P e _, σ, h₁, hσ, h₂ => by
      simp only [LeCo.sealsOK, LeCo.subst] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h])),
        LeCo.sealsOK_subst (h := none) e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [LeCo.sealSite, h]))⟩
  | h, _, _, .seal p D, σ, h₁, _, h₂ => by
      match h, h₁, h₂ with
      | some (.var y), _, h₂ =>
          obtain ⟨z, hz, hC⟩ := h₂ y (p, D) (by simp [LeCo.sealSite])
          show LeCo.sealsOK (some (σ.var y).path) _ _ = true
          rw [hz]
          exact hC
      | some (.sel _ _), h₁, _ => simp [LeCo.sealsOK] at h₁
      | none, h₁, _ => simp [LeCo.sealsOK] at h₁
theorem EqCo.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (φ : EqCo s₁) (σ : CoSubst s₁ s₂), EqCo.sealsOK ξ φ = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, EqCo.sealSite φ x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    EqCo.sealsOK ξ' (φ.subst σ) = true
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .symm φ, σ, h₁, hσ, h₂ => EqCo.sealsOK_subst φ σ h₁ hσ h₂
  | _, _, .trans φ ψ, σ, h₁, hσ, h₂ => by
      simp only [EqCo.sealsOK, EqCo.subst] at h₁ ⊢; bsplit
      exact ⟨EqCo.sealsOK_subst φ σ h₁.1 hσ (fun x C h => h₂ x C (by simp [EqCo.sealSite, h])),
        EqCo.sealsOK_subst ψ σ h₁.2 hσ (fun x C h => h₂ x C (by simp [EqCo.sealSite, h]))⟩
  | _, _, .defP _ _, _, _, _, _ => rfl
  | _, _, .lift _ π, σ, h₁, hσ, h₂ => PEq.sealsOK_subst π σ h₁ hσ h₂
  | _, _, .dom φ, σ, h₁, hσ, h₂ => EqCo.sealsOK_subst φ σ h₁ hσ h₂
  | _, _, .cod φ _, σ, h₁, hσ, h₂ => EqCo.sealsOK_subst φ σ h₁ hσ h₂
theorem Morphism.sealsOK_subst : ∀ {h : Option (Path s₁)} {ξ : Alloc s₁} {ξ' : Alloc s₂} (m : Morphism s₁)
    (σ : CoSubst s₁ s₂), Morphism.sealsOK h ξ m = true → (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Morphism.sealSite h m x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Morphism.sealsOK (h.map (·.subst σ.paths)) ξ' (m.subst σ) = true
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .le m pre _ post, σ, h₁, hσ, h₂ => by
      simp only [Morphism.sealsOK, Morphism.subst] at h₁ ⊢; bsplit
      exact ⟨⟨Morphism.sealsOK_subst m σ h₁.1.1 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_subst pre σ h₁.1.2 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩,
        Side.sealsOK_subst post σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .fld m _ sd, σ, h₁, hσ, h₂ => by
      simp only [Morphism.sealsOK, Morphism.subst] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_subst m σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        Side.sealsOK_subst sd σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
  | _, _, _, .alias m _, σ, h₁, hσ, h₂ => Morphism.sealsOK_subst m σ h₁ hσ h₂
  | _, _, _, .is m e, σ, h₁, hσ, h₂ => by
      simp only [Morphism.sealsOK, Morphism.subst] at h₁ ⊢; bsplit
      exact ⟨Morphism.sealsOK_subst m σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h])),
        LeCo.sealsOK_subst e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Morphism.sealSite, h]))⟩
theorem Side.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (sd : Side s₁) (σ : CoSubst s₁ s₂), Side.sealsOK ξ sd = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Side.sealSite sd x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Side.sealsOK ξ' (sd.subst σ) = true
  | _, _, .none, _, _, _, _ => rfl
  | _, _, .some e, σ, h₁, hσ, h₂ => LeCo.sealsOK_subst (h := none) e σ h₁ hσ h₂
  | _, _, .bot _, _, _, _, _ => rfl
  | _, _, .top _, _, _, _, _ => rfl
end

mutual
theorem Tm.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (t : Tm s₁) (σ : CoSubst s₁ s₂), Tm.sealsOK ξ t = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Tm.sealSite t x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Tm.sealsOK ξ' (t.subst σ) = true
  | _, _, .path P, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst P σ h₁ hσ h₂
  | _, _, .val v, σ, h₁, hσ, h₂ => Value.sealsOK_subst v σ h₁ hσ h₂
  | _, _, .app P Q, σ, h₁, hσ, h₂ => by
      simp only [Tm.sealsOK, Tm.subst] at h₁ ⊢; bsplit
      exact ⟨PathCo.sealsOK_subst P σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        PathCo.sealsOK_subst Q σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
  | ξ, _, .lett t u, σ, h₁, hσ, h₂ => by
      simp only [Tm.sealsOK, Tm.subst] at h₁ ⊢; bsplit
      refine ⟨Tm.sealsOK_subst t σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Tm.sealSite, h])), ?_⟩
      have e : letLbl (t.subst σ) = letLbl t := by simp only [letLbl, Tm.valShaped_subst]
      rw [e]
      exact Tm.sealsOK_subst u σ.lift h₁.2 (CoSubst.lift_ok hσ)
        (CoSubst.lift_sites (fun x C h => Tm.sealsOK_site (ξ := ξ.cons (letLbl t)) u h₁.2 h)
          (fun y C h => h₂ y C (by simp [Tm.sealSite, h])))
  | _, _, .cast t e, σ, h₁, hσ, h₂ => by
      simp only [Tm.sealsOK, Tm.subst] at h₁ ⊢; bsplit
      exact ⟨Tm.sealsOK_subst t σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Tm.sealSite, h])),
        LeCo.sealsOK_subst (h := none) e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Tm.sealSite, h]))⟩
theorem Value.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (v : Value s₁) (σ : CoSubst s₁ s₂), Value.sealsOK ξ v = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Value.sealSite v x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Value.sealsOK ξ' (v.subst σ) = true
  | ξ, _, .lam _ t, σ, h₁, hσ, h₂ =>
      Tm.sealsOK_subst t σ.lift h₁ (CoSubst.lift_ok hσ)
        (CoSubst.lift_sites (fun x C h => Tm.sealsOK_site (ξ := ξ.cons Lbl.none) t h₁ h)
          (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | ξ, _, .obj _ ds, σ, h₁, hσ, h₂ =>
      Defs.sealsOK_subst ds σ.lift h₁ (CoSubst.lift_ok hσ)
        (CoSubst.lift_sites (fun x C h => Defs.sealsOK_site (ξ := ξ.cons Lbl.any) ds h₁ h)
          (fun y C h => h₂ y C (by simp [Value.sealSite, h])))
  | _, _, .cast v e, σ, h₁, hσ, h₂ => by
      simp only [Value.sealsOK, Value.subst] at h₁ ⊢; bsplit
      exact ⟨Value.sealsOK_subst v σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Value.sealSite, h])),
        LeCo.sealsOK_subst (h := none) e σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Value.sealSite, h]))⟩
theorem Defs.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (ds : Defs s₁) (σ : CoSubst s₁ s₂), Defs.sealsOK ξ ds = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Defs.sealSite ds x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Defs.sealsOK ξ' (ds.subst σ) = true
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .typ ds _ _, σ, h₁, hσ, h₂ => Defs.sealsOK_subst ds σ h₁ hσ h₂
  | _, _, .fld ds _ rhs, σ, h₁, hσ, h₂ => by
      simp only [Defs.sealsOK, Defs.subst] at h₁ ⊢; bsplit
      exact ⟨Defs.sealsOK_subst ds σ h₁.1 hσ (fun x C h => h₂ x C (by simp [Defs.sealSite, h])),
        Rhs.sealsOK_subst rhs σ h₁.2 hσ (fun x C h => h₂ x C (by simp [Defs.sealSite, h]))⟩
  | _, _, .cls ds _ _, σ, h₁, hσ, h₂ => Defs.sealsOK_subst ds σ h₁ hσ h₂
theorem Rhs.sealsOK_subst : ∀ {ξ : Alloc s₁} {ξ' : Alloc s₂} (rhs : Rhs s₁) (σ : CoSubst s₁ s₂), Rhs.sealsOK ξ rhs = true →
    (∀ x, PathCo.sealsOK ξ' (σ.var x) = true) →
    (∀ x C, Rhs.sealSite rhs x C = true → ∃ y, (σ.var x).path = .var y ∧ ξ' y (Key.subst C σ) = true) →
    Rhs.sealsOK ξ' (rhs.subst σ) = true
  | _, _, .path P, σ, h₁, hσ, h₂ => PathCo.sealsOK_subst P σ h₁ hσ h₂
  | _, _, .fn v, σ, h₁, hσ, h₂ => Value.sealsOK_subst v σ h₁ hσ h₂
  | _, _, .nest _ ds, σ, h₁, hσ, h₂ => Defs.sealsOK_subst ds σ h₁ hσ h₂
end

/-! ## Preservation -/

theorem Key.weaken_subst_one (k : Key s) (Q : PathCo s) : Key.subst (Key.weaken k : Key (s,x)) (CoSubst.one Q) = k := by
  obtain ⟨q, C⟩ := k
  simp only [Key.subst, Key.weaken, CoSubst.one_paths, Path.subst_one]
  congr 1
  induction q with
  | var y => rfl
  | sel q a ih => exact congrArg (Path.sel · a) ih

theorem Key.subst_selfCast (k : Key (s,x)) (E : LeCo s) : Key.subst k (CoSubst.selfCast E) = k := by
  obtain ⟨q, C⟩ := k
  simp only [Key.subst, CoSubst.selfCast_paths, Path.subst_ofRename, Path.rename_id]

theorem Value.sealsOK_core {ξ : Alloc s} : ∀ (v : Value s), Value.sealsOK ξ v = true → Value.sealsOK ξ v.core = true
  | .lam _ _, h => h
  | .obj _ _, h => h
  | .cast v _, h => by
      simp only [Value.sealsOK, Bool.and_eq_true] at h
      exact Value.sealsOK_core v h.1

theorem Value.sealsOK_composite {ξ : Alloc s} : ∀ (v : Value s) {E : LeCo s}, Value.sealsOK ξ v = true →
    v.composite = some E → LeCo.sealsOK none ξ E = true
  | .lam _ _, _, _, h => by simp [Value.composite] at h
  | .obj _ _, _, _, h => by simp [Value.composite] at h
  | .cast v e, E, hv, hc => by
      simp only [Value.sealsOK, Bool.and_eq_true] at hv
      simp only [Value.composite, Option.some.injEq] at hc
      cases hc' : v.composite with
      | none => rw [hc'] at hc; simp only at hc; subst hc; exact hv.2
      | some E' =>
          rw [hc'] at hc; simp only at hc; subst hc
          simp only [LeCo.sealsOK, Bool.and_eq_true]
          exact ⟨Value.sealsOK_composite v hv.1 hc', hv.2⟩

/-- The frames under a renaming that keeps every admitted key. -/
theorem Cont.sealsOK_rename {ξ : Alloc s₁} {ξ' : Alloc s₂} {ρ : Rename s₁ s₂}
    (hm : ∀ x C, ξ x C = true → ξ' (ρ.var x) (Key.rename C ρ) = true) : ∀ (b : Bool) (K : Cont s₁),
    Cont.sealsOK ξ b K = true → Cont.sealsOK ξ' b (K.rename ρ) = true
  | _, .nil, _ => rfl
  | b, .cons K (.lett u), h => by
      simp only [Cont.sealsOK, Bool.and_eq_true] at h
      simp only [Cont.rename, Frame.rename, Cont.sealsOK, Bool.and_eq_true]
      refine ⟨Tm.sealsOK_rename u ρ.lift h.1
        (Alloc.cons_of_rename (fun x C hs => Tm.sealsOK_site u h.1 hs)
          (fun y C hs => hm y C (by have := Tm.sealsOK_site u h.1 hs; rwa [Alloc.cons_there] at this))),
        Cont.sealsOK_rename hm false K h.2⟩
  | b, .cons K (.cast e), h => by
      simp only [Cont.sealsOK, Bool.and_eq_true] at h
      simp only [Cont.rename, Frame.rename, Cont.sealsOK, Bool.and_eq_true]
      exact ⟨LeCo.sealsOK_rename (h := none) e ρ h.1 (fun x C hs => hm x C (LeCo.sealsOK_site e h.1 hs)),
        Cont.sealsOK_rename hm b K h.2⟩

/-- A hole that receives no value with certainty admits fewer seals at the binder of its `let`. -/
theorem Cont.sealsOK_of_false {ξ : Alloc s} : ∀ (b : Bool) (K : Cont s), Cont.sealsOK ξ false K = true →
    Cont.sealsOK ξ b K = true
  | _, .nil, _ => rfl
  | b, .cons K (.lett u), h => by
      simp only [Cont.sealsOK, Bool.and_eq_true] at h
      simp only [Cont.sealsOK, Bool.and_eq_true]
      refine ⟨Tm.sealsOK_mono h.1 (fun x C hx => ?_), h.2⟩
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true hx
      cases x with
      | here => simp [Alloc.cons_here, Lbl.none] at hx
      | there y => rw [Alloc.cons_there] at hx ⊢; exact hx
  | b, .cons K (.cast e), h => by
      simp only [Cont.sealsOK, Bool.and_eq_true] at h
      simp only [Cont.sealsOK, Bool.and_eq_true]
      exact ⟨h.1, Cont.sealsOK_of_false b K h.2⟩

/-- Substitution of the newest variable, which admits no seal, by path evidence that meets the predicate. -/
theorem Tm.sealsOK_substCo {A : Alloc s} {u : Tm (s,x)} {Q : PathCo s} (hu : Tm.sealsOK (A.cons Lbl.none) u = true)
    (hQ : PathCo.sealsOK A Q = true) : Tm.sealsOK A (u.substCo Q) = true :=
  Tm.sealsOK_subst u (CoSubst.one Q) hu
    (fun x => by cases x with | here => exact hQ | there y => rfl)
    (fun x C h => by
      have h' := Tm.sealsOK_site u hu h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      rw [Key.weaken_subst_one]
      cases x with
      | here => simp [Alloc.cons_here, Lbl.none] at h'
      | there y => rw [Alloc.cons_there] at h'; exact ⟨y, rfl, h'⟩)

theorem LeCo.sealsOK_substCo {A : Alloc s} {c : LeCo (s,x)} {Q : PathCo s}
    (hc : LeCo.sealsOK none (A.cons Lbl.none) c = true) (hQ : PathCo.sealsOK A Q = true) :
    LeCo.sealsOK none A (c.substCo Q) = true :=
  LeCo.sealsOK_subst (h := none) c (CoSubst.one Q) hc
    (fun x => by cases x with | here => exact hQ | there y => rfl)
    (fun x C h => by
      have h' := LeCo.sealsOK_site c hc h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      rw [Key.weaken_subst_one]
      cases x with
      | here => simp [Alloc.cons_here, Lbl.none] at h'
      | there y => rw [Alloc.cons_there] at h'; exact ⟨y, rfl, h'⟩)

/-- The keys below the new variable are those of `A`. -/
theorem Alloc.consO_weaken_ok {A : Alloc s} {b : Key s → Bool} (x : BVar s .var) (C : Key s) (hx : A x C = true) :
    (A.consO b) (Rename.succ.var x) (Key.rename C Rename.succ) = true := by
  show (A.consO b) (.there x) (Key.weaken C) = true
  rw [Alloc.consO_there]; exact hx

/-- MS-LetVal's body, through `adjust`: the new variable admits exactly the keys `allocLbl u v`. -/
theorem Tm.sealsOK_adjust {A : Alloc s} {u : Tm (s,x)} {v : Value s} (hu : Tm.sealsOK (A.cons Lbl.any) u = true)
    (hv : Value.sealsOK A v = true) : Tm.sealsOK (A.consO (allocLbl u v)) (u.adjust v) = true := by
  have hsite : ∀ x C, Tm.sealSite u x C = true → (A.consO (allocLbl u v)) x C = true := fun x C h => by
    have h' := Tm.sealsOK_site u hu h
    obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
    cases x with
    | here => rw [Alloc.consO_here]; simp [allocLbl, h]
    | there y => rw [Alloc.cons_there] at h'; rw [Alloc.consO_there]; exact h'
  unfold Tm.adjust
  cases hc : v.composite with
  | none => exact Tm.sealsOK_of_sites u hu hsite
  | some E =>
      have hE : LeCo.sealsOK none A E = true := Value.sealsOK_composite v hv hc
      have hE' : LeCo.sealsOK none (A.consO (allocLbl u v)) (E.rename Rename.succ) = true :=
        LeCo.sealsOK_rename (h := none) E Rename.succ hE
          (fun x C hs => Alloc.consO_weaken_ok x C (LeCo.sealsOK_site E hE hs))
      exact Tm.sealsOK_subst u (CoSubst.selfCast E) hu
        (fun x => by
          cases x with
          | here =>
              show (true && LeCo.sealsOK (some (Path.var .here)) _ (E.rename Rename.succ)) = true
              simp only [Bool.true_and]
              exact LeCo.sealsOK_head _ _ hE'
          | there y => rfl)
        (fun x C h => by
          rw [Key.subst_selfCast]
          cases x with
          | here => exact ⟨.here, rfl, hsite .here C h⟩
          | there y => exact ⟨.there y, rfl, hsite (.there y) C h⟩)

/-- The stored value of MS-LetVal. -/
theorem Stored.sealsOK_alloc {A : Alloc s} {u : Tm (s,x)} {v : Value s} (hv : Value.sealsOK A v = true) :
    Stored.sealsOK (A.consO (allocLbl u v)) v.core = true := by
  have hc := Value.sealsOK_core v hv
  rcases Value.core_shape v with ⟨S, t, e⟩ | ⟨Tel, ds, e⟩
  · rw [e] at hc ⊢
    show Value.sealsOK (A.consO (allocLbl u v)).tail (.lam S t) = true
    rw [Alloc.consO_tail]; exact hc
  · rw [e] at hc ⊢
    show Defs.sealsOK ((A.consO (allocLbl u v)).tail.consO (fun k => (A.consO (allocLbl u v)) .here k.weaken)) ds = true
    have e2 : (fun k => (A.consO (allocLbl u v)) .here (Key.weaken k)) = allocLbl u v := by
      funext k; exact Alloc.consO_here _ _ k
    rw [Alloc.consO_tail, e2]
    exact Defs.sealsOK_of_sites ds hc (fun x C h => by
      have h' := Defs.sealsOK_site ds hc h
      obtain ⟨k₀, rfl⟩ := Alloc.consO_true h'
      cases x with
      | here => rw [Alloc.consO_here]; simp [allocLbl, Value.selfLbl, e, h]
      | there y => rw [Alloc.cons_there] at h'; rw [Alloc.consO_there]; exact h')

/-- **Preservation.**  Every rule of the machine keeps the state predicate, with the records of `AStep`,
over every application view that meets `AppView.SealsOK`. -/
theorem AStep.sealsAtCtors {V : AppView} (hV : AppView.SealsOK V) {g : AState s} {g' : AState s'}
    (h : AStep V g g') (hg : State.SealsAtCtors g.A g.st = true) : State.SealsAtCtors g'.A g'.st = true := by
  cases h with
  | lett =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Cont.sealsOK, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨hg.1.1, by simpa [letLbl] using hg.2.2, hg.1.2⟩, hg.2.1⟩
  | castPush =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Cont.sealsOK, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨hg.1.1, hg.2.2, hg.1.2⟩, hg.2.1⟩
  | castVal =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Value.sealsOK, Cont.sealsOK, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨hg.1.1, hg.1.2.2⟩, hg.2, hg.1.2.1⟩
  | castPath =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, PathCo.sealsOK, Cont.sealsOK, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨hg.1.1, hg.1.2.2⟩, hg.2, LeCo.sealsOK_head _ _ hg.1.2.1⟩
  | @letVal σ K u v A =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Cont.sealsOK, Bool.and_eq_true, if_true] at hg
      obtain ⟨⟨hσ, hu, hK⟩, hv⟩ := hg
      simp only [State.SealsAtCtors, Store.sealsOK, Bool.and_eq_true]
      refine ⟨⟨⟨by rw [Alloc.consO_tail]; exact hσ, Stored.sealsOK_alloc hv⟩, ?_⟩, Tm.sealsOK_adjust hu hv⟩
      exact Cont.sealsOK_of_false _ _
        (Cont.sealsOK_rename (ρ := Rename.succ) (fun x C hx => Alloc.consO_weaken_ok x C hx) false K hK)
  | letPath =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Cont.sealsOK, Bool.and_eq_true] at hg
      obtain ⟨⟨hσ, hu, hK⟩, hP⟩ := hg
      simp only [State.SealsAtCtors, Bool.and_eq_true]
      exact ⟨⟨hσ, Cont.sealsOK_of_false _ _ hK⟩, Tm.sealsOK_substCo (by simpa using hu) hP⟩
  | appId hv =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Bool.and_eq_true] at hg
      obtain ⟨⟨hσ, hK⟩, hP, hQ⟩ := hg
      obtain ⟨ht, _⟩ := hV _ hv hσ hP
      simp only [State.SealsAtCtors, Bool.and_eq_true]
      exact ⟨⟨hσ, Cont.sealsOK_of_false _ _ hK⟩, Tm.sealsOK_substCo ht hQ⟩
  | appPi hv =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Bool.and_eq_true] at hg
      obtain ⟨⟨hσ, hK⟩, hP, hQ⟩ := hg
      obtain ⟨ht, hh⟩ := hV _ hv hσ hP
      simp only [AppHead.sealsOK, Bool.and_eq_true] at hh
      simp only [State.SealsAtCtors, Tm.sealsOK, Bool.and_eq_true]
      refine ⟨⟨hσ, Cont.sealsOK_of_false _ _ hK⟩, Tm.sealsOK_substCo ht ?_, LeCo.sealsOK_substCo hh.2 hQ⟩
      simp only [PathCo.sealsOK, Bool.and_eq_true]
      exact ⟨hQ, LeCo.sealsOK_head _ _ hh.1⟩
  | appEq hv =>
      simp only [State.SealsAtCtors, Tm.valShaped, Tm.sealsOK, Bool.and_eq_true] at hg
      obtain ⟨⟨hσ, hK⟩, hP, hQ⟩ := hg
      obtain ⟨ht, hh⟩ := hV _ hv hσ hP
      simp only [AppHead.sealsOK] at hh
      simp only [State.SealsAtCtors, Tm.sealsOK, Bool.and_eq_true]
      refine ⟨⟨hσ, Cont.sealsOK_of_false _ _ hK⟩, Tm.sealsOK_substCo ht ?_, ?_⟩
      · simp only [PathCo.sealsOK, LeCo.sealsOK, EqCo.sealsOK, Bool.and_eq_true]
        exact ⟨hQ, hh⟩
      · simp only [LeCo.sealsOK, EqCo.sealsOK]
        exact hh

theorem ASteps.sealsAtCtors {V : AppView} (hV : AppView.SealsOK V) {g : AState s} {g' : AState s'}
    (h : ASteps V g g') (hg : State.SealsAtCtors g.A g.st = true) : State.SealsAtCtors g'.A g'.st = true := by
  induction h with
  | refl => exact hg
  | tail _ h ih => exact AStep.sealsAtCtors hV h (ih hg)

theorem init_sealsAtCtors {t : Tm []} (ht : Tm.InitSeals t = true) :
    State.SealsAtCtors Alloc.empty (⟨.nil, .nil, t⟩ : State []) = true := by
  simp only [State.SealsAtCtors, Store.sealsOK, Cont.sealsOK, Bool.true_and]
  exact ht

/-- **The reachable-state theorem**: every state that a program meeting the initial condition reaches
has allocation records, the function of the run that `AStep` computes, under which it meets the
predicate and every owner is older than the variable it seals. -/
theorem reachable_sealsAtCtors {V : AppView} (hV : AppView.SealsOK V) {t : Tm []} {s' : Sig} {st : State s'}
    (ht : Tm.InitSeals t = true) (run : Steps V ⟨.nil, .nil, t⟩ st) :
    ∃ A : Alloc s', ASteps V ⟨⟨.nil, .nil, t⟩, Alloc.empty⟩ ⟨st, A⟩ ∧ State.SealsAtCtors A st = true ∧
      A.OwnersOlder := by
  obtain ⟨A, hA⟩ := Steps.alloc run Alloc.empty
  exact ⟨A, hA, ASteps.sealsAtCtors hV hA (init_sealsAtCtors ht), ASteps.ownersOlder hA Alloc.empty_ownersOlder⟩

/-- The path in focus of a state that meets the predicate meets it. -/
theorem State.focus_sealsOK {A : Alloc s} {st : State s} {P : PathCo s} (h : State.SealsAtCtors A st = true)
    (hP : st.t = .path P) : PathCo.sealsOK A P = true := by
  simp only [State.SealsAtCtors, Bool.and_eq_true] at h
  have := h.2; rw [hP] at this; exact this


end Nominal.FCn
