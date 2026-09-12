import Coercions.Classifiers.DotMNF.Typing

namespace Classifiers

/-!
# DOT-MNF^cc store machine

A state is a store of values, a continuation of `let` frames, and a running
term, all indexed by one signature.  Allocation extends the signature.  The
two steps that enter a body enter three binders and two binders at once, so
they use the substitution of `DotMNF.Subst`; every other step still moves by
a renaming.

This is Plan III §3.5 plus the unboxing step of stage A3a:

```text
⟨σ, K, let x = t in u⟩                       ⟶  ⟨σ, K ▹ (x. u), t⟩
⟨σ, K ▹ (x. u), v⟩                           ⟶  ⟨σ, v ; K↑, u⟩
⟨σ, K ▹ (x. u), y⟩                           ⟶  ⟨σ, K, u[x := y]⟩
⟨σ, K, x y⟩       σ(x) = λ[κ](z : T) t       ⟶  ⟨σ, K, t[enter y]⟩
⟨σ, K, x.a⟩       σ(x) = ν[κ](z. d), d ∋ {a = t} ⟶  ⟨σ, K, t[enterObj x]⟩
⟨σ, K, C ⊸ x⟩     σ(x) = □ y                 ⟶  ⟨σ, K, y⟩
```

A store now has a data-free slot for a capture binder, as the runtime's
does, so that erasure maps slot to slot; a box is a value and is allocated
by `alloc` like any other.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Stores -/

/-- A store: one value per term binder of the signature, and a data-free
slot per capture binder.  (`consᶜ` of the plan: `ᶜ` is not a legal Lean
identifier character, so the capture-sort twin of a name carries the suffix
`C`.) -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)
  | consC : Store s → Store (s,c)

/-- The value stored at a binder, weakened into the current scope; lookup
weakens through a capture slot as it does through a term slot. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken
  | .consC σ, .there y => (σ.lookup y).weaken

/-! ## The platform prefix

A program is typed under a prefix of capture binders, the platform
capabilities.  Its initial store is the store of those slots, and nothing
else: a capture slot carries no value. -/

/-- Evidence that a signature is a prefix of capture binders.  A binder is
either plain, as it was, or declares a classifier, which is the seventh
context flavour of K2 read at the platform (decision 10 and D7). -/
inductive Platform : Sig → Type where
  | nil : Platform []
  | cons : Platform s → Platform (s,c)
  | consCls : Platform s → Cls.Classifier → Platform (s,c)

/-- The initial store over a platform prefix: one data-free slot per
binder.  A classifier is not runtime content, so a classified binder gets the
same slot a plain one gets. -/
def Platform.store : Platform s → Store s
  | .nil => .nil
  | .cons P => .consC P.store
  | .consCls P _ => .consC P.store

/-- The classifier a platform binder declares.  A plain binder declares none,
and reads as the root classifier `⊤`, which is what `FCdot.Ctx.classOf`
answers at a bound with no declaration. -/
def Platform.classOf : Platform s → BVar s .cap → Cls.Classifier
  | .consCls _ c, .here => c
  | .consCls P _, .there κ => P.classOf κ
  | .cons P, .there κ => P.classOf κ
  | .cons _, .here => .top

/-! ## Continuations -/

/-- A continuation: frames `let x = □ in u`, innermost last. -/
inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Tm (s,x) → Cont s
  /-- An unpacking frame `letex ⟨κ, x⟩ = □ in u`. -/
  | consE : Cont s → Tm ((s,c),x) → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K u, ρ => .cons (K.rename ρ) (u.rename ρ.lift)
  | .consE K u, ρ => .consE (K.rename ρ) (u.rename ρ.lift.lift)

/-- Weaken a continuation under a newly allocated store binder. -/
def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

/-- Weaken a continuation under the capture binder an unpacking opens.
`Cont.rename` is kind generic, so this is one line beside `Cont.weaken`. -/
def Cont.weakenC (K : Cont s) : Cont (s,c) := K.rename Rename.succ

/-! ## States and steps -/

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- The root the state reads next, if any. -/
def State.inspects (st : State s) : Option (BVar s .var) := st.t.inspects

@[simp] theorem State.inspects_mk (σ : Store s) (K : Cont s) (t : Tm s) :
    State.inspects ⟨σ, K, t⟩ = t.inspects := rfl

/-- The reduction relation.  `alloc` is the only rule that changes the
signature. -/
inductive Step : State s → State s' → Prop where
  /-- Push a `let` frame. -/
  | «let» : Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K u, t⟩
  /-- Allocate a value answer in the store.  A box is a value, so it is
      allocated here like a lambda or a literal. -/
  | alloc : Step ⟨σ, .cons K u, .val v⟩ ⟨.cons σ v, K.weaken, u⟩
  /-- A path answer is consumed by a renaming. -/
  | rename : Step ⟨σ, .cons K u, .path (.var y)⟩ ⟨σ, K, u.substVar y⟩
  /-- Application: look the closure up in the store and enter its body, which
      instantiates the parameter by the argument, the arrow's capture binder
      by the argument, and the body root by the outermost reading. -/
  | app : σ.lookup x = .lam T t → Step ⟨σ, K, .app x y⟩ ⟨σ, K, t.subst (Subst.enter y)⟩
  /-- Selection: look the object up in the store and enter the field's body,
      which instantiates the self binder by the receiver and the class root by
      the outermost reading. -/
  | proj :
      σ.lookup x = .obj d → d.lookupTrm a = some t →
      Step ⟨σ, K, .proj x a⟩ ⟨σ, K, t.subst (Subst.enterObj x)⟩
  /-- Unboxing: look the box up in the store and continue at its content. -/
  | unbox :
      σ.lookup x = .box y →
      Step ⟨σ, K, .unbox C x⟩ ⟨σ, K, .path (.var y)⟩
  /-- Push an unpacking frame. -/
  | letex : Step ⟨σ, K, .letex t u⟩ ⟨σ, .consE K u, t⟩
  /-- Unpack a path answer: the store gains a capture slot for the witness
      and the body is instantiated at the answer's binder. -/
  | unpack :
      Step ⟨σ, .consE K u, .path (.var y)⟩ ⟨σ.consC, K.weakenC, u.substVar (.there y)⟩
  /-- Unpack a value answer: the store gains a capture slot and then the
      value, as `alloc` does one binder further in. -/
  | allocE :
      Step ⟨σ, .consE K u, .val v⟩
        ⟨(σ.consC).cons (v.weaken (k := .cap)), (K.weakenC).weaken, u⟩

/-- Reflexive transitive closure, across signatures. -/
inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

/-- Answers with an empty continuation are final. -/
def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ ((∃ v, st.t = .val v) ∨ (∃ p, st.t = .path p))

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end DotMNF

end Classifiers
