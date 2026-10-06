import Coercions.CapturesCC.FCdot.Normalizer
import Coercions.CapturesCC.FCdot.Resolution
import Coercions.CapturesCC.FCdot.CheckerCompleteness

namespace CapturesCC

/-!
# FCdot store machine

States are a store of literals, a continuation of frames, and a running
term, all indexed by one signature.  Allocation extends the signature.
Casts on values are wrappers: allocation strips them, stores the literal at
its own type, and rewrites the continuation so that the new variable is used
under the composite cast.  A `recap a f` carries no type inclusion, so
`Atom.coercions` steps past it and `Tm.adjust` strips it exactly as it strips
casts.  The application steps are the vanilla ones.  Application on a coerced
closure reads the domain and codomain evidence off the head normal form of
the atom's casts (`Normalizer.lean`).  A box is a value, allocated by the
same `alloc` step as any other literal, and `unbox` is a term whose steps
read the head normal form of its atom's casts in the same way: an identity or
a conversion hands back the stored atom, and a box coercion `boxed d` hands
it back under the cast `d`, as `appCast` casts an argument by the domain
evidence.  Progress needs that this normalization succeeds on a closed atom
of function or box type, and preservation needs the resulting evidence to be
typed; both are consequences of the canonical-forms theorem.

A let frame carries the use set its body declares and the avoidance evidence,
exactly as the `let` term does, so that the use set of a state is structural.
Allocation stores `v.core`, which keeps the value's annotation, and `adjust`
substitutes through the whole body, the evidence inside it included, since
`Tm.subst` acts on every field of a let.
-/

namespace FCdot

/-! ## Continuations -/

inductive Frame : Sig → Type where
  /-- `let x = □ in u ⦃U'; f⦄`: the body, the use set it declares, and the
      avoidance evidence putting the body's use set below it. -/
  | «let» : Tm (s,x) → CaptureSet s → CapCo (s,x) → Frame s
  | cast : LeCo s → Frame s
  /-- The answer cast frame.  It holds the coercion itself and not a head
      form, so its three steps are unconditional. -/
  | castE : ELeCo s → Frame s
  /-- `letex ⟨κ, x⟩ = □ in u ⦃U'; h; f⦄`: the body, the use set it declares,
      the evidence putting the head's bound below that set, and the body's
      avoidance evidence. -/
  | letex : Tm ((s,c),x) → CaptureSet s → CapCo s → CapCo ((s,c),x) → Frame s

def Frame.rename : Frame s1 → Rename s1 s2 → Frame s2
  | .let u U f, ρ => .let (u.rename ρ.lift) (U.rename ρ) (f.rename ρ.lift)
  | .cast e, ρ => .cast (e.rename ρ)
  | .castE g, ρ => .castE (g.rename ρ)
  | .letex u U h f, ρ =>
      .letex (u.rename ρ.lift.lift) (U.rename ρ) (h.rename ρ) (f.rename ρ.lift.lift)

/-- Continuation: frames, innermost last. -/
inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Frame s → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K f, ρ => .cons (K.rename ρ) (f.rename ρ)

def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

/-- The capture-kind twin of `Cont.weaken`.  `Cont.rename` is already kind
generic, so the twin is one line; `Cont.weaken` is not, because its result
signature names `,x`. -/
def Cont.weakenC (K : Cont s) : Cont (s,c) := K.rename Rename.succ

scoped postfix:max "↑" => Cont.weaken

scoped infixl:65 " ▹ " => Cont.cons

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ₖ " K:51 " : " T:51 " ⇒ " U:51 => Cont.Typed Γ K T U

/-- `Γ ⊢ₖ K : E ⇒ U`: `K` accepts an answer `E` and produces the type `U`.
Only what a continuation accepts is widened to an answer; `nil` accepts a
plain `.ty T` and produces `T`, so a continuation still produces a type. -/
inductive Cont.Typed : Ctx s → Cont s → ETy s → Ty s → Prop where
  | nil : Γ ⊢ₖ .nil : .ty T ⇒ T
  | «let» :
      Γ.cons (.opaque T) ⊢ u :ᵉ E↑ →
      Γ.cons (.opaque T) ⊢ᶜ f : u.uses ⊑ U'↑ →
      Γ ⊢ₖ K : E ⇒ V →
      Γ ⊢ₖ K ▹ .let u U' f : .ty T ⇒ V
  | cast :
      Γ ⊢ e : T ≤ U →
      Γ ⊢ₖ K : .ty U ⇒ V →
      Γ ⊢ₖ K ▹ .cast e : .ty T ⇒ V
  | castE :
      Γ ⊢ᵉ g : E ≤ E' →
      Γ ⊢ₖ K : E' ⇒ V →
      Γ ⊢ₖ K ▹ .castE g : E ⇒ V
  | letex {T : Ty (s,c)} {C₀ U' : CaptureSet s} {E : ETy s} :
      Γ ⊢ᶜ h : C₀ ⊑ U' →
      ((Γ.consC .star).cons (.opaque T)) ⊢ u :ᵉ
        (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) →
      ((Γ.consC .star).cons (.opaque T)) ⊢ᶜ f :
        u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.cvar (.there .here)]) →
      Γ ⊢ₖ K : E ⇒ V →
      Γ ⊢ₖ K ▹ .letex u U' h f : ∃ᶜ[C₀] T ⇒ V

open Lean PrettyPrinter in
@[app_unexpander Cont.Typed] def Cont.Typed.unexpand : Unexpander
  | `($_ $Γ $K $T $U) => `($Γ ⊢ₖ $K : $T ⇒ $U)
  | _ => throw ()

/-! ## States -/

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- A state is typed when its store is typed in a transparent context in
which the term and continuation are typed. -/
def State.Typed (st : State s) (U : Ty s) : Prop :=
  ∃ (Γ : Ctx s) (E : ETy s),
    ⊢ st.σ : Γ ∧ Γ ⊢ st.t :ᵉ E ∧ Γ ⊢ₖ st.K : E ⇒ U

def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ (∃ v, st.t = .val v) ∨ st.K = .nil ∧ (∃ p, st.t = .atom p)

/-! ## Use sets of a continuation and of a state

The use set of a continuation is the union of the sets its let frames
declare.  A cast frame declares nothing.  The use set of a state is the use
set of its term united with that of its continuation.  Both are total and
structural, as `Tm.uses` is. -/

/-- `usesK K`: the use set a continuation declares. -/
def usesK : Cont s → CaptureSet s
  | .nil => []
  | K ▹ .let _ U _ => usesK K ∪ U
  | K ▹ .cast _ => usesK K
  | K ▹ .castE _ => usesK K
  | K ▹ .letex _ U _ _ => usesK K ∪ U

@[simp] theorem usesK_nil : usesK (.nil : Cont s) = [] := rfl
@[simp] theorem usesK_let (K : Cont s) (u : Tm (s,x)) (U : CaptureSet s) (f : CapCo (s,x)) :
    usesK (K ▹ .let u U f) = usesK K ∪ U := rfl
@[simp] theorem usesK_cast (K : Cont s) (e : LeCo s) :
    usesK (K ▹ .cast e) = usesK K := rfl
@[simp] theorem usesK_castE (K : Cont s) (g : ELeCo s) :
    usesK (K ▹ .castE g) = usesK K := rfl
@[simp] theorem usesK_letex (K : Cont s) (u : Tm ((s,c),x)) (U : CaptureSet s)
    (h : CapCo s) (f : CapCo ((s,c),x)) :
    usesK (K ▹ .letex u U h f) = usesK K ∪ U := rfl

/-- The use set of a continuation travels with a renaming. -/
theorem usesK_rename {s1 s2 : Sig} : ∀ (K : Cont s1) (ρ : Rename s1 s2),
    usesK (K.rename ρ) = (usesK K).rename ρ
  | .nil, _ => rfl
  | K ▹ .let u U f, ρ => by
      simp only [Cont.rename, Frame.rename, usesK_let, CaptureSet.rename_union,
        usesK_rename K ρ]
  | K ▹ .cast e, ρ => by
      simp only [Cont.rename, Frame.rename, usesK_cast, usesK_rename K ρ]
  | K ▹ .castE g, ρ => by
      simp only [Cont.rename, Frame.rename, usesK_castE, usesK_rename K ρ]
  | K ▹ .letex u U h f, ρ => by
      simp only [Cont.rename, Frame.rename, usesK_letex, CaptureSet.rename_union,
        usesK_rename K ρ]

@[simp] theorem usesK_weaken (K : Cont s) : usesK (K↑) = (usesK K).weaken :=
  usesK_rename K Rename.succ

/-- The capture-kind twin of `usesK_weaken`, beside it for the same reason
`Cont.weakenC` sits beside `Cont.weaken`. -/
@[simp] theorem usesK_weakenC (K : Cont s) :
    usesK K.weakenC = CaptureSet.weaken (k := .cap) (usesK K) :=
  usesK_rename K Rename.succ

/-- The use set of a state. -/
def State.uses (st : State s) : CaptureSet s := st.t.uses ∪ usesK st.K

/-- The root a state reads when it steps. -/
def State.inspects (st : State s) : Option (BVar s .var) := st.t.inspects

@[simp] theorem State.uses_mk (σ : Store s) (K : Cont s) (t : Tm s) :
    State.uses ⟨σ, K, t⟩ = t.uses ∪ usesK K := rfl

@[simp] theorem State.inspects_mk (σ : Store s) (K : Cont s) (t : Tm s) :
    State.inspects ⟨σ, K, t⟩ = t.inspects := rfl

/-- An inspected root of a state is in its use set. -/
theorem State.inspects_mem_uses {st : State s} {x : BVar s .var}
    (h : st.inspects = some x) : CapAtom.var x ∈ st.uses :=
  List.mem_append.mpr (Or.inl (Tm.inspects_mem_uses h))

/-- Fold a nonempty list of coercions into one, oldest first. -/
def LeCo.composite (e : LeCo s) : List (LeCo s) → LeCo s
  | [] => e
  | f :: fs => LeCo.composite (.trans e f) fs

/-- The composite of a value's wrappers, if any. -/
def Value.composite? (v : Value s) : Option (LeCo s) :=
  match v.coercions with
  | [] => none
  | e :: es => some (LeCo.composite e es)

/-- Adjust a continuation body to a stripped value: if the value carried
casts, every use of the new variable goes under their composite. -/
def Tm.adjust (u : Tm (s,x)) (v : Value s) : Tm (s,x) :=
  match v.composite? with
  | none => u
  | some E => u.subst (Subst.selfCast E.weaken)

/-! ## Applying an answer coercion to a wrapper

Both functions are total and structural on the coercion, which is what makes
the three answer-cast steps unconditional.  The `cong` clause composes the
wrapper's residual, read at `Ctx.scopeInst C`, with the congruence's, read at
`Ctx.scope`, after transporting the second along `Ctx.Ren.instC` at the
identity renaming.  The two clauses that hand back their input unchanged are
the typed-impossible combinations, and preservation closes them by inverting
the two typings.  No nesting arises in a typed state, because a `pack`
coercion has a plain left endpoint and a packed value has an existential
answer. -/

def Value.applyE : Value s → ELeCo s → Value s
  | v, .plain e => .cast v e
  | v, .pack D h e => .pack D h e v
  | .pack C h e v, .cong h' f => .pack C (.trans h h') (e.trans f) v
  | v, .cong _ _ => v
  | v, .trans g g' => (v.applyE g).applyE g'

def PAtom.applyE : PAtom s → ELeCo s → PAtom s
  | .plain a, .plain e => .plain (.cast a e)
  | .plain a, .pack D h e => .pack D h e a
  | .pack C h e a, .cong h' f => .pack C (.trans h h') (e.trans f) a
  -- The three typed-impossible combinations: a plain or a packing coercion
  -- at a packed atom, and a congruence at a plain one.  `PAtom.pack` carries
  -- an `Atom` and cannot nest, so each hands back its input, and preservation
  -- closes each by inverting the two typings.  They stand before the `trans`
  -- clause so that the `trans` clause is the generic one and reduces by
  -- definition, as `Value.applyE`'s does.
  | p@(.pack _ _ _ _), .plain _ => p
  | p@(.pack _ _ _ _), .pack _ _ _ => p
  | p@(.plain _), .cong _ _ => p
  | p, .trans g g' => (p.applyE g).applyE g'

/-- A composite coercion applies in two steps.  It holds by definition at
`Value.applyE`; at `PAtom.applyE` the three typed-impossible clauses stand
between, so the equation is proven by one case split on the wrapper. -/
@[simp] theorem PAtom.applyE_trans (p : PAtom s) (g g' : ELeCo s) :
    p.applyE (.trans g g') = (p.applyE g).applyE g' := by
  cases p <;> rfl

@[simp] theorem Value.applyE_trans (v : Value s) (g g' : ELeCo s) :
    v.applyE (.trans g g') = (v.applyE g).applyE g' := rfl

/-- Applying an answer coercion does not move the root a wrapper reads.  It
is what keeps the use set of an answer-cast step equal to the use set of the
state it fires on. -/
@[simp] theorem PAtom.root_applyE : ∀ (p : PAtom s) (g : ELeCo s),
    (p.applyE g).root = p.root
  | .plain _, .plain _ => rfl
  | .pack _ _ _ _, .plain _ => rfl
  | .plain _, .pack _ _ _ => rfl
  | .pack _ _ _ _, .pack _ _ _ => rfl
  | .plain _, .cong _ _ => rfl
  | .pack _ _ _ _, .cong _ _ => rfl
  | p, .trans g g' => by
      rw [PAtom.applyE_trans, PAtom.root_applyE _ g', PAtom.root_applyE p g]

/-! ## Steps -/

set_option hygiene false in
scoped infix:40 " ⟶ " => Step
set_option hygiene false in
scoped infix:40 " ⟶* " => Steps

/-- `st ⟶ st'`.  Contexts in which a step's evidence side conditions are
checked: the transparent context of the current store. -/
inductive Step : State s → State s' → Prop where
  | «let» :
      ⟨σ, K, .let t u U f⟩ ⟶ ⟨σ, K ▹ .let u U f, t⟩
  | castPush :
      ⟨σ, K, .cast t e⟩ ⟶ ⟨σ, K ▹ .cast e, t⟩
  | castVal :
      ⟨σ, K ▹ .cast e, .val v⟩ ⟶ ⟨σ, K, .val (.cast v e)⟩
  /-- A plain cast frame at an atom focus.  The wrapper is read through
      `PAtom.applyE` at the plain coercion, which is `Atom.cast` on a plain
      atom and the identity on a packed one, so the step stays unconditional
      and `castRedex_steps`, which has no typing hypothesis, keeps its
      statement.  A packed atom under a plain cast frame is typed-impossible
      and preservation closes it by inversion. -/
  | castAtom :
      ⟨σ, K ▹ .cast e, .atom p⟩ ⟶ ⟨σ, K, .atom (p.applyE (.plain e))⟩
  | alloc :
      ⟨σ, K ▹ .let u U f, .val v⟩ ⟶ ⟨.cons σ v.core, K.weaken, u.adjust v⟩
  | rename :
      ⟨σ, K ▹ .let u U f, .atom (.plain a)⟩ ⟶ ⟨σ, K, u.substAtom a⟩
  /-- The answer cast pushes its coercion onto the continuation.  No
      premise: the frame holds the coercion itself, so the step is a cast
      redex for erasure. -/
  | castEPush :
      ⟨σ, K, .castE t g⟩ ⟶ ⟨σ, K ▹ .castE g, t⟩
  | castEVal :
      ⟨σ, K ▹ .castE g, .val v⟩ ⟶ ⟨σ, K, .val (v.applyE g)⟩
  | castEAtom :
      ⟨σ, K ▹ .castE g, .atom p⟩ ⟶ ⟨σ, K, .atom (p.applyE g)⟩
  | letex :
      ⟨σ, K, .letex t u U h f⟩ ⟶ ⟨σ, K ▹ .letex u U h f, t⟩
  /-- Unpacking a packed atom: the store gains the witness as an instance
      binder, the continuation is weakened into the new scope, and the body
      is substituted by the wrapper's atom read there under the residual
      coercion collapsed by `Subst.instRoot`.  No premise, no fuel, no head
      form. -/
  | unpackAtom :
      ⟨σ, K ▹ .letex u U h f, .atom (.pack C h₀ e a)⟩ ⟶
        ⟨σ.consC (.inst C), K.weakenC,
          u.substAtom (.cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot))⟩
  /-- Unpacking a packed value: the store gains the witness as an instance
      binder and then the literal, as `alloc` does. -/
  | unpackVal :
      ⟨σ, K ▹ .letex u U h f, .val (.pack C h₀ e v)⟩ ⟶
        ⟨(σ.consC (.inst C)).cons
            (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot)).core,
          (K.weakenC).weaken,
          u.adjust (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot))⟩
  /-- Application through a bare variable. -/
  | appVar :
      σ.lookup x = .lam A S₀ t₀ g →
      ⟨σ, K, .app (.var x) b⟩ ⟶ ⟨σ, K, t₀.subst (Subst.enter b)⟩
  /-- Application through a wrapped atom whose casts normalize to the
      identity: the atom's function type and the closure's coincide. -/
  | appCastRefl :
      σ.lookup a.root = .lam A S₀ t₀ g →
      a ≠ .var a.root →
      σ ⊢ a ⇓ᶜ[n] (a', F) →
      (F = .id ∨ ∃ φ, F = .eqv φ) →
      ⟨σ, K, .app a b⟩ ⟶ ⟨σ, K, t₀.subst (Subst.enter b)⟩
  /-- Application through a wrapped atom whose casts normalize to a function
      coercion `pi d c`: the domain evidence is instantiated at the argument's
      root before it casts the argument, and the result is cast by the
      codomain evidence read at the argument. -/
  | appCast :
      σ.lookup a.root = .lam A S₀ t₀ g →
      a ≠ .var a.root →
      σ ⊢ a ⇓ᶜ[n] (a', .pi d c) →
      ⟨σ, K, .app a b⟩ ⟶
        ⟨σ, K, .castE (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
                      (c.subst (Subst.enter b))⟩
  | proj :
      σ.lookup a.root = .obj A W Wc F →
      F.get? ℓ = some t →
      ⟨σ, K, .proj a ℓ h⟩ ⟶ ⟨σ, K, t.subst (Subst.enterObj a.root)⟩
  /-- Unboxing an atom rooted at a stored box whose casts normalize to the
      identity or to a conversion: the boxed atom, weakened into the current
      scope by `Store.lookup`, is the result. -/
  | unboxRefl :
      σ.lookup a.root = .box b →
      σ ⊢ a ⇓ᶜ[n] (a', F) →
      (F = .id ∨ ∃ φ, F = .eqv φ) →
      ⟨σ, K, .unbox a U f⟩ ⟶ ⟨σ, K, .atom (.plain b)⟩
  /-- Unboxing an atom whose casts normalize to a box coercion `boxed d`:
      the boxed atom is handed back under `d`, as `appCast` hands the
      argument to the closure under the domain evidence. -/
  | unboxCast :
      σ.lookup a.root = .box b →
      σ ⊢ a ⇓ᶜ[n] (a', .boxed d) →
      ⟨σ, K, .unbox a U f⟩ ⟶ ⟨σ, K, .atom (.plain (.cast b d))⟩

/-- `st ⟶* st'`: reflexive transitive closure across signatures. -/
inductive Steps : State s → State s' → Prop where
  | refl : st ⟶* st
  | tail : st ⟶* st' → st' ⟶ st'' → st ⟶* st''

open Lean PrettyPrinter in
@[app_unexpander Step] def Step.unexpand : Unexpander
  | `($_ $st $st') => `($st ⟶ $st')
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Steps] def Steps.unexpand : Unexpander
  | `($_ $st $st') => `($st ⟶* $st')
  | _ => throw ()

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

/-! ## Store extension

A run only extends the store: every step keeps the entries it had and may
append one.  `Store.Ext σ σ' ρ` records that `σ'` is `σ` with entries
appended, and `ρ` is the embedding of the old scope into the new one.  Over
typed stores, resolution commutes with that embedding: the roots of a
renamed set are the renamed roots, because each appended entry is a weakening
(`Ctx.caps_weaken` and `Ctx.caps_weakenC`), iterated along the extension. -/

/-- `Store.Ext σ σ' ρ`: `σ'` extends `σ`, and `ρ` embeds the old scope. -/
inductive Store.Ext : Store s → Store s' → Rename s s' → Prop where
  | refl {σ : Store s} : Store.Ext σ σ Rename.id
  | cons {σ : Store s} {σ' : Store s'} {ρ : Rename s s'} :
      Store.Ext σ σ' ρ → ∀ v : Value s', Store.Ext σ (σ'.cons v) (ρ.comp Rename.succ)
  | consC {σ : Store s} {σ' : Store s'} {ρ : Rename s s'} :
      Store.Ext σ σ' ρ → ∀ b : CapBound s', b.opaque = false →
        Store.Ext σ (σ'.consC b) (ρ.comp Rename.succ)

/-- Store extension composes. -/
theorem Store.Ext.comp {s1 s2 s3 : Sig} {σ1 : Store s1} {σ2 : Store s2} {σ3 : Store s3}
    {ρ : Rename s1 s2} {ρ' : Rename s2 s3}
    (h : Store.Ext σ1 σ2 ρ) (h' : Store.Ext σ2 σ3 ρ') :
    Store.Ext σ1 σ3 (ρ.comp ρ') := by
  induction h' with
  | refl => rw [Rename.comp_id]; exact h
  | cons _ v ih => rw [← Rename.comp_assoc]; exact (ih h).cons v
  | consC _ b hb ih => rw [← Rename.comp_assoc]; exact (ih h).consC b hb

/-! ### Injectivity on capture atoms -/

/-- A renaming is injective on capture atoms when it separates them. -/
def Rename.InjectiveOnAtoms {s1 s2 : Sig} (ρ : Rename s1 s2) : Prop :=
  ∀ a b : CapAtom s1, a.rename ρ = b.rename ρ → a = b

theorem Rename.InjectiveOnAtoms.id {s : Sig} :
    Rename.InjectiveOnAtoms (Rename.id : Rename s s) := by
  intro a b h; simpa using h

theorem Rename.InjectiveOnAtoms.comp_succ {s1 s2 : Sig} {ρ : Rename s1 s2}
    (h : ρ.InjectiveOnAtoms) {k : Kind} :
    (ρ.comp (Rename.succ (k := k))).InjectiveOnAtoms := by
  intro a b hab
  refine h a b ?_
  cases a <;> cases b <;>
    simp only [CapAtom.rename, Rename.comp_var, Rename.succ_var,
      CapAtom.var.injEq, CapAtom.cvar.injEq, CapAtom.name.injEq] at hab ⊢ <;>
    simp_all

/-- The embedding of a store extension is injective on capture atoms. -/
theorem Store.Ext.injective {s s' : Sig} {σ : Store s} {σ' : Store s'} {ρ : Rename s s'}
    (h : Store.Ext σ σ' ρ) : ρ.InjectiveOnAtoms := by
  induction h with
  | refl => exact Rename.InjectiveOnAtoms.id
  | cons _ _ ih => exact ih.comp_succ
  | consC _ _ _ ih => exact ih.comp_succ

/-- Membership under a renaming injective on atoms. -/
theorem CaptureSet.mem_rename_iff {s1 s2 : Sig} {ρ : Rename s1 s2}
    (hρ : ρ.InjectiveOnAtoms) (a : CapAtom s1) (C : CaptureSet s1) :
    a.rename ρ ∈ C.rename ρ ↔ a ∈ C := by
  constructor
  · intro h
    simp only [CaptureSet.rename, List.mem_map] at h
    obtain ⟨b, hb, hab⟩ := h
    exact hρ a b hab.symm ▸ hb
  · intro h
    simp only [CaptureSet.rename, List.mem_map]
    exact ⟨a, h, rfl⟩

/-! ### The context of a typed store is unique

Store typing types each entry by the unique value rule, so a store has at
most one context.  This is what makes the roots lemma below a statement about
two arbitrary typings of the two stores. -/

theorem Store.Typed.ctx_unique {s : Sig} {σ : Store s} {Γ Γ' : Ctx s}
    (h : ⊢ σ : Γ) (h' : ⊢ σ : Γ') : Γ = Γ' := by
  induction h with
  | nil => cases h'; rfl
  | @cons _ σ0 Γ0 v T _ _ value ih =>
      cases h' with
      | cons store' _ value' =>
          have hΓ := ih store'
          subst hΓ
          rw [Value.HasType.type_unique value value']
  | consC _ _ ih =>
      cases h' with
      | consC store' _ => rw [ih store']

/-! ### Resolution commutes with the embedding -/

/-- Over typed stores related by an extension, the roots of a renamed set are
the renamed roots.  Each appended entry contributes one weakening. -/
theorem Store.Ext.roots {s s' : Sig} {σ : Store s} {σ' : Store s'} {ρ : Rename s s'}
    (hE : Store.Ext σ σ' ρ) {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    ∀ {Γ' : Ctx s'}, (⊢ σ' : Γ') → ∀ (n : Nat) (C : CaptureSet s),
      Γ'.roots n (C.rename ρ) = (Γ.roots n C).rename ρ := by
  induction hE with
  | refl =>
      intro Γ' hσ' n C
      cases Store.Typed.ctx_unique hσ hσ'
      simp
  | @cons s1 σ0 σ1 ρ0 hE0 v ih =>
      intro Γ' hσ' n C
      cases hσ' with
      | cons store' _ _ =>
          show Ctx.expand _ (Ctx.caps _ n (C.rename (ρ0.comp Rename.succ))) = _
          rw [show C.rename (ρ0.comp Rename.succ) = (C.rename ρ0).weaken by
                simp [CaptureSet.weaken]]
          rw [Ctx.caps_weaken, Ctx.expand_weaken]
          have hih := ih hσ store' n C
          simp only [Ctx.roots_eq_expand_caps] at hih
          rw [hih]
          simp [CaptureSet.weaken]
  | @consC s1 σ0 σ1 ρ0 hE0 b hb ih =>
      intro Γ' hσ' n C
      cases hσ' with
      | consC store' _ =>
          show Ctx.expand _ (Ctx.caps _ n (C.rename (ρ0.comp Rename.succ))) = _
          rw [show C.rename (ρ0.comp Rename.succ) = (C.rename ρ0).weaken by
                simp [CaptureSet.weaken]]
          rw [Ctx.caps_weakenC, Ctx.expand_weakenC _ _ hb]
          have hih := ih hσ store' n C
          simp only [Ctx.roots_eq_expand_caps] at hih
          rw [hih]
          simp [CaptureSet.weaken]

/-- The membership form of the roots lemma. -/
theorem Store.Ext.root_iff {s s' : Sig} {σ : Store s} {σ' : Store s'} {ρ : Rename s s'}
    (hE : Store.Ext σ σ' ρ) {Γ : Ctx s} {Γ' : Ctx s'}
    (hσ : ⊢ σ : Γ) (hσ' : ⊢ σ' : Γ') (a : CapAtom s) (C : CaptureSet s) :
    Γ'.Root (a.rename ρ) (C.rename ρ) ↔ Γ.Root a C := by
  constructor
  · rintro ⟨n, hn⟩
    rw [hE.roots hσ hσ' n C] at hn
    exact ⟨n, (CaptureSet.mem_rename_iff hE.injective a (Γ.roots n C)).mp hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hE.roots hσ hσ' n C]
    exact (CaptureSet.mem_rename_iff hE.injective a (Γ.roots n C)).mpr hn

/-- Subcapturing travels along a store extension. -/
theorem Store.Ext.capLe {s s' : Sig} {σ : Store s} {σ' : Store s'} {ρ : Rename s s'}
    (hE : Store.Ext σ σ' ρ) {Γ : Ctx s} {Γ' : Ctx s'}
    (hσ : ⊢ σ : Γ) (hσ' : ⊢ σ' : Γ') {C D : CaptureSet s} (h : CapLe Γ C D) :
    CapLe Γ' (C.rename ρ) (D.rename ρ) := by
  rintro a ⟨n, hn⟩
  rw [hE.roots hσ hσ' n C] at hn
  simp only [CaptureSet.rename, List.mem_map] at hn
  obtain ⟨b, hb, rfl⟩ := hn
  obtain ⟨m, hm⟩ := h b ⟨n, hb⟩
  refine ⟨m, ?_⟩
  rw [hE.roots hσ hσ' m D]
  exact (CaptureSet.mem_rename_iff hE.injective b (Γ.roots m D)).mpr hm

end FCdot

end CapturesCC
