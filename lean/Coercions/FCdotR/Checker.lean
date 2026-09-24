import Coercions.FCdotR.TermTyping

/-!
# An executable checker for FCdotR typing

FCdotR's syntax is fully annotated: every node names the types its typing rule
cannot compute from its premises, and every node has exactly one typing rule.
So each of the five judgments synthesises its outputs from the syntax and the
context, and the checker never searches:

```text
Γ ⊢ e : S ≤ T      synthesises S and T        Γ ⊢ₐ a : T     synthesises T
Γ ⊢ v :: p : T     synthesises T, given p     Γ ⊢ t : T      synthesises T
                                              Γ ⊢d ds : T    synthesises T
```

A rule is a recipe: synthesise the premises, compare what they report with the
types the node names (`trans`'s middle type, `vcSub`'s source, a method's
codomain, …), and build the conclusion.  The two location rules take the
decidable premise `Typing.LitMatch`, decided here by `litMatchB`.  `TmTy.let`
types its body at a weakening, so the body's type is strengthened past the
bound variable, by `Ty.strengthen?`; as in `FCdot/Checker.lean` that is the
action of a partial renaming.  FCdotR imports no FCdot module beyond
`FCdot.Debruijn`, so the partial renaming is repeated here for `Oopsla16.Ty`.

The checker decides FCdotR typing of fully annotated evidence and terms, which
is what the elaboration of a source derivation produces.  It does not decide
`Oopsla16` typing: the annotations it compares are what a source derivation
records.  Nor does it check that the store typing tells the truth: `vcLoc` and
`var (conc ℓ)` read their types off `W`, and `Store.Honest` is a separate
invariant.

The kernels (`synthLeCore`, …) return the derivation they validated, so
soundness is extraction.  Derivations are `Type`-valued, so the soundness
statements (`synthLe_sound`, …) are functions that return one.  Completeness is
in `CheckerCompleteness`.

## How the recursion compiles

* `synthLeCore`/`synthVcCore` recurse on evidence whose scope index is the
  subject's prefix, `Vc σ (scopeAt p)`, which is not a variable.  Lean compiles
  the block by well-founded recursion on the size of the evidence, a `Nat`, so
  it is irreducible for the elaborator but reduces in the kernel: examples are
  decided by `decide +kernel`, as in `FCdot/Examples.lean`.
* `synthAtomCore` and the block `synthTmCore`/`synthDefsCore` recurse on
  syntax whose index is a variable, and are structural.
* A recursion over types at the fixed index `Ty σ []` compiles by well-founded
  recursion as well, and that one the kernel does not reduce.  The `LitMatch`
  decision therefore recurses at a variable index `s`, with the equation
  `s = []` carried alongside (`litMatchBAux`), which is structural.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Dm renameNil)

/-! ## Lookups that carry their equation -/

/-- Attach the defining equation to a lookup result.  `FCdot/Checker.lean`'s
`witness?`, repeated because FCdotR imports no FCdot module but
`FCdot.Debruijn`. -/
def witness? {α : Type} : (o : Option α) → Option { a : α // o = some a }
  | some a => some ⟨a, rfl⟩
  | none => none

/-- `witness?` of a known lookup. -/
theorem witness?_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    witness? o = some ⟨a, h⟩ := by subst h; rfl

/-! ## Deciding `LitMatch`

`LitMatch g B` asks one thing of each conjunct of `B` and nothing of any method
body, so it is decided by one pass over `B`: a type member must be what `g`
defines at its label, exactly; a method member must find there a method stored
with both annotations, and those annotations must be the member's two types,
exactly.  A method stored without an annotation is refused. -/

/-- One conjunct against the stored literal's member lookup `g`. -/
def memberMatchB {σ : Sig} (g : Lb → Option (Dm σ [])) : Ty σ [] → Bool
  | .TTyp b S U =>
      match g b with
      | some (.dty TX) => decide (S = TX) && decide (U = TX)
      | _ => false
  | .TFun b S U =>
      match g b with
      | some (.dfun (some S') (some U') _) => decide (S = S') && decide (U = U')
      | _ => false
  | _ => false

/-- The pass over the conjuncts.  It recurses at a variable scope index `s`,
with `s = []` carried alongside, so that it compiles structurally; at the fixed
index `[]` Lean would compile it by well-founded recursion, which the kernel
does not reduce. -/
def litMatchBAux {σ : Sig} (g : Lb → Option (Dm σ [])) :
    {s : Sig} → Ty σ s → s = [] → Bool
  | _, .TTop, _ => true
  | _, .TAnd M B, h => memberMatchB g (h ▸ M) && litMatchBAux g B h
  | _, _, _ => false

/-- **The decision procedure for `LitMatch`**, the premise of the two location
rules `VcTy.vcLocAny` and `AtomTy.varConcAny`. -/
def litMatchB {σ : Sig} (g : Lb → Option (Dm σ [])) (B : Ty σ []) : Bool :=
  litMatchBAux g B rfl

/-! The equations of `litMatchB`, one per head constructor. -/

section LitMatchB
variable {σ : Sig} (g : Lb → Option (Dm σ []))

@[simp] theorem litMatchB_TTop : litMatchB g (.TTop : Ty σ []) = true := rfl
@[simp] theorem litMatchB_TAnd (M B : Ty σ []) :
    litMatchB g (.TAnd M B) = (memberMatchB g M && litMatchB g B) := rfl
@[simp] theorem litMatchB_TBot : litMatchB g (.TBot : Ty σ []) = false := rfl
@[simp] theorem litMatchB_TFun (l : Lb) (S : Ty σ []) (U : Ty σ ([],x)) :
    litMatchB g (.TFun l S U) = false := rfl
@[simp] theorem litMatchB_TTyp (l : Lb) (S U : Ty σ []) :
    litMatchB g (.TTyp l S U) = false := rfl
@[simp] theorem litMatchB_TSel (p : Vr σ []) (l : Lb) :
    litMatchB g (.TSel p l) = false := rfl
@[simp] theorem litMatchB_TBind (T : Ty σ ([],x)) : litMatchB g (.TBind T) = false := rfl
@[simp] theorem litMatchB_TOr (S T : Ty σ []) : litMatchB g (.TOr S T) = false := rfl

end LitMatchB

/-- **`litMatchB` is sound**: an accepted type matches the literal, and the
match is returned.  A verdict never evaluates the derivation this goes into,
so it does not matter that this recursion, at the fixed index `Ty σ []`,
compiles by well-founded recursion. -/
def litMatchB_sound {σ : Sig} (g : Lb → Option (Dm σ [])) :
    (B : Ty σ []) → litMatchB g B = true → LitMatch g B
  | .TTop, _ => .top
  | .TAnd M B, h => by
      simp only [litMatchB_TAnd, Bool.and_eq_true] at h
      obtain ⟨hM, hB⟩ := h
      have r := litMatchB_sound g B hB
      cases M with
      | TTyp b S U =>
          simp only [memberMatchB] at hM
          split at hM
          · rename_i TX hgb
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hM
            obtain ⟨rfl, rfl⟩ := hM
            exact .typ hgb r
          · cases hM
      | TFun b S U =>
          simp only [memberMatchB] at hM
          split at hM
          · rename_i S' U' t hgb
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hM
            obtain ⟨rfl, rfl⟩ := hM
            exact .fn hgb r
          · cases hM
      | TBot => simp [memberMatchB] at hM
      | TTop => simp [memberMatchB] at hM
      | TSel _ _ => simp [memberMatchB] at hM
      | TBind _ => simp [memberMatchB] at hM
      | TAnd _ _ => simp [memberMatchB] at hM
      | TOr _ _ => simp [memberMatchB] at hM
  | .TBot, h => by simp at h
  | .TFun _ _ _, h => by simp at h
  | .TTyp _ _ _, h => by simp at h
  | .TSel _ _, h => by simp at h
  | .TBind _, h => by simp at h
  | .TOr _ _, h => by simp at h

/-- **`litMatchB` is complete**: every match is accepted. -/
theorem litMatchB_complete {σ : Sig} {g : Lb → Option (Dm σ [])} :
    {B : Ty σ []} → LitMatch g B → litMatchB g B = true
  | _, .top => rfl
  | _, .typ h r => by
      simp only [litMatchB_TAnd, memberMatchB, h, decide_true, Bool.and_self, Bool.true_and]
      exact litMatchB_complete r
  | _, .fn h r => by
      simp only [litMatchB_TAnd, memberMatchB, h, decide_true, Bool.and_self, Bool.true_and]
      exact litMatchB_complete r

/-- A match is unique: the type fixes the constructor at every conjunct, the
lookup fixes the stored member (a method's body included), and the remaining
premises are propositions. -/
instance LitMatch.instSubsingleton {σ : Sig} {g : Lb → Option (Dm σ [])} {B : Ty σ []} :
    Subsingleton (LitMatch g B) := by
  constructor
  intro h1 h2
  induction h1 with
  | top => cases h2; rfl
  | typ h r ih => cases h2 with | typ h' r' => rw [ih r']
  | fn h r ih =>
      cases h2 with
      | fn h' r' =>
          rw [h] at h'
          cases h'
          rw [ih r']

/-- `litMatchB` decides `LitMatch`. -/
theorem litMatchB_iff {σ : Sig} {g : Lb → Option (Dm σ [])} {B : Ty σ []} :
    litMatchB g B = true ↔ Nonempty (LitMatch g B) :=
  ⟨fun h => ⟨litMatchB_sound g B h⟩, fun ⟨h⟩ => litMatchB_complete h⟩

/-! ## Strengthening of types

`TmTy.let` types its body at a weakening, so the checker has to undo one
weakening, and fail when the bound variable occurs.  As in
`FCdot/Checker.lean`, strengthening is the action of a *partial* renaming,
which is what lets the traversal pass under binders; only the local scope is
renamed, and a location is left alone. -/

/-- A renaming of the local scope that may fail on some variables. -/
structure PartialRename (s1 s2 : Sig) where
  /-- The image of a variable, if it has one. -/
  var : ∀ {k}, BVar s1 k → Option (BVar s2 k)

namespace PartialRename

/-- Lift under one binder: the new binder maps to itself. -/
def lift {s1 s2 : Sig} (ρ : PartialRename s1 s2) {k : Kind} :
    PartialRename (s1,,k) (s2,,k) where
  var := fun
    | .here => some .here
    | .there x => (ρ.var x).map .there

/-- The partial inverse of `Rename.succ`: it drops the innermost binder. -/
def unshift {s : Sig} {k : Kind} : PartialRename (s,,k) s where
  var := fun
    | .here => none
    | .there x => some x

@[simp] theorem lift_here {s1 s2 : Sig} (ρ : PartialRename s1 s2) {k : Kind} :
    (ρ.lift (k := k)).var .here = some .here := rfl

@[simp] theorem lift_there {s1 s2 : Sig} (ρ : PartialRename s1 s2) {k k0 : Kind}
    (x : BVar s1 k) : (ρ.lift (k := k0)).var (.there x) = (ρ.var x).map .there := rfl

@[simp] theorem unshift_here {s : Sig} {k : Kind} :
    (unshift (s := s) (k := k)).var .here = none := rfl

@[simp] theorem unshift_there {s : Sig} {k k0 : Kind} (x : BVar s k) :
    (unshift (s := s) (k := k0)).var (.there x) = some x := rfl

/-- `ρ` is the partial inverse of the total renaming `τ`. -/
def Inverts {s1 s2 : Sig} (ρ : PartialRename s1 s2) (τ : Rename s2 s1) : Prop :=
  ∀ {k} (x : BVar s1 k) (y : BVar s2 k), ρ.var x = some y ↔ x = τ.var y

/-- Lifting preserves inversion. -/
theorem Inverts.lift {s1 s2 : Sig} {ρ : PartialRename s1 s2} {τ : Rename s2 s1}
    (h : Inverts ρ τ) {k : Kind} : Inverts (ρ.lift (k := k)) τ.lift := by
  intro k' x y
  cases x with
  | here =>
      cases y with
      | here => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | there y => simp only [lift_here, Rename.lift_there]; simp
  | there x =>
      cases y with
      | here =>
          simp only [lift_there, Rename.lift_here]
          cases hxx : ρ.var x with
          | none => simp
          | some z => simp
      | there y =>
          simp only [lift_there, Rename.lift_there, BVar.there.injEq]
          cases hxx : ρ.var x with
          | none =>
              simp only [Option.map_none, reduceCtorEq, false_iff]
              intro hxy
              have := (h x y).mpr hxy
              rw [hxx] at this
              simp at this
          | some z =>
              simp only [Option.map_some, Option.some.injEq, BVar.there.injEq]
              constructor
              · intro hzy; subst hzy; exact (h x z).mp hxx
              · intro hxy
                have := (h x y).mpr hxy
                rw [hxx] at this
                simpa using this

/-- `unshift` inverts weakening. -/
theorem unshift_inverts {s : Sig} {k : Kind} :
    Inverts (unshift (s := s) (k := k)) Rename.succ := by
  intro k' x y
  cases x with
  | here => simp only [unshift_here, Rename.succ_var]; simp
  | there x => simp only [unshift_there, Rename.succ_var, Option.some.injEq, BVar.there.injEq]

end PartialRename

/-- A partial renaming of a variable.  A location is in no local scope, so it
is always kept. -/
def Vr.rename? {σ s1 s2 : Sig} : Vr σ s1 → PartialRename s1 s2 → Option (Vr σ s2)
  | .conc l, _ => some (.conc l)
  | .abs y, ρ => (ρ.var y).map .abs

/-- A partial renaming of a type: `none` exactly when a variable without an
image occurs. -/
def Ty.rename? {σ : Sig} : {s1 s2 : Sig} → Ty σ s1 → PartialRename s1 s2 → Option (Ty σ s2)
  | _, _, .TBot, _ => some .TBot
  | _, _, .TTop, _ => some .TTop
  | _, _, .TFun l S U, ρ =>
      match Ty.rename? S ρ, Ty.rename? U ρ.lift with
      | some S', some U' => some (.TFun l S' U')
      | _, _ => none
  | _, _, .TTyp l S U, ρ =>
      match Ty.rename? S ρ, Ty.rename? U ρ with
      | some S', some U' => some (.TTyp l S' U')
      | _, _ => none
  | _, _, .TSel p l, ρ => (Vr.rename? p ρ).map (.TSel · l)
  | _, _, .TBind T, ρ => (Ty.rename? T ρ.lift).map .TBind
  | _, _, .TAnd A B, ρ =>
      match Ty.rename? A ρ, Ty.rename? B ρ with
      | some A', some B' => some (.TAnd A' B')
      | _, _ => none
  | _, _, .TOr A B, ρ =>
      match Ty.rename? A ρ, Ty.rename? B ρ with
      | some A', some B' => some (.TOr A' B')
      | _, _ => none

/-- Renaming the local scope commutes with pushing under a binder. -/
theorem ofRename_lift {σ s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Oopsla16.Subst.ofRename (σ := σ) ρ).lift = Oopsla16.Subst.ofRename ρ.lift := by
  apply Oopsla16.Subst.ext
  · intro l; rfl
  · intro y; cases y <;> rfl

/-- A partial inverse undoes the total renaming it inverts. -/
theorem Ty.rename?_complete {σ : Sig} : {s1 s2 : Sig} → (U : Ty σ s2) →
    (ρ : PartialRename s1 s2) → (τ : Rename s2 s1) → ρ.Inverts τ →
    Ty.rename? (U.rename τ) ρ = some U
  | _, _, .TBot, _, _, _ => rfl
  | _, _, .TTop, _, _, _ => rfl
  | _, _, .TFun l S U, ρ, τ, h => by
      show Ty.rename? (.TFun l (S.subst (.ofRename τ))
        (U.subst (Oopsla16.Subst.ofRename τ).lift)) ρ = _
      rw [ofRename_lift]
      simp only [Ty.rename?]
      rw [Ty.rename?_complete S ρ τ h, Ty.rename?_complete U ρ.lift τ.lift h.lift]
  | _, _, .TTyp l S U, ρ, τ, h => by
      show Ty.rename? (.TTyp l (S.rename τ) (U.rename τ)) ρ = _
      simp only [Ty.rename?]
      rw [Ty.rename?_complete S ρ τ h, Ty.rename?_complete U ρ τ h]
  | _, _, .TSel p l, ρ, τ, h => by
      cases p with
      | conc c => rfl
      | abs y =>
          show Ty.rename? (Ty.TSel (Vr.abs (τ.var y)) l) ρ = _
          simp [Ty.rename?, Vr.rename?, (h (τ.var y) y).mpr rfl]
  | _, _, .TBind T, ρ, τ, h => by
      show Ty.rename? (.TBind (T.subst (Oopsla16.Subst.ofRename τ).lift)) ρ = _
      rw [ofRename_lift]
      simp only [Ty.rename?]
      rw [Ty.rename?_complete T ρ.lift τ.lift h.lift]; rfl
  | _, _, .TAnd A B, ρ, τ, h => by
      show Ty.rename? (.TAnd (A.rename τ) (B.rename τ)) ρ = _
      simp only [Ty.rename?]
      rw [Ty.rename?_complete A ρ τ h, Ty.rename?_complete B ρ τ h]
  | _, _, .TOr A B, ρ, τ, h => by
      show Ty.rename? (.TOr (A.rename τ) (B.rename τ)) ρ = _
      simp only [Ty.rename?]
      rw [Ty.rename?_complete A ρ τ h, Ty.rename?_complete B ρ τ h]

/-- What a partial inverse returns, the total renaming maps back. -/
theorem Ty.rename?_sound {σ : Sig} : {s1 s2 : Sig} → (T : Ty σ s1) → (U : Ty σ s2) →
    (ρ : PartialRename s1 s2) → (τ : Rename s2 s1) → ρ.Inverts τ →
    Ty.rename? T ρ = some U → T = U.rename τ
  | _, _, .TBot, U, _, _, _, hU => by
      simp only [Ty.rename?, Option.some.injEq] at hU; subst hU; rfl
  | _, _, .TTop, U, _, _, _, hU => by
      simp only [Ty.rename?, Option.some.injEq] at hU; subst hU; rfl
  | _, _, .TFun l S V, U, ρ, τ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hS : Ty.rename? S ρ with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hV : Ty.rename? V ρ.lift with
        | none => rw [hS, hV] at hU; simp at hU
        | some V' =>
          rw [hS, hV] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          show _ = Ty.TFun l (S'.subst (.ofRename τ)) (V'.subst (Oopsla16.Subst.ofRename τ).lift)
          rw [ofRename_lift, Ty.rename?_sound S S' ρ τ h hS,
            Ty.rename?_sound V V' ρ.lift τ.lift h.lift hV]
  | _, _, .TTyp l S V, U, ρ, τ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hS : Ty.rename? S ρ with
      | none => rw [hS] at hU; simp at hU
      | some S' =>
        cases hV : Ty.rename? V ρ with
        | none => rw [hS, hV] at hU; simp at hU
        | some V' =>
          rw [hS, hV] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          show _ = Ty.TTyp l (S'.rename τ) (V'.rename τ)
          rw [← Ty.rename?_sound S S' ρ τ h hS, ← Ty.rename?_sound V V' ρ τ h hV]
  | _, _, .TSel p l, U, ρ, τ, h, hU => by
      cases p with
      | conc c =>
          simp only [Ty.rename?, Vr.rename?, Option.map_some, Option.some.injEq] at hU
          subst hU; rfl
      | abs y =>
          simp only [Ty.rename?, Vr.rename?, Option.map_map] at hU
          cases hy : ρ.var y with
          | none => rw [hy] at hU; simp at hU
          | some z =>
              rw [hy] at hU
              simp only [Option.map_some, Option.some.injEq, Function.comp] at hU
              subst hU
              show _ = Ty.TSel (.abs (τ.var z)) l
              rw [← (h y z).mp hy]
  | _, _, .TBind T, U, ρ, τ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hT : Ty.rename? T ρ.lift with
      | none => rw [hT] at hU; simp at hU
      | some T' =>
          rw [hT] at hU
          simp only [Option.map_some, Option.some.injEq] at hU
          subst hU
          show _ = Ty.TBind (T'.subst (Oopsla16.Subst.ofRename τ).lift)
          rw [ofRename_lift]
          exact congrArg _ (Ty.rename?_sound T T' ρ.lift τ.lift h.lift hT)
  | _, _, .TAnd A B, U, ρ, τ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hA : Ty.rename? A ρ with
      | none => rw [hA] at hU; simp at hU
      | some A' =>
        cases hB : Ty.rename? B ρ with
        | none => rw [hA, hB] at hU; simp at hU
        | some B' =>
          rw [hA, hB] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          show _ = Ty.TAnd (A'.rename τ) (B'.rename τ)
          rw [← Ty.rename?_sound A A' ρ τ h hA, ← Ty.rename?_sound B B' ρ τ h hB]
  | _, _, .TOr A B, U, ρ, τ, h, hU => by
      simp only [Ty.rename?] at hU
      cases hA : Ty.rename? A ρ with
      | none => rw [hA] at hU; simp at hU
      | some A' =>
        cases hB : Ty.rename? B ρ with
        | none => rw [hA, hB] at hU; simp at hU
        | some B' =>
          rw [hA, hB] at hU
          simp only [Option.some.injEq] at hU
          subst hU
          show _ = Ty.TOr (A'.rename τ) (B'.rename τ)
          rw [← Ty.rename?_sound A A' ρ τ h hA, ← Ty.rename?_sound B B' ρ τ h hB]

/-- **Strengthening**: undo one weakening of the local scope, if the innermost
binder does not occur. -/
def Ty.strengthen? {σ s : Sig} (T : Ty σ (s,x)) : Option (Ty σ s) :=
  Ty.rename? T PartialRename.unshift

/-- A strengthened type weakens back to the original. -/
theorem Ty.strengthen?_sound {σ s : Sig} {T : Ty σ (s,x)} {U : Ty σ s}
    (h : Ty.strengthen? T = some U) : T = U.weaken :=
  Ty.rename?_sound T U _ _ PartialRename.unshift_inverts h

/-- A weakening strengthens. -/
theorem Ty.strengthen?_weaken {σ s : Sig} (U : Ty σ s) : Ty.strengthen? U.weaken = some U :=
  Ty.rename?_complete U _ _ PartialRename.unshift_inverts

/-- Strengthening inverts weakening, on the nose. -/
theorem Ty.strengthen?_eq_some_iff {σ s : Sig} {T : Ty σ (s,x)} {U : Ty σ s} :
    Ty.strengthen? T = some U ↔ T = U.weaken := by
  constructor
  · exact Ty.strengthen?_sound
  · intro h; subst h; exact Ty.strengthen?_weaken U

/-- Strengthening, carrying the equation it establishes. -/
def Ty.strengthenW? {σ s : Sig} (T : Ty σ (s,x)) : Option { U : Ty σ s // T = U.weaken } :=
  match witness? (Ty.strengthen? T) with
  | some ⟨U, hU⟩ => some ⟨U, Ty.strengthen?_sound hU⟩
  | none => none

/-- `strengthenW?` of a weakening, with its equation. -/
theorem Ty.strengthenW?_weaken {σ s : Sig} (U : Ty σ s) :
    Ty.strengthenW? U.weaken = some ⟨U, rfl⟩ := by
  simp only [Ty.strengthenW?, witness?_eq_some (Ty.strengthen?_weaken U)]


/-! ## Checked results

Every kernel synthesises the outputs of its judgment and returns the
derivation it validated, so soundness is by construction. -/

/-- An inclusion, with the endpoints it proves. -/
structure LeChecked {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (e : Le σ s) : Type where
  /-- The left endpoint. -/
  source : Ty σ s
  /-- The right endpoint. -/
  target : Ty σ s
  /-- The derivation. -/
  typing : LeTy G W Γ e source target

/-- An observation of the subject `p`, with the type it reports, in `p`'s
prefix scope. -/
structure VcChecked {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (p : Vr σ s) (v : Vc σ (scopeAt p)) : Type where
  /-- The type reported. -/
  type : Ty σ (scopeAt p)
  /-- The derivation. -/
  typing : VcTy G W Γ p v type

/-- An atom, with its type. -/
structure AtomChecked {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (a : Atom σ s) : Type where
  /-- The type. -/
  type : Ty σ s
  /-- The derivation. -/
  typing : AtomTy G W Γ a type

/-- A term, with its type. -/
structure TmChecked {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (t : Tm σ s) : Type where
  /-- The type. -/
  type : Ty σ s
  /-- The derivation. -/
  typing : TmTy G W Γ t type

/-- A definition list, with its type. -/
structure DefsChecked {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (ds : Defs σ s) : Type where
  /-- The type. -/
  type : Ty σ s
  /-- The derivation. -/
  typing : DefsTy G W Γ ds type

/-! ### Rules that read a synthesised type

A type selection needs its observation to report a type member at the selected
label, and an application needs its receiver at a method type.  Each is
factored into a helper that takes the premise's derivation, so that its only
case analysis is on the type that premise reports; `defL`/`defR` read the
stored definition through `witness?`. -/

section Helpers
variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ}

/-- `LeTy.defL`: the stored literal must define `a` as a type, and the premise
must start there. -/
def leDefL {s : Sig} {Γ : Ctx σ s} (l : BVar σ .var) (a : Lb) {e : Le σ []}
    {S T : Ty σ []} (he : LeTy G W .nil e S T) : Option (LeChecked G W Γ (.defL l a e)) :=
  match witness? ((G.lookup l).get? a) with
  | some ⟨.dty TX, hg⟩ =>
      if h : S = TX then
        some ⟨.TSel (.conc l) a, T.rename renameNil, .defL hg (by rw [← h]; exact he)⟩
      else none
  | _ => none

/-- `LeTy.defR`: the stored literal must define `a` as a type, and the premise
must end there. -/
def leDefR {s : Sig} {Γ : Ctx σ s} (l : BVar σ .var) (a : Lb) {e : Le σ []}
    {S T : Ty σ []} (he : LeTy G W .nil e S T) : Option (LeChecked G W Γ (.defR l a e)) :=
  match witness? ((G.lookup l).get? a) with
  | some ⟨.dty TX, hg⟩ =>
      if h : T = TX then
        some ⟨S.rename renameNil, .TSel (.conc l) a, .defR hg (by rw [← h]; exact he)⟩
      else none
  | _ => none

/-- `LeTy.selL`: the observation must report `{a : ⊥ .. U}`. -/
def leSelL {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)} (a : Lb)
    {T : Ty σ (scopeAt p)} (hv : VcTy G W Γ p v T) : Option (LeChecked G W Γ (.selL p a v)) :=
  match T, hv with
  | .TTyp a' .TBot U, hv =>
      if h : a' = a then
        some ⟨.TSel p a, U.rename (renameAt p), .selL (by rw [← h]; exact hv)⟩
      else none
  | _, _ => none

/-- `LeTy.selR`: the observation must report `{a : S .. ⊤}`. -/
def leSelR {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)} (a : Lb)
    {T : Ty σ (scopeAt p)} (hv : VcTy G W Γ p v T) : Option (LeChecked G W Γ (.selR p a v)) :=
  match T, hv with
  | .TTyp a' S .TTop, hv =>
      if h : a' = a then
        some ⟨S.rename (renameAt p), .TSel p a, .selR (by rw [← h]; exact hv)⟩
      else none
  | _, _ => none

/-- `TmTy.app`: the receiver must be at a method type at the invoked label,
whose domain is the argument's type. -/
def tmApp {s : Sig} {Γ : Ctx σ s} {a b : Atom σ s} (l : Lb) {Ta Tb : Ty σ s}
    (ha : AtomTy G W Γ a Ta) (hb : AtomTy G W Γ b Tb) : Option (TmChecked G W Γ (.app a l b)) :=
  match Ta, ha with
  | .TFun l' S U, ha =>
      if hl : l' = l then
        if hS : Tb = S then
          some ⟨U.substVr b.root, .app (by rw [← hl]; exact ha) (by rw [← hS]; exact hb)⟩
        else none
      else none
  | _, _ => none

end Helpers

/-! ## The evidence kernel

`synthLeCore` synthesises both endpoints of an inclusion; `synthVcCore`, given
the subject, the type an observation reports.  An observation's scope index is
its subject's prefix, so the subject is an argument, and the rules that fix
its zone (`vcVar` at an abstract variable; `vcLoc`, `vcLocAny` and `vcPack` at a
location) look at it.  In particular `vcPack` at an abstract variable is
rejected: no rule types it. -/

mutual

/-- The inclusion kernel. -/
def synthLeCore {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (e : Le σ s) :
    Option (LeChecked G W Γ e) :=
  match e with
  | .refl T => some ⟨T, T, .refl T⟩
  | .trans M e f => do
      let ce ← synthLeCore G W Γ e
      let cf ← synthLeCore G W Γ f
      if h1 : ce.target = M then
        if h2 : cf.source = M then
          some ⟨ce.source, cf.target,
            .trans M (by rw [← h1]; exact ce.typing) (by rw [← h2]; exact cf.typing)⟩
        else none
      else none
  | .top T => some ⟨T, .TTop, .top T⟩
  | .bot T => some ⟨.TBot, T, .bot T⟩
  | .dtyp l e f => do
      let ce ← synthLeCore G W Γ e
      let cf ← synthLeCore G W Γ f
      some ⟨.TTyp l ce.target cf.source, .TTyp l ce.source cf.target, .dtyp ce.typing cf.typing⟩
  | .dfun l e f => do
      let ce ← synthLeCore G W Γ e
      let cf ← synthLeCore G W (Γ.cons ce.source.weaken) f
      some ⟨.TFun l ce.target cf.source, .TFun l ce.source cf.target, .dfun ce.typing cf.typing⟩
  | .andI T1 T2 e f => do
      let ce ← synthLeCore G W Γ e
      let cf ← synthLeCore G W Γ f
      if h1 : ce.target = T1 then
        if h2 : cf.target = T2 then
          if h3 : cf.source = ce.source then
            some ⟨ce.source, .TAnd T1 T2, .andI T1 T2 (by rw [← h1]; exact ce.typing)
              (by rw [← h2, ← h3]; exact cf.typing)⟩
          else none
        else none
      else none
  | .andE1 T2 e => do
      let ce ← synthLeCore G W Γ e
      some ⟨.TAnd ce.source T2, ce.target, .andE1 T2 ce.typing⟩
  | .andE2 T1 e => do
      let ce ← synthLeCore G W Γ e
      some ⟨.TAnd T1 ce.source, ce.target, .andE2 T1 ce.typing⟩
  | .orI1 T2 e => do
      let ce ← synthLeCore G W Γ e
      some ⟨ce.source, .TOr ce.target T2, .orI1 T2 ce.typing⟩
  | .orI2 T1 e => do
      let ce ← synthLeCore G W Γ e
      some ⟨ce.source, .TOr T1 ce.target, .orI2 T1 ce.typing⟩
  | .orE S1 S2 e f => do
      let ce ← synthLeCore G W Γ e
      let cf ← synthLeCore G W Γ f
      if h1 : ce.source = S1 then
        if h2 : cf.source = S2 then
          if h3 : cf.target = ce.target then
            some ⟨.TOr S1 S2, ce.target, .orE S1 S2 (by rw [← h1]; exact ce.typing)
              (by rw [← h2, ← h3]; exact cf.typing)⟩
          else none
        else none
      else none
  | .defL l a e => do
      let ce ← synthLeCore G W .nil e
      leDefL l a ce.typing
  | .defR l a e => do
      let ce ← synthLeCore G W .nil e
      leDefR l a ce.typing
  | .selL p a v => do
      let cv ← synthVcCore G W Γ p v
      leSelL a cv.typing
  | .selR p a v => do
      let cv ← synthVcCore G W Γ p v
      leSelR a cv.typing
  | .bindx S T e => do
      let ce ← synthLeCore G W (Γ.cons S) e
      if h1 : ce.source = S then
        if h2 : ce.target = T then
          some ⟨.TBind S, .TBind T, .bindx S T (by
            have d := ce.typing; rw [h1, h2] at d; exact d)⟩
        else none
      else none
  | .muDrop T => some ⟨.TBind T.weaken, T, .muDrop T⟩

/-- The observation kernel, at the subject `p`. -/
def synthVcCore {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (p : Vr σ s)
    (v : Vc σ (scopeAt p)) : Option (VcChecked G W Γ p v) :=
  match v with
  | .vcVar =>
      match p with
      | .abs x => some ⟨Γ.lookupAt x, .vcVar⟩
      | .conc _ => none
  | .vcLoc l =>
      match p with
      | .conc l' => if h : l = l' then some ⟨tyOf W l', by rw [← h]; exact .vcLoc⟩ else none
      | .abs _ => none
  | .vcLocAny l T =>
      match p with
      | .conc l' =>
          if h : l = l' then
            if hb : litMatchB (G.lookup l).get? (T.substVr (.conc l)) = true then
              some ⟨T.substVr (.conc l'), by rw [← h]; exact .vcLocAny (litMatchB_sound _ _ hb)⟩
            else none
          else none
      | .abs _ => none
  | .vcPack T v =>
      match p, T, v with
      | .conc l, T, v => do
          let cv ← synthVcCore G W Γ (.conc l) v
          if h : cv.type = T.substVr (.conc l) then
            some ⟨.TBind T, .vcPack (by rw [← h]; exact cv.typing)⟩
          else none
      | .abs _, _, _ => none
  | .vcUnfold T v => do
      let cv ← synthVcCore G W Γ p v
      if h : cv.type = .TBind T then
        some ⟨T.substVr (selfAt p), .vcUnfold (by rw [← h]; exact cv.typing)⟩
      else none
  | .vcSub T1 e v => do
      let cv ← synthVcCore G W Γ p v
      let ce ← synthLeCore G W (ctxAt Γ p) e
      if h1 : cv.type = T1 then
        if h2 : ce.source = T1 then
          some ⟨ce.target, .vcSub T1 (by rw [← h1]; exact cv.typing)
            (by rw [← h2]; exact ce.typing)⟩
        else none
      else none

end


/-! ## The term kernel

Atoms first, on their own, since terms and definition lists contain atoms but
atoms contain only evidence.  A location is typed by the rule of its node:
`var (conc ℓ)` at the recorded type, `loc ℓ T` at `T[ℓ]` once `litMatchB`
accepts it. -/

/-- The atom kernel. -/
def synthAtomCore {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (a : Atom σ s) :
    Option (AtomChecked G W Γ a) :=
  match a with
  | .var (.abs x) => some ⟨Γ.lookup x, .varAbs⟩
  | .var (.conc l) => some ⟨(tyOf W l).rename renameNil, .varConc⟩
  | .loc l T =>
      if hb : litMatchB (G.lookup l).get? (T.substVr (.conc l)) = true then
        some ⟨(T.substVr (.conc l)).rename renameNil, .varConcAny (litMatchB_sound _ _ hb)⟩
      else none
  | .cast a e => do
      let ca ← synthAtomCore G W Γ a
      let ce ← synthLeCore G W Γ e
      if h : ce.source = ca.type then
        some ⟨ce.target, .cast ca.typing (by rw [← h]; exact ce.typing)⟩
      else none
  | .pack T a => do
      let ca ← synthAtomCore G W Γ a
      if h : ca.type = T.substVr a.root then
        some ⟨.TBind T, .pack (by rw [← h]; exact ca.typing)⟩
      else none
  | .unpack T a => do
      let ca ← synthAtomCore G W Γ a
      if h : ca.type = .TBind T then
        some ⟨T.substVr a.root, .unpack (by rw [← h]; exact ca.typing)⟩
      else none

mutual

/-- The term kernel.  A `let` body's type must strengthen past the bound
variable, which is `TmTy.let`'s weakened result type read backwards. -/
def synthTmCore {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (t : Tm σ s) :
    Option (TmChecked G W Γ t) :=
  match t with
  | .atom a => do
      let ca ← synthAtomCore G W Γ a
      some ⟨ca.type, .atom ca.typing⟩
  | .new T ds => do
      let cd ← synthDefsCore G W (Γ.cons T) ds
      if h : cd.type = T then
        some ⟨.TBind T, .new T (by have d := cd.typing; rw [h] at d; exact d)⟩
      else none
  | .app a l b => do
      let ca ← synthAtomCore G W Γ a
      let cb ← synthAtomCore G W Γ b
      tmApp l ca.typing cb.typing
  | .let t u => do
      let ct ← synthTmCore G W Γ t
      let cu ← synthTmCore G W (Γ.cons ct.type.weaken) u
      match Ty.strengthenW? cu.type with
      | some ⟨T, hT⟩ =>
          some ⟨T, .let ct.typing (by have d := cu.typing; rw [hT] at d; exact d)⟩
      | none => none
  | .cast t e => do
      let ct ← synthTmCore G W Γ t
      let ce ← synthLeCore G W Γ e
      if h : ce.source = ct.type then
        some ⟨ce.target, .cast ct.typing (by rw [← h]; exact ce.typing)⟩
      else none

/-- The definition-list kernel.  Labels are positions, so each member's label
is the length of its tail. -/
def synthDefsCore {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (ds : Defs σ s) :
    Option (DefsChecked G W Γ ds) :=
  match ds with
  | .dnil => some ⟨.TTop, .dnil⟩
  | .dty T ds => do
      let cd ← synthDefsCore G W Γ ds
      some ⟨.TAnd (.TTyp ds.length T T) cd.type, .dty cd.typing⟩
  | .dfun S U t ds => do
      let cd ← synthDefsCore G W Γ ds
      let ct ← synthTmCore G W (Γ.cons S.weaken) t
      if h : ct.type = U then
        some ⟨.TAnd (.TFun ds.length S U) cd.type,
          .dfun cd.typing (by rw [← h]; exact ct.typing)⟩
      else none

end

/-! ## Public interface

Each judgment has a synthesising mode and a checking mode; the checking mode
compares the synthesised outputs with the expected ones. -/

section Public
variable {σ s : Sig}

/-- Synthesise both endpoints of an inclusion. -/
def synthLe (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (e : Le σ s) :
    Option (Ty σ s × Ty σ s) :=
  (synthLeCore G W Γ e).map fun c => (c.source, c.target)

/-- Check an inclusion at given endpoints. -/
def checkLe (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (e : Le σ s) (S T : Ty σ s) :
    Bool :=
  decide (synthLe G W Γ e = some (S, T))

/-- Synthesise the type an observation reports about the subject `p`. -/
def synthVc (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (p : Vr σ s)
    (v : Vc σ (scopeAt p)) : Option (Ty σ (scopeAt p)) :=
  (synthVcCore G W Γ p v).map VcChecked.type

/-- Check an observation of the subject `p` at a given type. -/
def checkVc (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (p : Vr σ s)
    (v : Vc σ (scopeAt p)) (T : Ty σ (scopeAt p)) : Bool :=
  decide (synthVc G W Γ p v = some T)

/-- Synthesise the type of an atom. -/
def synthAtom (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (a : Atom σ s) :
    Option (Ty σ s) :=
  (synthAtomCore G W Γ a).map AtomChecked.type

/-- Check an atom at a given type. -/
def checkAtom (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (a : Atom σ s) (T : Ty σ s) :
    Bool :=
  decide (synthAtom G W Γ a = some T)

/-- Synthesise the type of a term. -/
def synthTm (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (t : Tm σ s) : Option (Ty σ s) :=
  (synthTmCore G W Γ t).map TmChecked.type

/-- Check a term at a given type. -/
def checkTm (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (t : Tm σ s) (T : Ty σ s) : Bool :=
  decide (synthTm G W Γ t = some T)

/-- Synthesise the type of a definition list. -/
def synthDefs (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (ds : Defs σ s) :
    Option (Ty σ s) :=
  (synthDefsCore G W Γ ds).map DefsChecked.type

/-- Check a definition list at a given type. -/
def checkDefs (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s) (ds : Defs σ s) (T : Ty σ s) :
    Bool :=
  decide (synthDefs G W Γ ds = some T)

end Public

/-! ## Soundness

Each kernel already carries the derivation, so soundness is extraction.  The
derivations are data, so these are functions: an accepted input comes with its
typing. -/

section Soundness
variable {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}

/-- **An inclusion the checker accepts is typed** at the endpoints it
synthesises. -/
def synthLe_sound {e : Le σ s} {S T : Ty σ s} (h : synthLe G W Γ e = some (S, T)) :
    LeTy G W Γ e S T :=
  match hc : synthLeCore G W Γ e with
  | some c =>
      have h' : c.source = S ∧ c.target = T := by simpa [synthLe, hc] using h
      h'.1 ▸ h'.2 ▸ c.typing
  | none => absurd h (by simp [synthLe, hc])

/-- An inclusion the checker accepts at given endpoints is typed there. -/
def checkLe_sound {e : Le σ s} {S T : Ty σ s} (h : checkLe G W Γ e S T = true) :
    LeTy G W Γ e S T :=
  synthLe_sound (of_decide_eq_true h)

/-- **An observation the checker accepts is typed** at the type it
synthesises. -/
def synthVc_sound {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (h : synthVc G W Γ p v = some T) : VcTy G W Γ p v T :=
  match hc : synthVcCore G W Γ p v with
  | some c =>
      have h' : c.type = T := by simpa [synthVc, hc] using h
      h' ▸ c.typing
  | none => absurd h (by simp [synthVc, hc])

/-- An observation the checker accepts at a given type is typed there. -/
def checkVc_sound {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (h : checkVc G W Γ p v T = true) : VcTy G W Γ p v T :=
  synthVc_sound (of_decide_eq_true h)

/-- **An atom the checker accepts is typed** at the type it synthesises. -/
def synthAtom_sound {a : Atom σ s} {T : Ty σ s} (h : synthAtom G W Γ a = some T) :
    AtomTy G W Γ a T :=
  match hc : synthAtomCore G W Γ a with
  | some c =>
      have h' : c.type = T := by simpa [synthAtom, hc] using h
      h' ▸ c.typing
  | none => absurd h (by simp [synthAtom, hc])

/-- An atom the checker accepts at a given type is typed there. -/
def checkAtom_sound {a : Atom σ s} {T : Ty σ s} (h : checkAtom G W Γ a T = true) :
    AtomTy G W Γ a T :=
  synthAtom_sound (of_decide_eq_true h)

/-- **A term the checker accepts is typed** at the type it synthesises. -/
def synthTm_sound {t : Tm σ s} {T : Ty σ s} (h : synthTm G W Γ t = some T) :
    TmTy G W Γ t T :=
  match hc : synthTmCore G W Γ t with
  | some c =>
      have h' : c.type = T := by simpa [synthTm, hc] using h
      h' ▸ c.typing
  | none => absurd h (by simp [synthTm, hc])

/-- A term the checker accepts at a given type is typed there. -/
def checkTm_sound {t : Tm σ s} {T : Ty σ s} (h : checkTm G W Γ t T = true) :
    TmTy G W Γ t T :=
  synthTm_sound (of_decide_eq_true h)

/-- **A definition list the checker accepts is typed** at the type it
synthesises. -/
def synthDefs_sound {ds : Defs σ s} {T : Ty σ s} (h : synthDefs G W Γ ds = some T) :
    DefsTy G W Γ ds T :=
  match hc : synthDefsCore G W Γ ds with
  | some c =>
      have h' : c.type = T := by simpa [synthDefs, hc] using h
      h' ▸ c.typing
  | none => absurd h (by simp [synthDefs, hc])

/-- A definition list the checker accepts at a given type is typed there. -/
def checkDefs_sound {ds : Defs σ s} {T : Ty σ s} (h : checkDefs G W Γ ds T = true) :
    DefsTy G W Γ ds T :=
  synthDefs_sound (of_decide_eq_true h)

end Soundness

end FCdotR
