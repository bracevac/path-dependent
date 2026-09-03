import Coercions.FCdot.Store

/-!
# Head normal forms of closed evidence

Inclusion evidence over a store normalizes to a head form: `bot`, `top`,
`refl`, a function coercion with closed domain and codomain evidence, or a
chain of object coercions.  Evidence is normalized under an environment
that closes its opaque binders by store atoms and records, for each such
binder, the normal forms of its type's telescope (its *view*).  Views are
data: eliminating a member fact looks a view up rather than substituting
evidence, and composing object coercions chains closures rather than
substituting one morphism into the other.  This keeps every recursion
structural in the evidence term, so the normalizer is a fuel-indexed total
function whose fuel bound is syntactic.

The metatheory (existence of fuel, typing of forms, and the corollaries
used by progress) is in `CanonicalMetatheory.lean`.
-/

namespace FCdot

/-! ## Resolution of names through transparent definitions -/

def Ctx.length : Ctx s → Nat
  | .nil => 0
  | .cons Γ _ => Γ.length + 1

/-- Follow definitions at the head of a type, with fuel. -/
def Ctx.resolveFuel (Γ : Ctx s) : Nat → Ty s → Ty s
  | 0, T => T
  | n + 1, .sel x ℓ =>
      match Γ.lookupDef x ℓ with
      | some W => Γ.resolveFuel n W
      | none => .sel x ℓ
  | _ + 1, T => T

/-- Resolution with enough fuel for any alias chain in the context. -/
def Ctx.resolve (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resolveFuel (Γ.length + 1) T

/-! ## Forms, views, environments -/

mutual

/-- Head normal forms of inclusion evidence, closed over the store scope `s`. -/
inductive Form (s : Sig) : Type where
  | bot : Form s
  | top : Form s
  /-- Syntactic identity: both endpoints are the same type. -/
  | id : Form s
  /-- Definitional conversion: closed equality evidence between the endpoints. -/
  | eqv : EqCo s → Form s
  /-- Function coercion: closed domain evidence and codomain evidence under
      the target domain binder. -/
  | pi : LeCo s → LeCo (s,x) → Form s
  /-- Object coercion: a chain of steps applied in order. -/
  | obj : List (ChainStep s) → Form s

/-- The normal form of one telescope proposition at a self atom. -/
inductive PropForm (s : Sig) : Type where
  | le : Form s → PropForm s
  | eq : PropForm s
  /-- Field `ℓ` is present at binder `x`. -/
  | has : BVar s .var → Label → PropForm s

/-- One step of an object coercion chain: a definitional conversion of the
self atom, or a morphism under a self binder together with the environment
closing its other binders into the store scope. -/
inductive ChainStep (s : Sig) : Type where
  | conv : EqCo s → ChainStep s
  | clos : (s' : Sig) → Telescope (s',x) → Morphism (s',x) → Env s s' → ChainStep s

/-- Environment closing an open scope into the store scope: for each binder
of the open scope, a closing atom and the view of its type. -/
inductive Env (s : Sig) : Sig → Type where
  | nil : Env s []
  | cons : Env s s' → Atom s → List (PropForm s) → Env s (s',x)

end

abbrev View (s : Sig) := List (PropForm s)

namespace Env

def atom : Env s s' → BVar s' .var → Atom s
  | .cons _ a _, .here => a
  | .cons η _ _, .there y => η.atom y

def view : Env s s' → BVar s' .var → View s
  | .cons _ _ V, .here => V
  | .cons η _ _, .there y => η.view y

/-- The closing substitution induced by an environment. -/
def toSubst (η : Env s s') : Subst s' s where
  var := η.atom

end Env

/-- The `i`-th proposition form of a view. -/
def View.nth? : View s → Nat → Option (PropForm s)
  | [], _ => none
  | P :: _, 0 => some P
  | _ :: V, i + 1 => View.nth? V i

/-! ### Renaming of forms over the store scope -/

mutual

def Form.rename : Form s → Rename s s₂ → Form s₂
  | .bot, _ => .bot
  | .top, _ => .top
  | .id, _ => .id
  | .eqv φ, ρ => .eqv (φ.rename ρ)
  | .pi d c, ρ => .pi (d.rename ρ) (c.rename ρ.lift)
  | .obj cs, ρ => .obj (ChainStep.renameList cs ρ)

def ChainStep.renameList : List (ChainStep s) → Rename s s₂ → List (ChainStep s₂)
  | [], _ => []
  | c :: cs, ρ => c.rename ρ :: ChainStep.renameList cs ρ

def ChainStep.rename : ChainStep s → Rename s s₂ → ChainStep s₂
  | .conv φ, ρ => .conv (φ.rename ρ)
  | .clos s' Tel m η, ρ => .clos s' Tel m (η.rename ρ)

def PropForm.rename : PropForm s → Rename s s₂ → PropForm s₂
  | .le F, ρ => .le (F.rename ρ)
  | .eq, _ => .eq
  | .has x ℓ, ρ => .has (ρ.var x) ℓ

def PropForm.renameList : List (PropForm s) → Rename s s₂ → List (PropForm s₂)
  | [], _ => []
  | P :: V, ρ => P.rename ρ :: PropForm.renameList V ρ

def Env.rename : Env s s' → Rename s s₂ → Env s₂ s'
  | .nil, _ => .nil
  | .cons η a V, ρ => .cons (η.rename ρ) (a.rename ρ) (PropForm.renameList V ρ)

end

def Env.weaken (η : Env s s') : Env (s,,k) s' := η.rename Rename.succ

/-! ## Composition of forms -/

/-- Combine the head forms of two composable coercions.  Conversions are
composed as equalities and absorbed into function forms; object chains
concatenate, with conversions recorded as chain steps. -/
def Form.combine : Form s → Form s → Form s
  | .id, F => F
  | F, .id => F
  | .bot, _ => .bot
  | _, .top => .top
  | .eqv _, .bot => .bot
  | .eqv φ, .eqv ψ => .eqv (.trans φ ψ)
  | .eqv _, .pi d c => .pi d c
  | .pi d c, .eqv _ => .pi d c
  | .eqv φ, .obj cs => .obj (.conv φ :: cs)
  | .obj cs, .eqv ψ => .obj (cs ++ [.conv ψ])
  | .pi d₁ c₁, .pi d₂ c₂ =>
      .pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂.weaken)) c₂)
  | .obj cs₁, .obj cs₂ => .obj (cs₁ ++ cs₂)
  | F, _ => F

/-- Close the morphism of a closure step into an object coercion over the store. -/
def ChainStep.close : ChainStep s → LeCo s
  | .conv φ => .eqToLe φ
  | .clos _ Tel m η => .obj (Tel.rename η.toSubst.root.lift) (m.subst η.toSubst.lift)

/-- The environment of a store with no views. -/
def emptyEnv : Store s → Env s s
  | .nil => .nil
  | .cons σ _ => .cons ((emptyEnv σ).weaken) (.var .here) []

/-! ## The normalizer -/

mutual

/-- Head form of inclusion evidence under an environment, with fuel. -/
def hnf (σ : Store s) : Nat → Env s s' → LeCo s' → Option (Form s)
  | 0, _, _ => none
  | _ + 1, η, .refl T => some (.eqv (.refl (T.rename η.toSubst.root)))
  | _ + 1, _, .top _ => some .top
  | _ + 1, _, .bot _ => some .bot
  | _ + 1, η, .eqToLe φ => some (.eqv (φ.subst η.toSubst))
  | _ + 1, η, .pi d c => some (.pi (d.subst η.toSubst) (c.subst η.toSubst.lift))
  | _ + 1, η, .obj Tel m => some (.obj [ChainStep.clos _ Tel m η])
  | n + 1, η, .trans e f => do
      let F ← hnf σ n η e
      let G ← hnf σ n η f
      pure (F.combine G)
  | n + 1, η, .member a e i => do
      let F ← hnf σ n η e
      let (a', V) ← atomView σ n η a
      let V' ← applyForm σ n F a' V
      match View.nth? V' i with
      | some (.le G) => some G
      | _ => none

/-- The closing atom of an open atom and the view of its type. -/
def atomView (σ : Store s) : Nat → Env s s' → Atom s' → Option (Atom s × View s)
  | 0, _, _ => none
  | _ + 1, η, .var y => some (η.atom y, η.view y)
  | n + 1, η, .cast a e => do
      let (a', V) ← atomView σ n η a
      let F ← hnf σ n η e
      let V' ← applyForm σ n F a' V
      pure (.cast a' (e.subst η.toSubst), V')
  | n + 1, η, .foldSelf Tel a => do
      let (a', V) ← atomView σ n η a
      pure (.foldSelf (Tel.rename η.toSubst.root.lift) a', V)
  | n + 1, η, .unfoldSelf a => do
      let (a', V) ← atomView σ n η a
      pure (.unfoldSelf a', V)

/-- The closing atom of an open atom and the head form of its wrappers,
from its root's type. -/
def atomForm (σ : Store s) : Nat → Env s s' → Atom s' → Option (Atom s × Form s)
  | 0, _, _ => none
  | n + 1, η, .var y => closedAtomForm σ n (η.atom y)
  | n + 1, η, .cast a e => do
      let (a', F) ← atomForm σ n η a
      let G ← hnf σ n η e
      pure (.cast a' (e.subst η.toSubst), F.combine G)
  | n + 1, η, .foldSelf Tel a => do
      let (a', F) ← atomForm σ n η a
      pure (.foldSelf (Tel.rename η.toSubst.root.lift) a', F)
  | n + 1, η, .unfoldSelf a => do
      let (a', F) ← atomForm σ n η a
      pure (.unfoldSelf a', F)

/-- The head form of a closed atom's wrappers, from its root's literal type. -/
def closedAtomForm (σ : Store s) : Nat → Atom s → Option (Atom s × Form s)
  | 0, _ => none
  | _ + 1, .var x => some (.var x, .id)
  | n + 1, .cast a e => do
      let (a', F) ← closedAtomForm σ n a
      let G ← hnf σ n (storeEnv n σ) e
      pure (.cast a' e, F.combine G)
  | n + 1, .foldSelf Tel a => do
      let (a', F) ← closedAtomForm σ n a
      pure (.foldSelf Tel a', F)
  | n + 1, .unfoldSelf a => do
      let (a', F) ← closedAtomForm σ n a
      pure (.unfoldSelf a', F)

/-- Apply a head form of an object coercion to a self atom with its view,
producing the view of the target telescope. -/
def applyForm (σ : Store s) : Nat → Form s → Atom s → View s → Option (View s)
  | 0, _, _, _ => none
  | _ + 1, .id, _, V => some V
  | _ + 1, .eqv _, _, V => some V
  | n + 1, .obj cs, a, V => applyChain σ n cs a V
  -- A non-object target has no telescope: its view is empty.
  | _ + 1, .pi _ _, _, _ => some []
  | _ + 1, .top, _, _ => some []
  | _ + 1, .bot, _, _ => some []

def applyChain (σ : Store s) : Nat → List (ChainStep s) → Atom s → View s → Option (View s)
  | 0, _, _, _ => none
  | _ + 1, [], _, V => some V
  | n + 1, .conv φ :: cs, a, V => applyChain σ n cs (.cast a (.eqToLe φ)) V
  | n + 1, .clos _ Tel m η :: cs, a, V => do
      let V' ← morphismView σ n (η.cons a V) m
      applyChain σ n cs (.cast a (.obj (Tel.rename η.toSubst.root.lift) (m.subst η.toSubst.lift))) V'

def morphismView (σ : Store s) : Nat → Env s (s',x) → Morphism (s',x) → Option (View s)
  | 0, _, _ => none
  | _ + 1, _, .nil => some []
  | n + 1, η, .le m e => do
      let V ← morphismView σ n η m
      let F ← hnf σ n η e
      pure (V ++ [.le F])
  | n + 1, η, .eq m _ => do
      let V ← morphismView σ n η m
      pure (V ++ [.eq])
  | n + 1, η, .has m h => do
      let V ← morphismView σ n η m
      let p ← hasView σ n η .here h
      pure (V ++ [.has p.1 p.2])

/-- Field presence witnessed by `has` evidence at the expected binder `x`. -/
def hasView (σ : Store s) : Nat → Env s s' → BVar s' .var → Has s' → Option (BVar s .var × Label)
  | 0, _, _, _ => none
  | _ + 1, η, x, .field ℓ => some ((η.atom x).root, ℓ)
  | n + 1, η, _, .member a e i => do
      let F ← hnf σ n η e
      let (a', V) ← atomView σ n η a
      let V' ← applyForm σ n F a' V
      match View.nth? V' i with
      | some (.has x ℓ) => some (x, ℓ)
      | _ => none

/-- The environment of the store scope itself: every binder closes to its
own variable and views its own literal's telescope evidence. -/
def storeEnv : Nat → Store s → Env s s
  | _, .nil => .nil
  | 0, σ => emptyEnv σ
  | n + 1, .cons σ v =>
      let η := (storeEnv n σ).weaken
      let V : View _ :=
        match v with
        | .obj _ _ E _ => (morphismView (.cons σ v) n (η.cons (.var .here) []) E).getD []
        | _ => []
      .cons η (.var .here) V

end

end FCdot
