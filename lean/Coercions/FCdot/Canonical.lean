import Coercions.FCdot.Machine

/-!
# Head normal forms of closed evidence

Closed inclusion evidence over a store normalizes to a head form: `bot`,
`top`, `refl`, a function coercion with explicit domain and codomain
evidence, or an object coercion with an explicit morphism.  Normalization
is a fuel-indexed total function on closed terms; existence of fuel and
typing of the result are the theorems of `CanonicalMetatheory.lean`.

Elimination at an atom substitutes the atom into the morphism obtained for
the view; composing two object coercions substitutes the first into the
second under a cast of the self binder.  Both are eager substitutions, so
the normalizer never re-enters a term it produced.
-/

namespace FCdot

/-! ## Resolution of names through transparent definitions -/

/-- Follow definitions at the head of a type, with fuel. -/
def Ctx.resolveFuel (Γ : Ctx s) : Nat → Ty s → Ty s
  | 0, T => T
  | n + 1, .sel x ℓ =>
      match Γ.lookupDef x ℓ with
      | some W => Γ.resolveFuel n W
      | none => .sel x ℓ
  | _ + 1, T => T

def Ctx.length : Ctx s → Nat
  | .nil => 0
  | .cons Γ _ => Γ.length + 1

/-- Resolution with enough fuel for any alias chain in the context. -/
def Ctx.resolve (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resolveFuel (Γ.length + 1) T

/-! ## Forms -/

/-- Head normal forms of closed inclusion evidence. -/
inductive Form : Sig → Type where
  | bot : Form s
  | top : Form s
  | refl : Form s
  /-- Function coercion: domain evidence and codomain evidence under the
      target domain binder. -/
  | pi : LeCo s → LeCo (s,x) → Form s
  /-- Object coercion: a morphism under the source object's self binder. -/
  | obj : Morphism (s,x) → Form s

/-- Index into a morphism, oldest entry first (mirrors `Telescope.At`). -/
def Morphism.length : Morphism s → Nat
  | .nil => 0
  | .le m _ => m.length + 1
  | .eq m _ => m.length + 1
  | .has m _ => m.length + 1

/-- The `i`-th inclusion entry of a morphism, if it is one. -/
def Morphism.getLe? : Morphism s → Nat → Option (LeCo s)
  | .nil, _ => none
  | .le m e, i => if i = m.length then some e else m.getLe? i
  | .eq m _, i => if i = m.length then none else m.getLe? i
  | .has m _, i => if i = m.length then none else m.getLe? i

def Morphism.getHas? : Morphism s → Nat → Option (Has s)
  | .nil, _ => none
  | .le m _, i => if i = m.length then none else m.getHas? i
  | .eq m _, i => if i = m.length then none else m.getHas? i
  | .has m h, i => if i = m.length then some h else m.getHas? i

/-- Instantiate the self binder of a morphism by an atom. -/
def Morphism.at (m : Morphism (s,x)) (a : Atom s) : Morphism s := m.subst (Subst.single a)

/-- Compose two object coercions: use the self binder of the second under
a cast by the first. -/
def Morphism.compose (m₁ m₂ : Morphism (s,x)) : Morphism (s,x) :=
  m₂.subst (Subst.selfCast (LeCo.obj m₁).weaken)

/-- Combine the head forms of two composable coercions. -/
def Form.combine : Form s → Form s → Form s
  | .refl, F => F
  | F, .refl => F
  | .bot, _ => .bot
  | _, .top => .top
  | .pi d₁ c₁, .pi d₂ c₂ =>
      .pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂.weaken)) c₂)
  | .obj m₁, .obj m₂ => .obj (Morphism.compose m₁ m₂)
  | F, _ => F

/-- The identity morphism on a telescope: each proposition by elimination
at the self binder with reflexive evidence. -/
def Telescope.identity (Tel : Telescope (s,x)) (T : Ty (s,x)) : Morphism (s,x) :=
  go Tel
where
  go : Telescope (s,x) → Morphism (s,x)
    | .nil => .nil
    | .cons Tel' (.le _ _) => .le (go Tel') (.member (.var .here) (.refl T) Tel'.length)
    | .cons Tel' (.eq _ _) => .eq (go Tel') (.member (.var .here) (.refl T) Tel'.length)
    | .cons Tel' (.has _) => .has (go Tel') (.member (.var .here) (.refl T) Tel'.length)

/-! ## The normalizer -/

/-- Telescope evidence of a stored literal, instantiated at its binder. -/
def Store.literalEvidence (σ : Store s) (x : BVar s .var) : Option (Morphism s) :=
  match σ.lookup x with
  | .obj _ _ E _ => some (E.at (.var x))
  | _ => none

mutual

/-- Head form of closed inclusion evidence, with fuel. -/
def hnf (σ : Store s) : Nat → LeCo s → Option (Form s)
  | 0, _ => none
  | _ + 1, .refl _ => some .refl
  | _ + 1, .top _ => some .top
  | _ + 1, .bot _ => some .bot
  | _ + 1, .eqToLe _ => some .refl
  | _ + 1, .pi d c => some (.pi d c)
  | _ + 1, .obj m => some (.obj m)
  | n + 1, .trans e f => do
      let F ← hnf σ n e
      let G ← hnf σ n f
      pure (F.combine G)
  | n + 1, .member a e i => do
      let F ← hnf σ n e
      match F with
      | .obj m => do
          let e' ← (m.at a).getLe? i
          hnf σ n e'
      | .refl => viewLe σ n a i
      | _ => none
  | n + 1, .piDom a => do
      let F ← atomForm σ n a
      match F with
      | .pi d _ => hnf σ n d
      | .refl => some .refl
      | _ => none
  | n + 1, .piCod a b => do
      let F ← atomForm σ n a
      match F with
      | .pi _ c => hnf σ n (c.subst (Subst.single b))
      | .refl => some .refl
      | _ => none

/-- The form of the `i`-th inclusion proposition of an atom's own type,
at the atom. -/
def viewLe (σ : Store s) : Nat → Atom s → Nat → Option (Form s)
  | 0, _, _ => none
  | n + 1, .var x, i => do
      let m ← σ.literalEvidence x
      let e ← m.getLe? i
      hnf σ n e
  | n + 1, .cast a e, i => hnf σ n (.member a e i)
  | n + 1, .foldSelf a, i => viewLe σ n a i
  | n + 1, .unfoldSelf a, i => viewLe σ n a i

/-- The form of an atom's composite wrappers, from its root's literal type. -/
def atomForm (σ : Store s) : Nat → Atom s → Option (Form s)
  | 0, _ => none
  | _ + 1, .var _ => some .refl
  | n + 1, .cast a e => do
      let F ← atomForm σ n a
      let G ← hnf σ n e
      pure (F.combine G)
  | n + 1, .foldSelf a => atomForm σ n a
  | n + 1, .unfoldSelf a => atomForm σ n a

end

/-- Field presence witnessed by closed `has` evidence, with fuel. -/
def hnfHas (σ : Store s) : Nat → Has s → Option (BVar s .var × Label)
  | 0, _ => none
  | _ + 1, .field _ => none
  | n + 1, .member a e i => do
      let F ← hnf σ n e
      match F with
      | .obj m => do
          let h ← (m.at a).getHas? i
          hnfHas σ n h
      | .refl => viewHas σ n a i
      | _ => none
where
  viewHas (σ : Store s) : Nat → Atom s → Nat → Option (BVar s .var × Label)
    | 0, _, _ => none
    | n + 1, .var x, i =>
        match σ.lookup x with
        | .obj Tel _ _ F =>
            match Tel.get? i with
            | some (.has ℓ) => if (F.get? ℓ).isSome then some (x, ℓ) else none
            | _ => none
        | _ => none
    | n + 1, .cast a e, i => hnfHas σ n (.member a e i)
    | n + 1, .foldSelf a, i => viewHas σ n a i
    | n + 1, .unfoldSelf a, i => viewHas σ n a i

end FCdot
