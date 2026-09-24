import Coercions.Paths.FCdot.Typing

namespace Paths

/-!
# FCdot stores

A store holds literals, one per allocated binder.  Store typing types each
entry in the transparent context of the entries before it.
-/

namespace FCdot

/-! ## Stores -/

inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)

/-- The value stored at a binder, weakened into the current scope. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken

/-- Block witnesses of a value: those of the underlying literal. -/
def Value.witnesses : Value s → Witnesses (s,x)
  | .lam _ _ => .nil
  | .obj W _ => W
  | .cast v _ => v.witnesses

/-- Field labels of a value: those of the underlying literal. -/
def Value.fieldLabels : Value s → List Label
  | .lam _ _ => []
  | .obj _ F => F.labels
  | .cast v _ => v.fieldLabels

/-- Stable field labels of a value: those of the underlying literal. -/
def Value.valLabels : Value s → List Label
  | .lam _ _ => []
  | .obj _ F => F.valLabels
  | .cast v _ => v.valLabels

/-- The literal under the cast wrappers. -/
def Value.core : Value s → Value s
  | .cast v _ => v.core
  | v => v

/-- The cast wrappers of a value, innermost first. -/
def Value.coercions : Value s → List (LeCo s)
  | .cast v e => v.coercions ++ [e]
  | _ => []

/-- The cast wrappers of an atom, innermost first (along the first component
of an intersection). -/
def Atom.coercions : Atom s → List (LeCo s)
  | .var _ => []
  | .cast a e => a.coercions ++ [e]
  | .foldSelf _ a => a.coercions
  | .unfoldSelf a => a.coercions
  | .both _ _ a _ => a.coercions
  | .sngl a _ _ => a.coercions

/-- Fold a nonempty list of coercions into one, oldest first.  Declared here,
beside the wrappers it folds, because the coercion of a field is read off the
store before the machine is defined. -/
def LeCo.composite (e : LeCo s) : List (LeCo s) → LeCo s
  | [] => e
  | f :: fs => LeCo.composite (.trans e f) fs

/-! ## The coercion of a field, read off the store

The literal at a node of the forest sits under its own self and the selves of
the literals that enclose it.  `Store.litAt` finds it, stepping through
object-literal field bodies, and carries the path substitution that closes
those selves over the store's scope: the self of the literal at a variable
`y` goes to `var y`, as `Tm.selfAt` renames it, and the self of the literal
at a deeper `p` goes to the node at `p`.  Values are carried and never
substituted.  `Store.fieldCo` composes the casts of a stable field's body and
applies the substitution, which is evidence only (Fact 1). -/

/-- A field body as a value under casts: the value and the casts, innermost
first. -/
def Tm.castList : Tm s → Option (Value s × List (LeCo s))
  | .val v => some (v, [])
  | .cast t e => (t.castList).map fun ve => (ve.1, ve.2 ++ [e])
  | .atom _ => none
  | .app _ _ => none
  | .proj _ _ _ => none
  | .let _ _ => none

/-- The coercion of a field body: the value's own casts, then the term's,
composed.  A body with no cast has none. -/
def Tm.fieldCo (t : Tm s) : Option (LeCo s) :=
  match t.castList with
  | some (v, es) =>
      match v.coercions ++ es with
      | [] => none
      | e :: rest => some (LeCo.composite e rest)
  | none => none

/-- The object literal under a value's casts. -/
def Value.coreObj? : Value s → Option (Witnesses (s,x) × Fields (s,x))
  | .obj W F => some (W, F)
  | .cast v _ => v.coreObj?
  | .lam _ _ => none

/-- The self of the literal at `p`: a variable at depth zero, as `Tm.selfAt`
has it, and the node at depth one and more. -/
def PathCo.selfAt (p : Path s) (W : Witnesses (s,x)) (ls vls : List Label) : PathCo s :=
  match p with
  | .var y => .var y
  | .sel _ _ => .node p W ls vls

/-- The literal at a node of the forest, still under its enclosing selves,
with the path substitution that closes them. -/
def Store.litAt (σ : Store s) : Path s → Option (Σ s' : Sig, Value s' × PSub s' s)
  | .var x => some ⟨s, σ.lookup x, PSub.id⟩
  | .sel p a => do
      let ⟨s', v, τ⟩ ← σ.litAt p
      let (W, F) ← v.coreObj?
      let t ← F.get? a
      let (v', _) ← t.castList
      pure ⟨(s',x), v', τ.cons (PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels)⟩

/-- The coercion of the stable field `a` of the literal at `p`, closed over the
store's scope by the path substitution. -/
def Store.fieldCo (σ : Store s) (p : Path s) (a : Label) : Option (LeCo s) := do
  let ⟨_, v, τ⟩ ← σ.litAt p
  let (W, F) ← v.coreObj?
  let t ← F.get? a
  let E ← t.fieldCo
  pure (E.psubst (τ.cons (PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels)))

/-- A stored value is a literal: no cast wrappers. -/
def Value.IsLiteral : Value s → Prop
  | .cast _ _ => False
  | _ => True

set_option hygiene false in
scoped notation:40 "⊢ " σ:51 " : " Γ:51 => Store.Typed σ Γ

/-- `⊢ σ : Γ`, store typing: every entry is a literal typed in the transparent
context of the entries before it, and the context records its witnesses and
fields. -/
inductive Store.Typed : Store s → Ctx s → Prop where
  | nil : ⊢ .nil : .nil
  | cons :
      ⊢ σ : Γ →
      v.IsLiteral →
      Γ ⊢ᵥ v : T →
      ⊢ .cons σ v : .cons Γ (.transparent T (v.weaken.blocksAt (.var .here)))

open Lean PrettyPrinter in
@[app_unexpander Store.Typed] def Store.Typed.unexpand : Unexpander
  | `($_ $σ $Γ) => `(⊢ $σ : $Γ)
  | _ => throw ()


/-! ## The forest is the store

Invariant A of P1.8: over a typed store the block of every binder is the
block the stored value defines at that binder's path.  A value's block is
always an object node, never a forwarding, so the path lookup at a variable
path agrees with the base's binder lookup. -/

/-- A value's block is an object node. -/
theorem Value.blocksAt_obj {s : Sig} :
    ∀ (v : Value s) (p : Path s),
      ∃ (W : Witnesses s) (ls vls : List Label) (ch : Children s),
        v.blocksAt p = .obj W ls vls ch
  | .lam _ _, _ => ⟨.nil, [], [], .nil, rfl⟩
  | .obj _ F, _ => ⟨_, F.labels, F.valLabels, _, rfl⟩
  | .cast v _, p => Value.blocksAt_obj v p

theorem Value.blocksAt_ne_fwd {s : Sig} (v : Value s) (p : Path s) (q : Path s) :
    v.blocksAt p ≠ .fwd q := by
  obtain ⟨W, ls, vls, ch, h⟩ := Value.blocksAt_obj v p
  rw [h]
  intro hc
  cases hc

/-- The stable field labels of a value are exactly the labels whose child in
its block is an object node (decisions 24 and 25).  This is the coherence the
`∋ᵛ` propositions of a literal's precise telescope rest on. -/
theorem Value.valLabels_children {s : Sig} :
    ∀ (v : Value s) (p : Path s) (a : Label),
      a ∈ v.valLabels ↔ ∃ W ls vls ch, (v.blocksAt p).childAt? a = some (.obj W ls vls ch)
  | .lam _ _, _, _ => by
      simp [Value.valLabels, Value.blocksAt, Value.blockSelf, Block.substPath, Block.subst,
        Block.childAt?, Children.subst, Children.at?]
  | .cast v _, p, a => Value.valLabels_children v p a
  | .obj W F, p, a => by
      show a ∈ F.valLabels ↔ _
      rw [Fields.mem_valLabels_iff_children F (.var .here) a]
      simp only [Value.blocksAt, Value.blockSelf, Block.substPath, Block.subst, Block.childAt?,
        Children.at?_subst, Option.map_eq_some_iff]
      constructor
      · rintro ⟨W', ls, vls, ch, h⟩
        exact ⟨_, _, _, _, _, h, rfl⟩
      · rintro ⟨W', ls, vls, ch, B, h, hB⟩
        cases B with
        | obj W'' ls' vls' ch' => exact ⟨W'', ls', vls', ch', h⟩
        | fwd q => simp [Block.subst] at hB

/-- The direction the walk reads: a label whose child in a value's block is
an object node is a stable label of the value. -/
theorem Value.mem_valLabels_of_childAt? {s : Sig} {v : Value s} {p : Path s} {a : Label}
    {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    (h : (v.blocksAt p).childAt? a = some (.obj W ls vls ch)) : a ∈ v.valLabels :=
  (Value.valLabels_children v p a).2 ⟨W, ls, vls, ch, h⟩

theorem Store.Typed.blockAt {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ x : BVar s .var, Γ.blockAt x = some ((σ.lookup x).blocksAt (.var x)) := by
  induction h with
  | nil => intro x; cases x
  | cons _ _ _ ih =>
      intro x
      cases x with
      | here => rfl
      | there y =>
          simp only [Ctx.blockAt, Store.lookup, ih y, Option.map_some,
            Value.blocksAt_weaken]

theorem Store.Typed.lookupBlock {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ)
    (x : BVar s .var) : Γ.lookupBlock (.var x) = some ((σ.lookup x).blocksAt (.var x)) := by
  obtain ⟨W, ls, vls, ch, hb⟩ := Value.blocksAt_obj (σ.lookup x) (.var x)
  refine Ctx.lookupBlock_var Γ x ((h.blockAt x).trans (congrArg some hb)) ?_ |>.trans ?_
  · intro q hq; cases hq
  · exact congrArg some hb.symm

/-- The agreement of the two lookups over a typed store: at a variable path
the block-forest lookup is the base's binder lookup. -/
theorem Store.Typed.lookupDefP {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ)
    (x : BVar s .var) (ℓ : Label) : Γ.lookupDefP (.var x) ℓ = Γ.lookupDef x ℓ := by
  refine Ctx.lookupDefP_var Γ x ℓ ?_
  intro q hq
  rw [h.blockAt x] at hq
  exact Value.blocksAt_ne_fwd (σ.lookup x) (.var x) q (Option.some.inj hq)

/-- The same for field labels. -/
theorem Store.Typed.lookupFieldsP {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ)
    (x : BVar s .var) : Γ.lookupFieldsP (.var x) = Γ.lookupFields x := by
  refine Ctx.lookupFieldsP_var Γ x ?_
  intro q hq
  rw [h.blockAt x] at hq
  exact Value.blocksAt_ne_fwd (σ.lookup x) (.var x) q (Option.some.inj hq)


end FCdot

end Paths
