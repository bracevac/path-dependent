import Coercions.Paths.FCdot.Preservation
import Coercions.Paths.FCdot.TypingPathSubst
import Coercions.Paths.FCdot.FormTyping

namespace Paths

/-!
# The invariants at nodes, and the field coercion

Three invariants of P1.8 over a typed store, at the nodes of the forest.

* *Invariant A at nodes* (`Store.Typed.blockOf_node`).  The block the table
  writes at a node is the block the store gives the path.
* *Invariant B at nodes* (`Store.Typed.nodeBlock_child`).  Below a node, the
  child at a stable label is a node, and it is the block of the object
  literal in that field, the literal `Store.litAt` finds.
* *Invariant C* (`Store.Typed.fieldCo`).  The coercion of a stable field of a
  node, read off the store by `Store.fieldCo`, is typed from the child's
  precise type to the parent's name `p ∙ a`, with the source equal to
  `Γ.nodeTy (p.a)` up to the opening at the child.

All three rest on one induction on the path (`Store.Typed.litAt_node`).  At a
node `p` the literal `Store.litAt` finds is typed in a context `Δ` that
extends the store context by the selves of the literals that enclose it, and
the path substitution that closes those selves sends every binder of `Δ` to
a node of `Γ` at its binder's type (`PSub.NodeTyped`).  At a variable the
substitution is the identity.  One step down, the literal's own self goes to
`PathCo.selfAt p ..`: the variable at depth zero, as `Ctx.Ren.selfObj`
renames it, and the node rule at depth one and more, whose premise is the
node at `p`.  A `PSub.NodeTyped` gives a `PSub.Typed` (`PSub.NodeTyped.typed`),
since a walk that starts at nodes is carried step for step, forwarding
children included (`Ctx.blockPass_psubst`).  Invariant C is then
`LeCo.HasType.psubst` at the field body's composite cast.
-/

namespace FCdot

/-! ## Blocks against a path substitution -/

mutual

theorem Block.subst_subst {s1 s2 s3 : Sig} :
    ∀ (B : Block s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (B.subst σ).subst τ = B.subst (σ.comp τ)
  | .obj W ls vls ch, σ, τ => by
      simp only [Block.subst, Witnesses.subst_subst, Children.subst_subst ch σ τ]
  | .fwd q, σ, τ => by simp only [Block.subst, Path.subst_subst]

theorem Children.subst_subst {s1 s2 s3 : Sig} :
    ∀ (ch : Children s1) (σ : PathSubst s1 s2) (τ : PathSubst s2 s3),
      (ch.subst σ).subst τ = ch.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons ch ℓ B, σ, τ => by
      simp only [Children.subst, Children.subst_subst ch σ τ, Block.subst_subst B σ τ]

end

theorem Block.def?_subst {s1 s2 : Sig} (B : Block s1) (σ : PathSubst s1 s2) (ℓ : Label) :
    (B.subst σ).def? ℓ = (B.def? ℓ).map (Ty.subst · σ) := by
  cases B <;> simp [Block.subst, Block.def?, Witnesses.get_subst]

/-! ## The paths of `PSub.id` and `PSub.cons` -/

theorem PSub.id_paths {s : Sig} : (PSub.id : PSub s s).paths = PathSubst.ofRename Rename.id :=
  PathSubst.funext' (fun _ => rfl)

theorem Ty.subst_psubId {s : Sig} (T : Ty s) : T.subst (PSub.id : PSub s s).paths = T := by
  rw [PSub.id_paths, Ty.subst_ofRename, Ty.rename_id]

theorem Witnesses.subst_psubId_lift {s : Sig} (W : Witnesses (s,x)) :
    W.subst (PSub.id : PSub s s).paths.lift = W := by
  rw [PSub.id_paths, PathSubst.lift_ofRename, Rename.lift_id, Witnesses.subst_ofRename,
    Witnesses.rename_id]

theorem Block.subst_psubId_lift {s : Sig} (B : Block (s,x)) :
    B.subst (PSub.id : PSub s s).paths.lift = B := by
  rw [PSub.id_paths, PathSubst.lift_ofRename, Rename.lift_id, Block.subst_ofRename,
    Block.rename_id]

/-- The paths of `τ.cons P` are those of `τ` under the self, with the self
instantiated at the path `P` names. -/
theorem PSub.cons_paths {s1 s2 : Sig} (τ : PSub s1 s2) (P : PathCo s2) :
    (τ.cons P).paths = τ.paths.lift.comp (PathSubst.one P.path) := by
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y =>
      show (τ.var y).path = (((τ.var y).path).weaken (k := .var)).subst (PathSubst.one P.path)
      rw [Path.subst_one, Path.weaken_substPath]

theorem PSub.succ_pathComp_cons {s1 s2 : Sig} (τ : PSub s1 s2) (P : PathCo s2) :
    (Rename.succ (k := .var)).pathComp (τ.cons P).paths = τ.paths :=
  PathSubst.funext' (fun _ => rfl)

theorem Ty.weaken_subst_cons {s1 s2 : Sig} (T : Ty s1) (τ : PSub s1 s2) (P : PathCo s2) :
    (T.weaken (k := .var)).subst (τ.cons P).paths = T.subst τ.paths := by
  rw [Ty.weaken, Ty.rename_subst, PSub.succ_pathComp_cons]

theorem Block.weaken_subst_cons {s1 s2 : Sig} (B : Block s1) (τ : PSub s1 s2) (P : PathCo s2) :
    (B.weaken (k := .var)).subst (τ.cons P).paths = B.subst τ.paths := by
  rw [Block.weaken, Block.rename_subst, PSub.succ_pathComp_cons]

/-- A block written under a literal's self, instantiated at the path the
literal sits at, is the block substituted by `τ.cons P`. -/
theorem Block.subst_lift_substPath {s1 s2 : Sig} (B : Block (s1,x)) (τ : PSub s1 s2)
    (P : PathCo s2) : (B.subst τ.paths.lift).substPath P.path = B.subst (τ.cons P).paths := by
  rw [Block.substPath, Block.subst_subst, PSub.cons_paths]

/-- The child of a literal's block at `a`, closed and instantiated at the
parent's path `p`, is the child's block closed by `τ.cons P` and instantiated
at `p.a`. -/
theorem Block.child_subst_substPath {s1 s2 : Sig} (B : Block ((s1,x),x)) (τ : PSub s1 s2)
    (P : PathCo s2) (a : Label) :
    ((B.substPath (.sel (.var .here) a)).subst τ.paths.lift).substPath P.path
      = (B.subst (τ.cons P).paths.lift).substPath (.sel P.path a) := by
  rw [Block.substPath, Block.substPath, Block.substPath, Block.subst_subst, Block.subst_subst,
    Block.subst_subst]
  congr 1
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y =>
      cases y with
      | here =>
          show P.path = ((P.path).weaken (k := .var)).subst (PathSubst.one (.sel P.path a))
          rw [Path.subst_one, Path.weaken_substPath]
      | there z =>
          show (((τ.var z).path).weaken (k := .var)).subst (PathSubst.one P.path)
            = ((τ.var z).path.weaken (k := .var)).subst (PathSubst.one (.sel P.path a))
          rw [Path.subst_one, Path.subst_one, Path.weaken_substPath, Path.weaken_substPath]

@[simp] theorem PathCo.selfAt_path {s : Sig} (p : Path s) (W : Witnesses (s,x))
    (ls vls : List Label) : (PathCo.selfAt p W ls vls).path = p := by
  cases p <;> rfl

/-! ## The walk carried along a path substitution

A path substitution that sends every binder to a node carrying its block
carries the whole walk, forwarding children included, step for step.  It is
the twin of `Ctx.blockPass_rename` with a node in place of a binder: a
forwarding child of the source block is a forwarding child of the target
node, to the substituted path. -/

theorem Ctx.blockPass_psubst {s1 s2 : Sig} {Δ : Ctx s1} {Γ : Ctx s2} {π : PathSubst s1 s2}
    (hb : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (π.var x) = some (B.subst π))
    {k : Path s1 → Option (Block s1)} {k' : Path s2 → Option (Block s2)}
    (hk : ∀ q B, k q = some B → k' (q.subst π) = some (B.subst π)) :
    ∀ (p : Path s1) (B : Block s1),
      Δ.blockPass k p = some B → Γ.blockPass k' (p.subst π) = some (B.subst π)
  | .var x, B, h => by
      simp only [Ctx.blockPass] at h
      cases hx : Δ.blockAt x with
      | none => simp only [hx] at h; exact absurd h (by simp)
      | some B₀ =>
          have hn := hb x B₀ hx
          cases B₀ with
          | fwd q =>
              simp only [Block.subst] at hn
              exact absurd hn (Γ.nodeBlock_ne_fwd _ _)
          | obj W ls vls ch =>
              simp only [hx] at h
              obtain rfl : Block.obj W ls vls ch = B := by simpa using h
              exact Γ.blockPass_mono (k := fun _ => none) (fun _ _ h' => by cases h') _ _ hn
  | .sel p a, B, h => by
      simp only [Ctx.blockPass] at h
      simp only [Path.subst, Ctx.blockPass]
      cases hp : Δ.blockPass k p with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some B₀ =>
          cases B₀ with
          | fwd q => simp only [hp] at h; exact absurd h (by simp)
          | obj W ls vls ch =>
              simp only [hp] at h
              have hp' := Ctx.blockPass_psubst hb hk p _ hp
              simp only [Block.subst] at hp'
              simp only [hp', Children.at?_subst]
              cases hc : ch.at? a with
              | none => simp only [hc] at h; exact absurd h (by simp)
              | some B₁ =>
                  cases B₁ with
                  | fwd q =>
                      simp only [hc] at h
                      simp only [Option.map_some, Block.subst]
                      exact hk q B h
                  | obj W' ls' vls' ch' =>
                      simp only [hc] at h
                      obtain rfl : Block.obj W' ls' vls' ch' = B := by simpa using h
                      simp only [Option.map_some, Block.subst]

theorem Ctx.blockFuel_psubst {s1 s2 : Sig} {Δ : Ctx s1} {Γ : Ctx s2} {π : PathSubst s1 s2}
    (hb : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (π.var x) = some (B.subst π)) :
    ∀ (n : Nat) (p : Path s1) (B : Block s1),
      Δ.blockFuel n p = some B → Γ.blockFuel n (p.subst π) = some (B.subst π)
  | 0, p, B, h => by rw [Ctx.blockFuel_zero] at h; exact absurd h (by simp)
  | n+1, p, B, h => by
      simp only [Ctx.blockFuel] at h ⊢
      exact Ctx.blockPass_psubst hb (fun q B' h' => Ctx.blockFuel_psubst hb n q B' h') p B h

theorem Ctx.lookupBlock_psubst {s1 s2 : Sig} {Δ : Ctx s1} {Γ : Ctx s2} {π : PathSubst s1 s2}
    (hb : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (π.var x) = some (B.subst π))
    {p : Path s1} {B : Block s1} (h : Δ.lookupBlock p = some B) :
    Γ.lookupBlock (p.subst π) = some (B.subst π) :=
  Γ.blockFuel_budget (Ctx.blockFuel_psubst hb Δ.aliasBudget p B h)

theorem Ctx.nodeBlock_psubst {s1 s2 : Sig} {Δ : Ctx s1} {Γ : Ctx s2} {π : PathSubst s1 s2}
    (hb : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (π.var x) = some (B.subst π))
    {p : Path s1} {B : Block s1} (h : Δ.nodeBlock p = some B) :
    Γ.nodeBlock (p.subst π) = some (B.subst π) :=
  Ctx.blockPass_psubst hb (k := fun _ => none) (k' := fun _ => none) (fun _ _ h' => by cases h')
    p B h

/-! ## Path substitutions onto nodes -/

/-- A path substitution that sends every binder of `Δ` to a path of `Γ` typed
at the binder's type and to a node carrying the binder's block.  The selves
of the literals that enclose a node are closed this way. -/
structure PSub.NodeTyped {s1 s2 : Sig} (Δ : Ctx s1) (τ : PSub s1 s2) (Γ : Ctx s2) : Prop where
  var : ∀ x, Γ ⊢ᵖ τ.var x : (Δ.lookupTy x).subst τ.paths
  node : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (τ.var x).path = some (B.subst τ.paths)

namespace PSub.NodeTyped

/-- A substitution onto nodes is a typed path substitution. -/
theorem typed {s1 s2 : Sig} {Δ : Ctx s1} {τ : PSub s1 s2} {Γ : Ctx s2}
    (h : PSub.NodeTyped Δ τ Γ) : PSub.Typed Δ τ Γ := by
  have hb : ∀ x B, Δ.blockAt x = some B → Γ.nodeBlock (τ.paths.var x) = some (B.subst τ.paths) :=
    h.node
  have hL : ∀ p B, Δ.lookupBlock p = some B →
      Γ.lookupBlock (p.subst τ.paths) = some (B.subst τ.paths) :=
    fun _ _ hp => Ctx.lookupBlock_psubst hb hp
  refine ⟨h.var, PSub.Typed.defP_of_lookupB hL, ?_, hL,
    fun _ _ hp => Ctx.nodeBlock_psubst hb hp⟩
  intro x ℓ W hW
  rw [Ctx.lookupDef_eq_blockAt] at hW
  cases hx : Δ.blockAt x with
  | none => rw [hx] at hW; exact absurd hW (by simp)
  | some B =>
      rw [hx, Option.bind_some] at hW
      have hl := Γ.nodeBlock_lookupBlock (h.node x B hx)
      rw [Ctx.lookupDefP_eq_bind, hl, Option.bind_some, Block.def?_subst, hW]
      rfl

/-- One more self, sent to a path typed at its type whose node carries its
block. -/
theorem cons {s1 s2 : Sig} {Δ : Ctx s1} {τ : PSub s1 s2} {Γ : Ctx s2}
    (h : PSub.NodeTyped Δ τ Γ) {T : Ty s1} {B : Block (s1,x)} {P : PathCo s2}
    (hP : Γ ⊢ᵖ P : T.subst τ.paths)
    (hn : Γ.nodeBlock P.path = some (B.subst (τ.cons P).paths)) :
    PSub.NodeTyped (Δ.cons (.transparent T B)) (τ.cons P) Γ where
  var x := by
    cases x with
    | here =>
        show Γ ⊢ᵖ P : ((Δ.cons (.transparent T B)).lookupTy .here).subst (τ.cons P).paths
        rw [Ctx.lookupTy_here, Binding.ty, Ty.weaken_subst_cons]
        exact hP
    | there y =>
        show Γ ⊢ᵖ τ.var y : ((Δ.cons (.transparent T B)).lookupTy (.there y)).subst (τ.cons P).paths
        rw [Ctx.lookupTy_there, Ty.weaken_subst_cons]
        exact h.var y
  node x B' hB' := by
    cases x with
    | here =>
        rw [Ctx.blockAt_here_transparent] at hB'
        obtain rfl := Option.some.inj hB'
        exact hn
    | there y =>
        rw [Ctx.blockAt_there] at hB'
        obtain ⟨B₀, hB₀, rfl⟩ := Option.map_eq_some_iff.mp hB'
        rw [Block.weaken_subst_cons]
        exact h.node y B₀ hB₀

end PSub.NodeTyped

/-! ## The literal under its casts -/

theorem Value.core_of_coreObj? {s : Sig} :
    ∀ {v : Value s} {W : Witnesses (s,x)} {F : Fields (s,x)},
      v.coreObj? = some (W, F) → v.core = .obj W F
  | .obj _ _, _, _, h => by
      simp only [Value.coreObj?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .cast v _, _, _, h => by
      simp only [Value.coreObj?] at h
      simpa [Value.core] using Value.core_of_coreObj? h
  | .lam _ _, _, _, h => by simp [Value.coreObj?] at h

theorem Value.blockSelf_of_coreObj? {s : Sig} :
    ∀ {v : Value s} {W : Witnesses (s,x)} {F : Fields (s,x)},
      v.coreObj? = some (W, F) →
        v.blockSelf = .obj W F.labels F.valLabels (F.children (.var .here))
  | .obj _ _, _, _, h => by
      simp only [Value.coreObj?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .cast v _, _, _, h => by
      simp only [Value.coreObj?] at h
      simpa [Value.blockSelf] using Value.blockSelf_of_coreObj? h
  | .lam _ _, _, _, h => by simp [Value.coreObj?] at h

theorem Value.blockSelf_of_coreObj?_none {s : Sig} :
    ∀ {v : Value s}, v.coreObj? = none → v.blockSelf = .obj .nil [] [] .nil
  | .obj _ _, h => by simp [Value.coreObj?] at h
  | .cast v _, h => by
      simp only [Value.coreObj?] at h
      simpa [Value.blockSelf] using Value.blockSelf_of_coreObj?_none h
  | .lam _ _, _ => rfl

theorem Value.coreObj?_of_isObjLit {s : Sig} :
    ∀ {v : Value s}, v.isObjLit = true → ∃ W F, v.coreObj? = some (W, F)
  | .obj W F, _ => ⟨W, F, rfl⟩
  | .cast v _, h => by
      simp only [Value.isObjLit] at h
      simpa [Value.coreObj?] using Value.coreObj?_of_isObjLit (v := v) h
  | .lam _ _, h => by simp [Value.isObjLit] at h

/-! ## A field body as a value under casts -/

theorem Tm.castList_of_isStable {s : Sig} :
    ∀ {t : Tm s}, t.isStable = true → ∃ v es, t.castList = some (v, es) ∧ v.isObjLit = true
  | .val v, h => ⟨v, [], rfl, Value.isObjLit_of_isStableLit h⟩
  | .cast t e, h => by
      simp only [Tm.isStable, Bool.and_eq_true] at h
      obtain ⟨v, es, hl, ho⟩ := Tm.castList_of_isStable (t := t) h.1
      exact ⟨v, es ++ [e], by simp [Tm.castList, hl], ho⟩
  | .atom _, h => by simp [Tm.isStable] at h
  | .app _ _, h => by simp [Tm.isStable] at h
  | .proj _ _ _, h => by simp [Tm.isStable] at h
  | .let _ _, h => by simp [Tm.isStable] at h

theorem Tm.castList_cast {s : Sig} {t : Tm s} {e : LeCo s} {v : Value s} {es : List (LeCo s)}
    (h : (Tm.cast t e).castList = some (v, es)) :
    ∃ es', t.castList = some (v, es') ∧ es = es' ++ [e] := by
  simp only [Tm.castList, Option.map_eq_some_iff] at h
  obtain ⟨⟨v', es'⟩, hl, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨es', hl, rfl⟩

/-- The child a body contributes is a forwarding, or the block of the literal
under its casts. -/
theorem Tm.childAt_cases {s : Sig} :
    ∀ {t : Tm s} {q : Path s} {B : Block s}, t.childAt q = some B →
      (∃ r, B = .fwd r) ∨
        ∃ v es, t.castList = some (v, es) ∧ v.isObjLit = true ∧ B = v.blockSelf.substPath q
  | .val v, q, B, h => by
      simp only [Tm.childAt] at h
      cases ho : v.isStableLit with
      | false => simp [ho] at h
      | true =>
          simp only [ho, if_true, Option.some.injEq] at h
          exact Or.inr ⟨v, [], rfl, Value.isObjLit_of_isStableLit ho, h.symm⟩
  | .atom a, q, B, h => by
      simp only [Tm.childAt, Option.some.injEq] at h
      exact Or.inl ⟨_, h.symm⟩
  | .cast t e, q, B, h => by
      simp only [Tm.childAt] at h
      split at h
      · cases h
      rcases Tm.childAt_cases h with hf | ⟨v, es, hl, ho, hB⟩
      · exact Or.inl hf
      · exact Or.inr ⟨v, es ++ [e], by simp [Tm.castList, hl], ho, hB⟩
  | .app _ _, _, _, h => by simp [Tm.childAt] at h
  | .proj _ _ _, _, _, h => by simp [Tm.childAt] at h
  | .let _ _, _, _, h => by simp [Tm.childAt] at h

theorem Tm.childAt_of_castList {s : Sig} :
    ∀ {t : Tm s} {v : Value s} {es : List (LeCo s)} (q : Path s),
      t.castList = some (v, es) → t.isStable = true →
        t.childAt q = some (v.blockSelf.substPath q)
  | .val v', v, es, q, h, ho => by
      simp only [Tm.castList, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Tm.isStable] at ho
      simp [Tm.childAt, ho]
  | .cast t e, v, es, q, h, ho => by
      obtain ⟨es', hl, _⟩ := Tm.castList_cast h
      simp only [Tm.isStable, Bool.and_eq_true] at ho
      simpa [Tm.childAt, ho.1, ho.2] using Tm.childAt_of_castList q hl ho.1
  | .atom _, _, _, _, h, _ => by simp [Tm.castList] at h
  | .app _ _, _, _, _, h, _ => by simp [Tm.castList] at h
  | .proj _ _ _, _, _, _, h, _ => by simp [Tm.castList] at h
  | .let _ _, _, _, _, h, _ => by simp [Tm.castList] at h

/-! ## Typed chains of casts

`CastsTyped Γ S es T`: the casts `es`, innermost first, lead from `S` to `T`,
each typed in `Γ`.  Their composite is a coercion `S ≤ T`. -/

def CastsTyped {s : Sig} (Γ : Ctx s) : Ty s → List (LeCo s) → Ty s → Prop
  | S, [], T => S = T
  | S, e :: es, T => ∃ M, Γ ⊢ e : S ≤ M ∧ CastsTyped Γ M es T

theorem CastsTyped.single {s : Sig} {Γ : Ctx s} {S T : Ty s} {e : LeCo s}
    (he : Γ ⊢ e : S ≤ T) : CastsTyped Γ S [e] T :=
  Exists.intro T ⟨he, rfl⟩

theorem CastsTyped.append {s : Sig} {Γ : Ctx s} :
    ∀ {S M T : Ty s} (l1 : List (LeCo s)) {l2 : List (LeCo s)},
      CastsTyped Γ S l1 M → CastsTyped Γ M l2 T → CastsTyped Γ S (l1 ++ l2) T
  | _, _, _, [], _, h1, h2 => by
      simp only [CastsTyped] at h1
      subst h1
      exact h2
  | _, _, _, e :: es, _, ⟨M', he, h1⟩, h2 => ⟨M', he, CastsTyped.append es h1 h2⟩

theorem CastsTyped.composite {s : Sig} {Γ : Ctx s} :
    ∀ (rest : List (LeCo s)) {e : LeCo s} {S M T : Ty s},
      Γ ⊢ e : S ≤ M → CastsTyped Γ M rest T → Γ ⊢ LeCo.composite e rest : S ≤ T
  | [], _, _, _, _, he, h => by
      simp only [CastsTyped] at h
      subst h
      exact he
  | f :: fs, _, _, _, _, he, ⟨M', hf, h⟩ => CastsTyped.composite fs (.trans he hf) h

/-- A typed value is its literal, typed, under typed casts. -/
theorem Value.HasType.castsTyped {s : Sig} {Γ : Ctx s} :
    ∀ {v : Value s} {T : Ty s}, Γ ⊢ᵥ v : T →
      ∃ S₀, Γ ⊢ᵥ v.core : S₀ ∧ CastsTyped Γ S₀ v.coercions T
  | .lam _ _, T, h => ⟨T, by simpa [Value.core] using h, rfl⟩
  | .obj _ _, T, h => ⟨T, by simpa [Value.core] using h, rfl⟩
  | .cast v e, T, h => by
      cases h with
      | cast hv he =>
          obtain ⟨S₀, hc, hcs⟩ := Value.HasType.castsTyped hv
          exact ⟨S₀, by simpa [Value.core] using hc,
            by simpa [Value.coercions] using CastsTyped.append _ hcs (CastsTyped.single he)⟩

/-- A typed field body that is a value under casts: the value is typed, and
the casts lead from its type to the body's. -/
theorem Tm.HasType.castsTyped {s : Sig} {Γ : Ctx s} :
    ∀ {t : Tm s} {T : Ty s} {v : Value s} {es : List (LeCo s)}, Γ ⊢ t : T →
      t.castList = some (v, es) → ∃ M, Γ ⊢ᵥ v : M ∧ CastsTyped Γ M es T
  | .val v', T, v, es, h, hl => by
      simp only [Tm.castList, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      cases h with
      | val hv => exact ⟨T, hv, rfl⟩
  | .cast t e, T, v, es, h, hl => by
      obtain ⟨es', hl', rfl⟩ := Tm.castList_cast hl
      cases h with
      | cast ht he =>
          obtain ⟨M, hv, hcs⟩ := Tm.HasType.castsTyped ht hl'
          exact ⟨M, hv, CastsTyped.append _ hcs (CastsTyped.single he)⟩
  | .atom _, _, _, _, _, hl => by simp [Tm.castList] at hl
  | .app _ _, _, _, _, _, hl => by simp [Tm.castList] at hl
  | .proj _ _ _, _, _, _, _, hl => by simp [Tm.castList] at hl
  | .let _ _, _, _, _, _, hl => by simp [Tm.castList] at hl

/-- The coercion of a typed field body whose type is not an object type: the
composite of its casts, from the literal's precise type. -/
theorem Tm.HasType.fieldCo {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} {v : Value s}
    {es : List (LeCo s)} {W : Witnesses (s,x)} {F : Fields (s,x)}
    (ht : Γ ⊢ t : T) (hl : t.castList = some (v, es)) (hco : v.coreObj? = some (W, F))
    (hT : ∀ Tel, T ≠ μ Tel) :
    ∃ E, t.fieldCo = some E ∧
      Γ ⊢ E : μ (Telescope.ofLiteral W F.labels F.valLabels) ≤ T := by
  obtain ⟨M, hv, hcs⟩ := Tm.HasType.castsTyped ht hl
  obtain ⟨S₀, hc, hcs'⟩ := Value.HasType.castsTyped hv
  rw [Value.core_of_coreObj? hco] at hc
  obtain ⟨rfl, -⟩ := Value.HasType.obj_inv hc
  have hall := CastsTyped.append _ hcs' hcs
  unfold Tm.fieldCo
  rw [hl]
  simp only
  cases hlist : v.coercions ++ es with
  | nil =>
      rw [hlist] at hall
      simp only [CastsTyped] at hall
      exact absurd hall.symm (hT _)
  | cons e rest =>
      rw [hlist] at hall
      obtain ⟨M', he, hrest⟩ := hall
      exact ⟨_, rfl, CastsTyped.composite rest he hrest⟩

/-! ## Stores: the literal at a variable, the walk at a variable -/

theorem Value.IsLiteral.rename' {s1 s2 : Sig} :
    ∀ {v : Value s1} (ρ : Rename s1 s2), v.IsLiteral → (v.rename ρ).IsLiteral
  | .lam _ _, _, _ => trivial
  | .obj _ _, _, _ => trivial
  | .cast _ _, _, h => h.elim

/-- Entries of a typed store are literals. -/
theorem Store.Typed.isLiteral_lookup {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ x : BVar s .var, (σ.lookup x).IsLiteral := by
  induction h with
  | nil => intro x; cases x
  | cons _ hl _ ih =>
      intro x
      cases x with
      | here => exact Value.IsLiteral.rename' _ hl
      | there y => exact Value.IsLiteral.rename' _ (ih y)

/-- A stored literal whose core is an object is that object. -/
theorem Store.Typed.lookup_coreObj {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ)
    (x : BVar s .var) {W : Witnesses (s,x)} {F : Fields (s,x)}
    (hco : (σ.lookup x).coreObj? = some (W, F)) : σ.lookup x = .obj W F := by
  have hlit := h.isLiteral_lookup x
  have hc := Value.core_of_coreObj? hco
  revert hlit hc
  cases σ.lookup x with
  | cast _ _ => intro hlit; exact hlit.elim
  | obj _ _ => intro _ hc; simpa [Value.core] using hc
  | lam _ _ => intro _ hc; simp [Value.core] at hc

/-- The node walk at a variable of a store context is the stored value's
block. -/
theorem Store.Typed.nodeBlock_var {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ)
    (x : BVar s .var) : Γ.nodeBlock (.var x) = some ((σ.lookup x).blocksAt (.var x)) := by
  show Γ.blockPass (fun _ => none) (.var x) = _
  obtain ⟨W, ls, vls, ch, hb⟩ := Value.blocksAt_obj (σ.lookup x) (.var x)
  simp only [Ctx.blockPass, h.blockAt x, hb]

/-- The identity closes the store context over itself. -/
theorem PSub.NodeTyped.id {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    PSub.NodeTyped Γ PSub.id Γ where
  var x := by
    rw [Ty.subst_psubId]
    exact .var
  node x B hB := by
    show Γ.nodeBlock (.var x) = _
    rw [PSub.id_paths, Block.subst_ofRename, Block.rename_id, h.nodeBlock_var x]
    rw [h.blockAt x] at hB
    exact hB

/-! ## The walk below a node -/

theorem Ctx.nodeBlock_sel_unfold {s : Sig} (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.nodeBlock (.sel p a) =
      (match Γ.nodeBlock p with
       | some (.obj _ _ _ ch) =>
           (match ch.at? a with
            | some (.fwd _) => none
            | b => b)
       | _ => none) := rfl

theorem Ctx.nodeTy_sel {s : Sig} (Γ : Ctx s) (p : Path s) (a : Label) :
    Γ.nodeTy (.sel p a) =
      (match Γ.nodeBlock (.sel p a) with
       | some (.obj W ls vls _) => .obj (Telescope.ofLiteral (W.rename Rename.succ) ls vls)
       | _ => .top) := rfl

/-- The literal at `p.a`, one step below the literal at `p`. -/
theorem Store.litAt_sel {s : Sig} {σ : Store s} {p : Path s} {a : Label} {s' : Sig}
    {v : Value s'} {τ : PSub s' s} {W : Witnesses (s',x)} {F : Fields (s',x)} {t : Tm (s',x)}
    {v' : Value (s',x)} {es : List (LeCo (s',x))}
    (hlit : σ.litAt p = some ⟨s', v, τ⟩) (hco : v.coreObj? = some (W, F))
    (hget : F.get? a = some t) (hcl : t.castList = some (v', es)) :
    σ.litAt (.sel p a) =
      some ⟨(s',x), v', τ.cons (PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels)⟩ := by
  simp [Store.litAt, hlit, hco, hget, hcl]

/-- The field coercion at `p.a` over the literal at `p`. -/
theorem Store.fieldCo_eq {s : Sig} {σ : Store s} {p : Path s} {a : Label} {s' : Sig}
    {v : Value s'} {τ : PSub s' s} {W : Witnesses (s',x)} {F : Fields (s',x)} {t : Tm (s',x)}
    {E : LeCo (s',x)}
    (hlit : σ.litAt p = some ⟨s', v, τ⟩) (hco : v.coreObj? = some (W, F))
    (hget : F.get? a = some t) (hfc : t.fieldCo = some E) :
    σ.fieldCo p a =
      some (E.psubst (τ.cons (PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels))) := by
  simp [Store.fieldCo, hlit, hco, hget, hfc]

/-- The node below a node: the child the literal's field writes, closed by
the literal's substitution extended by its self. -/
theorem Ctx.nodeBlock_sel_child {s1 s2 : Sig} {Γ : Ctx s2} {p : Path s2} {a : Label}
    {v : Value s1} {τ : PSub s1 s2} {W : Witnesses (s1,x)} {F : Fields (s1,x)} {t : Tm (s1,x)}
    {v' : Value (s1,x)} {es : List (LeCo (s1,x))} (P : PathCo s2) (hP : P.path = p)
    (hn : Γ.nodeBlock p = some ((v.blockSelf.subst τ.paths.lift).substPath p))
    (hco : v.coreObj? = some (W, F)) (hget : F.get? a = some t)
    (hcl : t.castList = some (v', es)) (ho : t.isStable = true) :
    Γ.nodeBlock (.sel p a) =
      some ((v'.blockSelf.subst (τ.cons P).paths.lift).substPath (.sel p a)) := by
  rw [Ctx.nodeBlock_sel_unfold, hn, Value.blockSelf_of_coreObj? hco]
  simp only [Block.subst, Block.substPath, Children.at?_subst, Fields.children_at?, hget,
    Option.bind_some, Tm.childAt_of_castList _ hcl ho, Option.map_some]
  obtain ⟨W', ls', vls', ch', hb⟩ := Value.blockSelf_obj v'
  have he := Block.child_subst_substPath v'.blockSelf τ P a
  rw [hP] at he
  simp only [Block.substPath] at he
  rw [← he, hb]
  rfl

/-! ## The literal at a node -/

/-- The core of the three invariants, by induction on the path.  At a node
`p` of a typed store's context, `Store.litAt` finds a literal `v` typed in a
context `Δ` that the substitution `τ` closes onto nodes of `Γ`, the self of
`v` is typed at its precise type by `PathCo.selfAt`, and the node is the
block of `v`, closed and instantiated at `p`. -/
theorem Store.Typed.litAt_node {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    ∀ (p : Path s) (B : Block s), Γ.nodeBlock p = some B →
      ∃ (s' : Sig) (v : Value s') (τ : PSub s' s) (Δ : Ctx s') (T : Ty s'),
        σ.litAt p = some ⟨s', v, τ⟩ ∧ Δ ⊢ᵥ v : T ∧ PSub.NodeTyped Δ τ Γ ∧
        (∀ W F, v.coreObj? = some (W, F) →
          Γ ⊢ᵖ PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels :
            μ (Telescope.ofLiteral (W.subst τ.paths.lift) F.labels F.valLabels)) ∧
        B = (v.blockSelf.subst τ.paths.lift).substPath p
  | .var x, B, hB => by
      refine ⟨s, σ.lookup x, PSub.id, Γ, Γ.lookupTy x, rfl, hσ.lookup x, PSub.NodeTyped.id hσ,
        ?_, ?_⟩
      · intro W F hco
        have hlk := hσ.lookup_coreObj x hco
        have hv := hσ.lookup x
        rw [hlk] at hv
        obtain ⟨hT, -⟩ := Value.HasType.obj_inv hv
        rw [Witnesses.subst_psubId_lift]
        show Γ ⊢ᵖ .var x : _
        rw [← hT]
        exact .var
      · rw [Block.subst_psubId_lift]
        rw [hσ.nodeBlock_var x] at hB
        exact (Option.some.inj hB).symm
  | .sel p a, B, hB => by
      have hB0 := hB
      rw [Ctx.nodeBlock_sel_unfold] at hB
      cases hp : Γ.nodeBlock p with
      | none => rw [hp] at hB; cases hB
      | some Bp =>
          rw [hp] at hB
          obtain ⟨s', v, τ, Δ, T, hlit, hv, hτ, hself, hBp⟩ := Store.Typed.litAt_node hσ p Bp hp
          have hn : Γ.nodeBlock p = some ((v.blockSelf.subst τ.paths.lift).substPath p) := by
            rw [hp, hBp]
          cases hco : v.coreObj? with
          | none =>
              rw [Value.blockSelf_of_coreObj?_none hco] at hBp
              subst hBp
              simp [Block.subst, Block.substPath, Children.subst, Children.at?] at hB
          | some WF =>
              obtain ⟨W, F⟩ := WF
              have hBp' := hBp
              rw [Value.blockSelf_of_coreObj? hco] at hBp'
              subst hBp'
              simp only [Block.subst, Block.substPath, Children.at?_subst,
                Fields.children_at?] at hB
              cases hget : F.get? a with
              | none => simp [hget] at hB
              | some t =>
                  simp only [hget, Option.bind_some] at hB
                  cases hch : t.childAt (.sel (.var .here) a) with
                  | none => simp [hch] at hB
                  | some B₀ =>
                      rcases Tm.childAt_cases hch with ⟨r, rfl⟩ | ⟨v', es, hcl, ho, hB₀⟩
                      · simp [hch, Block.subst] at hB
                      · -- the literal at `p.a` and its context
                        have hst : t.isStable = true := by
                          obtain ⟨W', ls', vls', ch', hb⟩ := Value.blockSelf_obj v'
                          exact (Tm.isStable_iff_childAt_obj t _).2
                            ⟨_, _, _, _, by rw [hch, hB₀, hb]; rfl⟩
                        let P := PathCo.selfAt p (W.subst τ.paths.lift) F.labels F.valLabels
                        have hPp : P.path = p := PathCo.selfAt_path _ _ _ _
                        have hchild := Ctx.nodeBlock_sel_child P hPp hn hco hget hcl hst
                        rw [hchild] at hB0
                        obtain rfl := Option.some.inj hB0
                        have hcore := Value.HasType.castsTyped hv
                        obtain ⟨S₀, hc, -⟩ := hcore
                        rw [Value.core_of_coreObj? hco] at hc
                        obtain ⟨-, hF⟩ := Value.HasType.obj_inv hc
                        have ht := Fields.HasType.get F hF a t hget
                        obtain ⟨M, hv', -⟩ := Tm.HasType.castsTyped ht hcl
                        refine ⟨(s',x), v', τ.cons P, _, M, Store.litAt_sel hlit hco hget hcl,
                          hv', ?_, ?_, rfl⟩
                        · refine hτ.cons ?_ ?_
                          · have := hself W F hco
                            simpa [Ty.subst, Telescope.ofLiteral_subst] using this
                          · rw [hPp, ← Block.subst_lift_substPath, hPp, hp, hBp,
                              Value.blockSelf_of_coreObj? hco]
                        · intro W' F' hco'
                          show Γ ⊢ᵖ .node (.sel p a) _ _ _ : _
                          apply PathCo.HasType.node rfl
                          rw [hchild, Value.blockSelf_of_coreObj? hco']
                          rfl

/-! ## Invariant A at nodes -/

/-- **Invariant A at nodes.**  Over a typed store the block the table writes
at a node is the block the store gives the path.  `Store.blockOf` and the node
walk step through the same object children, and they differ only at a
forwarding child, which `Store.blockOf` follows and the node walk never
meets. -/
theorem Store.Typed.blockOf_node {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) :
    ∀ {p : Path s} {B : Block s}, Γ.nodeBlock p = some B → σ.blockOf p = some B
  | .var x, B, h => by
      rw [hσ.nodeBlock_var x] at h
      exact h
  | .sel p a, B, h => by
      rw [Ctx.nodeBlock_sel_unfold] at h
      cases hp : Γ.nodeBlock p with
      | none => rw [hp] at h; cases h
      | some Bp =>
          rw [hp] at h
          have ih := Store.Typed.blockOf_node hσ hp
          cases Bp with
          | fwd q => cases h
          | obj W ls vls ch =>
              simp only [Store.blockOf, ih]
              simp only at h
              cases hc : ch.at? a with
              | none => rw [hc] at h; cases h
              | some B₁ =>
                  cases B₁ with
                  | fwd q => rw [hc] at h; cases h
                  | obj W' ls' vls' ch' => rw [hc] at h; exact h

/-! ## Invariant B at nodes -/

/-- **Invariant B at nodes.**  Below a node `p`, the child at a stable label
`a` is a node, and it is the block of the object literal in the field `a` of
the literal at `p`: the literal `Store.litAt` finds at `p.a`, closed by its
substitution and instantiated at `p.a`. -/
theorem Store.Typed.nodeBlock_child {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    {p : Path s} {a : Label} {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    (hp : Γ.nodeBlock p = some (.obj W ls vls ch)) (ha : a ∈ vls) :
    ∃ (s' : Sig) (v : Value s') (τ : PSub s' s),
      σ.litAt (.sel p a) = some ⟨s', v, τ⟩ ∧ v.isObjLit = true ∧
      Γ.nodeBlock (.sel p a) = some ((v.blockSelf.subst τ.paths.lift).substPath (.sel p a)) := by
  obtain ⟨s', v, τ, Δ, T, hlit, hv, hτ, hself, hBp⟩ := hσ.litAt_node p _ hp
  have hn : Γ.nodeBlock p = some ((v.blockSelf.subst τ.paths.lift).substPath p) := by
    rw [hp, hBp]
  cases hco : v.coreObj? with
  | none =>
      rw [Value.blockSelf_of_coreObj?_none hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, -⟩ := hBp
      simp at ha
  | some WF =>
      obtain ⟨W₀, F⟩ := WF
      rw [Value.blockSelf_of_coreObj? hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, -⟩ := hBp
      obtain ⟨t, hget, hst⟩ := (Fields.mem_valLabels_iff_get? F a).1 ha
      obtain ⟨v', es, hcl, ho⟩ := Tm.castList_of_isStable hst
      let P := PathCo.selfAt p (W₀.subst τ.paths.lift) F.labels F.valLabels
      exact ⟨(s',x), v', τ.cons P, Store.litAt_sel hlit hco hget hcl, ho,
        Ctx.nodeBlock_sel_child P (PathCo.selfAt_path _ _ _ _) hn hco hget hcl hst⟩

/-- The converse reading: a node below a node `p` sits at a stable label of
`p`'s block. -/
theorem Store.Typed.mem_valLabels_of_nodeBlock_sel {s : Sig} {Γ : Ctx s}
    {p : Path s} {a : Label} {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    {σ : Store s} (hσ : ⊢ σ : Γ) {B : Block s}
    (hp : Γ.nodeBlock p = some (.obj W ls vls ch)) (hB : Γ.nodeBlock (.sel p a) = some B) :
    a ∈ vls := by
  obtain ⟨s', v, τ, Δ, T, hlit, hv, hτ, hself, hBp⟩ := hσ.litAt_node p _ hp
  rw [Ctx.nodeBlock_sel_unfold, hp] at hB
  simp only at hB
  cases hco : v.coreObj? with
  | none =>
      rw [Value.blockSelf_of_coreObj?_none hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, -, rfl⟩ := hBp
      simp [Children.subst, Children.at?] at hB
  | some WF =>
      obtain ⟨W₀, F⟩ := WF
      rw [Value.blockSelf_of_coreObj? hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, rfl⟩ := hBp
      simp only [Children.at?_subst] at hB
      cases hc : (F.children (.var .here)).at? a with
      | none => simp [hc] at hB
      | some B₀ =>
          cases B₀ with
          | fwd r => simp [hc, Block.subst] at hB
          | obj W' ls' vls' ch' => exact Fields.mem_valLabels_of_at? hc

/-! ## Invariant C, the field coercion -/

/-- Witness entries read only the labels of the list they run over. -/
theorem Witnesses.eqEntriesOf_subst_right {s : Sig} (self : BVar s .var) (W₀ : Witnesses s)
    (π : PathSubst s s) :
    ∀ W : Witnesses s, W₀.eqEntriesOf self (W.subst π) = W₀.eqEntriesOf self W
  | .nil => rfl
  | .cons W ℓ T => by
      simp only [Witnesses.subst, Witnesses.eqEntriesOf,
        Witnesses.eqEntriesOf_subst_right self W₀ π W]

/-- Witness entries, substituted, read the definitions only through the
substitution. -/
theorem Witnesses.eqEntriesOf_subst_congr {s s' : Sig} (W₀ W₀' : Witnesses (s,x))
    (π : PathSubst (s,x) s') (h : ∀ ℓ, (W₀.get ℓ).subst π = (W₀'.get ℓ).subst π) :
    ∀ W : Witnesses (s,x),
      (W₀.eqEntriesOf .here W).subst π = (W₀'.eqEntriesOf .here W).subst π
  | .nil => rfl
  | .cons W ℓ T => by
      simp only [Witnesses.eqEntriesOf, Telescope.subst, Proposition.subst,
        Witnesses.eqEntriesOf_subst_congr W₀ W₀' π h W, h ℓ]

/-- The precise type of a literal and the node type at its path open to one
telescope at that path: the node's witnesses are the literal's, instantiated
at the path and weakened. -/
theorem Ctx.resolveAt_ofLiteral {s : Sig} (Γ : Ctx s) (r : Path s) (W : Witnesses (s,x))
    (ls vls : List Label) :
    Γ.resolveAt r (μ (Telescope.ofLiteral W ls vls))
      = Γ.resolveAt r (μ (Telescope.ofLiteral ((W.substPath r).rename Rename.succ) ls vls)) := by
  have hW : (W.substPath r).rename (Rename.succ (k := .var))
      = W.subst ((PathSubst.one r).compRename Rename.succ) := by
    rw [Witnesses.substPath, Witnesses.subst_rename]
  have hE : W.eqEntries.subst (PathSubst.one r)
      = ((W.substPath r).rename (Rename.succ (k := .var))).eqEntries.subst (PathSubst.one r) := by
    unfold Witnesses.eqEntries
    rw [hW, Witnesses.eqEntriesOf_subst_right]
    apply Witnesses.eqEntriesOf_subst_congr
    intro ℓ
    rw [← hW, Witnesses.get_rename, Witnesses.substPath, Witnesses.get_subst]
    exact (Ty.weaken_substPath _ r).symm
  have key : (Telescope.ofLiteral W ls vls).substPath r
      = (Telescope.ofLiteral ((W.substPath r).rename Rename.succ) ls vls).substPath r := by
    unfold Telescope.ofLiteral Telescope.substPath
    rw [Telescope.hasValEntries_subst, Telescope.hasValEntries_subst, Telescope.hasEntries_subst,
      Telescope.hasEntries_subst, hE]
  simp only [Ctx.resolveAt, Ctx.resolve_obj, Ty.unfoldAt_obj, key]

/-- **Invariant C.**  Over a typed store the coercion of a stable field `a` of
a node `p` is read off the store and typed from the child's precise type to
the parent's name `p ∙ a`.  The source is stated up to the opening at the
child, since the substituted precise type names its self where
`Γ.nodeTy` names the child's path.  The premise is the node at `p`, which is
what T1's `sel` case has by `root_node`.  With `σ.HasValFieldP p a` in its
place the statement is false (`invC_false`, `Plan:667`). -/
theorem Store.Typed.fieldCo {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) {p : Path s}
    {a : Label} {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    (hp : Γ.nodeBlock p = some (.obj W ls vls ch)) (ha : a ∈ vls) :
    ∃ E S, σ.fieldCo p a = some E ∧ Γ ⊢ E : S ≤ Ty.sel p a ∧
      Γ.resolveAt (.sel p a) S = Γ.resolveAt (.sel p a) (Γ.nodeTy (.sel p a)) := by
  obtain ⟨s', v, τ, Δ, T, hlit, hv, hτ, hself, hBp⟩ := hσ.litAt_node p _ hp
  have hn : Γ.nodeBlock p = some ((v.blockSelf.subst τ.paths.lift).substPath p) := by
    rw [hp, hBp]
  cases hco : v.coreObj? with
  | none =>
      rw [Value.blockSelf_of_coreObj?_none hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, -⟩ := hBp
      simp at ha
  | some WF =>
      obtain ⟨W₀, F⟩ := WF
      have hBp' := hBp
      rw [Value.blockSelf_of_coreObj? hco] at hBp'
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp'
      obtain ⟨-, -, rfl, -⟩ := hBp'
      obtain ⟨t, hget, hst⟩ := (Fields.mem_valLabels_iff_get? F a).1 ha
      obtain ⟨v', es, hcl, ho⟩ := Tm.castList_of_isStable hst
      obtain ⟨W', F', hco'⟩ := Value.coreObj?_of_isObjLit ho
      -- the field body, typed under the literal's self
      obtain ⟨S₀, hc, -⟩ := Value.HasType.castsTyped hv
      rw [Value.core_of_coreObj? hco] at hc
      obtain ⟨-, hF⟩ := Value.HasType.obj_inv hc
      have ht := Fields.HasType.get F hF a t hget
      obtain ⟨E₀, hfc, hE₀⟩ := Tm.HasType.fieldCo ht hcl hco' (by intro Tel h; cases h)
      -- the substitution closing the selves
      let P := PathCo.selfAt p (W₀.subst τ.paths.lift) F.labels F.valLabels
      have hPp : P.path = p := PathCo.selfAt_path _ _ _ _
      have hτ' : PSub.NodeTyped
          (Δ.cons (.transparent (μ (Telescope.ofLiteral W₀ F.labels F.valLabels))
            (.obj W₀ F.labels F.valLabels (F.children (.var .here))))) (τ.cons P) Γ := by
        refine hτ.cons ?_ ?_
        · have := hself W₀ F hco
          simpa [Ty.subst, Telescope.ofLiteral_subst] using this
        · rw [hPp, ← Block.subst_lift_substPath, hPp, hn, Value.blockSelf_of_coreObj? hco]
      have hE := LeCo.HasType.psubst hτ'.typed hE₀
      have hchild := Ctx.nodeBlock_sel_child P hPp hn hco hget hcl hst
      refine ⟨E₀.psubst (τ.cons P),
        μ (Telescope.ofLiteral (W'.subst (τ.cons P).paths.lift) F'.labels F'.valLabels),
        Store.fieldCo_eq hlit hco hget hfc, ?_, ?_⟩
      · have htgt : (Ty.sel (Path.var .here) a).subst (τ.cons P).paths = Ty.sel p a := by
          show Ty.sel P.path a = Ty.sel p a
          rw [hPp]
        rw [htgt] at hE
        simpa [Ty.subst, Telescope.ofLiteral_subst] using hE
      · rw [Ctx.nodeTy_sel, hchild, Value.blockSelf_of_coreObj? hco']
        exact Ctx.resolveAt_ofLiteral Γ _ _ _ _


/-! ## The field coercion is table-only

The chosen repair of the field forms (design-fieldforms.md): a stable body's
casts eliminate nowhere, so the coercion `Store.fieldCo` reads off a stable
field of a node is table-only, and its normal form reads no view. -/

mutual
theorem LeCo.tableOnly_psubst : ∀ (e : LeCo s1) (σ : PSub s1 s2),
    (e.psubst σ).tableOnly = e.tableOnly
  | .refl _, _ => rfl
  | .trans e f, σ => by
      simp [LeCo.psubst, LeCo.tableOnly, LeCo.tableOnly_psubst e σ, LeCo.tableOnly_psubst f σ]
  | .top _, _ => rfl
  | .bot _, _ => rfl
  | .eqToLe φ, σ => by simp [LeCo.psubst, LeCo.tableOnly, EqCo.tableOnly_psubst φ σ]
  | .pi _ _, _ => rfl
  | .obj _ m, σ => by simp [LeCo.psubst, LeCo.tableOnly, Morphism.tableOnly_psubst m σ]
  | .pair _ _ e f, σ => by
      simp [LeCo.psubst, LeCo.tableOnly, LeCo.tableOnly_psubst e σ, LeCo.tableOnly_psubst f σ]
  | .bound _ _, _ => rfl
  | .intoBnd e, σ => by simp [LeCo.psubst, LeCo.tableOnly, LeCo.tableOnly_psubst e σ]
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem EqCo.tableOnly_psubst : ∀ (φ : EqCo s1) (σ : PSub s1 s2),
    (φ.psubst σ).tableOnly = φ.tableOnly
  | .refl _, _ => rfl
  | .symm φ, σ => by simp [EqCo.psubst, EqCo.tableOnly, EqCo.tableOnly_psubst φ σ]
  | .trans φ ψ, σ => by
      simp [EqCo.psubst, EqCo.tableOnly, EqCo.tableOnly_psubst φ σ, EqCo.tableOnly_psubst ψ σ]
  | .def _ _, _ => rfl
  | .defP _ _, _ => rfl
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem Side.tableOnly_psubst : ∀ (p : Side s1) (σ : PSub s1 s2),
    (p.psubst σ).tableOnly = p.tableOnly
  | .none, _ => rfl
  | .some e, σ => by simp [Side.psubst, Side.tableOnly, LeCo.tableOnly_psubst e σ]
  | .bot _, _ => rfl
  | .top _, _ => rfl

theorem Morphism.tableOnly_psubst : ∀ (m : Morphism s1) (σ : PSub s1 s2),
    (m.psubst σ).tableOnly = m.tableOnly
  | .nil, _ => rfl
  | .le m pre _ post, σ => by
      simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ,
        Side.tableOnly_psubst pre σ, Side.tableOnly_psubst post σ]
  | .eq m _ _, σ => by simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ]
  | .has m _, σ => by simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ]
  | .bnd m e, σ => by
      simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ,
        LeCo.tableOnly_psubst e σ]
  | .hasVal m _, σ => by
      simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ]
  | .hasOfVal m _, σ => by
      simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ]
  | .aliasCopy m _, σ => by
      simp [Morphism.psubst, Morphism.tableOnly, Morphism.tableOnly_psubst m σ]
end

theorem LeCo.composite_tableOnly :
    ∀ (e : LeCo s) (es : List (LeCo s)),
      (LeCo.composite e es).tableOnly = (e.tableOnly && es.all LeCo.tableOnly)
  | e, [] => by simp [LeCo.composite]
  | e, f :: fs => by
      simp [LeCo.composite, LeCo.composite_tableOnly (.trans e f) fs, LeCo.tableOnly,
        Bool.and_assoc]

theorem Value.coercions_tableOnly :
    ∀ (v : Value s), v.isStableLit = true → v.coercions.all LeCo.tableOnly = true
  | .obj _ _, _ => by simp [Value.coercions]
  | .lam _ _, h => by simp [Value.isStableLit] at h
  | .cast v e, h => by
      simp only [Value.isStableLit, Bool.and_eq_true] at h
      have := Value.coercions_tableOnly v h.1
      simp_all [Value.coercions]

theorem Tm.castList_tableOnly :
    ∀ {t : Tm s} {v : Value s} {es : List (LeCo s)}, t.isStable = true →
      t.castList = some (v, es) → v.isStableLit = true ∧ es.all LeCo.tableOnly = true
  | .val v', _, _, h, hc => by
      simp only [Tm.castList, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨h, rfl⟩
  | .cast t e, v, es, h, hc => by
      simp only [Tm.isStable, Bool.and_eq_true] at h
      cases hl : t.castList with
      | none => simp [Tm.castList, hl] at hc
      | some ve =>
          obtain ⟨v', es'⟩ := ve
          simp only [Tm.castList, hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨h1, h2⟩ := Tm.castList_tableOnly h.1 hl
          exact ⟨h1, by simp_all⟩
  | .atom _, _, _, h, _ => by simp [Tm.isStable] at h
  | .app _ _, _, _, h, _ => by simp [Tm.isStable] at h
  | .proj _ _ _, _, _, h, _ => by simp [Tm.isStable] at h
  | .let _ _, _, _, h, _ => by simp [Tm.isStable] at h

/-- The coercion `Store.fieldCo` composes out of a stable body is table-only. -/
theorem Tm.fieldCo_tableOnly {t : Tm s} {E : LeCo s} (hs : t.isStable = true)
    (h : t.fieldCo = some E) : E.tableOnly = true := by
  unfold Tm.fieldCo at h
  cases hl : t.castList with
  | none => rw [hl] at h; cases h
  | some ve =>
      obtain ⟨v, es⟩ := ve
      rw [hl] at h
      obtain ⟨hv, hes⟩ := Tm.castList_tableOnly hs hl
      have hvc := Value.coercions_tableOnly v hv
      cases hcs : v.coercions ++ es with
      | nil => simp [hcs] at h
      | cons e rest =>
          simp only [hcs, Option.some.injEq] at h
          subst h
          have hall : (v.coercions ++ es).all LeCo.tableOnly = true := by
            simp only [List.all_append, hvc, hes, Bool.and_self]
          rw [hcs] at hall
          simp only [List.all_cons, Bool.and_eq_true] at hall
          rw [LeCo.composite_tableOnly]
          simp [hall.1, hall.2]


/-- **The coercion of a stable field of a node is table-only.**  Syntactic:
the body is stable, so its casts are table-only, and the path substitution
sends `def` to `defP` and nothing to an elimination. -/
theorem Store.Typed.fieldCo_tableOnly {s : Sig} {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ)
    {p : Path s} {a : Label} {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    (hp : Γ.nodeBlock p = some (.obj W ls vls ch)) (ha : a ∈ vls) {E : LeCo s}
    (hE : σ.fieldCo p a = some E) : E.tableOnly = true := by
  obtain ⟨s', v, τ, Δ, T, hlit, -, -, -, hBp⟩ := hσ.litAt_node p _ hp
  cases hco : v.coreObj? with
  | none =>
      rw [Value.blockSelf_of_coreObj?_none hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, -⟩ := hBp
      simp at ha
  | some WF =>
      obtain ⟨W₀, F⟩ := WF
      rw [Value.blockSelf_of_coreObj? hco] at hBp
      simp only [Block.subst, Block.substPath, Block.obj.injEq] at hBp
      obtain ⟨-, -, rfl, -⟩ := hBp
      obtain ⟨t, hget, hst⟩ := (Fields.mem_valLabels_iff_get? F a).1 ha
      cases hfc : t.fieldCo with
      | none =>
          simp [Store.fieldCo, hlit, hco, hget, hfc] at hE
      | some E₀ =>
          rw [Store.fieldCo_eq hlit hco hget hfc] at hE
          obtain rfl := Option.some.inj hE
          rw [LeCo.tableOnly_psubst]
          exact Tm.fieldCo_tableOnly hst hfc

end FCdot

end Paths
