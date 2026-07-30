import LambdaP.Context

/-!
The judgments of λ_p, mechanizing the *pure subtyping* variant of the paper
draft (Figure `pdt-pure-subtype-rules`) — see DESIGN.md for why the
path-typing variant is not the primary system.

Judgments are parameterized by a store typing `Θ` (for heap locations) and a
context `Γ` (for bound variables). Subtyping relates *generalized types*
(`Tau`): proper types or intervals `S..T`; the only rules mixing the two are
the type-member selection rules (`p.A <: S..T`), exactly as in the paper.

Deliberate deviations (documented in DESIGN.md):
- no `sel-l` label-skipping rules yet (the draft's rule has a scoping bug;
  a fixed "selection skip" form can be added later),
- the `typed` rule ascribes the term from its premise (draft has a typo).
-/

namespace LambdaP

/-- A generalized type: a proper type or a type interval `S..T`.
Used only in judgments, never in the syntax of types. -/
inductive Tau : Sig -> Type where
| ty : Ty s -> Tau s
| intv : Ty s -> Ty s -> Tau s

def Tau.rename : Tau s1 -> Rename s1 s2 -> Tau s2
| .ty T, f => .ty (T.rename f)
| .intv S T, f => .intv (S.rename f) (T.rename f)

def Tau.subst : Tau s1 -> Subst s1 s2 -> Tau s2
| .ty T, σ => .ty (T.subst σ)
| .intv S T, σ => .intv (S.subst σ) (T.subst σ)

def Tau.weaken (τ : Tau s) : Tau (s+1) := τ.rename Rename.succ

def Tau.open (τ : Tau (s+1)) (p : Path s) : Tau s := τ.subst (Subst.openPath p)

theorem Tau.rename_id {τ : Tau s} : τ.rename Rename.id = τ := by
  cases τ <;> simp [Tau.rename, Ty.rename_id]

theorem Tau.rename_comp {τ : Tau s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (τ.rename f).rename g = τ.rename (f.comp g) := by
  cases τ <;> simp [Tau.rename, Ty.rename_comp]

theorem Tau.subst_id {τ : Tau s} : τ.subst Subst.id = τ := by
  cases τ <;> simp [Tau.subst, Ty.subst_id]

theorem Tau.subst_rename_comm {τ : Tau s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
    (τ.subst σ).rename f = τ.subst (σ.compRename f) := by
  cases τ <;> simp [Tau.subst, Tau.rename, Ty.subst_rename_comm]

theorem Tau.rename_subst_comm {τ : Tau s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
    (τ.rename f).subst σ = τ.subst (f.compSubst σ) := by
  cases τ <;> simp [Tau.subst, Tau.rename, Ty.rename_subst_comm]

theorem Tau.subst_comp {τ : Tau s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
    (τ.subst σ1).subst σ2 = τ.subst (σ1.comp σ2) := by
  cases τ <;> simp [Tau.subst, Ty.subst_comp]

theorem Tau.open_rename_comm {τ : Tau (s1+1)} {p : Path s1} {f : Rename s1 s2} :
    (τ.rename f.lift).open (p.rename f) = (τ.open p).rename f := by
  simp [Tau.open, Tau.rename_subst_comm, Tau.subst_rename_comm, Subst.openPath_rename_comm]

theorem Tau.open_subst_comm {τ : Tau (s1+1)} {p : Path s1} {σ : Subst s1 s2} :
    (τ.subst σ.lift).open (p.subst σ) = (τ.open p).subst σ := by
  simp [Tau.open, Tau.subst_comp, Subst.openPath_subst_comm]

/-! ### Store-side path resolution

`Chains Θ p m`: the path `p` resolves through the store typing to the
location `m`, reading component locations off the precise entries
(the `Θ`-side mirror of big-step path evaluation, scope-generic since
location-rooted paths contain no bound variables). Selections skip
mismatched outer members into the first component (records as nested
pairs). -/
inductive Chains (Θ : Sto) : Path s -> Nat -> Prop where
| loc :
  Sto.Lookup Θ ℓ T ->
  Chains Θ (.var (.free ℓ)) ℓ
| fst_tm :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm (.single (.var (.free ℓ1))) a Tc) ->
  Chains Θ p.fst ℓ1
| fst_ty :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTy (.single (.var (.free ℓ1))) A T1 T2) ->
  Chains Θ p.fst ℓ1
| sel :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm S a (Ty.single (.var (.free ℓ2))).weaken) ->
  Chains Θ (p.sel a) ℓ2
| sel_skip_tm :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm S b Tc) ->
  a ≠ b ->
  Chains Θ ((Path.fst p).sel a) m ->
  Chains Θ (p.sel a) m
| sel_skip_ty :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTy S B T1 T2) ->
  Chains Θ ((Path.fst p).sel a) m ->
  Chains Θ (p.sel a) m

/-- Store-side resolution is monotone under store-typing extension. -/
theorem Chains.sto_weaken {Θ Θ' : Sto} {p : Path s} {m : Nat}
    (h : Chains Θ p m) (hext : Θ'.Extends Θ) : Chains Θ' p m := by
  induction h with
  | loc hl => exact .loc (hext hl)
  | fst_tm _ hl ih => exact .fst_tm ih (hext hl)
  | fst_ty _ hl ih => exact .fst_ty ih (hext hl)
  | sel _ hl ih => exact .sel ih (hext hl)
  | sel_skip_tm _ hl hne _ ih ihs => exact .sel_skip_tm ih (hext hl) hne ihs
  | sel_skip_ty _ hl _ ih ihs => exact .sel_skip_ty ih (hext hl) ihs

/-- Store-side resolution only touches locations, so it is invariant
under substitution. -/
theorem Chains.subst {Θ : Sto} {p : Path s1} {m : Nat}
    (h : Chains Θ p m) {σ : Subst s1 s2} : Chains Θ (p.subst σ) m := by
  induction h with
  | loc hl => exact .loc hl
  | fst_tm _ hl ih => exact .fst_tm ih hl
  | fst_ty _ hl ih => exact .fst_ty ih hl
  | sel _ hl ih => exact .sel ih hl
  | sel_skip_tm _ hl hne _ ih ihs => exact .sel_skip_tm ih hl hne ihs
  | sel_skip_ty _ hl _ ih ihs => exact .sel_skip_ty ih hl ihs

/-- Store-side resolution only touches locations, so it is invariant
under renaming. -/
theorem Chains.rename {Θ : Sto} {p : Path s1} {m : Nat}
    (h : Chains Θ p m) {f : Rename s1 s2} : Chains Θ (p.rename f) m := by
  induction h with
  | loc hl => exact .loc hl
  | fst_tm _ hl ih => exact .fst_tm ih hl
  | fst_ty _ hl ih => exact .fst_ty ih hl
  | sel _ hl ih => exact .sel ih hl
  | sel_skip_tm _ hl hne _ ih ihs => exact .sel_skip_tm ih hl hne ihs
  | sel_skip_ty _ hl _ ih ihs => exact .sel_skip_ty ih hl ihs

/-- Store-side resolution is deterministic. -/
theorem Chains.deterministic {Θ : Sto} {p : Path s} {ℓ1 ℓ2 : Nat}
    (h1 : Chains Θ p ℓ1) (h2 : Chains Θ p ℓ2) : ℓ1 = ℓ2 := by
  induction h1 generalizing ℓ2 with
  | loc _ => cases h2 with | loc _ => rfl
  | fst_tm h1 hl1 ih =>
    cases h2 with
    | fst_tm h2 hl2 =>
      cases ih h2
      have := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      cases this
      rfl
    | fst_ty h2 hl2 =>
      cases ih h2
      have := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      cases this
  | fst_ty h1 hl1 ih =>
    cases h2 with
    | fst_tm h2 hl2 =>
      cases ih h2
      have := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      cases this
    | fst_ty h2 hl2 =>
      cases ih h2
      have := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      cases this
      rfl
  | sel h1 hl1 ih =>
    cases h2 with
    | sel h2 hl2 =>
      cases ih h2
      have := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      cases this
      rfl
    | sel_skip_tm h2 hl2 hne2 _ =>
      cases ih h2
      have heq := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      injection heq with hs h1e h2e h3e
      exact absurd h2e hne2
    | sel_skip_ty h2 hl2 _ =>
      cases ih h2
      cases Option.some_inj.mp ((Eq.symm hl1).trans hl2)
  | sel_skip_tm h1 hl1 hne1 _ ihp ihin =>
    cases h2 with
    | sel h2 hl2 =>
      cases ihp h2
      have heq := Option.some_inj.mp ((Eq.symm hl1).trans hl2)
      injection heq with hs h1e h2e h3e
      exact absurd h2e.symm hne1
    | sel_skip_tm h2 hl2 hne2 hin2 => exact ihin hin2
    | sel_skip_ty h2 hl2 hin2 =>
      cases ihp h2
      cases Option.some_inj.mp ((Eq.symm hl1).trans hl2)
  | sel_skip_ty h1 hl1 _ ihp ihin =>
    cases h2 with
    | sel h2 hl2 =>
      cases ihp h2
      cases Option.some_inj.mp ((Eq.symm hl1).trans hl2)
    | sel_skip_tm h2 hl2 hne2 hin2 =>
      cases ihp h2
      cases Option.some_inj.mp ((Eq.symm hl1).trans hl2)
    | sel_skip_ty h2 hl2 hin2 => exact ihin hin2

/-! ### Subtyping and path wellformedness (mutual)

`sel_lo` introduces a type selection on the right out of nothing, so it
carries a `Path.Wf` premise: a member of `p` may only be reflected when
`p` is a wellformed path. (The draft's path-typing variant demands the
same implicitly — `p.A :: I` requires `p` typed. Without the premise, a
vacuous selection through a stuck path can be introduced below a type
with inhabitants, which breaks the semantic subtyping lemma; see
DESIGN.md, inversion architecture.) This makes `Sub` and `Path.Wf`
mutually inductive. -/

mutual

/-- Pure subtyping on generalized types, `Θ; Γ ⊢ τ1 <: τ2`. -/
inductive Sub : Sto -> Ctx s -> Tau s -> Tau s -> Prop where
/-- τ <: τ -/
| refl :
  Sub Θ Γ τ τ
/-- Transitivity. -/
| trans :
  Sub Θ Γ τ1 τ2 ->
  Sub Θ Γ τ2 τ3 ->
  Sub Θ Γ τ1 τ3
/-- ⊥ <: T -/
| bot :
  Sub Θ Γ (.ty .bot) (.ty T)
/-- T <: ⊤ -/
| top :
  Sub Θ Γ (.ty T) (.ty .top)
/-- A bound variable is a subtype of its declared type. -/
| var_bound :
  Ctx.LookupVar Γ x T ->
  Sub Θ Γ (.ty (.single (.var (.bound x)))) (.ty T)
/-- A heap location is a subtype of its recorded type. -/
| var_free :
  Sto.Lookup Θ ℓ T ->
  Sub Θ Γ (.ty (.single (.var (.free ℓ)))) (.ty T.fromClosed)
/-- Singleton subtyping is symmetric: paths that alias are mutual
subtypes. Aliasing presupposes that the path denotes, hence the
wellformedness premise (like `sel_lo`). -/
| symm :
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.single q)) ->
  Sub Θ Γ (.ty (.single q)) (.ty (.single p))
/-- First projection, term-member pair. -/
| fst_tm :
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) ->
  Sub Θ Γ (.ty (.single p.fst)) (.ty S)
/-- First projection, type-member pair. -/
| fst_ty :
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) ->
  Sub Θ Γ (.ty (.single p.fst)) (.ty S)
/-- Term-member selection: p.a is below the declared member type. -/
| sel_tm :
  p.root.IsBound ->
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (T.open p.fst))
/-- Store-anchored term-member selection for location-rooted paths
(deviation 10): the stored component is a location, so the selection
is an exact alias of it. -/
| sel_tm_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTm S a (Ty.single (.var (.free ℓ2))).weaken) ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single (.var (.free ℓ2))))
/-- A type selection is below the (opened) declared upper bound of *its own*
member. The pair-type premise anchors the bounds to the member being
selected (DOT's SEL-<:); the draft's unanchored formulation is unsound —
see DESIGN.md, deviation 7. The second premise is the draft's non-empty
interval guard. -/
| sel_hi :
  p.root.IsBound ->
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) ->
  Sub Θ Γ (.ty (T1.open p.fst)) (.ty (T2.open p.fst)) ->
  Sub Θ Γ (.ty (.tsel p A)) (.ty (T2.open p.fst))
/-- A type selection is above the (opened) declared lower bound of its own
member (DOT's <:-Sel), with the same anchoring and non-emptiness guard,
plus wellformedness of the selected path (see the mutual-block comment). -/
| sel_lo :
  p.root.IsBound ->
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) ->
  Sub Θ Γ (.ty (T1.open p.fst)) (.ty (T2.open p.fst)) ->
  Sub Θ Γ (.ty (T1.open p.fst)) (.ty (.tsel p A))
/-- Store-anchored selection bounds for location-rooted paths
(deviation 9, minidot's strong selection): at runtime the path resolves
through the precise store to its member's stored alias interval. The
evidence-shaped `sel_hi`/`sel_lo` above are scoped to bound-var-rooted
paths, so at the empty context every selection derivation is forced
through the store — which is what makes runtime subtyping invertible.
Source programs cannot mention locations, so declarative typing is
unchanged. No interval guard is needed: alias intervals are non-empty
by reflexivity. -/
| sel_hi_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  Sub Θ Γ (.ty (.tsel p A)) (.ty (Ty.fromClosed W))
| sel_lo_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  Sub Θ Γ (.ty (Ty.fromClosed W)) (.ty (.tsel p A))
/-- Dependent function types: contravariant domain, covariant codomain
under the smaller domain. -/
| arrow :
  Sub Θ Γ (.ty S') (.ty S) ->
  Sub Θ (Γ.push S') (.ty T) (.ty T') ->
  Sub Θ Γ (.ty (.arrow S T)) (.ty (.arrow S' T'))
/-- Pair types with a term member, covariant in both components. -/
| pair_tm :
  Sub Θ Γ (.ty S) (.ty S') ->
  Sub Θ (Γ.push S) (.ty T) (.ty T') ->
  Sub Θ Γ (.ty (.pairTm S a T)) (.ty (.pairTm S' a T'))
/-- Pair types with a type member, covariant with interval widening. -/
| pair_ty :
  Sub Θ Γ (.ty S) (.ty S') ->
  Sub Θ (Γ.push S) (.ty T1') (.ty T1) ->
  Sub Θ (Γ.push S) (.ty T2) (.ty T2') ->
  Sub Θ Γ (.ty (.pairTy S A T1 T2)) (.ty (.pairTy S' A T1' T2'))
/-- Path replacement: mutually-aliased wellformed paths are interchangeable
under type openings (cf. pDOT's replacement subtyping). Without this rule
subtyping cannot track aliasing through dependent openings, which
preservation needs (`T.open q` vs `T.open ℓ` for `q ⇓ ℓ`); see DESIGN.md,
deviation 8. Bidirectionality of the premises is essential: one-sided
singleton inclusion would be unsound at contravariant positions. -/
| repl :
  Path.Wf Θ Γ p ->
  Path.Wf Θ Γ q ->
  Sub Θ Γ (.ty (.single p)) (.ty (.single q)) ->
  Sub Θ Γ (.ty (.single q)) (.ty (.single p)) ->
  Sub Θ Γ (.ty (Ty.open T p)) (.ty (Ty.open T q))
/-- Selection skip over a term member with a different label (records
as nested pairs; the fixed form of the draft's scoping-buggy sel-l). -/
| skip_tm :
  p.root.IsBound ->
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S b T)) ->
  a ≠ b ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a)))
/-- Selection skip over a type member. -/
| skip_ty :
  p.root.IsBound ->
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S B T1 T2)) ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a)))
/-- Store-anchored selection skips for location-rooted paths
(completing deviation 9 for records-as-nested-pairs). -/
| skip_tm_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm S b Tc) ->
  a ≠ b ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a)))
| skip_ty_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTy S B T1 T2) ->
  Sub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a)))

/-- Wellformedness of paths: every projection/selection is justified by
subtyping evidence at a pair type. -/
inductive Path.Wf : Sto -> Ctx s -> Path s -> Prop where
| var_bound :
  Ctx.LookupVar Γ x T ->
  Path.Wf Θ Γ (.var (.bound x))
| var_free :
  Sto.Lookup Θ ℓ T ->
  Path.Wf Θ Γ (.var (.free ℓ))
| fst_tm :
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) ->
  Path.Wf Θ Γ p.fst
| fst_ty :
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) ->
  Path.Wf Θ Γ p.fst
| sel :
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) ->
  Path.Wf Θ Γ (p.sel a)
/-- A skipping selection is wellformed when its skipped form is. -/
| sel_skip_tm :
  Path.Wf Θ Γ ((Path.fst p).sel a) ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTm S b T)) ->
  a ≠ b ->
  Path.Wf Θ Γ (p.sel a)
| sel_skip_ty :
  Path.Wf Θ Γ ((Path.fst p).sel a) ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S B T1 T2)) ->
  Path.Wf Θ Γ (p.sel a)

end

/-! ### Wellformedness of types -/

/-- Wellformedness of generalized types. -/
inductive Wf : Sto -> Ctx s -> Tau s -> Prop where
| bot :
  Wf Θ Γ (.ty .bot)
| top :
  Wf Θ Γ (.ty .top)
| single :
  Path.Wf Θ Γ p ->
  Wf Θ Γ (.ty (.single p))
| tsel :
  Path.Wf Θ Γ p ->
  Sub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) ->
  Wf Θ Γ (.ty (.tsel p A))
| arrow :
  Wf Θ Γ (.ty S) ->
  Wf Θ (Γ.push S) (.ty T) ->
  Wf Θ Γ (.ty (.arrow S T))
| pair_tm :
  Wf Θ Γ (.ty S) ->
  Wf Θ (Γ.push S) (.ty T) ->
  Wf Θ Γ (.ty (.pairTm S a T))
| pair_ty :
  Wf Θ Γ (.ty S) ->
  Wf Θ (Γ.push S) (.intv T1 T2) ->
  Wf Θ Γ (.ty (.pairTy S A T1 T2))
| intv :
  Wf Θ Γ (.ty S) ->
  Wf Θ Γ (.ty T) ->
  Sub Θ Γ (.ty S) (.ty T) ->
  Wf Θ Γ (.intv S T)

/-! ### Typing -/

/-- Term typing, `Θ; Γ ⊢ t : T`. Typings are precise: a path has itself
(as a singleton) for its type, and pair values have singleton pair types;
subsumption widens. -/
inductive HasType : Sto -> Ctx s -> Tm s -> Ty s -> Prop where
/-- A wellformed path has its singleton type. -/
| path :
  Path.Wf Θ Γ p ->
  HasType Θ Γ (.path p) (.single p)
/-- Subsumption. -/
| sub :
  HasType Θ Γ t S ->
  Sub Θ Γ (.ty S) (.ty T) ->
  Wf Θ Γ (.ty T) ->
  HasType Θ Γ t T
/-- λ-abstraction. -/
| abs :
  Wf Θ Γ (.ty S) ->
  HasType Θ (Γ.push S) t T ->
  HasType Θ Γ (.abs S t) (.arrow S T)
/-- Dependent application: the result type opens with the argument path. -/
| app :
  HasType Θ Γ (.path p) (.arrow S T) ->
  HasType Θ Γ (.path q) S ->
  HasType Θ Γ (.app p q) (T.open q)
/-- Term-member pair introduction, with a precise singleton pair type. -/
| pair_tm :
  Path.Wf Θ Γ (.var y) ->
  Path.Wf Θ Γ (.var z) ->
  HasType Θ Γ (.pairTm y a z)
    (.pairTm (.single (.var y)) a (Ty.single (.var z)).weaken)
/-- Type-member pair introduction: the member gets the alias interval T..T. -/
| pair_ty :
  Path.Wf Θ Γ (.var y) ->
  Wf Θ Γ (.ty T) ->
  HasType Θ Γ (.pairTy y A T)
    (.pairTy (.single (.var y)) A T.weaken T.weaken)
/-- Let binding; the result type lives in the outer scope. -/
| letin :
  HasType Θ Γ t1 S ->
  Wf Θ Γ (.ty T) ->
  HasType Θ (Γ.push S) t2 T.weaken ->
  HasType Θ Γ (.letin t1 t2) T
/-- Type ascription. -/
| typed :
  HasType Θ Γ t T ->
  Wf Θ Γ (.ty T) ->
  HasType Θ Γ (.typed t T) T

end LambdaP
