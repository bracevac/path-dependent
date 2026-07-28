import LambdaP.Lemmas.Locs
import LambdaP.Soundness.Preservation

/-!
M1 slice 1: precise path typing over the store typing — the Θ-side mirror
of `PathEval`. Two layers, following the pDOT artifact's ⊢!/⊢!! split but
with λ_p's discounts: elimination (`PrecisePath`) never follows aliases,
so it is functional; alias-following (`PreciseChain`) strictly descends
locations because precise store types are location-bounded.
-/

namespace LambdaP

/-- Alias-free precise elimination: start from a location's recorded type
and project through pair components. Over a well-typed store every
projected component is a location singleton, so this mirrors `PathEval`
syntactically. -/
inductive PrecisePath (Θ : Sto) : Path 0 -> Ty 0 -> Prop where
| loc :
  Sto.Lookup Θ ℓ T ->
  PrecisePath Θ (.var (.free ℓ)) T
| fst_tm :
  PrecisePath Θ p (.pairTm S a T) ->
  PrecisePath Θ p.fst S
| fst_ty :
  PrecisePath Θ p (.pairTy S A T1 T2) ->
  PrecisePath Θ p.fst S
| sel :
  PrecisePath Θ p (.pairTm S a T) ->
  PrecisePath Θ (p.sel a) (T.open p.fst)

/-- One alias-following step: a path precisely typed at a location
singleton re-anchors at that location's recorded type. -/
inductive PreciseStep (Θ : Sto) : Path 0 -> Path 0 -> Prop where
| step :
  PrecisePath Θ p (.single (.var (.free ℓ))) ->
  PreciseStep Θ p (.var (.free ℓ))

/-- Elimination is functional: a path has at most one precise type. -/
theorem PrecisePath.unique {Θ : Sto} {p : Path 0} {T1 T2 : Ty 0}
    (h1 : PrecisePath Θ p T1) (h2 : PrecisePath Θ p T2) : T1 = T2 := by
  induction h1 generalizing T2 with
  | loc hl1 =>
    cases h2 with
    | loc hl2 => exact Option.some_inj.mp ((Eq.symm hl1).trans hl2)
  | fst_tm h1 ih =>
    cases h2 with
    | fst_tm h2 => cases ih h2; rfl
    | fst_ty h2 => cases ih h2
  | fst_ty h1 ih =>
    cases h2 with
    | fst_tm h2 => cases ih h2
    | fst_ty h2 => cases ih h2; rfl
  | sel h1 ih =>
    cases h2 with
    | sel h2 => cases ih h2; rfl

/-- `LocsBelow` is monotone in the bound. -/
theorem Var.LocsBelow.mono {x : Var s} {k k' : Nat}
    (h : x.LocsBelow k) (hk : k ≤ k') : x.LocsBelow k' := by
  cases x with
  | bound b => trivial
  | free ℓ => exact Nat.lt_of_lt_of_le h hk

theorem Path.LocsBelow.mono {p : Path s} {k k' : Nat}
    (h : p.LocsBelow k) (hk : k ≤ k') : p.LocsBelow k' := by
  induction p with
  | var x => exact Var.LocsBelow.mono h hk
  | fst _ ih => exact ih h
  | sel _ _ ih => exact ih h

theorem Ty.LocsBelow.mono {T : Ty s} {k k' : Nat}
    (h : T.LocsBelow k) (hk : k ≤ k') : T.LocsBelow k' := by
  induction T with
  | top => trivial
  | bot => trivial
  | arrow S T ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | pairTm S a T ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | pairTy S A T1 T2 ih1 ih2 ih3 => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | single p => exact Path.LocsBelow.mono h hk
  | tsel p A => exact Path.LocsBelow.mono h hk

/-- Precisely typed paths mention only recorded locations. -/
theorem PrecisePath.path_locsBelow {Θ : Sto} {p : Path 0} {T : Ty 0}
    (h : PrecisePath Θ p T) : p.LocsBelow Θ.length := by
  induction h with
  | loc hl => exact (List.getElem?_eq_some_iff.mp hl).1
  | fst_tm _ ih => exact ih
  | fst_ty _ ih => exact ih
  | sel _ ih => exact ih

/-- Precise types are location-bounded (over a well-typed heap: recorded
types are bounded by their own location, hence by the store length). -/
theorem PrecisePath.locsBelow {Θ : Sto} {h : Heap} {p : Path 0} {T : Ty 0}
    (hh : HeapTyped Θ h) (hp : PrecisePath Θ p T) : T.LocsBelow Θ.length := by
  induction hp with
  | loc hl =>
    have hb := (hh.2 hl).1
    exact hb.mono (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hl).1)
  | fst_tm _ ih => exact ih.1
  | fst_ty _ ih => exact ih.1
  | sel hp ih => exact Ty.LocsBelow.open ih.2 hp.path_locsBelow

/-! ### Shallow structure over a well-typed heap -/

/-- Store entries have one of the three precise value-type shapes. -/
theorem HeapTyped.lookup_shape {Θ : Sto} {h : Heap} {ℓ : Nat} {T : Ty 0}
    (hh : HeapTyped Θ h) (hl : Sto.Lookup Θ ℓ T) :
    (∃ S B, T = .arrow S B) ∨
    (∃ ℓ1 a ℓ2, T = .pairTm (.single (.var (.free ℓ1))) a
      (Ty.single (.var (.free ℓ2))).weaken) ∨
    (∃ (ℓ1 : Nat) (A : Name) (W : Ty 0), T = .pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) := by
  obtain ⟨-, v, -, -, hpre⟩ := hh.2 hl
  cases hpre with
  | abs _ _ => exact .inl ⟨_, _, rfl⟩
  | pair_tm _ _ => exact .inr (.inl ⟨_, _, _, rfl⟩)
  | pair_ty _ _ => exact .inr (.inr ⟨_, _, _, rfl⟩)

/-- Characterization over a well-typed heap: a precisely typed path is
either a bare location carrying its store entry, or its type is a
location singleton strictly below some recorded location (its root). -/
theorem PrecisePath.char {Θ : Sto} {h : Heap} {p : Path 0} {T : Ty 0}
    (hh : HeapTyped Θ h) (hp : PrecisePath Θ p T) :
    (∃ ℓr, p = .var (.free ℓr) ∧ Sto.Lookup Θ ℓr T) ∨
    (∃ ℓ', T = .single (.var (.free ℓ')) ∧
      ∃ ℓr Tr, Sto.Lookup Θ ℓr Tr ∧ ℓ' < ℓr) := by
  induction hp with
  | loc hl => exact .inl ⟨_, rfl, hl⟩
  | fst_tm hp' ih =>
    rcases ih with ⟨ℓr, -, hl⟩ | ⟨ℓ', he, -⟩
    · rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨ℓ1, a', ℓ2, he⟩ | ⟨_, _, _, he⟩ <;>
        cases he
      have hb := (hh.2 hl).1
      exact .inr ⟨ℓ1, rfl, ℓr, _, hl, hb.1⟩
    · cases he
  | fst_ty hp' ih =>
    rcases ih with ⟨ℓr, -, hl⟩ | ⟨ℓ', he, -⟩
    · rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨ℓ1, A', W, he⟩ <;>
        cases he
      have hb := (hh.2 hl).1
      exact .inr ⟨ℓ1, rfl, ℓr, _, hl, hb.1⟩
    · cases he
  | sel hp' ih =>
    rcases ih with ⟨ℓr, -, hl⟩ | ⟨ℓ', he, -⟩
    · rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨ℓ1, a', ℓ2, he⟩ | ⟨_, _, _, he⟩ <;>
        cases he
      have hb := (hh.2 hl).1
      rw [Ty.weaken_open]
      exact .inr ⟨ℓ2, rfl, ℓr, _, hl, Ty.locsBelow_rename.mp hb.2⟩
    · cases he

/-- A path precisely typed at a term-member pair type is a bare location. -/
theorem PrecisePath.pairTm_inv {Θ : Sto} {h : Heap} {p : Path 0}
    {S : Ty 0} {a : Name} {Tc : Ty 1}
    (hh : HeapTyped Θ h) (hp : PrecisePath Θ p (.pairTm S a Tc)) :
    ∃ ℓr, p = .var (.free ℓr) ∧ Sto.Lookup Θ ℓr (.pairTm S a Tc) := by
  rcases hp.char hh with ⟨ℓr, hpe, hl⟩ | ⟨ℓ', he, -⟩
  · exact ⟨ℓr, hpe, hl⟩
  · cases he

/-- A path precisely typed at a type-member pair type is a bare location. -/
theorem PrecisePath.pairTy_inv {Θ : Sto} {h : Heap} {p : Path 0}
    {S : Ty 0} {A : Name} {T1 T2 : Ty 1}
    (hh : HeapTyped Θ h) (hp : PrecisePath Θ p (.pairTy S A T1 T2)) :
    ∃ ℓr, p = .var (.free ℓr) ∧ Sto.Lookup Θ ℓr (.pairTy S A T1 T2) := by
  rcases hp.char hh with ⟨ℓr, hpe, hl⟩ | ⟨ℓ', he, -⟩
  · exact ⟨ℓr, hpe, hl⟩
  · cases he

/-- Descent: a path precisely typed at a location singleton points
strictly below some recorded location. This is the measure for alias
chains. -/
theorem PrecisePath.single_lt {Θ : Sto} {h : Heap} {p : Path 0} {ℓ' : Nat}
    (hh : HeapTyped Θ h)
    (hp : PrecisePath Θ p (.single (.var (.free ℓ')))) :
    ∃ ℓr Tr, Sto.Lookup Θ ℓr Tr ∧ ℓ' < ℓr := by
  rcases hp.char hh with ⟨ℓr, -, hl⟩ | ⟨ℓ'', he, hlt⟩
  · rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
  · cases he
    exact hlt

/-! ### Store-side path resolution -/

/-- `Chains Θ p ℓ`: the store-typing mirror of `PathEval` — the path
resolves to `ℓ` reading component locations off the precise entries. -/
inductive Chains (Θ : Sto) : Path 0 -> Nat -> Prop where
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

theorem Chains.deterministic {Θ : Sto} {p : Path 0} {ℓ1 ℓ2 : Nat}
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

/-- Recorded pair entries agree with stored pair values componentwise. -/
theorem HeapTyped.entry_value_tm {Θ : Sto} {h : Heap} {ℓ ℓ1 : Nat}
    {a : Name} {Tc : Ty 1}
    (hh : HeapTyped Θ h)
    (hl : Sto.Lookup Θ ℓ (.pairTm (.single (.var (.free ℓ1))) a Tc)) :
    ∃ ℓ2, Tc = (Ty.single (.var (.free ℓ2))).weaken ∧
      Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) := by
  obtain ⟨-, v, hvl, -, hpre⟩ := hh.2 hl
  cases hpre with
  | pair_tm hy hz =>
    exact ⟨_, rfl, hvl⟩

theorem HeapTyped.entry_value_ty {Θ : Sto} {h : Heap} {ℓ ℓ1 : Nat}
    {A : Name} {T1 T2 : Ty 1}
    (hh : HeapTyped Θ h)
    (hl : Sto.Lookup Θ ℓ (.pairTy (.single (.var (.free ℓ1))) A T1 T2)) :
    ∃ W, T1 = W.weaken ∧ T2 = W.weaken ∧
      Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) := by
  obtain ⟨-, v, hvl, -, hpre⟩ := hh.2 hl
  cases hpre with
  | pair_ty hy hwf =>
    exact ⟨_, rfl, rfl, hvl⟩

/-- Store-side resolution transfers to heap evaluation. -/
theorem Chains.pathEval {Θ : Sto} {h : Heap} {p : Path 0} {ℓ : Nat}
    (hh : HeapTyped Θ h) (hc : Chains Θ p ℓ) : PathEval h p ℓ := by
  induction hc with
  | loc _ => exact .var
  | fst_tm _ hl ih =>
    obtain ⟨ℓ2, -, hvl⟩ := hh.entry_value_tm hl
    exact .fst_tm ih hvl
  | fst_ty _ hl ih =>
    obtain ⟨W, -, -, hvl⟩ := hh.entry_value_ty hl
    exact .fst_ty ih hvl
  | sel hc hl ih =>
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨ℓ1', a', ℓ2', he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
    obtain ⟨ℓ2'', heq, hvl⟩ := hh.entry_value_tm hl
    simp only [Ty.weaken, Ty.rename, Path.rename, Var.rename] at heq
    cases heq
    exact .sel ih hvl
  | sel_skip_tm hc hl hne hin ihc ihin =>
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨ℓ1', b', ℓ2', he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
    obtain ⟨ℓ2'', heq, hvl⟩ := hh.entry_value_tm hl
    exact .sel_skip_tm ihc hvl hne ihin
  | sel_skip_ty hc hl hin ihc ihin =>
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨ℓ1', B', W', he⟩ <;>
      cases he
    obtain ⟨W'', heq1, heq2, hvl⟩ := hh.entry_value_ty hl
    exact .sel_skip_ty ihc hvl ihin

end LambdaP
