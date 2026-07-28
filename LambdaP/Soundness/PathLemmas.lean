import LambdaP.Soundness.Den

/-!
Path-evaluation lemmas: determinism, and congruence of evaluation under
replacement of a co-evaluating prefix. The congruence lemma is what makes
`T.open q` and `T.open (var ℓ)` semantically interchangeable when `q ⇓ ℓ`
— paths in types are only ever *resolved* through the store, never
evaluated as programs, so replacing a prefix by any co-evaluating path is
invisible to every store consultation. With the selection-skip steps,
congruence is by induction on the evaluation derivation (the skip premise
is not structurally below the path).
-/

namespace LambdaP

/-- Path evaluation is deterministic. -/
theorem PathEval.deterministic {h : Heap} {p : Path 0} {m1 m2 : Nat}
    (h1 : PathEval h p m1) (h2 : PathEval h p m2) : m1 = m2 := by
  induction h1 generalizing m2 with
  | var =>
    cases h2 with
    | var => rfl
  | fst_tm _ hl1 ih =>
    cases h2 with
    | fst_tm h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl
    | fst_ty h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
  | fst_ty _ hl1 ih =>
    cases h2 with
    | fst_tm h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
    | fst_ty h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl
  | sel _ hl1 ih =>
    cases h2 with
    | sel h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl
    | sel_skip_tm hp2 hl2 hne2 _ =>
      cases ih hp2
      cases Option.some.inj (hl1.symm.trans hl2)
      exact absurd rfl hne2
    | sel_skip_ty hp2 hl2 _ =>
      cases ih hp2
      cases Option.some.inj (hl1.symm.trans hl2)
  | sel_skip_tm hp1 hl1 hne1 _ ihp ihin =>
    cases h2 with
    | sel h2' hl2 =>
      cases ihp h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      exact absurd rfl hne1
    | sel_skip_tm hp2 hl2 hne2 hin2 => exact ihin hin2
    | sel_skip_ty hp2 hl2 hin2 =>
      cases ihp hp2
      cases Option.some.inj (hl1.symm.trans hl2)
  | sel_skip_ty hp1 hl1 _ ihp ihin =>
    cases h2 with
    | sel h2' hl2 =>
      cases ihp h2'
      cases Option.some.inj (hl1.symm.trans hl2)
    | sel_skip_tm hp2 hl2 hne2 hin2 =>
      cases ihp hp2
      cases Option.some.inj (hl1.symm.trans hl2)
    | sel_skip_ty hp2 hl2 hin2 => exact ihin hin2

/-- Pointwise co-evaluation of two closing substitutions. -/
def CoEval (h : Heap) (σ1 σ2 : Subst s 0) : Prop :=
  ∀ (x : BVar s) (m : Nat), PathEval h (σ1.var x) m ↔ PathEval h (σ2.var x) m

/-- Evaluation of a substituted path only depends on the targets of the
substituted-in paths. By induction on the evaluation derivation with the
path generalized (skip premises recurse at larger paths). -/
theorem PathEval.subst_congr {h : Heap} {σ1 σ2 : Subst s 0}
    (hco : CoEval h σ1 σ2) :
    ∀ {p : Path s} {m : Nat},
      PathEval h (p.subst σ1) m -> PathEval h (p.subst σ2) m := by
  intro p m he
  generalize hE : p.subst σ1 = r at he
  induction he generalizing p with
  | var =>
    match p, hE with
    | .var (.bound b), hE => exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .var)
    | .var (.free n), hE =>
      cases hE
      exact .var
  | fst_tm he' hl ih =>
    match p, hE with
    | .var (.bound b), hE => exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_tm he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_tm (ih (p := p') rfl) hl
  | fst_ty he' hl ih =>
    match p, hE with
    | .var (.bound b), hE => exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_ty he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_ty (ih (p := p') rfl) hl
  | sel he' hl ih =>
    match p, hE with
    | .var (.bound b), hE => exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel he' hl)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel (ih (p := p') rfl) hl
  | sel_skip_tm hp hl hne hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_tm hp hl hne hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_tm (ihp (p := p') rfl) hl hne
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))
  | sel_skip_ty hp hl hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show PathEval h ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_ty hp hl hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_ty (ihp (p := p') rfl) hl
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))

/-- Co-evaluation of the two opening substitutions induced by
co-evaluating opener paths. -/
theorem CoEval.openPath {h : Heap} {q q' : Path 0} {ℓq : Nat}
    (hq : PathEval h q ℓq) (hq' : PathEval h q' ℓq) :
    CoEval h (Subst.openPath q) (Subst.openPath q') := by
  intro x m
  cases x with
  | here =>
    constructor
    · intro he
      cases PathEval.deterministic he hq
      exact hq'
    · intro he
      cases PathEval.deterministic he hq'
      exact hq
  | there b => exact nomatch b

/-- Evaluation of an opened path only depends on the target of the
opening path. -/
theorem PathEval.open_congr {h : Heap} {q q' : Path 0} {ℓq : Nat}
    (hq : PathEval h q ℓq) (hq' : PathEval h q' ℓq) :
    ∀ {p : Path 1} {m : Nat},
      PathEval h (p.subst (Subst.openPath q)) m ->
      PathEval h (p.subst (Subst.openPath q')) m :=
  fun he => PathEval.subst_congr (CoEval.openPath hq hq') he

/-- In a well-typed heap, a path that evaluates to an in-store target is
wellformed: each projection step is justified by the precise pair type of
the location it goes through. -/
theorem PathEval.to_wf {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {p : Path 0} {m : Nat} (he : PathEval h p m) :
    m < Θ.length -> Path.Wf Θ .empty p := by
  induction he with
  | var =>
    intro hm
    exact .var_free (List.getElem?_eq_getElem hm)
  | fst_tm he' hl ih =>
    intro _
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    have hmid := (List.getElem?_eq_some_iff.mp hl).1
    rw [← hh.1] at hmid
    cases hpre with
    | pair_tm _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .fst_tm (ih hmid) (.trans (he'.to_sub hh) hloc)
  | fst_ty he' hl ih =>
    intro _
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    have hmid := (List.getElem?_eq_some_iff.mp hl).1
    rw [← hh.1] at hmid
    cases hpre with
    | pair_ty _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .fst_ty (ih hmid) (.trans (he'.to_sub hh) hloc)
  | sel he' hl ih =>
    intro _
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    have hmid := (List.getElem?_eq_some_iff.mp hl).1
    rw [← hh.1] at hmid
    cases hpre with
    | pair_tm _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .sel (ih hmid) (.trans (he'.to_sub hh) hloc)
  | sel_skip_tm he' hl hne hin ihp ihin =>
    intro hm
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .sel_skip_tm (ihin hm) (.trans (he'.to_sub hh) hloc) hne
  | sel_skip_ty he' hl hin ihp ihin =>
    intro hm
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_ty _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .sel_skip_ty (ihin hm) (.trans (he'.to_sub hh) hloc)

/-- A skipped selection's prefix evaluates, through a stored pair. -/
theorem PathEval.sel_fst_prefix {h : Heap} {r : Path 0} {a : Name} {m : Nat}
    (he : PathEval h ((Path.fst r).sel a) m) :
    ∃ ℓr, PathEval h r ℓr ∧
      ((∃ ℓ1 b ℓ2, Heap.Lookup h ℓr (.pairTm (.free ℓ1) b (.free ℓ2))) ∨
       (∃ (ℓ1 : Nat) (B : Name) (T : Ty 0), Heap.Lookup h ℓr (.pairTy (.free ℓ1) B T))) := by
  have hf : ∃ ℓf, PathEval h (Path.fst r) ℓf := by
    cases he with
    | sel he' _ => exact ⟨_, he'⟩
    | sel_skip_tm he' _ _ _ => exact ⟨_, he'⟩
    | sel_skip_ty he' _ _ => exact ⟨_, he'⟩
  obtain ⟨ℓf, hf⟩ := hf
  cases hf with
  | fst_tm he' hl => exact ⟨_, he', .inl ⟨_, _, _, hl⟩⟩
  | fst_ty he' hl => exact ⟨_, he', .inr ⟨_, _, _, hl⟩⟩

/-- A selection evaluates whenever its skipped form does (matching label
selects directly; otherwise the skip steps apply). -/
theorem PathEval.sel_from_skip {h : Heap} {r : Path 0} {a : Name} {m : Nat}
    (hin : PathEval h ((Path.fst r).sel a) m) :
    ∃ m', PathEval h (r.sel a) m' := by
  obtain ⟨ℓr, hevp, hpair⟩ := hin.sel_fst_prefix
  rcases hpair with ⟨ℓ1, b, ℓ2, hlk⟩ | ⟨ℓ1, B, T, hlk⟩
  · by_cases hab : a = b
    · subst hab
      exact ⟨ℓ2, .sel hevp hlk⟩
    · exact ⟨m, .sel_skip_tm hevp hlk hab hin⟩
  · exact ⟨m, .sel_skip_ty hevp hlk hin⟩

end LambdaP
