import LambdaP.Soundness.Embedding

/-!
The realized substitution layer (P4): substituting a variable by a
resolved runtime path preserves typing, with the substituted
variable's selection facts re-anchored through the store. The motive
carries a Δ-level facts table (`DOut`, the declarative twin of `SOut`)
whose tokens are either capture (a bound-rooted, wellformed mediator —
discharged by replacement transport, verified patterns below) or
honest store anchors with recursive residues, well-founded by the
anchor-location bound.
-/

namespace LambdaP

variable {s : Sig} {Θ : Sto} {Δ : Ctx s}

/-! ### Capture discharge (Lean-verified patterns from the matrix
probe): a captured pair-evidence re-derives selection conclusions via
the mediator. -/

theorem Captured.discharge_sel_hi {p r : Path s} {A : Name} {S : Ty s} {T1 T2 : Ty (s+1)}
    (hwr : Path.Wf Θ Δ r)          -- MISSING from the refined token
    (hwp : Path.Wf Θ Δ p)          -- from sel_hi's Wf premise (motive)
    (hcap : Sub Θ Δ (.ty (.single p)) (.ty (.single r)))
    (hev : Sub Θ Δ (.ty (.single p)) (.ty (.pairTy S A T1 T2)))
    (hgd : Sub Θ Δ (.ty (T1.open p.fst)) (.ty (T2.open p.fst))) :
    Sub Θ Δ (.ty (.tsel p A)) (.ty (T2.open p.fst)) := by
  have hrev : Sub Θ Δ (.ty (.single r)) (.ty (.single p)) := .symm hwp hcap
  have hevr : Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) := .trans hrev hev
  have hwpf : Path.Wf Θ Δ p.fst := .fst_ty hwp hev
  have hwrf : Path.Wf Θ Δ r.fst := .fst_ty hwr hevr                    -- uses hwr
  have hf1 : Sub Θ Δ (.ty (.single p.fst)) (.ty (.single r.fst)) :=
    Sub.repl_fst hwp hwr hcap hrev                                     -- uses hwr
  have hf2 : Sub Θ Δ (.ty (.single r.fst)) (.ty (.single p.fst)) :=
    Sub.repl_fst hwr hwp hrev hcap                                     -- uses hwr
  have hgdr : Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) :=
    .trans (Sub.repl (T := T1) hwrf hwpf hf2 hf1)
      (.trans hgd (Sub.repl (T := T2) hwpf hwrf hf1 hf2))
  exact .trans (Sub.repl_tsel hwp hwr hcap hrev)                       -- uses hwr
    (.trans (.sel_hi hwr hevr hgdr)                                -- uses hwr (rule premise)
      (Sub.repl (T := T2) hwrf hwpf hf2 hf1))

/-- sel_tm consumption, captured evidence. The rule `Sub.sel_tm` has NO
`Path.Wf p` premise, so `hwp` has no source in the motive — yet symm,
repl_sel, repl_fst, and the final repl all demand it. -/
theorem Captured.discharge_sel_tm {p r : Path s} {a : Name} {S : Ty s} {T : Ty (s+1)}
    (hwr : Path.Wf Θ Δ r)          -- MISSING from the refined token
    (hwp : Path.Wf Θ Δ p)          -- NO source: sel_tm carries no Wf premise
    (hcap : Sub Θ Δ (.ty (.single p)) (.ty (.single r)))
    (hev : Sub Θ Δ (.ty (.single p)) (.ty (.pairTm S a T))) :
    Sub Θ Δ (.ty (.single (p.sel a))) (.ty (T.open p.fst)) := by
  have hrev : Sub Θ Δ (.ty (.single r)) (.ty (.single p)) := .symm hwp hcap
  have hevr : Sub Θ Δ (.ty (.single r)) (.ty (.pairTm S a T)) := .trans hrev hev
  have hwpf : Path.Wf Θ Δ p.fst := .fst_tm hwp hev
  have hwrf : Path.Wf Θ Δ r.fst := .fst_tm hwr hevr
  have hf1 : Sub Θ Δ (.ty (.single p.fst)) (.ty (.single r.fst)) :=
    Sub.repl_fst hwp hwr hcap hrev
  have hf2 : Sub Θ Δ (.ty (.single r.fst)) (.ty (.single p.fst)) :=
    Sub.repl_fst hwr hwp hrev hcap
  exact .trans (Sub.repl_sel hwp hwr hcap hrev)
    (.trans (.sel_tm hwr hevr) (Sub.repl (T := T) hwrf hwpf hf2 hf1))

/-- skip_tm consumption, captured evidence. Same Wf gap as sel_tm. -/
theorem Captured.discharge_skip_tm {p r : Path s} {a b : Name} {S : Ty s} {T : Ty (s+1)}
    (hwr : Path.Wf Θ Δ r)          -- MISSING from the refined token
    (hwp : Path.Wf Θ Δ p)          -- NO source: skip_tm carries no Wf premise
    (hcap : Sub Θ Δ (.ty (.single p)) (.ty (.single r)))
    (hev : Sub Θ Δ (.ty (.single p)) (.ty (.pairTm S b T)))
    (hne : a ≠ b) :
    Sub Θ Δ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) := by
  have hrev : Sub Θ Δ (.ty (.single r)) (.ty (.single p)) := .symm hwp hcap
  have hevr : Sub Θ Δ (.ty (.single r)) (.ty (.pairTm S b T)) := .trans hrev hev
  have hwpf : Path.Wf Θ Δ p.fst := .fst_tm hwp hev
  have hwrf : Path.Wf Θ Δ r.fst := .fst_tm hwr hevr
  have hf1 : Sub Θ Δ (.ty (.single p.fst)) (.ty (.single r.fst)) :=
    Sub.repl_fst hwp hwr hcap hrev
  have hf2 : Sub Θ Δ (.ty (.single r.fst)) (.ty (.single p.fst)) :=
    Sub.repl_fst hwr hwp hrev hcap
  exact .trans (Sub.repl_sel hwp hwr hcap hrev)
    (.trans (.skip_tm hwr hevr hne) (Sub.repl_sel hwrf hwpf hf2 hf1))

/-- Cone descent: the alias component of a pairTy entry is strictly
older than the entry itself. -/
theorem alias_component_lt {Θ : Sto} (hwf : Sto.Shaped Θ) {m ℓ1 : Nat}
    {A : Name} {W : Ty 0}
    (hE : Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W))) :
    ℓ1 < m := by
  have h := (hwf hE).2
  simp [Ty.LocsBelow, Path.LocsBelow, Var.LocsBelow] at h
  exact h.1

/-- The sandwich instantiation at `p.fst`, done the review's way:
`hlo0`/`hhi0` are the results of the RECURSIVE substR call at the bare
image `ℓ1` (a legal SubstTypingR image; `ℓ1 < m` by `alias_component_lt`),
and the bridge to `p.fst` is repl over the co-chain `p.fst ~ ℓ1`.
No path-shaped substitution image is ever needed. -/
theorem bridge_fst_component {Θ : Sto} (hwf : Sto.Shaped Θ) {p : Path 0} {m ℓ1 : Nat}
    {A : Name} {W : Ty 0} {T1 T2 : Ty 1}
    (hc : Chains Θ p m)
    (hE : Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)))
    (hlo0 : Sub Θ .empty (.ty (T1.open (.var (.free ℓ1)))) (.ty W.fromClosed))
    (hhi0 : Sub Θ .empty (.ty W.fromClosed) (.ty (T2.open (.var (.free ℓ1))))) :
    Sub Θ .empty (.ty (T1.open p.fst)) (.ty W.fromClosed) ∧
    Sub Θ .empty (.ty W.fromClosed) (.ty (T2.open p.fst)) := by
  have hcf : Chains Θ p.fst ℓ1 := .fst_ty hc hE
  obtain ⟨E1, hl1⟩ := Chains.in_dom hwf hcf
  have hcl : Chains Θ (.var (.free ℓ1) : Path 0) ℓ1 := .loc hl1
  have h1 : Sub Θ .empty (.ty (.single p.fst)) (.ty (.single (.var (.free ℓ1)))) :=
    hcf.to_sub
  have h2 : Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty (.single p.fst)) :=
    Chains.mutual_sub hcl hcf
  have hwpf : Path.Wf Θ .empty p.fst := hcf.wf
  have hwl : Path.Wf Θ .empty (.var (.free ℓ1) : Path 0) := .var_free hl1
  exact ⟨.trans (Sub.repl (T := T1) hwpf hwl h1 h2) hlo0,
         .trans hhi0 (Sub.repl (T := T2) hwl hwpf h2 h1)⟩



/-- sel_lo consumption, captured evidence (mirror of `discharge_sel_hi`). -/
theorem Captured.discharge_sel_lo {p r : Path s} {A : Name} {S : Ty s} {T1 T2 : Ty (s+1)}
    (hwr : Path.Wf Θ Δ r)
    (hwp : Path.Wf Θ Δ p)
    (hcap : Sub Θ Δ (.ty (.single p)) (.ty (.single r)))
    (hev : Sub Θ Δ (.ty (.single p)) (.ty (.pairTy S A T1 T2)))
    (hgd : Sub Θ Δ (.ty (T1.open p.fst)) (.ty (T2.open p.fst))) :
    Sub Θ Δ (.ty (T1.open p.fst)) (.ty (.tsel p A)) := by
  have hrev : Sub Θ Δ (.ty (.single r)) (.ty (.single p)) := .symm hwp hcap
  have hevr : Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S A T1 T2)) := .trans hrev hev
  have hwpf : Path.Wf Θ Δ p.fst := .fst_ty hwp hev
  have hwrf : Path.Wf Θ Δ r.fst := .fst_ty hwr hevr
  have hf1 : Sub Θ Δ (.ty (.single p.fst)) (.ty (.single r.fst)) :=
    Sub.repl_fst hwp hwr hcap hrev
  have hf2 : Sub Θ Δ (.ty (.single r.fst)) (.ty (.single p.fst)) :=
    Sub.repl_fst hwr hwp hrev hcap
  have hgdr : Sub Θ Δ (.ty (T1.open r.fst)) (.ty (T2.open r.fst)) :=
    .trans (Sub.repl (T := T1) hwrf hwpf hf2 hf1)
      (.trans hgd (Sub.repl (T := T2) hwpf hwrf hf1 hf2))
  exact .trans (Sub.repl (T := T1) hwpf hwrf hf1 hf2)
    (.trans (.sel_lo hwr hevr hgdr)
      (Sub.repl_tsel hwr hwp hrev hcap))

/-- skip_ty consumption, captured evidence (mirror of `discharge_skip_tm`). -/
theorem Captured.discharge_skip_ty {p r : Path s} {a : Name} {S : Ty s}
    {B : Name} {T1 T2 : Ty (s+1)}
    (hwr : Path.Wf Θ Δ r)
    (hwp : Path.Wf Θ Δ p)
    (hcap : Sub Θ Δ (.ty (.single p)) (.ty (.single r)))
    (hev : Sub Θ Δ (.ty (.single p)) (.ty (.pairTy S B T1 T2))) :
    Sub Θ Δ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) := by
  have hrev : Sub Θ Δ (.ty (.single r)) (.ty (.single p)) := .symm hwp hcap
  have hevr : Sub Θ Δ (.ty (.single r)) (.ty (.pairTy S B T1 T2)) := .trans hrev hev
  have hwpf : Path.Wf Θ Δ p.fst := .fst_ty hwp hev
  have hwrf : Path.Wf Θ Δ r.fst := .fst_ty hwr hevr
  have hf1 : Sub Θ Δ (.ty (.single p.fst)) (.ty (.single r.fst)) :=
    Sub.repl_fst hwp hwr hcap hrev
  have hf2 : Sub Θ Δ (.ty (.single r.fst)) (.ty (.single p.fst)) :=
    Sub.repl_fst hwr hwp hrev hcap
  exact .trans (Sub.repl_sel hwp hwr hcap hrev)
    (.trans (.skip_ty hwr hevr) (Sub.repl_sel hwrf hwpf hf2 hf1))


/-! ### §6 Realized conforming substitutions -/

/-- A realized conforming substitution (P4.4): conformance and
wellformedness as in `SubstTyping`, but images may be BARE heap
locations instead of bound-rooted paths, provided the declared type
substitutes to a CLOSED type to which the location conforms at the
empty context (dischargeable: λ-domains and let-binder types are
wellformed at their outer scope, closed at top level; preservation
only ever opens ONE variable with a bare location). Ambient
`Sto.Shaped` is a hypothesis of the theorems, not a field. -/
structure SubstTypingR (Θ : Sto) (σ : Subst s1 s2) (Γ : Ctx s1) (Δ : Ctx s2) : Prop where
  conforms : ∀ {x : BVar s1} {T : Ty s1},
    Ctx.LookupVar Γ x T → Sub Θ Δ (.ty (.single (σ.var x))) (.ty (T.subst σ))
  wf : ∀ (x : BVar s1), Path.Wf Θ Δ (σ.var x)
  images : ∀ (x : BVar s1),
    (σ.var x).root.IsBound ∨ ∃ ℓ : Nat, σ.var x = .var (.free ℓ)
  realized : ∀ {x : BVar s1} {T : Ty s1} {ℓ : Nat},
    Ctx.LookupVar Γ x T → σ.var x = .var (.free ℓ) →
    ∃ T0 : Ty 0, T.subst σ = Ty.fromClosed T0 ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ)))) (.ty T0)

/-- Realized conforming substitutions extend under a binder (the new
variable maps to itself: bound-rooted, so `realized` is vacuous there;
`there`-images keep their closed realizations via
`Ty.fromClosed_weaken`). -/
theorem SubstTypingR.lift {s1 s2 : Sig} {Θ : Sto} {σ : Subst s1 s2}
    {Γ : Ctx s1} {Δ : Ctx s2}
    (hσ : SubstTypingR Θ σ Γ Δ) {S : Ty s1} :
    SubstTypingR Θ σ.lift (Γ.push S) (Δ.push (S.subst σ)) := by
  constructor
  · intro x T h
    cases h with
    | here =>
      rw [Ty.weaken_subst_comm]
      exact Sub.var_bound .here
    | there h' =>
      rw [Ty.weaken_subst_comm]
      exact (hσ.conforms h').weaken
  · intro x
    cases x with
    | here => exact .var_bound .here
    | there x' => exact (hσ.wf x').weaken
  · intro x
    cases x with
    | here => exact Or.inl trivial
    | there x' =>
      rcases hσ.images x' with hb | ⟨ℓ, he⟩
      · exact Or.inl (Path.root_isBound_rename hb)
      · exact Or.inr ⟨ℓ, by
          show (σ.var x').rename Rename.succ = _
          rw [he]
          rfl⟩
  · intro x T ℓ hlk he
    cases x with
    | here =>
      exact absurd he (by intro h; cases h)
    | there x' =>
      cases hlk with
      | there hlk' =>
      have he' : σ.var x' = .var (.free ℓ) := by
        have hshow : (σ.var x').rename Rename.succ = .var (.free ℓ) := he
        cases hv : σ.var x' with
        | var v =>
          rw [hv] at hshow
          cases v with
          | bound b => exact absurd hshow (by intro h; cases h)
          | free ℓ' =>
            have : ℓ' = ℓ := by
              have := hshow
              simp [Path.rename, Var.rename] at this
              exact this
            subst this
            rfl
        | fst p' =>
          rw [hv] at hshow
          exact absurd hshow (by intro h; cases h)
        | sel p' a' =>
          rw [hv] at hshow
          exact absurd hshow (by intro h; cases h)
      obtain ⟨T0, hTs, hsub⟩ := hσ.realized hlk' he'
      refine ⟨T0, ?_, hsub⟩
      rw [Ty.weaken_subst_comm, hTs]
      exact Ty.fromClosed_rename

end LambdaP
