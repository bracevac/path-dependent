import LambdaP.Original.Lookup
import LambdaP.Original.PreciseStore
import LambdaP.Original.PathFunctionality
import LambdaP.Original.TypingInversion

/-!
Typing preservation for big-step path lookup in the original calculus.

The precise path judgment synthesizes a signature, so lookup cannot preserve
that judgment literally: a projection may synthesize the singleton of its
result while the resulting variable synthesizes its context entry.  The
useful statement is the corresponding ordinary typing fact, or equivalently
that the result singleton is below the synthesized type.

This first theorem uses a precise-store invariant.  The later machine proof
must retain this invariant alongside any public type obtained by subsumption.
-/

namespace LambdaP.Original

/-- Every variable in an intrinsically scoped context has a binding. -/
theorem Ctx.Binds.exists (Γ : Ctx n) (x : Fin n) :
    ∃ T, Ctx.Binds Γ x T := by
  induction Γ with
  | nil => exact Fin.elim0 x
  | snoc Γ S ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨S.weaken, .here⟩
      · obtain ⟨T, hT⟩ := ih y
        exact ⟨T.weaken, .there hT⟩

/-- The substitution-level form of `Ty.weaken_open`, convenient when an
opened result has not yet been folded back to the `Ty.open` notation. -/
theorem Ty.weaken_subst_openAt {T : Ty n} {p : Path n} :
    T.weaken.subst (PathSubst.openAt p) = T := by
  simpa [Ty.open] using Ty.weaken_open T p

/-- Under a precise store, the type synthesized for a resolving path is
either the context type of the result (the variable case) or exactly the
result's singleton type (a projection or term-member hit). -/
theorem Path.lookup_type_shape
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.lookup p σ x)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    Ctx.Binds Γ x T ∨ T = Ty.Single (Path.var x) := by
  induction hr generalizing T with
  | var =>
      cases hp with
      | var hT => exact .inl hT
  | fst hr hb ih =>
      cases hp with
      | fst hp =>
          rcases ih hσ hp with hT | hbad
          · have hv := hσ.lookup hb hT
            cases hv with
            | pair => exact .inr rfl
            | tpair => exact .inr rfl
          · cases hbad
  | sel_hit hr hb ih =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, _, hne⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hσ hparent with hT | hbad
            · have hv := hσ.lookup hb hT
              cases hv with
              | pair =>
                  exact .inr rfl
            · cases hbad
        | intv L U => cases heq
      · rcases ih hσ hparent with hT | hbad
        · have hv := hσ.lookup hb hT
          cases hv with
          | pair => exact (hne rfl).elim
        · cases hbad
  | sel_miss hr hb hne hin ih ihr =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, htail, hne'⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hσ hparent with hT | hbad
            · have hv := hσ.lookup hb hT
              cases hv with
              | pair => exact (hne rfl).elim
            · cases hbad
        | intv L U => cases heq
      · exact ihr hσ htail

/-- Strengthened shape theorem: the context-type alternative occurs only for
an atomic variable.  Every projection or term-member lookup synthesizes the
singleton of its result under an exact store. -/
theorem Path.lookup_type_shape_strong
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.lookup p σ x)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    (p = Path.var x ∧ Ctx.Binds Γ x T) ∨
      T = Ty.Single (Path.var x) := by
  induction hr generalizing T with
  | var =>
      cases hp with
      | var hT => exact .inl ⟨rfl, hT⟩
  | fst hr hb ih =>
      cases hp with
      | fst hp =>
          rcases ih hσ hp with hT | hbad
          · have hv := hσ.lookup hb hT.2
            cases hv with
            | pair => exact .inr rfl
            | tpair => exact .inr rfl
          · cases hbad
  | sel_hit hr hb ih =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, _, hne⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hσ hparent with hT | hbad
            · have hv := hσ.lookup hb hT.2
              cases hv with
              | pair => exact .inr rfl
            · cases hbad
        | intv L U => cases heq
      · rcases ih hσ hparent with hT | hbad
        · have hv := hσ.lookup hb hT.2
          cases hv with
          | pair => exact (hne rfl).elim
        · cases hbad
  | sel_miss hr hb hne hin ih ihr =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, htail, hne'⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hσ hparent with hT | hbad
            · have hv := hσ.lookup hb hT.2
              cases hv with
              | pair => exact (hne rfl).elim
            · cases hbad
        | intv L U => cases heq
      · rcases ihr hσ htail with hbad | hT
        · cases hbad.1
        · exact .inr hT

/-- A resolving path and its result location are aliases in source subtyping
under an exact store. -/
theorem Path.lookup_preserves_singleton_alias
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.lookup p σ x)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    Tau.Sub Γ
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Single p)) := by
  rcases Path.lookup_type_shape_strong hσ hr hp with hvar | hsingle
  · cases hvar.1
    exact .refl
  · cases hsingle
    exact .symm hp

/-- The resolved location's singleton is below the proper type synthesized
for the source path. -/
theorem Path.lookup_preserves_subtyping
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.lookup p σ x)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    Tau.Sub Γ (Tau.ty (Ty.Single (Path.var x))) (Tau.ty T) := by
  rcases Path.lookup_type_shape hσ hr hp with hT | hT
  · exact Tau.Sub.widen (Path.Ty.var hT)
  · cases hT
    exact .refl

/-- Big-step lookup preserves ordinary typing of term paths. -/
theorem Path.lookup_preserves_typing
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.lookup p σ x)
    (hp : Path.Ty Γ p (Tau.ty T))
    (hwf : Tau.Wf Γ (Tau.ty T)) :
    Tm.Ty Γ (Tm.path (Path.var x)) T := by
  obtain ⟨U, hU⟩ := Ctx.Binds.exists Γ x
  exact Tm.Ty.sub (Tm.Ty.path (Path.Ty.var hU))
    (Path.lookup_preserves_subtyping hσ hr hp) hwf

/-- The same theorem for the literal historical `Path.reduce` relation. -/
theorem Path.reduce_preserves_typing
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.reduce p σ x)
    (hp : Path.Ty Γ p (Tau.ty T))
    (hwf : Tau.Wf Γ (Tau.ty T)) :
    Tm.Ty Γ (Tm.path (Path.var x)) T :=
  Path.lookup_preserves_typing hσ hr.toLookup hp hwf

/-- Under an exact store, path normalization preserves the complete ordinary
typing derivation, including trailing subsumption. -/
theorem Path.reduce_preserves_source_typing
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.reduce p σ x)
    (ht : Tm.Ty Γ (Tm.path p) T) :
    Tm.Ty Γ (Tm.path (Path.var x)) T := by
  obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
  obtain ⟨X, hx⟩ := Ctx.Binds.exists Γ x
  exact Tm.Ty.sub (Tm.Ty.path (Path.Ty.var hx))
    (.trans (Path.lookup_preserves_singleton_alias hσ hr.toLookup hp) hsub)
    hwf

end LambdaP.Original
