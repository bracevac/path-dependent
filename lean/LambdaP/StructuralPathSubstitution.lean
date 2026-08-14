import LambdaP.StructuralTermTyping
import LambdaP.PathPreservation

/-!
Path substitution for the structural judgments.

The earlier development proves renaming and opening at a variable.  A
dependent application additionally needs the standard substitution lemma in
which the formal parameter is replaced by an arbitrary checked path.  This
module proves that lemma directly for `Path.StructCheck`, `Tau.StructSub`, and
`Tau.StructWf`; it does not assume any store or runtime-path validity
property.
-/

namespace LambdaP

/-! ## Relation and context substitutions -/

/-- A path substitution maps an abstract source relation into a target
relation. -/
abbrev Path.SubstRelHom
    (R : Path n -> Path n -> Prop)
    (E : Path m -> Path m -> Prop) (rho : PathSubst n m) : Prop :=
  forall {p q}, R p q -> E (p.subst rho) (q.subst rho)

/-- Identity substitution preserves a path relation. -/
theorem Path.SubstRelHom.id :
    Path.SubstRelHom R R PathSubst.id := by
  intro p q hpq
  simpa only [Path.subst_id] using hpq

/-- Relation-respecting substitutions are closed under composition. -/
theorem Path.SubstRelHom.comp
    (hρ : Path.SubstRelHom R E ρ)
    (hθ : Path.SubstRelHom E F θ) :
    Path.SubstRelHom R F (ρ.comp θ) := by
  intro p q hpq
  simpa only [Path.subst_comp] using hθ (hρ hpq)

/-- A relation-respecting path substitution lifts through a binder. -/
theorem Path.SubstRelHom.scoped
    (h : Path.SubstRelHom R E rho) :
    Path.SubstRelHom (Path.ScopedLift R) (Path.ScopedLift E) rho.lift := by
  intro p q hpq
  induction hpq with
  | bound => exact .bound
  | old hpq =>
      simpa only [Path.weaken_subst_lift] using
        (Path.ScopedLift.old (h hpq))
  | symm hpq ih => exact .symm ih
  | trans hpq hqr ih1 ih2 => exact .trans ih1 ih2
  | fst hpq ih => exact .fst ih
  | sel hpq ih => exact .sel ih

/-- Structural conversion is natural with respect to path substitution. -/
theorem Tau.StructConv.subst
    (h : Tau.StructConv R d1 d2)
    (hrel : Path.SubstRelHom R E rho) :
    Tau.StructConv E (d1.subst rho) (d2.subst rho) := by
  induction h with
  | refl => exact .refl
  | symm h ih => exact .symm ih
  | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2
  | replace template hpq =>
      simpa only [Tau.open_subst] using
        (Tau.StructConv.replace (template := template.subst rho.lift)
          (hrel hpq))

/-- A structural context substitution maps each source variable to a target
path checked at the correspondingly substituted context type. -/
abbrev Path.StructSubstitution
    (Gamma : Ctx n) (rho : PathSubst n m) (Delta : Ctx m)
    (E : Path m -> Path m -> Prop) : Prop :=
  forall {x T}, Ctx.Binds Gamma x T ->
    Path.StructCheck Delta E (rho x) (Tau.ty (T.subst rho))

/-- Identity is a structural context substitution. -/
theorem Path.StructSubstitution.id :
    Path.StructSubstitution Gamma PathSubst.id Gamma E := by
  intro x T hx
  simpa only [Path.subst_id, Tau.subst, Ty.subst_id] using
    (Path.StructCheck.var (R := E) hx)

/-- Structural context substitutions extend through a dependent binder. -/
theorem Path.StructSubstitution.lift
    (h : Path.StructSubstitution Gamma rho Delta E) :
    Path.StructSubstitution (Gamma.snoc S) rho.lift
      (Delta.snoc (S.subst rho)) (Path.ScopedLift E) := by
  intro x T hx
  cases hx with
  | here =>
      simpa only [PathSubst.lift_zero, Path.subst, Tau.subst,
        Ty.weaken_subst_lift] using
        (Path.StructCheck.var (R := Path.ScopedLift E)
          (Ctx.Binds.here (Γ := Delta) (T := S.subst rho)))
  | there hx =>
      have hold := h hx
      have hweak := hold.renameExact
        (Renaming.weaken (S := S.subst rho))
        (Path.RelHom.weaken (R := E))
      simpa only [PathSubst.lift_succ, Tau.subst,
        Ty.weaken_subst_lift] using hweak

private abbrev PathSubstMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Gamma R p d) : Prop :=
  forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
    Path.StructSubstitution Gamma rho Delta E ->
    Path.SubstRelHom R E rho ->
    Path.StructCheck Delta E (p.subst rho) (d.subst rho)

private abbrev StructSubstMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop :=
  forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
    Path.StructSubstitution Gamma rho Delta E ->
    Path.SubstRelHom R E rho ->
    Tau.StructSub Delta E (d1.subst rho) (d2.subst rho)

mutual

/-- Structural path checking is stable under a structural path
substitution. -/
theorem Path.StructCheck.subst
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {k : Kind} {p : Path n} {d : Tau n k}
    (h : Path.StructCheck Gamma R p d) :
    forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
        {E : Path m -> Path m -> Prop},
      Path.StructSubstitution Gamma rho Delta E ->
      Path.SubstRelHom R E rho ->
      Path.StructCheck Delta E (p.subst rho) (d.subst rho) := by
  induction h using Path.StructCheck.rec
      (motive_2 := StructSubstMotive) with
  | var hb =>
      intro m rho Delta E hctx hrel
      exact hctx hb
  | sub hp hs ihp ihs =>
      intro m rho Delta E hctx hrel
      exact .sub (ihp hctx hrel) (ihs hctx hrel)
  | promote hp hs ihp ihs =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Path.StructCheck.promote (ihp hctx hrel) (ihs hctx hrel)
  | fst hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst] using
        Path.StructCheck.fst (ih hctx hrel)
  | sel_r hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst, Tau.open_subst] using
        Path.StructCheck.sel_r (ih hctx hrel)
  | sel_l hp htail hne ihp ihtail =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst] using
        Path.StructCheck.sel_l (ihp hctx hrel) (ihtail hctx hrel) hne
  | refl =>
      intro m rho Delta E hctx hrel
      exact .refl
  | trans h1 h2 ih1 ih2 =>
      intro m rho Delta E hctx hrel
      exact .trans (ih1 hctx hrel) (ih2 hctx hrel)
  | conv hconv =>
      intro m rho Delta E hctx hrel
      exact .conv (hconv.subst hrel)
  | bot =>
      intro m rho Delta E hctx hrel
      simp only [Tau.subst, Ty.subst]
      exact .bot
  | top =>
      intro m rho Delta E hctx hrel
      simp only [Tau.subst, Ty.subst]
      exact .top
  | widen hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.widen (ih hctx hrel)
  | symm hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.symm (ih hctx hrel)
  | sel_hi hp hbounds ihp ihbounds =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.sel_hi (ihp hctx hrel) (ihbounds hctx hrel)
  | sel_lo hp hbounds ihp ihbounds =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.sel_lo (ihp hctx hrel) (ihbounds hctx hrel)
  | «fun» hdom hcod ihdom ihcod =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst] using
        Tau.StructSub.fun (ihdom hctx hrel)
          (ihcod hctx.lift hrel.scoped)
  | pair_fst hfst ihfst =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst] using
        Tau.StructSub.pair_fst (ihfst hctx hrel)
  | pair_single_member hp hsnd hopen ihp ihsnd ihopen =>
      intro m rho Delta E hctx hrel
      have hopen' := ihopen hctx hrel
      rw [Tau.open_subst, Tau.open_subst] at hopen'
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.pair_single_member (ihp hctx hrel)
          (ihsnd hctx.lift hrel.scoped) hopen'
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst] using
        Tau.StructSub.bounds (ihlo hctx hrel) (ihhi hctx hrel)
          (ihnonempty hctx hrel)

/-- Structural generalized subtyping is stable under the same structural
path substitution. -/
theorem Tau.StructSub.subst
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {k : Kind} {d1 d2 : Tau n k}
    (h : Tau.StructSub Gamma R d1 d2) :
    forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
        {E : Path m -> Path m -> Prop},
      Path.StructSubstitution Gamma rho Delta E ->
      Path.SubstRelHom R E rho ->
      Tau.StructSub Delta E (d1.subst rho) (d2.subst rho) := by
  induction h using Tau.StructSub.rec
      (motive_1 := PathSubstMotive) with
  | var hb =>
      intro m rho Delta E hctx hrel
      exact hctx hb
  | sub hp hs ihp ihs =>
      intro m rho Delta E hctx hrel
      exact .sub (ihp hctx hrel) (ihs hctx hrel)
  | promote hp hs ihp ihs =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Path.StructCheck.promote (ihp hctx hrel) (ihs hctx hrel)
  | fst hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst] using
        Path.StructCheck.fst (ih hctx hrel)
  | sel_r hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst, Tau.open_subst] using
        Path.StructCheck.sel_r (ih hctx hrel)
  | sel_l hp htail hne ihp ihtail =>
      intro m rho Delta E hctx hrel
      simpa only [Path.subst, Tau.subst, Ty.subst] using
        Path.StructCheck.sel_l (ihp hctx hrel) (ihtail hctx hrel) hne
  | refl =>
      intro m rho Delta E hctx hrel
      exact .refl
  | trans h1 h2 ih1 ih2 =>
      intro m rho Delta E hctx hrel
      exact .trans (ih1 hctx hrel) (ih2 hctx hrel)
  | conv hconv =>
      intro m rho Delta E hctx hrel
      exact .conv (hconv.subst hrel)
  | bot =>
      intro m rho Delta E hctx hrel
      simp only [Tau.subst, Ty.subst]
      exact .bot
  | top =>
      intro m rho Delta E hctx hrel
      simp only [Tau.subst, Ty.subst]
      exact .top
  | widen hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.widen (ih hctx hrel)
  | symm hp ih =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.symm (ih hctx hrel)
  | sel_hi hp hbounds ihp ihbounds =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.sel_hi (ihp hctx hrel) (ihbounds hctx hrel)
  | sel_lo hp hbounds ihp ihbounds =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.sel_lo (ihp hctx hrel) (ihbounds hctx hrel)
  | «fun» hdom hcod ihdom ihcod =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst] using
        Tau.StructSub.fun (ihdom hctx hrel)
          (ihcod hctx.lift hrel.scoped)
  | pair_fst hfst ihfst =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst, Ty.subst] using
        Tau.StructSub.pair_fst (ihfst hctx hrel)
  | pair_single_member hp hsnd hopen ihp ihsnd ihopen =>
      intro m rho Delta E hctx hrel
      have hopen' := ihopen hctx hrel
      rw [Tau.open_subst, Tau.open_subst] at hopen'
      simpa only [Tau.subst, Ty.subst, Path.subst] using
        Tau.StructSub.pair_single_member (ihp hctx hrel)
          (ihsnd hctx.lift hrel.scoped) hopen'
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro m rho Delta E hctx hrel
      simpa only [Tau.subst] using
        Tau.StructSub.bounds (ihlo hctx hrel) (ihhi hctx hrel)
          (ihnonempty hctx hrel)

end

/-! ## Structural well-formedness and one-binder opening -/

/-- Structural well-formedness is stable under structural path
substitution. -/
theorem Tau.StructWf.subst
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {k : Kind} {d : Tau n k}
    (h : Tau.StructWf Gamma R d) :
    forall {m : Nat} {rho : PathSubst n m} {Delta : Ctx m}
        {E : Path m -> Path m -> Prop},
      Path.StructSubstitution Gamma rho Delta E ->
      Path.SubstRelHom R E rho ->
      Tau.StructWf Delta E (d.subst rho) := by
  induction h with
  | bot =>
      intro m rho Delta E hctx hrel
      exact .bot
  | top =>
      intro m rho Delta E hctx hrel
      exact .top
  | path hp =>
      intro m rho Delta E hctx hrel
      exact .path (hp.subst hctx hrel)
  | sel hp =>
      intro m rho Delta E hctx hrel
      exact .sel (hp.subst hctx hrel)
  | «fun» hS hT ihS ihT =>
      intro m rho Delta E hctx hrel
      exact .fun (ihS hctx hrel) (ihT hctx.lift hrel.scoped)
  | pair hS hd ihS ihd =>
      intro m rho Delta E hctx hrel
      exact .pair (ihS hctx hrel) (ihd hctx.lift hrel.scoped)
  | bounds_wf hS hT hsub ihS ihT =>
      intro m rho Delta E hctx hrel
      exact .bounds_wf (ihS hctx hrel) (ihT hctx hrel)
        (hsub.subst hctx hrel)

/-- Structural context substitutions are closed under composition. -/
theorem Path.StructSubstitution.comp
    {Gamma : Ctx n} {Delta : Ctx m} {Xi : Ctx l}
    {rho : PathSubst n m} {theta : PathSubst m l}
    {E : Path m -> Path m -> Prop} {F : Path l -> Path l -> Prop}
    (hρ : Path.StructSubstitution Gamma rho Delta E)
    (hθ : Path.StructSubstitution Delta theta Xi F)
    (hrel : Path.SubstRelHom E F theta) :
    Path.StructSubstitution Gamma (rho.comp theta) Xi F := by
  intro x T hx
  have h := (hρ hx).subst hθ hrel
  simpa only [PathSubst.comp_apply, Tau.subst, Ty.subst_comp] using h

/-- Replacing the newest context variable by an arbitrary path checked at
the binder type is a structural context substitution. -/
theorem Path.StructSubstitution.openAt
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {q : Path n} {S : LambdaP.Ty n}
    (hq : Path.StructCheck Gamma R q (Tau.ty S)) :
    Path.StructSubstitution (Gamma.snoc S) (PathSubst.openAt q) Gamma R := by
  intro x T hx
  cases hx with
  | here =>
      simpa only [PathSubst.openAt_zero, Tau.subst,
        LambdaP.Ty.weaken_subst_openAt] using hq
  | there hx =>
      simpa only [PathSubst.openAt_succ, Tau.subst,
        LambdaP.Ty.weaken_subst_openAt] using
        (Path.StructCheck.var (R := R) hx)

/-- Opening a scoped relation at one path maps it back to the ambient
relation. -/
theorem Path.SubstRelHom.openAt
    {n : Nat} {R : Path n -> Path n -> Prop}
    (hR : Path.IsEquivCongr R) (q : Path n) :
    Path.SubstRelHom (Path.ScopedLift R) R (PathSubst.openAt q) := by
  intro p r hpr
  exact hpr.open_paths hR (hR.refl q)

/-- Standard dependent opening for structural well-formedness at an
arbitrary checked path. -/
theorem Tau.StructWf.open_path
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S : LambdaP.Ty n} {q : Path n} {k : Kind}
    {d : Tau (n + 1) k}
    (h : Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d)
    (hR : Path.IsEquivCongr R)
    (hq : Path.StructCheck Gamma R q (Tau.ty S)) :
    Tau.StructWf Gamma R (d.open q) := by
  exact h.subst (Path.StructSubstitution.openAt hq)
    (Path.SubstRelHom.openAt hR q)

end LambdaP
