import LambdaPHistory.DeepRuntimeTyping

/-!
Path checking with singleton promotion.

`Path.DeepCheck` may eliminate a path once that judgment itself exposes a
pair type.  A deeply typed path term, however, records subsumption from the
singleton `{p}` to its observed type in `Tm.DeepCheck`; that chain cannot in
general be turned back into `Path.DeepCheck p T`.  `Path.PromotedCheck` adds
exactly this bridge and then permits the usual eliminations.

The final theorem tests the bridge at the point where it is needed: opening a
source path derivation below one binder when the replacement variable checks
at the binder type only through deep term typing.
-/

namespace LambdaPHistory

/-- Deep path checking extended with proper-type promotion from deep typing
of the corresponding path term. -/
inductive Path.PromotedCheck (Gamma : Ctx n) (R : Path.ConvRel n) :
    Path n -> Tau n k -> Prop where
| of_deep :
    Path.DeepCheck Gamma R p d ->
    Path.PromotedCheck Gamma R p d
| promote :
    Tm.DeepCheck Gamma R (Tm.path p) T ->
    Path.PromotedCheck Gamma R p (Tau.ty T)
| fst :
    Path.PromotedCheck Gamma R p
      (Tau.ty (Ty.Pair S a d)) ->
    Path.PromotedCheck Gamma R p.fst (Tau.ty S)
| sel_r :
    Path.PromotedCheck Gamma R p
      (Tau.ty (Ty.Pair S a d)) ->
    Path.PromotedCheck Gamma R (p.sel a) (d.open p.fst)
| sel_l :
    Path.PromotedCheck Gamma R p
      (Tau.ty (Ty.Pair S b d')) ->
    Path.PromotedCheck Gamma R (p.fst.sel a) d ->
    a ≠ b ->
    Path.PromotedCheck Gamma R (p.sel a) d

/-! ## Bridges to the existing deep judgments -/

theorem Path.DeepCheck.toPromoted
    (h : Path.DeepCheck Gamma R p d) :
    Path.PromotedCheck Gamma R p d :=
  .of_deep h

/-- The new rule is precisely the path-term-to-path bridge. -/
theorem Tm.DeepCheck.toPromotedPath
    (h : Tm.DeepCheck Gamma R (Tm.path p) T) :
    Path.PromotedCheck Gamma R p (Tau.ty T) :=
  .promote h

/-- Existing deep path checking always yields promoted checking at the
singleton type through path-term introduction. -/
theorem Path.DeepCheck.toPromotedSingleton
    (h : Path.DeepCheck Gamma R p (Tau.ty U)) :
    Path.PromotedCheck Gamma R p (Tau.ty (Ty.Single p)) :=
  .promote (.path h)

/-- Explicit singleton-chain form of promotion. -/
theorem Path.PromotedCheck.promote_of_chain
    (hp : Path.DeepCheck Gamma R p (Tau.ty U))
    (hs : Tau.DeepSub Gamma R
      (Tau.ty (Ty.Single p)) (Tau.ty T))
    (hwf : Tau.DeepWf Gamma R (Tau.ty T)) :
    Path.PromotedCheck Gamma R p (Tau.ty T) :=
  .promote (.sub (.path hp) hs hwf)

private theorem Tm.DeepCheck.path_result_wf_for_promotion
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {t : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R t T) :
    ∀ {p : Path n}, t = Tm.path p ->
      Tau.DeepWf Gamma R (Tau.ty T) := by
  induction h with
  | path hp => intro p heq; exact .path hp
  | abs _ _ _ => intro p heq; cases heq
  | app _ _ _ _ => intro p heq; cases heq
  | pair _ _ => intro p heq; cases heq
  | tpair _ _ => intro p heq; cases heq
  | «let» _ _ _ _ _ => intro p heq; cases heq
  | typed _ _ _ => intro p heq; cases heq
  | sub _ _ hwf _ => intro p heq; exact hwf

/-- Deep typing of a path term is equivalent to a structural path premise,
the singleton-to-result deep-subtyping chain, and result well-formedness. -/
theorem Tm.DeepCheck.path_iff_singleton_chain
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {p : Path n} {T : LambdaPHistory.Ty n} :
    Tm.DeepCheck Gamma R (Tm.path p) T ↔
      ∃ U,
        Path.DeepCheck Gamma R p (Tau.ty U) ∧
        Tau.DeepSub Gamma R
          (Tau.ty (Ty.Single p)) (Tau.ty T) ∧
        Tau.DeepWf Gamma R (Tau.ty T) := by
  constructor
  · intro h
    obtain ⟨U, hp, hs⟩ := h.path_inversion rfl
    exact ⟨U, hp, hs, h.path_result_wf_for_promotion rfl⟩
  · rintro ⟨U, hp, hs, hwf⟩
    exact .sub (.path hp) hs hwf

/-- Chain-oriented introduction form, equivalent to `promote` by
`Tm.DeepCheck.path_iff_singleton_chain`. -/
theorem Path.PromotedCheck.promote_iff_chain
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {p : Path n} {T : LambdaPHistory.Ty n} :
    Tm.DeepCheck Gamma R (Tm.path p) T ↔
      ∃ U,
        Path.DeepCheck Gamma R p (Tau.ty U) ∧
        Tau.DeepSub Gamma R
          (Tau.ty (Ty.Single p)) (Tau.ty T) ∧
        Tau.DeepWf Gamma R (Tau.ty T) :=
  Tm.DeepCheck.path_iff_singleton_chain

/-!
There is intentionally no converse from an arbitrary proper
`Path.PromotedCheck` derivation to `Tm.DeepCheck` at the same proper type.
After a promoted `fst` or `sel`, the existing term judgment can introduce
only the resulting singleton and has no rule reconstructing the eliminated
proper type.  That missing converse is exactly why this small extension is
needed; the promotion premise itself is nevertheless characterized completely
by `path_iff_singleton_chain` above.
-/

/-! ## One-binder source opening -/

private theorem Ty.weaken_rename_openAt_var
    (T : LambdaPHistory.Ty n) (x : Fin n) :
    T.weaken.rename (FinFun.openAt x) = T := by
  rw [LambdaPHistory.Ty.weaken, Ty.rename_rename,
    FinFun.openAt_weaken, Ty.rename_id]

/-- A source context renaming whose variable cases are justified by promoted
checking rather than exact target-context lookup. -/
abbrev Path.PromotedRenaming
    (Gamma : Ctx n) (f : FinFun n m) (Delta : Ctx m)
    (R : Path.ConvRel m) : Prop :=
  ∀ {x T}, Ctx.Binds Gamma x T ->
    Path.PromotedCheck Delta R (Path.var (f x))
      (Tau.ty (T.rename f))

/-- Source path typing is natural with respect to a promoted variable
environment. -/
theorem Path.Ty.rename_promoted
    (h : Path.Ty Gamma p d)
    (rho : Path.PromotedRenaming Gamma f Delta R) :
    Path.PromotedCheck Delta R (p.rename f) (d.rename f) := by
  induction h with
  | var hb =>
      simpa only [Path.rename, Tau.rename] using rho hb
  | fst hp ih =>
      simpa only [Path.rename, Tau.rename, Ty.rename] using
        Path.PromotedCheck.fst (ih rho)
  | sel_r hp ih =>
      simpa only [Path.rename, Tau.rename, Ty.rename, Tau.open_rename] using
        Path.PromotedCheck.sel_r (ih rho)
  | sel_l hp htail hne ihp ihtail =>
      simpa only [Path.rename, Tau.rename, Ty.rename] using
        Path.PromotedCheck.sel_l (ihp rho) (ihtail rho) hne

/-- Open a source path derivation with a variable which is known at the
binder type through deep *term* checking.

The variable case is the new content: the newest source variable uses
`promote`, while old variables still use ordinary context lookup.  Projection
and both selection rules then proceed structurally. -/
theorem Path.Ty.open_var_promoted
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {B : LambdaPHistory.Ty n} {p : Path (n + 1)}
    {k : Kind} {d : Tau (n + 1) k} {x : Fin n}
    (h : Path.Ty (Gamma.snoc B) p d)
    (hx : Tm.DeepCheck Gamma R (Tm.path (Path.var x)) B) :
    Path.PromotedCheck Gamma R
      (p.rename (FinFun.openAt x))
      (d.rename (FinFun.openAt x)) := by
  apply h.rename_promoted
  intro y T hy
  cases hy with
  | here =>
      simpa only [FinFun.openAt_zero, Path.rename, Tau.rename,
        Ty.weaken_rename_openAt_var] using
        (Path.PromotedCheck.promote hx)
  | there hy =>
      have hold : Path.DeepCheck Gamma R (Path.var _)
          (Tau.ty _) := Path.DeepCheck.var hy
      simpa only [FinFun.openAt_succ, Path.rename, Tau.rename,
        Ty.weaken_rename_openAt_var] using
        (Path.PromotedCheck.of_deep hold)

end LambdaPHistory
