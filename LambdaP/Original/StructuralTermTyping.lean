import LambdaP.Original.StructuralRuntimeTyping

/-!
Structural well-formedness and term checking.

This file completes the proof-only structural layer begun in
`StructuralRuntimeTyping`.  Every source well-formedness and term-typing
constructor is represented directly.  Path and subtyping premises use the
structural judgments, and recursive premises below functions, pairs,
abstractions, and lets use `Path.ScopedLift`.

The source pair-value rules retain their exact `Ctx.Binds` premises.  Their
result types mention only the selected variables, not the types synthesized
by those lookups; after a structural renaming, totality of lookup in an
intrinsically sized context supplies the required target witnesses.
-/

namespace LambdaP.Original

/-! ## Structural well-formedness -/

/-- Generalized-type well-formedness with structural path and subtyping
premises. -/
inductive Tau.StructWf : {n : Nat} -> (Gamma : Ctx n) ->
    (R : Path n -> Path n -> Prop) -> {k : Kind} -> Tau n k -> Prop where
| bot : Tau.StructWf Gamma R (Tau.ty Ty.Bot)
| top : Tau.StructWf Gamma R (Tau.ty Ty.Top)
| path :
    Path.StructCheck Gamma R p (Tau.ty T) ->
    Tau.StructWf Gamma R (Tau.ty (Ty.Single p))
| sel :
    Path.StructCheck Gamma R p
      (Tau.ty (Ty.Pair S A (Tau.intv T U))) ->
    Tau.StructWf Gamma R (Tau.ty (Ty.Single (p.sel A)))
| «fun» :
    Tau.StructWf Gamma R (Tau.ty S) ->
    Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) (Tau.ty T) ->
    Tau.StructWf Gamma R (Tau.ty (Ty.Fun S T))
| pair :
    Tau.StructWf Gamma R (Tau.ty S) ->
    Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d ->
    Tau.StructWf Gamma R (Tau.ty (Ty.Pair S a d))
| bounds_wf :
    Tau.StructWf Gamma R (Tau.ty S) ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tau.StructSub Gamma R (Tau.ty S) (Tau.ty T) ->
    Tau.StructWf Gamma R (Tau.intv S T)

/-- Every source well-formedness derivation embeds, recursively including
premises below binders. -/
theorem Tau.StructWf.of_source
    {n : Nat} {Gamma : Ctx n} {k : Kind} {d : Tau n k}
    (h : Tau.Wf Gamma d) :
    forall R : Path n -> Path n -> Prop, Tau.StructWf Gamma R d := by
  induction h with
  | bot => intro R; exact .bot
  | top => intro R; exact .top
  | path hp =>
      intro R
      exact .path (Path.StructCheck.of_source hp R)
  | sel hp =>
      intro R
      exact .sel (Path.StructCheck.of_source hp R)
  | «fun» hS hT ihS ihT =>
      intro R
      exact .fun (ihS R) (ihT (Path.ScopedLift R))
  | pair hS hd ihS ihd =>
      intro R
      exact .pair (ihS R) (ihd (Path.ScopedLift R))
  | bounds_wf hS hT hsub ihS ihT =>
      intro R
      exact .bounds_wf (ihS R) (ihT R)
        (Tau.StructSub.of_source hsub R)

/-! ## Structural term checking -/

/-- Term checking with all source constructors exposed and every subsidiary
judgment interpreted structurally. -/
inductive Tm.StructCheck : {n : Nat} -> (Gamma : Ctx n) ->
    (R : Path n -> Path n -> Prop) -> Tm n ->
    LambdaP.Original.Ty n -> Prop where
| path :
    Path.StructCheck Gamma R p (Tau.ty T) ->
    Tm.StructCheck Gamma R (Tm.path p) (Ty.Single p)
| abs :
    Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T ->
    Tau.StructWf Gamma R (Tau.ty S) ->
    Tm.StructCheck Gamma R (Tm.abs S t) (Ty.Fun S T)
| app :
    Tm.StructCheck Gamma R (Tm.path p) (Ty.Fun S T) ->
    Tm.StructCheck Gamma R (Tm.path q) S ->
    Tm.StructCheck Gamma R (Tm.app p q) (T.open q)
| pair :
    Ctx.Binds Gamma y S ->
    Ctx.Binds Gamma z T ->
    Tm.StructCheck Gamma R (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Gamma y S ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructCheck Gamma R (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)
| «let» :
    Tm.StructCheck Gamma R s S ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T.weaken ->
    Tm.StructCheck Gamma R (Tm.let s t) T
| typed :
    Tm.StructCheck Gamma R t T ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructCheck Gamma R (Tm.typed t T) T
| sub :
    Tm.StructCheck Gamma R t S ->
    Tau.StructSub Gamma R (Tau.ty S) (Tau.ty T) ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructCheck Gamma R t T

/-- Every source term-typing derivation embeds at every abstract relation. -/
theorem Tm.StructCheck.of_source
    {n : Nat} {Gamma : Ctx n} {t : Tm n}
    {T : LambdaP.Original.Ty n}
    (h : Tm.Ty Gamma t T) :
    forall R : Path n -> Path n -> Prop,
      Tm.StructCheck Gamma R t T := by
  induction h with
  | path hp =>
      intro R
      exact .path (Path.StructCheck.of_source hp R)
  | abs ht hwf iht =>
      intro R
      exact .abs (iht (Path.ScopedLift R))
        (Tau.StructWf.of_source hwf R)
  | app hp hq ihp ihq =>
      intro R
      exact .app (ihp R) (ihq R)
  | pair hy hz =>
      intro R
      exact .pair hy hz
  | tpair hy hwf =>
      intro R
      exact .tpair hy (Tau.StructWf.of_source hwf R)
  | «let» hs hwf ht ihs iht =>
      intro R
      exact .let (ihs R) (Tau.StructWf.of_source hwf R)
        (iht (Path.ScopedLift R))
  | typed ht hwf iht =>
      intro R
      exact .typed (iht R) (Tau.StructWf.of_source hwf R)
  | sub ht hsub hwf iht =>
      intro R
      exact .sub (iht R) (Tau.StructSub.of_source hsub R)
        (Tau.StructWf.of_source hwf R)

/-! ## Exact relation-respecting renaming -/

/-- Structural well-formedness is preserved by an exact context renaming
and a compatible abstract-relation morphism. -/
theorem Tau.StructWf.renameExact
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {k : Kind} {d : Tau n k}
    (h : Tau.StructWf Gamma R d) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
      Renaming Gamma f Delta ->
      Path.RelHom R E f ->
      Tau.StructWf Delta E (d.rename f) := by
  induction h with
  | bot =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        (Tau.StructWf.bot (Gamma := Delta) (R := E))
  | top =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        (Tau.StructWf.top (Gamma := Delta) (R := E))
  | path hp =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.StructWf.path (hp.renameExact rho hrel)
  | sel hp =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.StructWf.sel (hp.renameExact rho hrel)
  | «fun» hS hT ihS ihT =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        Tau.StructWf.fun (ihS rho hrel)
          (ihT (Renaming.ext rho) hrel.scoped)
  | pair hS hd ihS ihd =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        Tau.StructWf.pair (ihS rho hrel)
          (ihd (Renaming.ext rho) hrel.scoped)
  | bounds_wf hS hT hsub ihS ihT =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename] using
        Tau.StructWf.bounds_wf (ihS rho hrel) (ihT rho hrel)
          (hsub.renameExact rho hrel)

/-- Structural term checking is preserved by exact context renaming. -/
theorem Tm.StructCheck.renameExact
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {t : Tm n} {T : LambdaP.Original.Ty n}
    (h : Tm.StructCheck Gamma R t T) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
      Renaming Gamma f Delta ->
      Path.RelHom R E f ->
      Tm.StructCheck Delta E (t.rename f) (T.rename f) := by
  induction h with
  | path hp =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename, Path.rename] using
        Tm.StructCheck.path (hp.renameExact rho hrel)
  | abs ht hwf iht =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename] using
        Tm.StructCheck.abs
          (iht (Renaming.ext rho) hrel.scoped)
          (hwf.renameExact rho hrel)
  | app hp hq ihp ihq =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename, Ty.open_rename] using
        Tm.StructCheck.app (ihp rho hrel) (ihq rho hrel)
  | pair hy hz =>
      intro m f Delta E rho hrel
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.StructCheck.pair (R := E) (rho hy) (rho hz)
  | tpair hy hwf =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Def.rename, LambdaP.Original.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.StructCheck.tpair (R := E) (rho hy)
          (hwf.renameExact rho hrel)
  | «let» hs hwf ht ihs iht =>
      intro m f Delta E rho hrel
      simp only [Tm.rename]
      apply Tm.StructCheck.let (ihs rho hrel) (hwf.renameExact rho hrel)
      rw [Ty.weaken_rename]
      exact iht (Renaming.ext rho) hrel.scoped
  | typed ht hwf iht =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename] using
        Tm.StructCheck.typed (iht rho hrel) (hwf.renameExact rho hrel)
  | sub ht hsub hwf iht =>
      intro m f Delta E rho hrel
      exact Tm.StructCheck.sub (iht rho hrel)
        (hsub.renameExact rho hrel) (hwf.renameExact rho hrel)

/-! ## Structural renaming -/

/-- Every intrinsically scoped variable has some exact context lookup.  The
lookup type is not fixed by either pair-value conclusion, so this totality
fact is sufficient to preserve their source-shaped `Ctx.Binds` premises. -/
private theorem Ctx.target_binding (Gamma : Ctx n) (x : Fin n) :
    exists T, Ctx.Binds Gamma x T := by
  induction Gamma with
  | nil => exact Fin.elim0 x
  | snoc Gamma S ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨S.weaken, .here⟩
      · obtain ⟨T, hT⟩ := ih y
        exact ⟨T.weaken, .there hT⟩

/-- Structural well-formedness is stable under a structural variable
environment and a compatible relation morphism. -/
theorem Tau.StructWf.rename
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {k : Kind} {d : Tau n k}
    (h : Tau.StructWf Gamma R d) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
      Path.StructRenaming Gamma f Delta E ->
      Path.RelHom R E f ->
      Tau.StructWf Delta E (d.rename f) := by
  induction h with
  | bot =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        (Tau.StructWf.bot (Gamma := Delta) (R := E))
  | top =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        (Tau.StructWf.top (Gamma := Delta) (R := E))
  | path hp =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.StructWf.path (hp.rename rho hrel)
  | sel hp =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.StructWf.sel (hp.rename rho hrel)
  | «fun» hS hT ihS ihT =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        Tau.StructWf.fun (ihS rho hrel)
          (ihT rho.ext hrel.scoped)
  | pair hS hd ihS ihd =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename, Ty.rename] using
        Tau.StructWf.pair (ihS rho hrel)
          (ihd rho.ext hrel.scoped)
  | bounds_wf hS hT hsub ihS ihT =>
      intro m f Delta E rho hrel
      simpa only [Tau.rename] using
        Tau.StructWf.bounds_wf (ihS rho hrel) (ihT rho hrel)
          (hsub.rename rho hrel)

/-- Structural term checking is stable under structural renaming. -/
theorem Tm.StructCheck.rename
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {t : Tm n} {T : LambdaP.Original.Ty n}
    (h : Tm.StructCheck Gamma R t T) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m}
      {E : Path m -> Path m -> Prop},
      Path.StructRenaming Gamma f Delta E ->
      Path.RelHom R E f ->
      Tm.StructCheck Delta E (t.rename f) (T.rename f) := by
  induction h with
  | path hp =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename, Path.rename] using
        Tm.StructCheck.path (hp.rename rho hrel)
  | abs ht hwf iht =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename] using
        Tm.StructCheck.abs
          (iht rho.ext hrel.scoped)
          (hwf.rename rho hrel)
  | app hp hq ihp ihq =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename, Ty.rename, Ty.open_rename] using
        Tm.StructCheck.app (ihp rho hrel) (ihq rho hrel)
  | pair hy hz =>
      intro m f Delta E rho hrel
      obtain ⟨Sy, hy'⟩ := Ctx.target_binding Delta (f _)
      obtain ⟨Sz, hz'⟩ := Ctx.target_binding Delta (f _)
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.StructCheck.pair (R := E) hy' hz'
  | tpair hy hwf =>
      intro m f Delta E rho hrel
      obtain ⟨Sy, hy'⟩ := Ctx.target_binding Delta (f _)
      simpa only [Tm.rename, Def.rename, LambdaP.Original.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.StructCheck.tpair (R := E) hy' (hwf.rename rho hrel)
  | «let» hs hwf ht ihs iht =>
      intro m f Delta E rho hrel
      simp only [Tm.rename]
      apply Tm.StructCheck.let (ihs rho hrel) (hwf.rename rho hrel)
      rw [Ty.weaken_rename]
      exact iht rho.ext hrel.scoped
  | typed ht hwf iht =>
      intro m f Delta E rho hrel
      simpa only [Tm.rename] using
        Tm.StructCheck.typed (iht rho hrel) (hwf.rename rho hrel)
  | sub ht hsub hwf iht =>
      intro m f Delta E rho hrel
      exact Tm.StructCheck.sub (iht rho hrel)
        (hsub.rename rho hrel) (hwf.rename rho hrel)

/-! ## Path-term inversion -/

/-- The information retained by typing a path term: a structural
classification of the path, the complete singleton-to-result subtyping
chain, and well-formedness of the observed result type. -/
inductive Tm.StructPathPackage
    (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    (p : Path n) (T : LambdaP.Original.Ty n) : Prop where
| intro (precise : LambdaP.Original.Ty n) :
    Path.StructCheck Gamma R p (Tau.ty precise) ->
    Tau.StructSub Gamma R
      (Tau.ty (Ty.Single p)) (Tau.ty T) ->
    Tau.StructWf Gamma R (Tau.ty T) ->
    Tm.StructPathPackage Gamma R p T

/-- Inverting a structurally checked path term collects all trailing
subsumption into the singleton-to-result chain. -/
theorem Tm.StructCheck.path_inversion
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {t : Tm n} {T : LambdaP.Original.Ty n}
    (h : Tm.StructCheck Gamma R t T) :
    forall {p : Path n}, t = Tm.path p ->
      Tm.StructPathPackage Gamma R p T := by
  induction h with
  | path hp =>
      intro p heq
      cases heq
      exact ⟨_, hp, .refl, .path hp⟩
  | abs ht hwf iht =>
      intro p heq
      cases heq
  | app hp hq ihp ihq =>
      intro p heq
      cases heq
  | pair hy hz =>
      intro p heq
      cases heq
  | tpair hy hwf =>
      intro p heq
      cases heq
  | «let» hs hwf ht ihs iht =>
      intro p heq
      cases heq
  | typed ht hwf iht =>
      intro p heq
      cases heq
  | sub ht hsub hwf iht =>
      intro p heq
      cases iht heq with
      | intro U hp hbase hbaseWf =>
          exact .intro U hp (.trans hbase hsub) hwf

/-! ## One-binder opening -/

/-- Exact context lookup is sufficient for opening structural
well-formedness. -/
theorem Tau.StructWf.open_var_exact
    (h : Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d)
    (hR : Path.IsEquivCongr R)
    (hx : Ctx.Binds Gamma x S) :
    Tau.StructWf Gamma R (d.rename (FinFun.openAt x)) :=
  h.renameExact (Renaming.open hx) (Path.RelHom.openAt hR x)

/-- Exact context lookup is sufficient for opening structural term
checking. -/
theorem Tm.StructCheck.open_var_exact
    (h : Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T)
    (hR : Path.IsEquivCongr R)
    (hx : Ctx.Binds Gamma x S) :
    Tm.StructCheck Gamma R (t.open x) (T.rename (FinFun.openAt x)) := by
  simpa only [Tm.open] using
    h.renameExact (Renaming.open hx) (Path.RelHom.openAt hR x)

/-- Structural checking of the replacement variable is sufficient for
opening well-formedness. -/
theorem Tau.StructWf.open_var
    (h : Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d)
    (hR : Path.IsEquivCongr R)
    (hx : Path.StructCheck Gamma R (.var x) (Tau.ty S)) :
    Tau.StructWf Gamma R (d.rename (FinFun.openAt x)) :=
  h.rename (Path.StructRenaming.openAt hx) (Path.RelHom.openAt hR x)

/-- Structural checking of the replacement variable is sufficient for
opening a term derivation. -/
theorem Tm.StructCheck.open_var
    (h : Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T)
    (hR : Path.IsEquivCongr R)
    (hx : Path.StructCheck Gamma R (.var x) (Tau.ty S)) :
    Tm.StructCheck Gamma R (t.open x) (T.rename (FinFun.openAt x)) := by
  simpa only [Tm.open] using
    h.rename (Path.StructRenaming.openAt hx) (Path.RelHom.openAt hR x)

/-- Operational form of well-formedness opening.  The replacement path need
only have some structural classification and singleton subtyping to the
binder type. -/
theorem Tau.StructWf.open_var_of_singleton
    (h : Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d)
    (hR : Path.IsEquivCongr R)
    (hx : Path.StructCheck Gamma R (.var x) (Tau.ty U))
    (hsub : Tau.StructSub Gamma R
      (Tau.ty (Ty.Single (.var x))) (Tau.ty S)) :
    Tau.StructWf Gamma R (d.rename (FinFun.openAt x)) :=
  h.open_var hR (Path.StructCheck.promote hx hsub)

/-- Operational one-binder opening.  Its hypothesis is exactly the package
obtained by inverting a checked path term: some precise/checkable type for
`x`, the full `{x} <: S` chain, and result well-formedness. -/
theorem Tm.StructCheck.open_var_of_path_package
    (h : Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T)
    (hR : Path.IsEquivCongr R)
    (hx : Tm.StructPathPackage Gamma R (.var x) S) :
    Tm.StructCheck Gamma R (t.open x) (T.rename (FinFun.openAt x)) := by
  cases hx with
  | intro U hx hsub hwf =>
      exact h.open_var hR (Path.StructCheck.promote hx hsub)

/-- Convenient form when the checked path term itself, rather than its
inversion package, is available. -/
theorem Tm.StructCheck.open_var_of_path_term
    (h : Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T)
    (hR : Path.IsEquivCongr R)
    (hx : Tm.StructCheck Gamma R (Tm.path (.var x)) S) :
    Tm.StructCheck Gamma R (t.open x) (T.rename (FinFun.openAt x)) :=
  h.open_var_of_path_package hR (hx.path_inversion rfl)

end LambdaP.Original
