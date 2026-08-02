import LambdaPHistory.DeepRuntimeTyping

/-!
Big-step path replacement for the full-syntax deep checking prototype.

This is the first computational preservation case at the stronger invariant.
It does not use a substitution theorem: a resolving path is runtime-equivalent
to its result location, and the path-term inversion exposes the complete
subtyping suffix from the original singleton.
-/

namespace LambdaPHistory

/-- Deep typing of a path term always makes its externally observed result
well formed.  The base singleton is well formed from the same structural path
checking derivation; every trailing subsumption rule records its target
well-formedness explicitly. -/
private theorem Tm.DeepCheck.path_result_wf_of_eq
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {t : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R t T) :
    forall {p : Path n}, t = Tm.path p ->
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

theorem Tm.DeepCheck.path_result_wf
    {n : Nat} {Gamma : Ctx n} {R : Path.ConvRel n}
    {p : Path n} {T : LambdaPHistory.Ty n}
    (h : Tm.DeepCheck Gamma R (Tm.path p) T) :
    Tau.DeepWf Gamma R (Tau.ty T) :=
  h.path_result_wf_of_eq rfl

/-- Runtime-equivalent paths have deeply convertible singleton types. -/
theorem Tau.DeepSub.single_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) :
    Tau.DeepSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single p)) (Tau.ty (Ty.Single q)) := by
  apply Tau.DeepSub.conv
  have hc := Tau.DeepConv.replace
    (R := Path.RuntimeEq sigma)
    (template := Tau.ty (Ty.Single (Path.var (0 : Fin (n + 1))))) h
  simpa [Tau.open, Tau.subst, Ty.open, Ty.subst, Path.open,
    Path.subst] using hc

/-- Big-step path lookup preserves the full-syntax deep checking judgment.

Unlike ordinary source preservation, this statement is valid for widened
stores: the conversion from `{x}` to `{p}` is justified by the concrete
reduction rather than postulated as source subtyping. -/
theorem Tm.DeepCheck.reduce_path
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {T : LambdaPHistory.Ty n}
    (hr : Path.reduce p sigma x)
    (h : Tm.DeepCheck Gamma (Path.RuntimeEq sigma) (Tm.path p) T) :
    Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) T := by
  obtain ⟨U, hp, hsub⟩ := h.path_inversion rfl
  obtain ⟨X, hx⟩ := Ctx.Binds.exists Gamma x
  have hbase : Tm.DeepCheck Gamma (Path.RuntimeEq sigma)
      (Tm.path (Path.var x)) (Ty.Single (Path.var x)) :=
    .path (.var hx)
  have heq : Path.RuntimeEq sigma (Path.var x) p :=
    (Path.RuntimeEq.of_reduce hr).symm
  exact .sub hbase
    (.trans (Tau.DeepSub.single_runtime heq) hsub)
    h.path_result_wf

end LambdaPHistory
