import LambdaPHistory.StructuralTermTyping

/-!
Narrowing for the structural judgments.

Precise source path typing is not stable when the newest context entry is
replaced by a subtype: the newest variable synthesizes a different type.
The structural checker was designed to express exactly this situation.  It
checks the variable at the narrower entry and then applies structural
subtyping before any elimination.  Consequently narrowing is an instance of
the existing structural-renaming theorem with the identity variable map.
-/

namespace LambdaPHistory

/-- Identity is a homomorphism for every path relation. -/
private theorem Path.RelHom.identity
    (R : Path n -> Path n -> Prop) : Path.RelHom R R FinFun.id := by
  intro p q hpq
  simpa only [Path.rename_id] using hpq

/-- Replacing the newest context entry by a subtype gives a structural
identity renaming from the old context to the narrowed context. -/
theorem Path.StructRenaming.narrow
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S S' : LambdaPHistory.Ty n}
    (hsub : Tau.StructSub Gamma R (Tau.ty S') (Tau.ty S)) :
    Path.StructRenaming (Gamma.snoc S) FinFun.id
      (Gamma.snoc S') (Path.ScopedLift R) := by
  intro x T hx
  cases hx with
  | here =>
      have hweak : Tau.StructSub (Gamma.snoc S') (Path.ScopedLift R)
          (Tau.ty S'.weaken) (Tau.ty S.weaken) := by
        simpa only [Tau.rename, Ty.weaken] using
          hsub.renameExact (Renaming.weaken (S := S'))
            (Path.RelHom.weaken (R := R))
      simpa only [FinFun.id_apply, Tau.rename, Ty.rename_id] using
        Path.StructCheck.sub
          (Path.StructCheck.var (R := Path.ScopedLift R)
            (Ctx.Binds.here (Γ := Gamma) (T := S')))
          hweak
  | there hx =>
      simpa only [FinFun.id_apply, Tau.rename, Ty.rename_id] using
        (Path.StructCheck.var (R := Path.ScopedLift R)
          (Ctx.Binds.there (S := S') hx))

theorem Path.StructCheck.narrow
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S S' : LambdaPHistory.Ty n} {p : Path (n + 1)}
    {d : Tau (n + 1) k}
    (h : Path.StructCheck (Gamma.snoc S) (Path.ScopedLift R) p d)
    (hsub : Tau.StructSub Gamma R (Tau.ty S') (Tau.ty S)) :
    Path.StructCheck (Gamma.snoc S') (Path.ScopedLift R) p d := by
  simpa only [Path.rename_id, Tau.rename_id] using
    h.rename (Path.StructRenaming.narrow hsub)
      (Path.RelHom.identity (Path.ScopedLift R))

theorem Tau.StructSub.narrow
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S S' : LambdaPHistory.Ty n} {d1 d2 : Tau (n + 1) k}
    (h : Tau.StructSub (Gamma.snoc S) (Path.ScopedLift R) d1 d2)
    (hsub : Tau.StructSub Gamma R (Tau.ty S') (Tau.ty S)) :
    Tau.StructSub (Gamma.snoc S') (Path.ScopedLift R) d1 d2 := by
  simpa only [Tau.rename_id] using
    h.rename (Path.StructRenaming.narrow hsub)
      (Path.RelHom.identity (Path.ScopedLift R))

theorem Tau.StructWf.narrow
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S S' : LambdaPHistory.Ty n} {d : Tau (n + 1) k}
    (h : Tau.StructWf (Gamma.snoc S) (Path.ScopedLift R) d)
    (hsub : Tau.StructSub Gamma R (Tau.ty S') (Tau.ty S)) :
    Tau.StructWf (Gamma.snoc S') (Path.ScopedLift R) d := by
  simpa only [Tau.rename_id] using
    h.rename (Path.StructRenaming.narrow hsub)
      (Path.RelHom.identity (Path.ScopedLift R))

theorem Tm.StructCheck.narrow
    {n : Nat} {Gamma : Ctx n} {R : Path n -> Path n -> Prop}
    {S S' : LambdaPHistory.Ty n} {t : Tm (n + 1)}
    {T : LambdaPHistory.Ty (n + 1)}
    (h : Tm.StructCheck (Gamma.snoc S) (Path.ScopedLift R) t T)
    (hsub : Tau.StructSub Gamma R (Tau.ty S') (Tau.ty S)) :
    Tm.StructCheck (Gamma.snoc S') (Path.ScopedLift R) t T := by
  simpa only [Tm.rename_id, Ty.rename_id] using
    h.rename (Path.StructRenaming.narrow hsub)
      (Path.RelHom.identity (Path.ScopedLift R))

end LambdaPHistory
