import LambdaPFC.Derivations
import LambdaPFC.StaticMetatheory

/-! Renaming and weakening for proof-relevant static derivations. -/

namespace LambdaPFC

noncomputable section

/-! ## Renaming -/

def PathCode.rename
    {n : Nat} {Gamma : Ctx n} {p : Path n}
    {k : Kind} {d : Tau n k}
    (code : PathCode Gamma p d) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      PathCode Delta (p.rename f) (d.rename f) := by
  induction code with
  | var binds =>
      intro m f Delta rho
      simpa [Path.rename, Tau.rename] using
        PathCode.var (rho binds)
  | fst receiver ih =>
      intro m f Delta rho
      simpa [Path.rename, Ty.rename, Tau.rename] using
        PathCode.fst (ih rho)
  | sel_r receiver ih =>
      intro m f Delta rho
      simpa [Path.rename, Ty.rename, Tau.rename, Tau.open_rename] using
        PathCode.sel_r (ih rho)
  | sel_l receiver member distinct ihReceiver ihMember =>
      intro m f Delta rho
      simpa [Path.rename, Ty.rename, Tau.rename] using
        PathCode.sel_l (ihReceiver rho) (ihMember rho) distinct

def SubCode.rename
    {n : Nat} {Gamma : Ctx n} {k : Kind}
    {d1 d2 : Tau n k}
    (code : SubCode Gamma d1 d2) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      SubCode Delta (d1.rename f) (d2.rename f) := by
  induction code with
  | refl =>
      intro m f Delta rho
      exact .refl
  | trans first second ihFirst ihSecond =>
      intro m f Delta rho
      exact .trans (ihFirst rho) (ihSecond rho)
  | bot =>
      intro m f Delta rho
      simpa only [Tau.rename, Ty.rename] using
        (SubCode.bot (Gamma := Delta))
  | top =>
      intro m f Delta rho
      simpa only [Tau.rename, Ty.rename] using
        (SubCode.top (Gamma := Delta))
  | widen path =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        SubCode.widen (path.rename rho)
  | symm path =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        SubCode.symm (path.rename rho)
  | sel_hi path bounds ihBounds =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        SubCode.sel_hi (path.rename rho) (ihBounds rho)
  | sel_lo path bounds ihBounds =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        SubCode.sel_lo (path.rename rho) (ihBounds rho)
  | «fun» domain codomain ihDomain ihCodomain =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename] using
        SubCode.fun (ihDomain rho) (ihCodomain rho.ext)
  | pair_fst first ihFirst =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename] using
        SubCode.pair_fst (ihFirst rho)
  | pair_single_member path underBinder opened
      ihUnderBinder ihOpened =>
      intro m f Delta rho
      have opened' := ihOpened rho
      rw [Tau.open_rename, Tau.open_rename] at opened'
      simpa [Tau.rename, Ty.rename, Path.rename] using
        SubCode.pair_single_member (path.rename rho)
          (ihUnderBinder rho.ext) opened'
  | bounds lower upper nonempty ihLower ihUpper ihNonempty =>
      intro m f Delta rho
      simpa [Tau.rename] using
        SubCode.bounds (ihLower rho) (ihUpper rho) (ihNonempty rho)

def WfCode.rename
    {n : Nat} {Gamma : Ctx n} {k : Kind} {d : Tau n k}
    (code : WfCode Gamma d) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      WfCode Delta (d.rename f) := by
  induction code with
  | bot =>
      intro m f Delta rho
      simpa only [Tau.rename, Ty.rename] using
        (WfCode.bot (Gamma := Delta))
  | top =>
      intro m f Delta rho
      simpa only [Tau.rename, Ty.rename] using
        (WfCode.top (Gamma := Delta))
  | path pathCode =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        WfCode.path (pathCode.rename rho)
  | sel pathCode =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename, Path.rename] using
        WfCode.sel (pathCode.rename rho)
  | «fun» domain codomain ihDomain ihCodomain =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename] using
        WfCode.fun (ihDomain rho) (ihCodomain rho.ext)
  | pair first member ihFirst ihMember =>
      intro m f Delta rho
      simpa [Tau.rename, Ty.rename] using
        WfCode.pair (ihFirst rho) (ihMember rho.ext)
  | bounds_wf lower upper bounds ihLower ihUpper =>
      intro m f Delta rho
      simpa [Tau.rename] using
        WfCode.bounds_wf (ihLower rho) (ihUpper rho)
          (bounds.rename rho)

def TermCode.rename
    {n : Nat} {Gamma : Ctx n} {t : Tm n} {T : Ty n}
    (code : TermCode Gamma t T) :
    forall {m : Nat} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      TermCode Delta (t.rename f) (T.rename f) := by
  induction code with
  | path pathCode =>
      intro m f Delta rho
      simpa [Tm.rename, Ty.rename, Path.rename] using
        TermCode.path (pathCode.rename rho)
  | abs body domain ihBody =>
      intro m f Delta rho
      simpa [Tm.rename, Ty.rename] using
        TermCode.abs (ihBody rho.ext) (domain.rename rho)
  | app function argument ihFunction ihArgument =>
      intro m f Delta rho
      simpa [Tm.rename, Ty.rename, Ty.open_rename] using
        TermCode.app (ihFunction rho) (ihArgument rho)
  | pair first member =>
      intro m f Delta rho
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        TermCode.pair (rho first) (rho member)
  | tpair first member =>
      intro m f Delta rho
      simpa only [Tm.rename, Def.rename, LambdaPFC.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        TermCode.tpair (rho first) (member.rename rho)
  | «let» bound result body ihBound ihBody =>
      intro m f Delta rho
      simp only [Tm.rename]
      apply TermCode.let (ihBound rho) (result.rename rho)
      rw [Ty.weaken_rename]
      exact ihBody rho.ext
  | typed term wf ihTerm =>
      intro m f Delta rho
      simpa [Tm.rename] using
        TermCode.typed (ihTerm rho) (wf.rename rho)
  | sub term subtype wf ihTerm =>
      intro m f Delta rho
      exact TermCode.sub (ihTerm rho) (subtype.rename rho)
        (wf.rename rho)

/-! ## Weakening -/

def PathCode.weaken
    {n : Nat} {Gamma : Ctx n} {p : Path n}
    {k : Kind} {d : Tau n k} {S : Ty n}
    (code : PathCode Gamma p d) :
    PathCode (Gamma.snoc S) p.weaken d.weaken := by
  simpa [Path.weaken, Tau.weaken] using
    code.rename (Renaming.weaken (S := S))

def SubCode.weaken
    {n : Nat} {Gamma : Ctx n} {k : Kind}
    {d1 d2 : Tau n k} {S : Ty n}
    (code : SubCode Gamma d1 d2) :
    SubCode (Gamma.snoc S) d1.weaken d2.weaken := by
  simpa [Tau.weaken] using
    code.rename (Renaming.weaken (S := S))

def WfCode.weaken
    {n : Nat} {Gamma : Ctx n} {k : Kind}
    {d : Tau n k} {S : Ty n}
    (code : WfCode Gamma d) :
    WfCode (Gamma.snoc S) d.weaken := by
  simpa [Tau.weaken] using
    code.rename (Renaming.weaken (S := S))

def TermCode.weaken
    {n : Nat} {Gamma : Ctx n} {t : Tm n}
    {T S : Ty n}
    (code : TermCode Gamma t T) :
    TermCode (Gamma.snoc S) t.weaken T.weaken := by
  simpa [Tm.weaken, Ty.weaken] using
    code.rename (Renaming.weaken (S := S))

end
end LambdaPFC
