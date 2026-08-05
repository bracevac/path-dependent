import LambdaPCC.Typing

/-!
Renaming for the static semantics. A renaming is admissible when it preserves
context lookup; its extension supplies the corresponding property beneath a
dependent binder.
-/

namespace LambdaPCC

noncomputable section

/-- A variable renaming that respects the types recorded by two contexts. -/
abbrev Renaming (Gamma : Ctx n) (f : FinFun n m) (Delta : Ctx m) : Prop :=
  forall x, Delta.lookup (f x) = (Gamma.lookup x).rename f

/-- Extend a context-respecting renaming beneath a dependent binder. -/
theorem Renaming.ext (rho : Renaming Gamma f Delta) :
    Renaming (Gamma.snoc T) f.ext (Delta.snoc (T.rename f)) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · simpa only [Ctx.lookup, FinFun.ext_zero] using Ty.weaken_rename T f
  · change (Delta.lookup (f i)).weaken =
      (Gamma.lookup i).weaken.rename f.ext
    rw [rho i, Ty.weaken_rename]

/-- Weakening is context-respecting. -/
theorem Renaming.weaken : Renaming Gamma FinFun.weaken (Gamma.snoc S) := by
  intro x
  rfl

/-! ## Renaming of judgments -/

/-- Precise path typing is preserved by a context-respecting renaming. -/
def Path.Ty.rename {Gamma : Ctx n} {p : Path n} {tau : Tau n k}
    (h : Path.Ty Gamma p tau) :
    forall {m} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      Path.Ty Delta (p.rename f) (tau.rename f) := by
  induction h with
  | @var _ x =>
      intro m f Delta rho
      simpa only [Path.rename, Tau.rename, rho x] using
        (Path.Ty.var (Gamma := Delta) (x := f x))
  | fst hp ih =>
      intro m f Delta rho
      simpa [Path.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename] using
        Path.Ty.fst (ih rho)
  | sel_r hp ih =>
      intro m f Delta rho
      simpa [Path.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename,
        Tau.open_rename] using Path.Ty.sel_r (ih rho)
  | sel_l hp htail hne ihp ihtail =>
      intro m f Delta rho
      simpa [Path.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename] using
        Path.Ty.sel_l (ihp rho) (ihtail rho) hne

/-- Subcapturing is preserved by a context-respecting renaming. -/
def CaptureSet.Sub.rename {Gamma : Ctx n} {C D : CaptureSet n}
    (h : CaptureSet.Sub Gamma C D) :
    forall {m} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      CaptureSet.Sub Delta (C.rename f) (D.rename f) := by
  induction h with
  | refl =>
      intro m f Delta rho
      exact .refl
  | trans hCD hDE ihCD ihDE =>
      intro m f Delta rho
      exact .trans (ihCD rho) (ihDE rho)
  | empty =>
      intro m f Delta rho
      simp only [CaptureSet.rename]
      exact .empty
  | union_left =>
      intro m f Delta rho
      simp only [CaptureSet.rename]
      exact .union_left
  | union_right =>
      intro m f Delta rho
      simp only [CaptureSet.rename]
      exact .union_right
  | union_elim hCE hDE ihCE ihDE =>
      intro m f Delta rho
      simpa only [CaptureSet.rename] using
        CaptureSet.Sub.union_elim (ihCE rho) (ihDE rho)
  | path hp =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Ty.rename, Shape.rename,
        Tau.rename] using CaptureSet.Sub.path (hp.rename rho)
  | alias hp =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Ty.rename, Shape.rename,
        Tau.rename] using CaptureSet.Sub.alias (hp.rename rho)
  | fst_root hp =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Sub.fst_root (hp.rename rho)
  | sel_root hp =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Sub.sel_root (hp.rename rho)
  | select_lower hp hLU ihLU =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Sub.select_lower (hp.rename rho) (ihLU rho)
  | select_upper hp hLU ihLU =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Sub.select_upper (hp.rename rho) (ihLU rho)

mutual

/-- Type subtyping is preserved by renaming. -/
def Ty.Sub.rename {Gamma : Ctx n} {S T : Ty n}
    (h : Ty.Sub Gamma S T) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) :
    Ty.Sub Delta (S.rename f) (T.rename f) :=
  match h with
  | .refl => .refl
  | .trans hST hTU => .trans (hST.rename rho) (hTU.rename rho)
  | .capt hC hS => by
      simpa only [Ty.rename] using
        Ty.Sub.capt (hC.rename rho) (hS.rename rho)

/-- Shape subtyping is preserved by renaming. -/
def Shape.Sub.rename {Gamma : Ctx n} {S T : Shape n}
    (h : Shape.Sub Gamma S T) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) :
    Shape.Sub Delta (S.rename f) (T.rename f) :=
  match h with
  | .refl => .refl
  | .trans hST hTU => .trans (hST.rename rho) (hTU.rename rho)
  | .bot => by simp only [Shape.rename]; exact .bot
  | .top => by simp only [Shape.rename]; exact .top
  | .singleton_widen hp => by
      simpa [Shape.rename, Path.rename, Ty.rename, Tau.rename] using
        Shape.Sub.singleton_widen (hp.rename rho)
  | .singleton_alias hp => by
      simpa [Shape.rename, Path.rename, Ty.rename, Tau.rename] using
        Shape.Sub.singleton_alias (hp.rename rho)
  | .select_lower hp hST => by
      simpa [Shape.rename, Path.rename, Tau.rename] using
        Shape.Sub.select_lower (hp.rename rho) (hST.rename rho)
  | .select_upper hp hST => by
      simpa [Shape.rename, Path.rename, Tau.rename] using
        Shape.Sub.select_upper (hp.rename rho) (hST.rename rho)
  | .fun hdom hcod => by
      simpa [Shape.rename] using
        Shape.Sub.fun (hdom.rename rho) (hcod.rename (Renaming.ext rho))
  | .pair hfst hmember => by
      simpa [Shape.rename] using
        Shape.Sub.pair (hfst.rename rho) (hmember.rename (Renaming.ext rho))

/-- Generalized-signature subtyping is preserved by renaming. -/
def Tau.Sub.rename {Gamma : Ctx n} {tau1 tau2 : Tau n k}
    (h : Tau.Sub Gamma tau1 tau2) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) :
    Tau.Sub Delta (tau1.rename f) (tau2.rename f) :=
  match h with
  | .refl => .refl
  | .trans h12 h23 => .trans (h12.rename rho) (h23.rename rho)
  | .term hST => by
      simpa only [Tau.rename] using Tau.Sub.term (hST.rename rho)
  | .type hlo hhi hconsistent => by
      simpa only [Tau.rename] using
        Tau.Sub.type (hlo.rename rho) (hhi.rename rho)
          (hconsistent.rename rho)
  | .capture hlo hhi hconsistent => by
      simpa only [Tau.rename] using
        Tau.Sub.capture (hlo.rename rho) (hhi.rename rho)
          (hconsistent.rename rho)

end

/-- Capture-set well-formedness is preserved by renaming. -/
def CaptureSet.Wf.rename {Gamma : Ctx n} {C : CaptureSet n}
    (h : CaptureSet.Wf Gamma C) :
    forall {m} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      CaptureSet.Wf Delta (C.rename f) := by
  induction h with
  | empty =>
      intro m f Delta rho
      simpa only [CaptureSet.rename] using
        (CaptureSet.Wf.empty (Gamma := Delta))
  | union hC hD ihC ihD =>
      intro m f Delta rho
      simpa only [CaptureSet.rename] using
        CaptureSet.Wf.union (ihC rho) (ihD rho)
  | singleton hp =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Wf.singleton (hp.rename rho)
  | select hp hLU =>
      intro m f Delta rho
      simpa [CaptureSet.rename, Path.rename, Tau.rename] using
        CaptureSet.Wf.select (hp.rename rho) (hLU.rename rho)

mutual

/-- Type well-formedness is preserved by renaming. -/
def Ty.Wf.rename {Gamma : Ctx n} {T : Ty n}
    (h : Ty.Wf Gamma T) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) : Ty.Wf Delta (T.rename f) :=
  match h with
  | .capt hC hS => by
      simpa only [Ty.rename] using
        Ty.Wf.capt (hC.rename rho) (hS.rename rho)

/-- Shape well-formedness is preserved by renaming. -/
def Shape.Wf.rename {Gamma : Ctx n} {S : Shape n}
    (h : Shape.Wf Gamma S) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) : Shape.Wf Delta (S.rename f) :=
  match h with
  | .bot => by simp only [Shape.rename]; exact .bot
  | .top => by simp only [Shape.rename]; exact .top
  | .singleton hp => by
      simpa [Shape.rename, Path.rename, Tau.rename] using
        Shape.Wf.singleton (hp.rename rho)
  | .select hp hST => by
      simpa [Shape.rename, Path.rename, Tau.rename] using
        Shape.Wf.select (hp.rename rho) (hST.rename rho)
  | .fun hdom hcod => by
      simpa only [Shape.rename] using
        Shape.Wf.fun (hdom.rename rho) (hcod.rename (Renaming.ext rho))
  | .pair hfst hmember => by
      simpa only [Shape.rename] using
        Shape.Wf.pair (hfst.rename rho) (hmember.rename (Renaming.ext rho))

/-- Generalized-signature well-formedness is preserved by renaming. -/
def Tau.Wf.rename {Gamma : Ctx n} {tau : Tau n k}
    (h : Tau.Wf Gamma tau) {m} {f : FinFun n m} {Delta : Ctx m}
    (rho : Renaming Gamma f Delta) : Tau.Wf Delta (tau.rename f) :=
  match h with
  | .term hT => by
      simpa only [Tau.rename] using Tau.Wf.term (hT.rename rho)
  | .type hS hT hsub => by
      simpa only [Tau.rename] using
        Tau.Wf.type (hS.rename rho) (hT.rename rho) (hsub.rename rho)
  | .capture hL hU hsub => by
      simpa only [Tau.rename] using
        Tau.Wf.capture (hL.rename rho) (hU.rename rho)
          (hsub.rename rho)

end

/-- Term typing, including its use set, is preserved by renaming. -/
def Tm.Ty.rename {Gamma : Ctx n} {term : Tm n} {T : LambdaPCC.Ty n}
    {C : CaptureSet n} (h : Tm.Ty Gamma term T C) :
    forall {m} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta ->
      Tm.Ty Delta (term.rename f) (T.rename f) (C.rename f) := by
  induction h with
  | path hp =>
      intro m f Delta rho
      simpa [Tm.rename, LambdaPCC.Ty.rename, Shape.rename, CaptureSet.rename,
        Path.rename] using Tm.Ty.path (hp.rename rho)
  | @abs n body Tbody Gamma S C hbody hS hC ihbody =>
      intro m f Delta rho
      have body' :
          Tm.Ty (Delta.snoc (S.rename f)) (body.rename f.ext)
            (Tbody.rename f.ext)
            (.union (C.rename f).weaken (.singleton (.var 0))) := by
        simpa only [CaptureSet.rename, Path.rename, FinFun.ext_zero,
          ← CaptureSet.weaken_rename] using
          ihbody (Renaming.ext rho)
      simpa [Tm.rename, LambdaPCC.Ty.rename, Shape.rename,
        CaptureSet.rename] using
        Tm.Ty.abs body' (hS.rename rho) (hC.rename rho)
  | app hfun harg ihfun iharg =>
      intro m f Delta rho
      simpa [Tm.rename, LambdaPCC.Ty.rename, Shape.rename,
        CaptureSet.rename, Path.rename, Ty.open_rename] using
        Tm.Ty.app (ihfun rho) (iharg rho)
  | @pair n Gamma y a z =>
      intro m f Delta rho
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Path.weaken_rename] using
        (Tm.Ty.pair (Gamma := Delta) (y := f y) (z := f z) (a := a))
  | @type_pair n Gamma T y a hT =>
      intro m f Delta rho
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← Shape.weaken_rename] using
        Tm.Ty.type_pair (y := f y) (a := a) (hT.rename rho)
  | @capture_pair n Gamma C y a hC =>
      intro m f Delta rho
      simpa [Tm.rename, Def.rename, LambdaPCC.Ty.rename, Shape.rename, Tau.rename,
        CaptureSet.rename, Path.rename, ← CaptureSet.weaken_rename] using
        Tm.Ty.capture_pair (y := f y) (a := a) (hC.rename rho)
  | @«let» n Gamma bound Tbound C body U hbound hbody hU hC
      ihbound ihbody =>
      intro m f Delta rho
      have body' :
          Tm.Ty (Delta.snoc (Tbound.rename f)) (body.rename f.ext)
            (U.rename f).weaken (C.rename f).weaken := by
        simpa only [← Ty.weaken_rename, ← CaptureSet.weaken_rename] using
          ihbody (Renaming.ext rho)
      simpa [Tm.rename] using
        Tm.Ty.let (ihbound rho) body'
          (hU.rename rho) (hC.rename rho)
  | sub hterm hsubT hsubC hT hD ihterm =>
      intro m f Delta rho
      exact Tm.Ty.sub (ihterm rho) (hsubT.rename rho)
        (hsubC.rename rho) (hT.rename rho) (hD.rename rho)

/-! ## Weakening corollaries -/

def Path.Ty.weaken (h : Path.Ty Gamma p tau) :
    Path.Ty (Gamma.snoc S) p.weaken tau.weaken := by
  simpa [Path.weaken, Tau.weaken] using
    h.rename (Renaming.weaken (S := S))

def CaptureSet.Sub.weaken (h : CaptureSet.Sub Gamma C D) :
    CaptureSet.Sub (Gamma.snoc S) C.weaken D.weaken := by
  simpa [CaptureSet.weaken] using h.rename (Renaming.weaken (S := S))

def Ty.Sub.weaken (h : Ty.Sub Gamma T U) :
    Ty.Sub (Gamma.snoc S) T.weaken U.weaken := by
  simpa [Ty.weaken] using h.rename (Renaming.weaken (S := S))

def Shape.Sub.weaken (h : Shape.Sub Gamma T U) :
    Shape.Sub (Gamma.snoc S) T.weaken U.weaken := by
  simpa [Shape.weaken] using h.rename (Renaming.weaken (S := S))

def Tau.Sub.weaken (h : Tau.Sub Gamma tau1 tau2) :
    Tau.Sub (Gamma.snoc S) tau1.weaken tau2.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

def CaptureSet.Wf.weaken (h : CaptureSet.Wf Gamma C) :
    CaptureSet.Wf (Gamma.snoc S) C.weaken := by
  simpa [CaptureSet.weaken] using h.rename (Renaming.weaken (S := S))

def Ty.Wf.weaken (h : Ty.Wf Gamma T) :
    Ty.Wf (Gamma.snoc S) T.weaken := by
  simpa [Ty.weaken] using h.rename (Renaming.weaken (S := S))

def Shape.Wf.weaken (h : Shape.Wf Gamma T) :
    Shape.Wf (Gamma.snoc S) T.weaken := by
  simpa [Shape.weaken] using h.rename (Renaming.weaken (S := S))

def Tau.Wf.weaken (h : Tau.Wf Gamma tau) :
    Tau.Wf (Gamma.snoc S) tau.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

def Tm.Ty.weaken (h : Tm.Ty Gamma term T C) :
    Tm.Ty (Gamma.snoc S) term.weaken T.weaken C.weaken := by
  simpa [Tm.weaken, LambdaPCC.Ty.weaken, CaptureSet.weaken] using
    h.rename (Renaming.weaken (S := S))

/-! ## Consistency of member bounds -/

/-- The bound-consistency property carried by a member signature. -/
def Tau.Consistent (Gamma : Ctx n) : Tau n k -> Type
| .term _ => Unit
| .type lower upper => Shape.Sub Gamma lower upper
| .capture lower upper => CaptureSet.Sub Gamma lower upper

/-- Well-formed member signatures have consistent bounds. -/
def Tau.Wf.consistent (wf : Tau.Wf Gamma tau) : tau.Consistent Gamma :=
  match wf with
  | .term _ => ()
  | .type _ _ bounds => bounds
  | .capture _ _ bounds => bounds

/-- Generalized-signature subtyping preserves bound consistency. -/
def Tau.Sub.preserveConsistency
    (sub : Tau.Sub Gamma source target) :
    source.Consistent Gamma -> target.Consistent Gamma :=
  match sub with
  | .refl => fun consistent => consistent
  | .trans first second => fun consistent =>
      second.preserveConsistency (first.preserveConsistency consistent)
  | .term _ => fun _ => ()
  | .type lower upper sourceBounds => fun _ =>
      .trans lower (.trans sourceBounds upper)
  | .capture lower upper sourceBounds => fun _ =>
      .trans lower (.trans sourceBounds upper)

end
end LambdaPCC
