import LambdaPCC.CaptureAction

/-!
Static operations for the qualifier-aware semantic interpretation.  Source
contexts are interpreted by `Cap.Environment`; path typing resolves to
capture-aware realization evidence, and source subtyping compiles to the
corresponding capture-aware coercions.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Environments -/

def Environment.lookup
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m}
    (environment : Environment world Gamma rho) (x : Fin n) :
    LocationEvidence world (rho x) ((Gamma.lookup x).rename rho) := by
  cases environment with
  | intro lookup => exact lookup x

def Environment.empty :
    Environment World.empty Ctx.nil Valuation.id :=
  .intro (fun x => Fin.elim0 x)

/-- Extend an interpreted source context with a realized location. -/
def Environment.snoc
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S : Ty n} {y : Fin m}
    (environment : Environment world Gamma rho)
    (argument : LocationEvidence world y (S.rename rho)) :
    Environment world (Gamma.snoc S) (Valuation.snoc rho y) := by
  apply Environment.intro
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · simpa [Ctx.lookup, Ty.weaken, Ty.rename_rename] using argument
  · simpa [Ctx.lookup, Ty.weaken, Ty.rename_rename] using
      environment.lookup i

/-! ## Resolving typed paths -/

/-- The runtime referent and precise realization obtained from a source
path-typing derivation. -/
structure PathResolution
    {n m : Nat} {k : Kind} {sigma : Store m} (world : World sigma)
    (rho : Valuation n m) (p : Path n) (d : Tau n k) : Type 1 where
  referent : Path.Referent m
  resolution : Path.Resolve (p.rename rho) sigma referent
  realizes : Realizes world referent (d.rename rho)

/-- Resolve a typed source path under a capture-aware environment. -/
noncomputable def Path.Ty.resolve
    {n m : Nat} {k : Kind} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {p : Path n} {d : Tau n k}
    (environment : Environment world Gamma rho)
    (code : Path.Ty Gamma p d) : PathResolution world rho p d := by
  induction code with
  | @var _ x =>
      exact ⟨.loc (rho x), .var, .loc (environment.lookup x)⟩
  | fst receiver ih =>
      obtain ⟨referent, resolution, realizes⟩ := ih environment
      cases realizes with
      | loc possible =>
          cases possible with
          | pair lookup first member captures =>
              exact ⟨.loc _, .fst resolution lookup.binds, .loc first⟩
  | @sel_r _ _ receiverPath C S a dependent receiver ih =>
      obtain ⟨referent, resolution, realizes⟩ := ih environment
      cases realizes with
      | loc possible =>
          cases possible with
          | @pair _ _ _ _ _ y _ _ _ delta _ _
              lookup first member captures =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.loc y) :=
                .fst resolution lookup.binds
              have paths :
                  Path.RuntimeEq sigma (.var y)
                    ((receiverPath.rename rho).fst) :=
                .ofResolve .var firstResolution
              have converted := member.convert
                (Tau.RuntimeConv.replace (dependent.rename rho.ext) paths)
              have converted' :
                  Realizes world delta.referent
                    ((dependent.open receiverPath.fst).rename rho) := by
                simpa [Tau.open_rename, Path.rename] using converted
              exact ⟨delta.referent, .sel resolution lookup.binds, converted'⟩
  | @sel_l _ _ receiverPath C S b receiverKind dependent a d
      receiver member distinct ihReceiver ihMember =>
      obtain ⟨receiverReferent, receiverResolution, receiverRealizes⟩ :=
        ihReceiver environment
      obtain ⟨memberReferent, memberResolution, memberRealizes⟩ :=
        ihMember environment
      cases receiverRealizes with
      | loc possible =>
          cases possible with
          | @pair _ _ _ _ _ y _ _ _ delta _ _
              lookup first storedMember captures =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.loc y) :=
                .fst receiverResolution lookup.binds
              have tailResolution := Path.Resolve.sel_congr
                memberResolution firstResolution Path.Resolve.var
              have labelsDistinct : Not (a = b) := by
                intro equal
                subst a
                simp at distinct
              exact ⟨memberReferent,
                .sel_miss receiverResolution lookup.binds labelsDistinct
                  tailResolution,
                memberRealizes⟩

/-! ## Compiling source subtyping -/

/-- Static subcapturing remains tied to the environment that justifies its
path premises. -/
noncomputable def CaptureSet.Sub.compile
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {C D : CaptureSet n}
    (environment : Environment world Gamma rho)
    (code : CaptureSet.Sub Gamma C D) :
    Relation world (C.rename rho) (D.rename rho) :=
  .source environment code

mutual

noncomputable def Ty.Sub.compile
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {T U : Ty n}
    (environment : Environment world Gamma rho) :
    Ty.Sub Gamma T U -> TyCoercion world (T.rename rho) (U.rename rho)
  | .refl => .refl
  | .trans first second =>
      .trans (Cap.Ty.Sub.compile environment first)
        (Cap.Ty.Sub.compile environment second)
  | .capt captures shape =>
      .capt (Cap.CaptureSet.Sub.compile environment captures)
        (Cap.Shape.Sub.compile environment shape)

noncomputable def Shape.Sub.compile
    {n m : Nat} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {S T : Shape n}
    (environment : Environment world Gamma rho) :
    Shape.Sub Gamma S T ->
      ShapeCoercion world (S.rename rho) (T.rename rho)
  | .refl => .refl
  | .trans first second =>
      .trans (Cap.Shape.Sub.compile environment first)
        (Cap.Shape.Sub.compile environment second)
  | .bot => .bot
  | .top => .top
  | .singleton_widen path => by
      obtain ⟨referent, resolution, realizes⟩ :=
        Cap.Path.Ty.resolve environment path
      cases realizes with
      | loc possible => exact .widen resolution possible
  | .singleton_alias path => by
      obtain ⟨referent, resolution, realizes⟩ :=
        Cap.Path.Ty.resolve environment path
      cases realizes with
      | loc possible =>
          cases possible with
          | single lookup targetResolution captures =>
              exact .alias resolution targetResolution
  | .select_lower path _ => by
      obtain ⟨referent, resolution, realizes⟩ :=
        Cap.Path.Ty.resolve environment path
      cases realizes with
      | type lower upper => exact .selectLower resolution lower
  | .select_upper path _ => by
      obtain ⟨referent, resolution, realizes⟩ :=
        Cap.Path.Ty.resolve environment path
      cases realizes with
      | type lower upper => exact .selectUpper resolution upper
  | .fun domain codomain =>
      .fun (Cap.Ty.Sub.compile environment domain)
        (.source environment codomain)
  | .pair first member =>
      .pair (Cap.Ty.Sub.compile environment first)
        (.source environment member)

end

noncomputable def Tau.Sub.compile
    {n m : Nat} {k : Kind} {sigma : Store m} {world : World sigma}
    {Gamma : Ctx n} {rho : Valuation n m} {d e : Tau n k}
    (environment : Environment world Gamma rho) :
    Tau.Sub Gamma d e -> Coercion world (d.rename rho) (e.rename rho)
  | .refl => .refl
  | .trans first second =>
      .trans (Cap.Tau.Sub.compile environment first)
        (Cap.Tau.Sub.compile environment second)
  | .term types => .term (Cap.Ty.Sub.compile environment types)
  | .type lower upper _ =>
      .type (Cap.Shape.Sub.compile environment lower)
        (Cap.Shape.Sub.compile environment upper)
  | .capture lower upper _ =>
      .capture (Cap.CaptureSet.Sub.compile environment lower)
        (Cap.CaptureSet.Sub.compile environment upper)

end
end Cap
end LambdaPCC
