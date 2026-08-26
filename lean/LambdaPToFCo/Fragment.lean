import LambdaPFC.Typing

/-!
# Restricted LambdaPFC source fragment

This source layer reuses LambdaPFC's intrinsically scoped syntax and
dependent `Ctx`, but its proof-relevant judgments accept only `Top`, typed
singletons, selections from bound interval packages, interval packages with
a fixed first component and label, and nondependent functions.  Package
introduction remains exact; abstract intervals arise by package covariance.
`Sub.refl` and `Sub.top` require this restricted well-formedness, so
unsupported host types cannot enter through them.
-/

namespace LambdaPToFCo
namespace Fragment

open LambdaPFC

def memberPackageTy (first : Fin n) (label : Name)
    (lower upper : Ty n) : Ty n :=
  .Pair (.Single (.var first)) label (Tau.intv lower upper).weaken

def exactPackageTy (first : Fin n) (label : Name) (witness : Ty n) : Ty n :=
  memberPackageTy first label witness witness

@[simp] theorem memberPackageTy_rename
    (first : Fin n) (label : Name) (lower upper : Ty n) (f : FinFun n m) :
    (memberPackageTy first label lower upper).rename f =
      memberPackageTy (f first) label (lower.rename f) (upper.rename f) := by
  simp only [memberPackageTy, Ty.rename, Path.rename]
  rw [← Tau.weaken_rename]
  rfl

@[simp] theorem exactPackageTy_rename
    (first : Fin n) (label : Name) (witness : Ty n) (f : FinFun n m) :
    (exactPackageTy first label witness).rename f =
      exactPackageTy (f first) label (witness.rename f) := by
  exact memberPackageTy_rename first label witness witness f

/-! The explicit `first` index is the payload path at the current scope.
`here`/`there` lets elaboration find the corresponding target interface slots
structurally, without inspecting an equality about `Ctx.lookup`. -/

inductive BoundMember :
    {n : Nat} -> Ctx n -> Fin n -> Name -> Ty n -> Ty n -> Fin n -> Type where
| here {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {lower upper : Ty n} :
    BoundMember
      (Γ.snoc (memberPackageTy first label lower upper))
      0 label lower.weaken upper.weaken first.succ
| there {n : Nat} {Γ : Ctx n} {package first : Fin n} {label : Name}
    {lower upper U : Ty n} :
    BoundMember Γ package label lower upper first ->
    BoundMember
      (Γ.snoc U) package.succ label lower.weaken upper.weaken first.succ

namespace BoundMember

@[simp] theorem lookup_eq {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n}
    (member : BoundMember Γ package label lower upper first) :
    Γ.lookup package = memberPackageTy first label lower upper := by
  induction member with
  | @here n Γ first label lower upper =>
      change (memberPackageTy first label lower upper).weaken =
        memberPackageTy first.succ label lower.weaken upper.weaken
      exact memberPackageTy_rename first label lower upper FinFun.weaken
  | @there n Γ package first label lower upper U member ih =>
      change (Γ.lookup package).weaken =
        memberPackageTy first.succ label lower.weaken upper.weaken
      rw [ih]
      exact memberPackageTy_rename first label lower upper FinFun.weaken

def weaken {n : Nat} {Γ : Ctx n} {package first : Fin n} {label : Name}
    {lower upper : Ty n}
    (member : BoundMember Γ package label lower upper first) (U : Ty n) :
    BoundMember (Γ.snoc U) package.succ label
      lower.weaken upper.weaken first.succ :=
  .there member

def packageTyping {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n}
    (member : BoundMember Γ package label lower upper first) :
    LambdaPFC.Path.Ty Γ (.var package)
      (.ty (memberPackageTy first label lower upper)) := by
  rw [← member.lookup_eq]
  exact .var

def firstTyping {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n}
    (member : BoundMember Γ package label lower upper first) :
    LambdaPFC.Path.Ty Γ (.fst (.var package))
      (.ty (.Single (.var first))) :=
  member.packageTyping.fst

def selection {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n}
    (member : BoundMember Γ package label lower upper first) :
    LambdaPFC.Path.Ty Γ (.sel (.var package) label)
      (.intv lower upper) := by
  simpa only [memberPackageTy, Tau.weaken_open] using
    member.packageTyping.sel_r

end BoundMember

/-- Compatibility spelling for the exact-bound special case. -/
abbrev BoundExactMember {n : Nat} (Γ : Ctx n) (package : Fin n)
    (label : Name) (witness : Ty n) (first : Fin n) : Type :=
  BoundMember Γ package label witness witness first

namespace BoundExactMember

def here {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {witness : Ty n} :
    BoundExactMember
      (Γ.snoc (exactPackageTy first label witness))
      0 label witness.weaken first.succ :=
  BoundMember.here

def there {n : Nat} {Γ : Ctx n} {package first : Fin n} {label : Name}
    {witness U : Ty n}
    (member : BoundExactMember Γ package label witness first) :
    BoundExactMember
      (Γ.snoc U) package.succ label witness.weaken first.succ :=
  BoundMember.there member

def weaken {n : Nat} {Γ : Ctx n} {package first : Fin n} {label : Name}
    {witness : Ty n}
    (member : BoundExactMember Γ package label witness first) (U : Ty n) :
    BoundExactMember (Γ.snoc U) package.succ label witness.weaken first.succ :=
  BoundMember.weaken member U

def packageTyping {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first) :
    LambdaPFC.Path.Ty Γ (.var package)
      (.ty (exactPackageTy first label witness)) :=
  BoundMember.packageTyping member

def firstTyping {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first) :
    LambdaPFC.Path.Ty Γ (.fst (.var package))
      (.ty (.Single (.var first))) :=
  BoundMember.firstTyping member

def selection {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first) :
    LambdaPFC.Path.Ty Γ (.sel (.var package) label)
      (.intv witness witness) :=
  BoundMember.selection member

end BoundExactMember

inductive PathTy : {n : Nat} -> Ctx n -> Path n -> Ty n -> Type where
| var {n : Nat} {Γ : Ctx n} {x : Fin n} :
    PathTy Γ (.var x) (Γ.lookup x)
| exactFst {n : Nat} {Γ : Ctx n} {package first : Fin n} {label : Name}
    {lower upper : Ty n} :
    BoundMember Γ package label lower upper first ->
    PathTy Γ (.fst (.var package)) (.Single (.var first))

namespace PathTy

def weaken {n : Nat} {Γ : Ctx n} {path : Path n} {T : Ty n} :
    PathTy Γ path T -> (U : Ty n) ->
    PathTy (Γ.snoc U) path.weaken T.weaken
| .var, _ => .var
| .exactFst member, _ => .exactFst member.there

def toLambdaPFC {n : Nat} {Γ : Ctx n} {path : Path n} {T : Ty n} :
    PathTy Γ path T -> LambdaPFC.Path.Ty Γ path (.ty T)
| .var => .var
| .exactFst member => member.firstTyping

end PathTy

mutual

inductive Wf : {n : Nat} -> Ctx n -> Ty n -> Type where
| top {n : Nat} {Γ : Ctx n} : Wf Γ .Top
| singleton {n : Nat} {Γ : Ctx n} {path : Path n} {T : Ty n} :
    PathTy Γ path T -> Wf Γ (.Single path)
| selection {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n} :
    BoundMember Γ package label lower upper first ->
    Sub Γ lower upper -> Wf Γ (.TSel (.var package) label)
| memberPackage {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {lower upper : Ty n} :
    Wf Γ lower -> Wf Γ upper -> Sub Γ lower upper ->
    Wf Γ (memberPackageTy first label lower upper)
| arrow {n : Nat} {Γ : Ctx n} {domain codomain : Ty n} :
    Wf Γ domain -> Wf Γ codomain ->
    Wf Γ (.Fun domain codomain.weaken)

inductive Sub : {n : Nat} -> Ctx n -> Ty n -> Ty n -> Type where
| refl {n : Nat} {Γ : Ctx n} {T : Ty n} : Wf Γ T -> Sub Γ T T
| trans {n : Nat} {Γ : Ctx n} {S T U : Ty n} :
    Sub Γ S T -> Sub Γ T U -> Sub Γ S U
| top {n : Nat} {Γ : Ctx n} {T : Ty n} : Wf Γ T -> Sub Γ T .Top
| widen {n : Nat} {Γ : Ctx n} {path : Path n} {T : Ty n} :
    PathTy Γ path T -> Wf Γ T -> Sub Γ (.Single path) T
| selectLower {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n} :
    BoundMember Γ package label lower upper first -> Sub Γ lower upper ->
    Sub Γ lower (.TSel (.var package) label)
| selectUpper {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {lower upper : Ty n} :
    BoundMember Γ package label lower upper first -> Sub Γ lower upper ->
    Sub Γ (.TSel (.var package) label) upper
| arrow {n : Nat} {Γ : Ctx n}
    {targetDomain sourceDomain sourceCodomain targetCodomain : Ty n} :
    Sub Γ targetDomain sourceDomain ->
    Sub Γ sourceCodomain targetCodomain ->
    Sub Γ (.Fun sourceDomain sourceCodomain.weaken)
      (.Fun targetDomain targetCodomain.weaken)
| package {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {lower1 upper1 lower2 upper2 : Ty n} :
    Sub Γ lower2 lower1 -> Sub Γ upper1 upper2 -> Sub Γ lower1 upper1 ->
    Sub Γ (memberPackageTy first label lower1 upper1)
      (memberPackageTy first label lower2 upper2)

end

namespace Sub

mutual
def sourceWf {n : Nat} {Γ : Ctx n} {S T : Ty n} : Sub Γ S T -> Wf Γ S
| .refl wf => wf
| .trans first _ => first.sourceWf
| .top wf => wf
| .widen pathTyping _ => .singleton pathTyping
| .selectLower _ nonempty => nonempty.sourceWf
| .selectUpper member nonempty => .selection member nonempty
| .arrow domain codomain => .arrow domain.targetWf codomain.sourceWf
| .package lower upper nonempty =>
    .memberPackage lower.targetWf upper.sourceWf nonempty

def targetWf {n : Nat} {Γ : Ctx n} {S T : Ty n} : Sub Γ S T -> Wf Γ T
| .refl wf => wf
| .trans _ second => second.targetWf
| .top _ => .top
| .widen _ targetWf => targetWf
| .selectLower member nonempty => .selection member nonempty
| .selectUpper _ nonempty => nonempty.targetWf
| .arrow domain codomain => .arrow domain.sourceWf codomain.targetWf
| .package lower upper nonempty =>
    .memberPackage lower.sourceWf upper.targetWf
      (.trans lower (.trans nonempty upper))
end

/-- Transport only the endpoint indices of a fragment subtyping plan. -/
def cast {n : Nat} {Γ : Ctx n} {S T S' T' : Ty n}
    (source : S = S') (target : T = T') (subtype : Sub Γ S T) :
    Sub Γ S' T' := by
  cases source
  cases target
  exact subtype

def depth {n : Nat} {Γ : Ctx n} {S T : Ty n} : Sub Γ S T -> Nat
| .refl _ | .top _ | .widen _ _ => 1
| .selectLower _ nonempty | .selectUpper _ nonempty => nonempty.depth + 1
| .trans first second | .arrow first second =>
    Nat.max first.depth second.depth + 1
| .package lower upper nonempty =>
    Nat.max lower.depth (Nat.max upper.depth nonempty.depth) + 1

@[simp] theorem depth_cast {n : Nat} {Γ : Ctx n} {S T S' T' : Ty n}
    (source : S = S') (target : T = T') (subtype : Sub Γ S T) :
    (cast source target subtype).depth = subtype.depth := by
  cases source
  cases target
  rfl

end Sub

mutual

noncomputable def Wf.weaken {n : Nat} {Γ : Ctx n} {T : Ty n}
    (wf : Wf Γ T) (U : Ty n) : Wf (Γ.snoc U) T.weaken :=
  match wf with
  | .top => .top
  | .singleton pathTyping => .singleton (pathTyping.weaken U)
  | .selection member nonempty =>
      .selection member.there (Sub.weaken nonempty U)
  | .memberPackage (first := first) (label := label)
      lowerWf upperWf nonempty => by
      change Wf (Γ.snoc U)
        ((memberPackageTy first label _ _).rename FinFun.weaken)
      rw [memberPackageTy_rename]
      exact .memberPackage (Wf.weaken lowerWf U) (Wf.weaken upperWf U)
        (Sub.weaken nonempty U)
  | .arrow (domain := domain) (codomain := codomain)
      domainWf codomainWf => by
      change Wf (Γ.snoc U)
        (.Fun domain.weaken (codomain.weaken.rename FinFun.weaken.ext))
      rw [← Ty.weaken_rename]
      exact .arrow (Wf.weaken domainWf U) (Wf.weaken codomainWf U)

noncomputable def Sub.weaken {n : Nat} {Γ : Ctx n} {S T : Ty n}
    (subtype : Sub Γ S T) (U : Ty n) :
    Sub (Γ.snoc U) S.weaken T.weaken :=
  match subtype with
  | .refl wf => .refl (Wf.weaken wf U)
  | .trans first second => .trans (Sub.weaken first U) (Sub.weaken second U)
  | .top wf => .top (Wf.weaken wf U)
  | .widen pathTyping targetWf =>
      .widen (pathTyping.weaken U) (Wf.weaken targetWf U)
  | .selectLower member nonempty =>
      .selectLower member.there (Sub.weaken nonempty U)
  | .selectUpper member nonempty =>
      .selectUpper member.there (Sub.weaken nonempty U)
  | .arrow (targetDomain := targetDomain) (sourceDomain := sourceDomain)
      (sourceCodomain := sourceCodomain) (targetCodomain := targetCodomain)
      domain codomain =>
      let sourceEq :
          (Ty.Fun sourceDomain.weaken sourceCodomain.weaken.weaken) =
            (Ty.Fun sourceDomain sourceCodomain.weaken).weaken := by
        change (Ty.Fun sourceDomain.weaken sourceCodomain.weaken.weaken) =
          (Ty.Fun sourceDomain.weaken
            (sourceCodomain.weaken.rename FinFun.weaken.ext))
        exact congrArg (Ty.Fun sourceDomain.weaken)
          (Ty.weaken_rename sourceCodomain FinFun.weaken)
      let targetEq :
          (Ty.Fun targetDomain.weaken targetCodomain.weaken.weaken) =
            (Ty.Fun targetDomain targetCodomain.weaken).weaken := by
        change (Ty.Fun targetDomain.weaken targetCodomain.weaken.weaken) =
          (Ty.Fun targetDomain.weaken
            (targetCodomain.weaken.rename FinFun.weaken.ext))
        exact congrArg (Ty.Fun targetDomain.weaken)
          (Ty.weaken_rename targetCodomain FinFun.weaken)
      Sub.cast sourceEq targetEq
        (Sub.arrow (Sub.weaken domain U) (Sub.weaken codomain U))
  | .package (first := first) (label := label)
      (lower1 := lower1) (upper1 := upper1)
      (lower2 := lower2) (upper2 := upper2)
      lower upper nonempty =>
      let sourceEq :
          memberPackageTy first.succ label lower1.weaken upper1.weaken =
            (memberPackageTy first label lower1 upper1).weaken :=
        (memberPackageTy_rename first label lower1 upper1 FinFun.weaken).symm
      let targetEq :
          memberPackageTy first.succ label lower2.weaken upper2.weaken =
            (memberPackageTy first label lower2 upper2).weaken :=
        (memberPackageTy_rename first label lower2 upper2 FinFun.weaken).symm
      Sub.cast sourceEq targetEq
        (.package (Sub.weaken lower U) (Sub.weaken upper U)
          (Sub.weaken nonempty U))

end

namespace Sub

@[simp] theorem depth_weaken {n : Nat} {Γ : Ctx n} {S T : Ty n}
    (subtype : Sub Γ S T) (U : Ty n) :
    (subtype.weaken U).depth = subtype.depth :=
  match subtype with
  | .refl _ | .top _ | .widen _ _ => rfl
  | .trans first second => by
      simp only [Sub.weaken, depth, depth_weaken first U,
        depth_weaken second U]
  | .selectLower _ nonempty | .selectUpper _ nonempty => by
      simp only [Sub.weaken, depth, depth_weaken nonempty U]
  | .arrow domain codomain => by
      simp only [Sub.weaken, depth, depth_cast, depth_weaken domain U,
        depth_weaken codomain U]
  | .package lower upper nonempty => by
      simp only [Sub.weaken, depth, depth_cast, depth_weaken lower U,
        depth_weaken upper U, depth_weaken nonempty U]

noncomputable def toLambdaPFC {n : Nat} {Γ : Ctx n} {S T : Ty n}
    (subtype : Sub Γ S T) :
    LambdaPFC.Tau.Sub Γ (.ty S) (.ty T) :=
  match subtype with
  | .refl _ => .refl
  | .trans first second => .trans first.toLambdaPFC second.toLambdaPFC
  | .top _ => .top
  | .widen pathTyping _ => .widen pathTyping.toLambdaPFC
  | .selectLower member nonempty =>
      .sel_lo member.selection nonempty.toLambdaPFC
  | .selectUpper member nonempty =>
      .sel_hi member.selection nonempty.toLambdaPFC
  | .arrow (targetDomain := targetDomain) domain codomain =>
      .fun domain.toLambdaPFC
        (codomain.weaken targetDomain).toLambdaPFC
  | .package (first := first) lower upper nonempty =>
      .pair .refl
        (.bounds
          (lower.weaken (.Single (.var first))).toLambdaPFC
          (upper.weaken (.Single (.var first))).toLambdaPFC
          (nonempty.weaken (.Single (.var first))).toLambdaPFC)
termination_by subtype.depth
decreasing_by
  all_goals simp only [depth, depth_weaken]
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  · exact Nat.lt_succ_of_le (Nat.le_refl _)
  · exact Nat.lt_succ_of_le (Nat.le_refl _)
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · exact Nat.lt_succ_of_le
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- Compatibility helper for the lower rule of an exact member. -/
def selectExactLower {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first)
    (witnessWf : Wf Γ witness) :
    Sub Γ witness (.TSel (.var package) label) :=
  .selectLower member (.refl witnessWf)

/-- Compatibility helper for the upper rule of an exact member. -/
def selectExactUpper {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first)
    (witnessWf : Wf Γ witness) :
    Sub Γ (.TSel (.var package) label) witness :=
  .selectUpper member (.refl witnessWf)

end Sub

namespace Wf

/-- The exact package is the reflexive interval special case. -/
def exactPackage {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {witness : Ty n} (witnessWf : Wf Γ witness) :
    Wf Γ (exactPackageTy first label witness) :=
  .memberPackage witnessWf witnessWf (.refl witnessWf)

/-- Compatibility helper for a selection whose two bounds coincide. -/
def exactSelection {n : Nat} {Γ : Ctx n} {package first : Fin n}
    {label : Name} {witness : Ty n}
    (member : BoundExactMember Γ package label witness first)
    (witnessWf : Wf Γ witness) :
    Wf Γ (.TSel (.var package) label) :=
  .selection member (.refl witnessWf)

noncomputable def toLambdaPFC {n : Nat} {Γ : Ctx n} {T : Ty n} :
    Wf Γ T -> LambdaPFC.Tau.Wf Γ (.ty T)
| .top => .top
| .singleton pathTyping => .path pathTyping.toLambdaPFC
| .selection member nonempty =>
    .sel member.selection nonempty.toLambdaPFC
| .memberPackage (first := first) lowerWf upperWf nonempty => by
    apply LambdaPFC.Tau.Wf.pair
    · exact .path (LambdaPFC.Path.Ty.var :
        LambdaPFC.Path.Ty _ (.var first) (.ty _))
    · exact .bounds_wf
        (lowerWf.weaken (.Single (.var first))).toLambdaPFC
        (upperWf.weaken (.Single (.var first))).toLambdaPFC
        (nonempty.weaken (.Single (.var first))).toLambdaPFC
| .arrow domainWf codomainWf =>
    .fun domainWf.toLambdaPFC (codomainWf.weaken _).toLambdaPFC

end Wf

inductive HasType : {n : Nat} -> Ctx n -> Tm n -> Ty n -> Type where
| path {n : Nat} {Γ : Ctx n} {path : Path n} {T : Ty n} :
    PathTy Γ path T -> HasType Γ (.path path) (.Single path)
| abs {n : Nat} {Γ : Ctx n} {domain codomain : Ty n}
    {body : Tm (n + 1)} :
    HasType (Γ.snoc domain) body codomain.weaken ->
    Wf Γ domain -> Wf Γ codomain ->
    HasType Γ (.abs domain body) (.Fun domain codomain.weaken)
| app {n : Nat} {Γ : Ctx n} {function argument : Path n}
    {domain codomain : Ty n} :
    HasType Γ (.path function) (.Fun domain codomain.weaken) ->
    HasType Γ (.path argument) domain -> Wf Γ codomain ->
    HasType Γ (.app function argument) codomain
| typePackage {n : Nat} {Γ : Ctx n} {first : Fin n} {label : Name}
    {witness : Ty n} :
    Wf Γ witness ->
    HasType Γ (.pair first label (.type witness))
      (exactPackageTy first label witness)
| «let» {n : Nat} {Γ : Ctx n} {bound : Tm n} {boundType resultType : Ty n}
    {body : Tm (n + 1)} :
    HasType Γ bound boundType -> Wf Γ resultType ->
    HasType (Γ.snoc boundType) body resultType.weaken ->
    HasType Γ (.let bound body) resultType
| sub {n : Nat} {Γ : Ctx n} {term : Tm n} {S T : Ty n} :
    HasType Γ term S -> Sub Γ S T -> HasType Γ term T

namespace HasType

def typeWf {n : Nat} {Γ : Ctx n} {term : Tm n} {T : Ty n} :
    HasType Γ term T -> Wf Γ T
| .path pathTyping => .singleton pathTyping
| .abs _ domainWf codomainWf => .arrow domainWf codomainWf
| .app _ _ resultWf => resultWf
| .typePackage witnessWf => .exactPackage witnessWf
| .let _ resultWf _ => resultWf
| .sub _ subtype => subtype.targetWf

noncomputable def toLambdaPFC {n : Nat} {Γ : Ctx n} {term : Tm n}
    {T : Ty n} : HasType Γ term T -> LambdaPFC.Tm.Ty Γ term T
| .path pathTyping => .path pathTyping.toLambdaPFC
| .abs bodyTyping domainWf _ =>
    .abs bodyTyping.toLambdaPFC domainWf.toLambdaPFC
| .app functionTyping argumentTyping _ => by
    simpa only [Ty.weaken_open] using
      LambdaPFC.Tm.Ty.app
        functionTyping.toLambdaPFC argumentTyping.toLambdaPFC
| .typePackage witnessWf => .tpair witnessWf.toLambdaPFC
| .let boundTyping resultWf bodyTyping =>
    .let boundTyping.toLambdaPFC resultWf.toLambdaPFC
      bodyTyping.toLambdaPFC
| .sub termTyping subtype =>
    .sub termTyping.toLambdaPFC subtype.toLambdaPFC
      subtype.targetWf.toLambdaPFC

end HasType

end Fragment
end LambdaPToFCo
