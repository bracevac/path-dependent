import SystemFSub.Substitution

/-!
# Proof-relevant declarative System F<:

Term assumptions and type-variable bounds inhabit one dependent context whose
index is the mixed signature.  Subtyping and typing derivations live in
`Type`, so later elaboration may recurse over their evidence.
-/

namespace SystemFSub

/-- The payload associated with a binder of each source-variable sort. -/
inductive Binding : Sig -> Kind -> Type where
| var : Ty s -> Binding s .var
| tvar : Ty s -> Binding s .tvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, rho => .var (T.rename rho)
| .tvar B, rho => .tvar (B.rename rho)

/-- A context whose binding sequence agrees exactly with its signature. -/
inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s ,, k)

def Ctx.pushVar (Gamma : Ctx s) (T : Ty s) : Ctx (s,x) :=
  Gamma.push (.var T)

def Ctx.pushTVar (Gamma : Ctx s) (B : Ty s) : Ctx (s,X) :=
  Gamma.push (.tvar B)

infixl:65 ",x:" => Ctx.pushVar
infixl:65 ",X<:" => Ctx.pushTVar

/-- Proof-relevant lookup of a term-variable assumption. -/
inductive Ctx.LookupVar : Ctx s -> BVar s .var -> Ty s -> Type where
| here :
    Ctx.LookupVar (.push Gamma (.var T)) .here (T.weaken (k := .var))
| there {T : Ty s} {b : Binding s k} :
    Ctx.LookupVar Gamma x T ->
    Ctx.LookupVar (.push Gamma b) (.there x) (T.weaken (k := k))

/-- Proof-relevant lookup of a type-variable upper bound. -/
inductive Ctx.LookupTVar : Ctx s -> BVar s .tvar -> Ty s -> Type where
| here :
    Ctx.LookupTVar (.push Gamma (.tvar B)) .here (B.weaken (k := .tvar))
| there {B : Ty s} {b : Binding s k} :
    Ctx.LookupTVar Gamma X B ->
    Ctx.LookupTVar (.push Gamma b) (.there X) (B.weaken (k := k))

namespace Ty

/-- Full declarative F<: subtyping, with explicit reflexivity/transitivity. -/
inductive Sub : {s : Sig} -> Ctx s -> Ty s -> Ty s -> Type where
| refl : Sub Gamma T T
| trans : Sub Gamma S T -> Sub Gamma T U -> Sub Gamma S U
| top : Sub Gamma T .top
| bound : Ctx.LookupTVar Gamma X B -> Sub Gamma (.tvar X) B
| arrow :
    Sub Gamma Tdom Sdom ->
    Sub Gamma Scod Tcod ->
    Sub Gamma (.arrow Sdom Scod) (.arrow Tdom Tcod)
| all :
    Sub Gamma Tbound Sbound ->
    Sub (Gamma,X<:Tbound) Sbody Tbody ->
    Sub Gamma (.all Sbound Sbody) (.all Tbound Tbody)

end Ty

namespace Tm

/-- Declarative typing for general source terms, including subsumption. -/
inductive HasType : {s : Sig} -> Ctx s -> Tm s -> Ty s -> Type where
| var : Ctx.LookupVar Gamma x T -> HasType Gamma (.var x) T
| abs :
    HasType (Gamma,x:S) t (T.weaken (k := .var)) ->
    HasType Gamma (.abs S t) (.arrow S T)
| app :
    HasType Gamma f (.arrow S T) ->
    HasType Gamma a S ->
    HasType Gamma (.app f a) T
| tabs :
    HasType (Gamma,X<:B) t T ->
    HasType Gamma (.tabs B t) (.all B T)
| tapp :
    HasType Gamma f (.all B T) ->
    SystemFSub.Ty.Sub Gamma U B ->
    HasType Gamma (.tapp f U) (T.open U)
| sub :
    HasType Gamma t S ->
    SystemFSub.Ty.Sub Gamma S T ->
    HasType Gamma t T

end Tm

notation:50 Gamma " |- " S " <: " T => Ty.Sub Gamma S T
notation:50 Gamma " |- " t " : " T => Tm.HasType Gamma t T

end SystemFSub
