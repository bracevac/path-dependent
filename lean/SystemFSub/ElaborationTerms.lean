import SystemFSub.ElaborationSyntax

/-!
# Derivation-directed F<: elaboration

Source subtyping derivations become explicit target coercion terms. Source
subsumption becomes `cast`; a bounded type abstraction becomes an ordinary
type abstraction followed by a coercion abstraction.
-/

namespace SystemFSub.Elaboration

def elaborateSub {sig : SystemFSub.Sig}
    {context : SystemFSub.Ctx sig} {source target : SystemFSub.Ty sig} :
    SystemFSub.Ty.Sub context source target ->
      SystemFCo.Co (translateSig sig)
| .refl => .refl (translateTy source)
| .trans first second =>
    .trans (elaborateSub first) (elaborateSub second)
| .top => .top (translateTy source)
| @SystemFSub.Ty.Sub.bound _ _ X _ _ =>
    .cvar (translateBound X)
| .arrow parameter result =>
    .arrow (elaborateSub parameter) (elaborateSub result)
| .all bound body =>
    .poly (.qual
      (.trans (.cvar .here)
        (((elaborateSub bound).weaken .tvar).weaken .cvar))
      (elaborateSub body))

def elaborateTerm {sig : SystemFSub.Sig}
    {context : SystemFSub.Ctx sig} {term : SystemFSub.Tm sig}
    {ty : SystemFSub.Ty sig} :
    SystemFSub.Tm.HasType context term ty ->
      SystemFCo.Exp (translateSig sig)
| @SystemFSub.Tm.HasType.var _ _ x _ _ => .var (translateVar x)
| @SystemFSub.Tm.HasType.abs _ _ S _ _ body =>
    .abs (translateTy S) (elaborateTerm body)
| .app function argument =>
    .app (elaborateTerm function) (elaborateTerm argument)
| @SystemFSub.Tm.HasType.tabs _ _ B _ _ body =>
    .tabs (.cabs (.tvar .here) ((translateTy B).weaken .tvar)
      (elaborateTerm body))
| @SystemFSub.Tm.HasType.tapp _ _ _ _ _ U function bound =>
    .capp (.tapp (elaborateTerm function) (translateTy U))
      (elaborateSub bound)
| .sub term subtype =>
    .cast (elaborateTerm term) (elaborateSub subtype)

end SystemFSub.Elaboration
