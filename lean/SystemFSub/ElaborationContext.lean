import SystemFSub.ElaborationRenameLaws

/-!
Lookup transport for the expanded elaboration context.  A source type-bound
lookup produces both membership of the translated type variable and lookup of
its paired coercion evidence.
-/

namespace SystemFSub.Elaboration

/-- Translate lookup of a source term-variable assumption. -/
def translateLookupVar :
    {sig : SystemFSub.Sig} ->
    {context : SystemFSub.Ctx sig} ->
    {index : SystemFSub.BVar sig .var} -> {ty : SystemFSub.Ty sig} ->
    context.LookupVar index ty ->
    SystemFCo.Ctx.VarLookup (translateCtx context)
      (translateVar index) (translateTy ty)
  | _, _, _, _, @SystemFSub.Ctx.LookupVar.here sig context ty => by
      have target := @SystemFCo.Ctx.Lookup.here
        (translateSig sig) .var (translateCtx context)
        (.var (translateTy ty))
      simpa only [translateCtx, translateVar, translateTy_weaken_var]
        using target
  | _, _, _, _, @SystemFSub.Ctx.LookupVar.there sig .var context index ty
      (.var addedTy) lookup => by
      have target := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.var (translateTy addedTy))
        (translateLookupVar lookup)
      simpa only [translateCtx, translateVar, translateTy_weaken_var]
        using target
  | _, _, _, _, @SystemFSub.Ctx.LookupVar.there sig .tvar context index ty
      (.tvar bound) lookup => by
      have throughTVar := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.tvar)
        (translateLookupVar lookup)
      have throughBound := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.cvar
          (.tvar .here) ((translateTy bound).weaken .tvar))
        throughTVar
      simpa only [translateCtx, translateVar, translateTy_weaken_tvar]
        using throughBound

/-- Translate membership of a source type variable. -/
def translateLookupTVar :
    {sig : SystemFSub.Sig} ->
    {context : SystemFSub.Ctx sig} ->
    {index : SystemFSub.BVar sig .tvar} -> {bound : SystemFSub.Ty sig} ->
    context.LookupTVar index bound ->
    SystemFCo.Ctx.TVarLookup (translateCtx context) (translateTVar index)
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.here sig context bound => by
      have atTypeBinder := @SystemFCo.Ctx.Lookup.here
        (translateSig sig) .tvar (translateCtx context)
        SystemFCo.Binding.tvar
      have throughBound := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.cvar
          (.tvar .here) ((translateTy bound).weaken .tvar))
        atTypeBinder
      simpa only [translateCtx, translateTVar] using throughBound
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.there sig .var context index bound
      (.var addedTy) lookup => by
      have target := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.var (translateTy addedTy))
        (translateLookupTVar lookup)
      simpa only [translateCtx, translateTVar] using target
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.there sig .tvar context index bound
      (.tvar addedBound) lookup => by
      have throughTVar := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.tvar)
        (translateLookupTVar lookup)
      have throughBound := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.cvar
          (.tvar .here) ((translateTy addedBound).weaken .tvar))
        throughTVar
      simpa only [translateCtx, translateTVar] using throughBound

/-- Translate a source bound lookup to its paired coercion-variable lookup. -/
def translateLookupBound :
    {sig : SystemFSub.Sig} ->
    {context : SystemFSub.Ctx sig} ->
    {index : SystemFSub.BVar sig .tvar} -> {bound : SystemFSub.Ty sig} ->
    context.LookupTVar index bound ->
    SystemFCo.Ctx.CVarLookup (translateCtx context)
      (translateBound index) (.tvar (translateTVar index))
      (translateTy bound)
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.here sig context bound => by
      have target := @SystemFCo.Ctx.Lookup.here
        (translateSig sig ,, .tvar) .cvar
        (translateCtx context).bindTVar
        (SystemFCo.Binding.cvar
          (.tvar .here) ((translateTy bound).weaken .tvar))
      simpa only [translateCtx, translateBound, translateTVar,
        translateTy_weaken_tvar] using target
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.there sig .var context index bound
      (.var addedTy) lookup => by
      have target := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.var (translateTy addedTy))
        (translateLookupBound lookup)
      simpa only [translateCtx, translateBound, translateTVar,
        translateTy_weaken_var] using target
  | _, _, _, _, @SystemFSub.Ctx.LookupTVar.there sig .tvar context index bound
      (.tvar addedBound) lookup => by
      have throughTVar := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.tvar)
        (translateLookupBound lookup)
      have throughBound := SystemFCo.Ctx.Lookup.there
        (newBinding := SystemFCo.Binding.cvar
          (.tvar .here) ((translateTy addedBound).weaken .tvar))
        throughTVar
      simpa only [translateCtx, translateBound, translateTVar,
        translateTy_weaken_tvar] using throughBound

end SystemFSub.Elaboration
