import SystemFSub.ElaborationSyntax

/-!
The source-to-target scope map expands each source type binder into a target
type binder followed by its bound-evidence binder.  The translations below
are bijections at each variable sort, and therefore transport every source
renaming to the expanded target signatures.
-/

namespace SystemFSub.Elaboration

def untranslateVar : {sig : SystemFSub.Sig} ->
    SystemFCo.BVar (translateSig sig) .var -> SystemFSub.BVar sig .var
  | [], x => nomatch x
  | .var :: tail, .here => .here
  | .var :: tail, .there x => .there (untranslateVar x)
  | .tvar :: tail, .there (.there x) => .there (untranslateVar x)

def untranslateTVar : {sig : SystemFSub.Sig} ->
    SystemFCo.BVar (translateSig sig) .tvar -> SystemFSub.BVar sig .tvar
  | [], x => nomatch x
  | .var :: tail, .there x => .there (untranslateTVar x)
  | .tvar :: tail, .there .here => .here
  | .tvar :: tail, .there (.there x) => .there (untranslateTVar x)

def untranslateBound : {sig : SystemFSub.Sig} ->
    SystemFCo.BVar (translateSig sig) .cvar -> SystemFSub.BVar sig .tvar
  | [], x => nomatch x
  | .var :: tail, .there x => .there (untranslateBound x)
  | .tvar :: tail, .here => .here
  | .tvar :: tail, .there (.there x) => .there (untranslateBound x)

def translateRename (rename : SystemFSub.Rename source target) :
    SystemFCo.Rename (translateSig source) (translateSig target) where
  var := fun {kind} x => match kind with
    | .var => translateVar (rename.var (untranslateVar x))
    | .tvar => translateTVar (rename.var (untranslateTVar x))
    | .cvar => translateBound (rename.var (untranslateBound x))

/-! ## Both directions of the variable bijections -/

@[simp] theorem untranslate_translateVar :
    {sig : SystemFSub.Sig} -> (x : SystemFSub.BVar sig .var) ->
    untranslateVar (translateVar x) = x
  | _, .here => rfl
  | _, @SystemFSub.BVar.there _ _ .var x =>
      congrArg SystemFSub.BVar.there (untranslate_translateVar x)
  | _, @SystemFSub.BVar.there _ _ .tvar x =>
      congrArg SystemFSub.BVar.there (untranslate_translateVar x)

@[simp] theorem untranslate_translateTVar :
    {sig : SystemFSub.Sig} -> (x : SystemFSub.BVar sig .tvar) ->
    untranslateTVar (translateTVar x) = x
  | _, .here => rfl
  | _, @SystemFSub.BVar.there _ _ .var x =>
      congrArg SystemFSub.BVar.there (untranslate_translateTVar x)
  | _, @SystemFSub.BVar.there _ _ .tvar x =>
      congrArg SystemFSub.BVar.there (untranslate_translateTVar x)

@[simp] theorem untranslate_translateBound :
    {sig : SystemFSub.Sig} -> (x : SystemFSub.BVar sig .tvar) ->
    untranslateBound (translateBound x) = x
  | _, .here => rfl
  | _, @SystemFSub.BVar.there _ _ .var x =>
      congrArg SystemFSub.BVar.there (untranslate_translateBound x)
  | _, @SystemFSub.BVar.there _ _ .tvar x =>
      congrArg SystemFSub.BVar.there (untranslate_translateBound x)

@[simp] theorem translate_untranslateVar :
    {sig : SystemFSub.Sig} ->
    (x : SystemFCo.BVar (translateSig sig) .var) ->
    translateVar (untranslateVar x) = x
  | [], x => nomatch x
  | .var :: tail, .here => rfl
  | .var :: tail, .there x =>
      congrArg SystemFCo.BVar.there (translate_untranslateVar x)
  | .tvar :: tail, .there (.there x) =>
      congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateVar x))

@[simp] theorem translate_untranslateTVar :
    {sig : SystemFSub.Sig} ->
    (x : SystemFCo.BVar (translateSig sig) .tvar) ->
    translateTVar (untranslateTVar x) = x
  | [], x => nomatch x
  | .var :: tail, .there x =>
      congrArg SystemFCo.BVar.there (translate_untranslateTVar x)
  | .tvar :: tail, .there .here => rfl
  | .tvar :: tail, .there (.there x) =>
      congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateTVar x))

@[simp] theorem translate_untranslateBound :
    {sig : SystemFSub.Sig} ->
    (x : SystemFCo.BVar (translateSig sig) .cvar) ->
    translateBound (untranslateBound x) = x
  | [], x => nomatch x
  | .var :: tail, .there x =>
      congrArg SystemFCo.BVar.there (translate_untranslateBound x)
  | .tvar :: tail, .here => rfl
  | .tvar :: tail, .there (.there x) =>
      congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateBound x))

/-! ## Renaming on translated variables -/

@[simp] theorem translateRename_var
    (rename : SystemFSub.Rename source target)
    (x : SystemFSub.BVar source .var) :
    (translateRename rename).var (translateVar x) =
      translateVar (rename.var x) := by
  simp [translateRename]

@[simp] theorem translateRename_tvar
    (rename : SystemFSub.Rename source target)
    (x : SystemFSub.BVar source .tvar) :
    (translateRename rename).var (translateTVar x) =
      translateTVar (rename.var x) := by
  simp [translateRename]

@[simp] theorem translateRename_bound
    (rename : SystemFSub.Rename source target)
    (x : SystemFSub.BVar source .tvar) :
    (translateRename rename).var (translateBound x) =
      translateBound (rename.var x) := by
  simp [translateRename]

@[simp] theorem untranslateVar_translateRename
    (rename : SystemFSub.Rename source target)
    (x : SystemFCo.BVar (translateSig source) .var) :
    untranslateVar ((translateRename rename).var x) =
      rename.var (untranslateVar x) := by
  change untranslateVar (translateVar (rename.var (untranslateVar x))) = _
  simp

@[simp] theorem untranslateTVar_translateRename
    (rename : SystemFSub.Rename source target)
    (x : SystemFCo.BVar (translateSig source) .tvar) :
    untranslateTVar ((translateRename rename).var x) =
      rename.var (untranslateTVar x) := by
  change untranslateTVar (translateTVar (rename.var (untranslateTVar x))) = _
  simp

@[simp] theorem untranslateBound_translateRename
    (rename : SystemFSub.Rename source target)
    (x : SystemFCo.BVar (translateSig source) .cvar) :
    untranslateBound ((translateRename rename).var x) =
      rename.var (untranslateBound x) := by
  change untranslateBound (translateBound (rename.var (untranslateBound x))) = _
  simp

end SystemFSub.Elaboration
