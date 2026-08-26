import SystemFCoExt.TelescopeReduction
import SystemFCoExt.Safety

/-!
# Mixed-telescope Church-beta regression

The closed example exercises all three telescope binder kinds in one package.
Its consumer returns the oldest term field after crossing a type binder and a
coercion binder, so the endpoint checks the full heterogeneous substitution.
-/

namespace SystemFCoExt.TelescopeReductionRegression

open SystemFCoExt
open Telescope

def arrowTop : Ty {} :=
  .arrow .top .top

def identity : Exp {} :=
  .abs .top (.var .here)

def identityTyping :
    Ctx.empty |-e identity : arrowTop :=
  .abs (.var .here)

/-- A genuinely mixed telescope: term, type, then coercion evidence. -/
def mixed : Telescope {} :=
  .var arrowTop (.tvar (.cvar .top .top .nil))

def mixedArgs : Args Ctx.empty mixed :=
  .var identity identityTyping
    (.tvar arrowTop (.cvar (.refl .top) .refl .nil))

theorem mixedArgs_allValues : mixedArgs.AllValues :=
  ⟨.abs, trivial⟩

/-- Return the oldest term field after crossing the type and coercion
binders. -/
def body : Exp mixed.scope :=
  .var (.there (.there .here))

noncomputable def bodyTyping :
    Exp.HasType (mixed.context Ctx.empty) body
      (arrowTop.rename mixed.weaken) :=
  .var (.there (.there .here))

noncomputable def program : Exp {} :=
  mixed.unpack (mixed.pack mixedArgs) arrowTop body

noncomputable def programTyping :
    Ctx.empty |-e program : arrowTop :=
  mixed.unpack_hasType (Telescope.pack_hasType mixedArgs) bodyTyping

def result : Exp {} :=
  body.subst mixedArgs.substitution

theorem result_eq : result = identity :=
  rfl

theorem mixed_ne_nil : mixed ≠ .nil := by
  intro equal
  cases equal

theorem churchBeta : Exp.Steps program result :=
  mixed.unpack_pack_steps_of_ne_nil mixedArgs mixedArgs_allValues
    arrowTop body mixed_ne_nil

theorem churchBeta_identity : Exp.Steps program identity := by
  rw [← result_eq]
  exact churchBeta

theorem programSound : Not (Exp.GoesWrong program) :=
  Exp.soundness programTyping

end SystemFCoExt.TelescopeReductionRegression
