import Coercions.DotMNF.WadlerFest.Correspondence

/-!
# An annotated self-dependent object

The program binds `ν(self : {A : ⊤..⊤} ∧ {a : self.A})
({A = ⊤} ∧ {a = self})` and projects its field `a`.

Inside the object, `Var` supplies the opened self type directly. Subtyping
through the lower bound of `self.A` types the field body `self`. After the
object is bound, recursive elimination recovers the member declarations.
The correspondence changes the self-context representation while retaining
the program after annotation erasure.
-/

namespace WadlerFest.Examples

open FCdot (Sig BVar Label)
open DotMNF (Ty)

def A : Label := .typ 0
def a : Label := .trm 0

def selfType : Ty ([],x) :=
  .and (.typ A .top .top) (.fld a (.sel (.var .here) A))

def objectDefs : Defs ([],x) :=
  .and (.typ A .top) (.trm a (.path (.var .here)))

def object : Tm [] := .val (.obj selfType objectDefs)

def openedSelf : Ctx ([],x) := Ctx.nil.extend selfType

def selfAlias : HasTy openedSelf (.path (.var .here)) (.typ A .top .top) :=
  .sub .var .and1

def selfAtSelection : HasTy openedSelf (.path (.var .here)) (.sel (.var .here) A) :=
  .sub .var (.trans .top (.selLower selfAlias))

def objectDefs_typed : DefsTy openedSelf objectDefs selfType :=
  .and .typ (.trm selfAtSelection) (by
    intro ℓ h
    simp only [Defs.labels, List.mem_singleton] at h ⊢
    subst ℓ
    decide)

def object_typed : HasTy .nil object (.mu selfType) := .obj objectDefs_typed

def boundObject : Ctx ([],x) := Ctx.nil.cons (.mu selfType)

def boundSelf : HasTy boundObject (.path (.var .here)) selfType := by
  have h : HasTy boundObject (.path (.var .here))
      ((selfType.rename FCdot.Rename.succ.lift).substVar .here) := .recE .var
  simpa only [DotMNF.Ty.open_self] using h

def projection_typed : HasTy boundObject (.proj .here a) .top :=
  .sub (.proj (.sub boundSelf .and2)) (.selUpper (.sub boundSelf .and1))

def program : Tm [] := .let object (.proj .here a)

def program_typed : HasTy .nil program .top := .let object_typed projection_typed

/-- The independently typed annotated program is accepted by DOT-MNF. -/
def program_erased_typed : DotMNF.HasTy .nil program.eraseAnnotations .top :=
  program_typed.eraseAnnotations_closed

/-- The annotation is removed, and the self-referencing field is retained. -/
theorem program_erases : program.eraseAnnotations =
    .let (.val (.obj (.and (.typ A .top) (.trm a (.path (.var .here))))))
      (.proj .here a) := rfl

end WadlerFest.Examples
