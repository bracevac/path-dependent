import LambdaPFC.Valuation
import LambdaPToFCo.OperationalEnvironment
import LambdaPToFCo.TermTranslationSoundness

/-!
# Valuation-indexed source code in the LambdaP CK machine

The CK machine runs terms in the scope of its *current store*.  A typing
derivation, however, belongs to the lexical scope in which the source code
was written.  Allocation makes those two scopes diverge.  Consequently a
runtime term should not be assigned a fresh typing derivation in a context
invented from the current store.

This file records the smaller invariant needed by an operational
correspondence:

* `TypedCode` keeps the original term and its fragment typing derivation;
* `SourceValuation` maps its lexical variables to locations in the current
  store;
* `CodeImage` says that the current term is the renamed original code, or is
  the location obtained by the CK machine's administrative path-resolution
  step;
* every `FrameImage` retains its own original let body, typing derivation, and
  valuation.  `ContImage` therefore permits heterogeneous lexical origins in
  one runtime stack.

The allocation and return constructions below are only source-side shape
lemmas.  They deliberately make no simulation or source-soundness claim.
No semantic realization or runtime interpretation of source typing
derivations is used here.
-/

namespace LambdaPToFCo
namespace OperationalCode

open LambdaPFC
open StaticTranslation

/-! ## Renaming valuations -/

/-- A purely syntactic map from an original lexical scope to the current
store scope.  Calling this a valuation means only that source variables have
become store locations; it carries no semantic interpretation of types. -/
abbrev SourceValuation (original current : Nat) : Type :=
  LambdaPFC.FinFun original current

namespace SourceValuation

/-- The valuation of code that has not crossed an allocation boundary. -/
def identity : SourceValuation n n := LambdaPFC.FinFun.id

/-- Preserve all existing locations when the store grows by one cell. -/
def weaken (valuation : SourceValuation original current) :
    SourceValuation original (current + 1) :=
  valuation.comp LambdaPFC.FinFun.weaken

/-- Interpret a source binder by an already allocated store location. -/
def bind (valuation : SourceValuation original current)
    (location : Fin current) : SourceValuation (original + 1) current :=
  Fin.cases location valuation

@[simp] theorem identity_apply (index : Fin n) :
    identity index = index := rfl

@[simp] theorem weaken_apply
    (valuation : SourceValuation original current) (index : Fin original) :
    valuation.weaken index = (valuation index).succ := rfl

@[simp] theorem bind_zero
    (valuation : SourceValuation original current) (location : Fin current) :
    valuation.bind location 0 = location := rfl

@[simp] theorem bind_succ
    (valuation : SourceValuation original current) (location : Fin current)
    (index : Fin original) :
    valuation.bind location index.succ = valuation index := rfl

/-- Renaming original code and then weakening the runtime scope is the same
as weakening its valuation. -/
theorem rename_weaken (term : Tm original)
    (valuation : SourceValuation original current) :
    (term.rename valuation).weaken = term.rename valuation.weaken := by
  simp only [Tm.weaken, Tm.rename_rename, weaken]

/-- A suspended body keeps its newest, lexical binder fixed while all
locations in the surrounding store move across a fresh allocation. -/
theorem rename_ext_weaken (body : Tm (original + 1))
    (valuation : SourceValuation original current) :
    (body.rename valuation.ext).rename LambdaPFC.FinFun.weaken.ext =
      body.rename valuation.weaken.ext := by
  rw [Tm.rename_rename, LambdaPFC.FinFun.ext_comp]
  rfl

/-- Returning a location to a suspended body replaces the body's lexical
binder by that location in the valuation. -/
theorem rename_ext_openAt (body : Tm (original + 1))
    (valuation : SourceValuation original current)
    (location : Fin current) :
    (body.rename valuation.ext).open location =
      body.rename (valuation.bind location) := by
  simpa only [Tm.open, bind] using
    (LambdaPFC.Tm.rename_ext_openAt body valuation location)

end SourceValuation

/-! ## Original typed code and its target compilation -/

/-- Source code together with the fragment derivation from its original
lexical context.  This data does not change when the machine allocates. -/
structure TypedCode : Type where
  arity : Nat
  context : LambdaPFC.Ctx arity
  term : LambdaPFC.Tm arity
  resultType : LambdaPFC.Ty arity
  typing : Fragment.HasType context term resultType

namespace TypedCode

def ofTyping
    {arity : Nat} {context : LambdaPFC.Ctx arity}
    {term : LambdaPFC.Tm arity} {resultType : LambdaPFC.Ty arity}
    (typing : Fragment.HasType context term resultType) : TypedCode where
  arity := arity
  context := context
  term := term
  resultType := resultType
  typing := typing

/-- Static target data for compiling original code.  In particular, the
compiler consumes the original derivation, not a derivation reconstructed at
the current store scope. -/
structure Compilation (code : TypedCode) : Type where
  targetSig : SystemFCo.Sig
  targetContext : SystemFCo.Ctx targetSig
  scope : StaticTranslation.Scope code.context targetContext
  coherent : scope.Coherent

namespace Compilation

/-- The open target expression generated from the retained source code. -/
noncomputable def expression (compilation : Compilation code) :
    SystemFCo.Exp compilation.targetSig :=
  TermTranslation.elaborate compilation.scope code.typing

/-- Type preservation applies directly to the retained original derivation. -/
noncomputable def expression_hasType (compilation : Compilation code) :
    SystemFCo.Exp.HasType compilation.targetContext compilation.expression
      (StaticTranslation.translateType compilation.scope
        code.typing.typeWf) :=
  TermTranslation.elaborate_hasType compilation.coherent code.typing

/-- Close an open compiled term with separately maintained target syntax.
The eventual simulation invariant must relate this substitution to the
source valuation; this definition intentionally does not assert that fact. -/
noncomputable def close (compilation : Compilation code)
    (environment : OperationalEnvironment.ClosingEnv
      compilation.targetSig []) : SystemFCo.Exp [] :=
  environment.closeExp compilation.expression

end Compilation

/-- The canonical compilation of closed original code. -/
noncomputable def closedCompilation
    {term : LambdaPFC.Tm 0} {resultType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term resultType) :
    Compilation (ofTyping typing) where
  targetSig := []
  targetContext := SystemFCo.Ctx.empty
  scope := StaticTranslation.Scope.empty
  coherent := StaticTranslation.Scope.Coherent.empty

end TypedCode

/-! ## Current-code images -/

/-- The two source-runtime forms of retained original code.

`direct` is ordinary valuation closure.  `resolvedPath` is necessary because
after CK path resolution the term `x` is usually not syntactically a renaming
of the original path `p`; the resolution derivation is the missing
administrative evidence. -/
inductive RuntimeForm {current : Nat} (store : LambdaPFC.Store current)
    (code : TypedCode) : LambdaPFC.Tm current -> Type where
| direct
    (valuation : SourceValuation code.arity current)
    (runtime_eq : runtime = code.term.rename valuation) :
    RuntimeForm store code runtime
| resolvedPath
    (path : LambdaPFC.Path code.arity)
    (term_eq : code.term = .path path)
    (valuation : SourceValuation code.arity current)
    (location : Fin current)
    (resolution : LambdaPFC.Path.Resolve (path.rename valuation) store
      (.loc location)) :
    RuntimeForm store code (.path (.var location))

/-- A current machine term paired with its immutable, originally typed code
and the syntactic closure explaining the current runtime form. -/
structure CodeImage {current : Nat} (store : LambdaPFC.Store current)
    (runtime : LambdaPFC.Tm current) : Type where
  original : TypedCode
  form : RuntimeForm store original runtime

namespace CodeImage

/-- Initially the lexical and store scopes are both empty. -/
def initial
    {term : LambdaPFC.Tm 0} {resultType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term resultType) :
    CodeImage LambdaPFC.Store.empty term where
  original := TypedCode.ofTyping typing
  form := .direct SourceValuation.identity
    (LambdaPFC.Tm.rename_id term).symm

/-- The direct image immediately before a CK path-resolution step. -/
def beforePath
    {original : Nat} {context : LambdaPFC.Ctx original}
    {path : LambdaPFC.Path original} {resultType : LambdaPFC.Ty original}
    (typing : Fragment.HasType context (.path path) resultType)
    (valuation : SourceValuation original current) :
    CodeImage store (.path (path.rename valuation)) where
  original := TypedCode.ofTyping typing
  form := .direct valuation rfl

/-- The retained image immediately after CK path resolution. -/
def afterPath
    {original : Nat} {context : LambdaPFC.Ctx original}
    {path : LambdaPFC.Path original} {resultType : LambdaPFC.Ty original}
    (typing : Fragment.HasType context (.path path) resultType)
    (valuation : SourceValuation original current)
    (resolution : LambdaPFC.Path.Resolve (path.rename valuation) store
      (.loc location)) :
    CodeImage store (.path (.var location)) where
  original := TypedCode.ofTyping typing
  form := .resolvedPath path rfl valuation location resolution

/-- Weakening an image across an allocation preserves both direct code and
resolved paths.  This is a structural lemma; the CK allocation rule uses the
more specific frame construction below for its new current term. -/
noncomputable def weaken
    {current : Nat} {store : LambdaPFC.Store current}
    {runtime : LambdaPFC.Tm current}
    (image : CodeImage store runtime)
    (value : LambdaPFC.Tm current) (isValue : value.IsValue) :
    CodeImage (.val store value isValue) runtime.weaken := by
  rcases image with ⟨code, form⟩
  cases form with
  | direct valuation runtime_eq =>
      exact
        { original := code
          form := .direct valuation.weaken (by
            rw [runtime_eq]
            exact SourceValuation.rename_weaken code.term valuation) }
  | resolvedPath path term_eq valuation location resolution =>
      have weakenedResolution :
          LambdaPFC.Path.Resolve (path.rename valuation.weaken)
            (.val store value isValue) (.loc location.succ) := by
        simpa only [SourceValuation.weaken, LambdaPFC.Path.weaken,
          LambdaPFC.Path.rename_rename] using
          resolution.weaken value isValue
      exact
        { original := code
          form := .resolvedPath path term_eq valuation.weaken location.succ
            weakenedResolution }

end CodeImage

/-! ## Saved let bodies -/

/-- Image of one suspended source `let` body.

The body is typed once, in its original context extended by the lexical hole
binder.  At runtime `valuation.ext` leaves that binder at index zero and maps
all older variables to their current store locations. -/
structure FrameImage {current : Nat}
    (runtimeBody : LambdaPFC.Tm (current + 1)) : Type where
  originalArity : Nat
  context : LambdaPFC.Ctx originalArity
  holeType : LambdaPFC.Ty originalArity
  resultType : LambdaPFC.Ty originalArity
  body : LambdaPFC.Tm (originalArity + 1)
  holeWf : Fragment.Wf context holeType
  resultWf : Fragment.Wf context resultType
  bodyTyping : Fragment.HasType (context.snoc holeType) body
    resultType.weaken
  valuation : SourceValuation originalArity current
  runtime_eq : runtimeBody = body.rename valuation.ext

namespace FrameImage

/-- Allocation shifts existing store locations but leaves the suspended
body's lexical hole fixed. -/
noncomputable def weaken (frame : FrameImage runtimeBody) :
    FrameImage (runtimeBody.rename LambdaPFC.FinFun.weaken.ext) where
  originalArity := frame.originalArity
  context := frame.context
  holeType := frame.holeType
  resultType := frame.resultType
  body := frame.body
  holeWf := frame.holeWf
  resultWf := frame.resultWf
  bodyTyping := frame.bodyTyping
  valuation := frame.valuation.weaken
  runtime_eq := by
    calc
      runtimeBody.rename LambdaPFC.FinFun.weaken.ext =
          (frame.body.rename frame.valuation.ext).rename
            LambdaPFC.FinFun.weaken.ext :=
        congrArg
          (fun term => term.rename LambdaPFC.FinFun.weaken.ext)
          frame.runtime_eq
      _ = frame.body.rename frame.valuation.weaken.ext :=
        SourceValuation.rename_ext_weaken frame.body frame.valuation

/-- After allocating the value computed for this frame, its hole denotes the
newest store cell.  The saved runtime body is therefore direct code under the
lifted valuation. -/
def enterAfterAllocation
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : FrameImage runtimeBody)
    (store : LambdaPFC.Store current)
    (value : LambdaPFC.Tm current) (isValue : value.IsValue) :
    CodeImage (.val store value isValue) runtimeBody where
  original :=
    { arity := frame.originalArity + 1
      context := frame.context.snoc frame.holeType
      term := frame.body
      resultType := frame.resultType.weaken
      typing := frame.bodyTyping }
  form := .direct frame.valuation.ext frame.runtime_eq

/-- Returning an existing location opens the saved body and binds its
lexical hole to that location in the retained valuation. -/
def enterAfterReturn
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : FrameImage runtimeBody)
    (store : LambdaPFC.Store current) (location : Fin current) :
    CodeImage store (runtimeBody.open location) where
  original :=
    { arity := frame.originalArity + 1
      context := frame.context.snoc frame.holeType
      term := frame.body
      resultType := frame.resultType.weaken
      typing := frame.bodyTyping }
  form := .direct (frame.valuation.bind location) (by
    calc
      runtimeBody.open location =
          (frame.body.rename frame.valuation.ext).open location :=
        congrArg (fun term => term.open location) frame.runtime_eq
      _ = frame.body.rename (frame.valuation.bind location) :=
        SourceValuation.rename_ext_openAt frame.body frame.valuation
          location)

end FrameImage

/-- Heterogeneous images of all suspended bodies.  Each constructor packages
its own original context and valuation; only the current store scope is
shared by the runtime continuation. -/
inductive ContImage {current : Nat} : LambdaPFC.Tm.Cont current -> Type where
| nil : ContImage []
| cons {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current} :
    FrameImage runtimeBody -> ContImage runtimeRest ->
    ContImage (runtimeBody :: runtimeRest)

namespace ContImage

/-- Allocation weakens every remaining frame valuation and runtime body. -/
noncomputable def weaken : {runtime : LambdaPFC.Tm.Cont current} ->
    ContImage runtime -> ContImage runtime.weaken
| [], .nil => .nil
| _ :: _, .cons frame rest => .cons frame.weaken rest.weaken

/-- Source images obtained by the CK `return` shape: the head frame becomes
the current code and the rest of the continuation is unchanged. -/
def afterReturn
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (image : ContImage (runtimeBody :: runtimeRest))
    (store : LambdaPFC.Store current) (location : Fin current) :
    CodeImage store (runtimeBody.open location) × ContImage runtimeRest := by
  cases image with
  | cons frame rest => exact ⟨frame.enterAfterReturn store location, rest⟩

/-- Source images obtained by the CK `allocate` shape: the head frame becomes
current code under `valuation.ext`, while all outer frames cross the new
store cell by weakening their valuations. -/
noncomputable def afterAllocation
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (image : ContImage (runtimeBody :: runtimeRest))
    (store : LambdaPFC.Store current)
    (value : LambdaPFC.Tm current) (isValue : value.IsValue) :
    CodeImage (.val store value isValue) runtimeBody ×
      ContImage (LambdaPFC.Tm.Cont.weaken runtimeRest) := by
  cases image with
  | cons frame rest =>
      exact ⟨frame.enterAfterAllocation store value isValue, rest.weaken⟩

end ContImage

/-! ## Minimal state invariant and its initial inhabitant -/

/-- Source-side code/stack shape retained by a future target simulation.
There is intentionally no requirement that the independently-originating
current term and continuation frames share one lexical typing context. -/
structure StateCodeImage {current : Nat} (state : LambdaPFC.State current) :
    Type where
  currentCode : CodeImage state.store state.term
  continuation : ContImage state.cont

namespace StateCodeImage

/-- Every closed, fragment-typed source program has the canonical initial
valuation-indexed image. -/
def initial
    {term : LambdaPFC.Tm 0} {resultType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term resultType) :
    StateCodeImage (LambdaPFC.State.initial term) where
  currentCode := CodeImage.initial typing
  continuation := .nil

end StateCodeImage

end OperationalCode
end LambdaPToFCo
