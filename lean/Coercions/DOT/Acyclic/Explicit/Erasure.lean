import Coercions.DOT.Acyclic.Explicit.Typing
import Coercions.DOT.Acyclic.Source.Runtime

/-!
# Erasure for the explicitly coerced calculus

Equality proofs, directed coercions, exposure recipes, and reusable member
handles are static.  Erasure removes all of them.  Exact-object binding keeps
only the unit-like runtime object and drops its private equality binder.
-/

namespace DotFC.Explicit

open DotFC

namespace Runtime

/-- Rename only the term variables occurring in an erased term.  This is more
general than `DotFC.Rename`: it can also remove a proof-only binder, because
an erased term cannot contain a variable of that kind. -/
def renameTerms {s₁ s₂ : Sig} (term : Source.Runtime.Tm s₁)
    (rho : ScopedTy.TermRename s₁ s₂) : Source.Runtime.Tm s₂ :=
  match term with
  | .var path => .var (rho.var path)
  | .lam body => .lam (renameTerms body rho.lift)
  | .obj => .obj
  | .app function argument =>
      .app (renameTerms function rho) (renameTerms argument rho)
  | .let' rhs body => .let' (renameTerms rhs rho) (renameTerms body rho.lift)

@[simp]
theorem renameTerms_var {s₁ s₂ : Sig} (path : BVar s₁ .term)
    (rho : ScopedTy.TermRename s₁ s₂) :
    renameTerms (.var path) rho = .var (rho.var path) := rfl

@[simp]
theorem renameTerms_lam {s₁ s₂ : Sig} (body : Source.Runtime.Tm (s₁ ▹ .term))
    (rho : ScopedTy.TermRename s₁ s₂) :
    renameTerms (.lam body) rho = .lam (renameTerms body rho.lift) := rfl

end Runtime

namespace Tm

/-- Erase an explicitly coerced term to the common untyped CBV runtime.

The `letHandle` case removes its non-runtime binder.  The `letExact` case
retains an ordinary let-bound object but removes the private equality binder
before erasing the body of that let. -/
def erase {s : Sig} (term : Tm s) : Source.Runtime.Tm s :=
  match term with
  | .var path => .var path
  | .lam _ body => .lam (erase body)
  | .obj _ _ => .obj
  | .app function argument _ _ => .app (.var function) (.var argument)
  | .let' rhs body => .let' (erase rhs) (erase body)
  | .cast term _ => erase term
  | .letHandle _ body =>
      Runtime.renameTerms (erase body) ScopedTy.TermRename.dropMember
  | .letExact _ _ body =>
      .let' .obj
        (Runtime.renameTerms (erase body) ScopedTy.TermRename.dropEvidence)

@[simp]
theorem erase_var {s : Sig} (path : BVar s .term) :
    (Tm.var path).erase = Source.Runtime.Tm.var path := rfl

@[simp]
theorem erase_lam {s : Sig} (domain : Source.Ty s) (body : Tm (s ▹ .term)) :
    (Tm.lam domain body).erase = Source.Runtime.Tm.lam body.erase := rfl

@[simp]
theorem erase_obj {s : Sig} (label : Name) (witness : Source.Ty s) :
    (Tm.obj label witness).erase = (Source.Runtime.Tm.obj : Source.Runtime.Tm s) := rfl

@[simp]
theorem erase_app {s : Sig} (function argument : BVar s .term)
    (functionView argumentView : LeCo s) :
    (Tm.app function argument functionView argumentView).erase =
      Source.Runtime.Tm.app (.var function) (.var argument) := rfl

@[simp]
theorem erase_let {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) :
    (Tm.let' rhs body).erase =
      Source.Runtime.Tm.let' rhs.erase body.erase := rfl

@[simp]
theorem erase_cast {s : Sig} (term : Tm s) (inclusion : LeCo s) :
    (Tm.cast term inclusion).erase = term.erase := rfl

@[simp]
theorem erase_letHandle {s : Sig} (exposure : Exposure s)
    (body : Tm (s ▹ .member)) :
    (Tm.letHandle exposure body).erase =
      Runtime.renameTerms body.erase ScopedTy.TermRename.dropMember := rfl

@[simp]
theorem erase_letExact {s : Sig} (label : Name) (witness : Source.Ty s)
    (body : Tm ((s ▹ .term) ▹ .evidence .equality)) :
    (Tm.letExact label witness body).erase =
      Source.Runtime.Tm.let' .obj
        (Runtime.renameTerms body.erase ScopedTy.TermRename.dropEvidence) := rfl

end Tm

end DotFC.Explicit
