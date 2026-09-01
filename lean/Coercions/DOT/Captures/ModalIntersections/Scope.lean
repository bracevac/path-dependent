import Coercions.DOT.Captures.Acyclic.Scope
import Coercions.DOT.Captures.BinderOnly.Scope

/-!
# Heterogeneous source scopes for modal captured intersections

This layer reuses the binder-only source's scope algebra.  Its syntax can
therefore contain ordinary term variables together with lexically bound type
and capture variables, while the all-term scopes used by the captured-DOT
intersection language remain a literal subfamily.
-/

namespace DOTCapture.ModalIntersections

abbrev StaticSort := DOTCapture.BinderOnly.StaticSort
abbrev BinderKind := DOTCapture.BinderOnly.BinderKind
abbrev Sig := DOTCapture.BinderOnly.Sig
abbrev BVar := DOTCapture.BinderOnly.BVar
abbrev Rename := DOTCapture.BinderOnly.Rename

/-- The heterogeneous presentation of a term-only captured-DOT scope. -/
@[simp]
def termScope : Nat → Sig
  | 0 => []
  | scope + 1 => termScope scope ▹ .term

/-- Embed an acyclic captured-DOT variable in the corresponding all-term
heterogeneous scope. -/
def embedVar : {scope : Nat} →
    DOTCapture.Acyclic.Var scope → BVar (termScope scope) .term
  | _ + 1, .here => .here
  | _ + 1, .there index => .there (embedVar index)

/-- Project a term variable from an all-term heterogeneous scope. -/
def projectVar : {scope : Nat} →
    BVar (termScope scope) .term → DOTCapture.Acyclic.Var scope
  | _ + 1, .here => .here
  | _ + 1, .there index => .there (projectVar index)

/-- An all-term scope contains no static variable. -/
def noStaticVar {scope : Nat} {sort : StaticSort} :
    BVar (termScope scope) (.static sort) → False
  := by
  induction scope with
  | zero => intro index; nomatch index
  | succ scope induction =>
      intro index
      cases index with
      | there older => exact induction older

@[simp]
theorem projectVar_embedVar {scope : Nat}
    (index : DOTCapture.Acyclic.Var scope) :
    projectVar (embedVar index) = index := by
  induction index with
  | here => rfl
  | there index induction =>
      simp only [embedVar, projectVar, induction]

@[simp]
theorem embedVar_projectVar {scope : Nat}
    (index : BVar (termScope scope) .term) :
    embedVar (projectVar index) = index := by
  induction scope with
  | zero => nomatch index
  | succ scope induction =>
      cases index with
      | here => rfl
      | there older =>
          simp only [projectVar, embedVar, induction]

/-- Lift an acyclic term renaming into heterogeneous all-term scopes. -/
def embedRename {source target : Nat}
    (rho : DOTCapture.Acyclic.Rename source target) :
    Rename (termScope source) (termScope target) where
  var := fun {kind} index =>
    match kind with
    | .term => embedVar (rho.var (projectVar index))
    | .static _ => False.elim (noStaticVar index)

@[simp]
theorem embedRename_term {source target : Nat}
    (rho : DOTCapture.Acyclic.Rename source target)
    (index : BVar (termScope source) .term) :
    (embedRename rho).var index = embedVar (rho.var (projectVar index)) :=
  rfl

@[simp]
theorem embedRename_embedVar {source target : Nat}
    (rho : DOTCapture.Acyclic.Rename source target)
    (index : DOTCapture.Acyclic.Var source) :
    (embedRename rho).var (embedVar index) = embedVar (rho.var index) := by
  simp only [embedRename_term, projectVar_embedVar]

@[simp]
theorem embedRename_id {scope : Nat} :
    embedRename (DOTCapture.Acyclic.Rename.id (scope := scope)) =
      (DOTCapture.BinderOnly.Rename.id :
        Rename (termScope scope) (termScope scope)) := by
  apply DOTCapture.BinderOnly.Rename.ext
  intro kind index
  cases kind with
  | term => simp only [embedRename_term,
      DOTCapture.Acyclic.Rename.id_var, embedVar_projectVar,
      DOTCapture.BinderOnly.Rename.id_var]
  | static sort => exact False.elim (noStaticVar index)

@[simp]
theorem embedRename_comp {first second third : Nat}
    (rho₁ : DOTCapture.Acyclic.Rename first second)
    (rho₂ : DOTCapture.Acyclic.Rename second third) :
    embedRename (rho₁.comp rho₂) =
      (embedRename rho₁).comp (embedRename rho₂) := by
  apply DOTCapture.BinderOnly.Rename.ext
  intro kind index
  cases kind with
  | term =>
      simp only [embedRename_term,
        DOTCapture.Acyclic.Rename.comp_var,
        DOTCapture.BinderOnly.Rename.comp_var,
        projectVar_embedVar]
  | static sort => exact False.elim (noStaticVar index)

@[simp]
theorem embedRename_lift {source target : Nat}
    (rho : DOTCapture.Acyclic.Rename source target) :
    embedRename rho.lift =
      (embedRename rho).lift (kind := .term) := by
  apply DOTCapture.BinderOnly.Rename.ext
  intro kind index
  cases kind with
  | term =>
      cases index with
      | here => rfl
      | there index =>
          simp only [embedRename_term, projectVar, embedVar,
            DOTCapture.Acyclic.Rename.lift_there,
            DOTCapture.BinderOnly.Rename.lift_there]
  | static sort => exact False.elim (noStaticVar index)

end DOTCapture.ModalIntersections
