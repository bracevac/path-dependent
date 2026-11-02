import Coercions.Paths.FCdot.TypingPathSubst

/-!
# pDOT syntax

The syntax of pDOT as `Definitions.v:59-115` of the Coq formalization states it.  The constructors
and their order are Coq's.  Coq is locally nameless.  Here every binder is a de Bruijn binder of the
Paths target: a family is indexed by a signature `s`, and `(s,x)` adds one variable, `.here`.

The paths, signatures, labels, renamings and path substitutions are the Paths target's, imported and
not copied.  A path is a variable followed by field selections, which is Coq's `p_sel x bs` with the
fields in the order they are selected.  Coq's two label sorts `typ_label` and `trm_label` are the two
sorts `Label.typ` and `Label.trm` of the one type `Label`.

Binders are named in comments only.  `μ(z. T)` binds `z` in `T`.  `∀(z : S) T` binds `z` in `T`.
`let z = t in u` binds `z` in `u`.  `ν(z : T) ds` binds `z` in `T` and in `ds`.  `λ(z : T) t` binds
`z` in `t`.  A context binds a variable at a type of the outer signature, `G, z : T`, or at a type that
mentions the variable itself, `G, z :ˢ T`, which is the self of a literal.  A store binds a variable
to a value of the outer signature.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Types and declarations (`Definitions.v:59-73`) -/

mutual
inductive Ty : Sig → Type where
  | top : Ty s
  | bot : Ty s
  | rcd : Dec s → Ty s
  | and : Ty s → Ty s → Ty s
  | sel : Path s → Label → Ty s          -- p.A
  | mu : Ty (s,x) → Ty s                 -- μ(z. T), z = .here of the body
  | all : Ty s → Ty (s,x) → Ty s         -- ∀(z : S) T
  | sngl : Path s → Ty s                 -- p.type
inductive Dec : Sig → Type where
  | typ : Label → Ty s → Ty s → Dec s    -- {A : S..U}
  | trm : Label → Ty s → Dec s           -- {a : T}
end

/-! ## Terms, values, definitions (`Definitions.v:84-115`) -/

mutual
inductive Tm : Sig → Type where
  | val : Val s → Tm s
  | app : Path s → Path s → Tm s         -- app p q applies p to q
  | lett : Tm s → Tm (s,x) → Tm s        -- let z = t in u
  | path : Path s → Tm s
inductive Val : Sig → Type where
  | new : Ty (s,x) → Defs (s,x) → Val s  -- ν(z : T) ds
  | lam : Ty s → Tm (s,x) → Val s        -- λ(z : T) t
inductive Def : Sig → Type where
  | typ : Label → Ty s → Def s           -- {A = T}
  | trm : Label → Rhs s → Def s          -- {a = r}
  | cls : Label → Ty s → Def s           -- {class C = T}, plan XII
inductive Defs : Sig → Type where
  | nil : Defs s
  | cons : Defs s → Def s → Defs s
inductive Rhs : Sig → Type where
  | defp : Path s → Rhs s
  | defv : Val s → Rhs s
end

deriving instance DecidableEq for Ty, Dec, Tm, Val, Def, Defs, Rhs

/-! ## Contexts, stores, configurations -/

/-- Typing contexts, newest binder last.  Coq's `ctx := env typ` (`Definitions.v:479`).  The self of
a literal is a binder of its own, since its type mentions it. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Ty s → Ctx (s,x)            -- G, z : T
  | consSelf : Ctx s → Ty (s,x) → Ctx (s,x)    -- G, z :ˢ T, T mentions z

/-- Stores, newest binding last.  Coq's `sta := env val` (`Definitions.v:483`).  The variable a store
binds is the new innermost variable. -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Val s → Store (s,x)       -- γ, x ↦ v

/-- A configuration `⟨s, γ, t⟩`: a store and a term over one signature. -/
structure Conf where
  s : Sig
  store : Store s
  tm : Tm s

/-! ## Functions on the syntax (plan S.1)

`Ctx.lookup` and `Store.get` weaken their result, so they are in `Binding`, after `Ty.weaken` and
`Val.weaken`. -/

/-- `p.nomExt bs` is `p` followed by the fields `bs`, first field first.  Coq's `p••bs`
(`Definitions.v:180-183`), whose list is in reverse order.  It is declared in the namespace of the
tree's `Path`, so that field notation `p.nomExt bs` finds it. -/
def _root_.Paths.FCdot.Path.nomExt : Path s → List Label → Path s
  | p, [] => p                                   -- p.nomExt [] = p
  | p, a :: bs => nomExt (p.sel a) bs               -- p.nomExt (a :: bs) = (p.sel a).nomExt bs

/-- The label of a definition, `label_of_def` (`Definitions.v:193-196`). -/
def Def.label : Def s → Label
  | .typ A _ => A                                -- {A = T}.label = A
  | .trm a _ => a                                -- {a = r}.label = a
  | .cls C _ => C                                -- {class C = T}.label = C

/-- The newest definition at a label, `get_def` (`Definitions.v:203-207`). -/
def Defs.get : Defs s → Label → Option (Def s)
  | .nil, _ => none                                              -- [].get l = none
  | .cons ds d, l => if d.label = l then some d else ds.get l    -- (ds ▹ d).get l

/-- No definition at a label, `defs_hasnt` (`Definitions.v:211`). -/
def Defs.hasnt (ds : Defs s) (l : Label) : Prop := ds.get l = none

end Nominal.Source
