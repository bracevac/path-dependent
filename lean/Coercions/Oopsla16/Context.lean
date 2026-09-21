import Coercions.Oopsla16.Structural

/-!
# Contexts and the prefix at a variable

Two things here are not the shape a reader of `DotMNF` will expect, and both
are forced by the reference.

**Context entries may mention their own binder.**  `DotMNF.Ctx.cons` takes a
`Ty s` and therefore cannot hold an opened self type; `DotMNF` instead binds
the folded `μ(x. T)` and recovers the opened body by `Rec-E`.  The reference
does the opposite: `stp_bindx` (`dot.v:335-341`) and `T_Obj` (`dot.v:241-245`)
push the *opened* body `open 0 (TVar false (length GH)) T`, which mentions the
variable it introduces, and there is no rule that folds an abstract variable
back up inside `Htp`.  That asymmetry is what the reference's recursive
subtyping rests on, so `Ctx.cons` here takes a `Ty σ (s,x)`.  A hypothesis
that does not mention its own binder — the parameter of `stp_fun`, `D_Fun` —
is a weakening.

The extrinsic shadow of this is visible in the reference: `htp_var` and
`htp_unpack` require `closed (S x) …`, not `closed x …` (`dot.v:378`,
`dot.v:382`), i.e. the type of the variable at `x` may mention `x`.

**Every variable determines a context prefix.**  `htp_sub` (`dot.v:384-393`)
runs its subtyping step in a context `GL` with `length GL = S x` and `GH = GU
++ GL`: only the hypotheses introduced no later than `x` may widen `x`'s type,
so the self assumption of an enclosing `stp_bindx` cannot.  With absolute
positions that has to be said with an append; with intrinsic scoping it is a
scope, `scopeUpTo x`, and the restriction becomes the *type* of the judgment
`Htp` rather than a side condition on one of its rules.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-! ## The prefix at a variable -/

/-- The scope consisting of `x` and every binder older than `x`.  The
reference's `GL` with `length GL = S x` (`dot.v:391`). -/
def scopeUpTo : {s : Sig} → BVar s .var → Sig
  | _ :: s, .here => s,x
  | _ :: _, .there y => scopeUpTo y

/-- The prefix at `x` embeds into the full scope; the reference's `GH = GU ++
GL` (`dot.v:392`) is this weakening. -/
def renameUpTo : {s : Sig} → (x : BVar s .var) → Rename (scopeUpTo x) s
  | _ :: _, .here => Rename.id
  | _ :: _, .there y => (renameUpTo y).comp Rename.succ

/-- `x` itself, as a variable of its own prefix: the newest binder there. -/
def varUpTo : {s : Sig} → (x : BVar s .var) → BVar (scopeUpTo x) .var
  | _ :: _, .here => .here
  | _ :: _, .there y => varUpTo y

@[simp] theorem renameUpTo_varUpTo : {s : Sig} → (x : BVar s .var) →
    (renameUpTo x).var (varUpTo x) = x
  | _ :: _, .here => rfl
  | _ :: _, .there y => congrArg BVar.there (renameUpTo_varUpTo y)

/-! ## Contexts -/

/-- A context: one type per binder of the local scope, newest binder first.
An entry lives in the scope *including* its own binder, so it may be the
opened body of a recursive type. -/
inductive Ctx : Sig → Sig → Type where
  /-- The empty context. -/
  | nil : Ctx σ []
  /-- Extend by a hypothesis that may mention itself. -/
  | cons : Ctx σ s → Ty σ (s,x) → Ctx σ (s,x)

/-- The type of `x` in the prefix at `x`, exactly as recorded.  This is
`index x GH = Some TX` together with `closed (S x) … TX` (`dot.v:377-378`). -/
def Ctx.lookupAt : Ctx σ s → (x : BVar s .var) → Ty σ (scopeUpTo x)
  | .cons _ T, .here => T
  | .cons Γ _, .there y => Γ.lookupAt y

/-- The type of `x`, weakened into the current scope. -/
def Ctx.lookup (Γ : Ctx σ s) (x : BVar s .var) : Ty σ s :=
  (Γ.lookupAt x).rename (renameUpTo x)

/-- The prefix of the context at `x`: the reference's `GL`. -/
def Ctx.upTo : Ctx σ s → (x : BVar s .var) → Ctx σ (scopeUpTo x)
  | .cons Γ T, .here => .cons Γ T
  | .cons Γ _, .there y => Γ.upTo y

end Oopsla16
