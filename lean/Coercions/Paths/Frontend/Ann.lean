import Coercions.Paths.DotMNF.Syntax

/-!
# Annotated DOT-MNF terms with paths

`ATm` is `Paths.DotMNF.Tm` with two extra fields: the self type of an object
literal and the optional result type of a `let`.

The self type must be carried because `HasTy.obj` checks the definitions of a
literal against a context entry that already holds it.  It cannot be
synthesized from the definitions.  `Value.obj` has no slot for it, so the
annotation lives in the front end's own syntax.  The `let` type is optional
because an unannotated `let` has its type strengthened or widened to `⊤` by the
typer.

The path term takes a variable.  A deeper path in term position is written
with a `let` per prefix, which `Resolve.lean` inserts.

`ATm.erase` drops the annotations and gives back a `Tm`.  Nothing here is part
of the metatheory.  The size functions count nodes and are positive, so a
walker can take a fuel from them that is never zero.  Every recursive
definition uses `termination_by structural`.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Ty Tm Defs)

/-! ## The syntax -/

mutual
/-- Terms of DOT-MNF with paths and the two annotations.  Application,
projection and the path term take variables, so the terms are in monadic normal
form by construction. -/
inductive ATm : Sig → Type where
  /-- A variable.  A deeper path in term position is a chain of `let`s. -/
  | path : BVar s .var → ATm s
  /-- `λ(x : T). t`. -/
  | lam : Ty s → ATm (s,x) → ATm s
  /-- `ν(x : T. d)`, the self type annotated. -/
  | obj : Ty (s,x) → ADefs (s,x) → ATm s
  /-- `x y`. -/
  | app : BVar s .var → BVar s .var → ATm s
  /-- `x.a`. -/
  | proj : BVar s .var → Label → ATm s
  /-- `let x (: U)? = t in u`. -/
  | «let» : Option (Ty s) → ATm s → ATm (s,x) → ATm s
/-- Definitions of an annotated object literal. -/
inductive ADefs : Sig → Type where
  /-- `{type A = T}`. -/
  | typ : Label → Ty s → ADefs s
  /-- `{a = t}`. -/
  | trm : Label → ATm s → ADefs s
  /-- `d ∧ e`. -/
  | and : ADefs s → ADefs s → ADefs s
end

deriving instance DecidableEq for ATm, ADefs

/-! ## Erasure

Erasure drops the annotations and changes nothing else. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase : {s : Sig} → ATm s → Tm s
  | _, .path x => .path x
  | _, .lam T t => .val (.lam T t.erase)
  | _, .obj _ d => .val (.obj d.erase)
  | _, .app x y => .app x y
  | _, .proj x a => .proj x a
  | _, .let _ t u => .let t.erase u.erase
termination_by structural _ t => t
/-- Drop the annotations of a definition list. -/
def ADefs.erase : {s : Sig} → ADefs s → Defs s
  | _, .typ A T => .typ A T
  | _, .trm a t => .trm a t.erase
  | _, .and d e => .and d.erase e.erase
termination_by structural _ d => d
end

/-! ## Renaming

As `Paths.DotMNF.Tm.rename`.  The self type of a literal is under the self
binder and takes the lifted renaming.  The type of a `let` is outside its
binder and takes the renaming itself. -/

mutual
/-- Rename the free variables of an annotated term. -/
def ATm.rename : {s1 s2 : Sig} → ATm s1 → Rename s1 s2 → ATm s2
  | _, _, .path x, ρ => .path (ρ.var x)
  | _, _, .lam T t, ρ => .lam (T.rename ρ) (t.rename ρ.lift)
  | _, _, .obj T d, ρ => .obj (T.rename ρ.lift) (d.rename ρ.lift)
  | _, _, .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | _, _, .proj x a, ρ => .proj (ρ.var x) a
  | _, _, .let ann t u, ρ =>
      .let (ann.map (fun U => U.rename ρ)) (t.rename ρ) (u.rename ρ.lift)
termination_by structural _ _ t => t
/-- Rename the free variables of an annotated definition list. -/
def ADefs.rename : {s1 s2 : Sig} → ADefs s1 → Rename s1 s2 → ADefs s2
  | _, _, .typ A T, ρ => .typ A (T.rename ρ)
  | _, _, .trm a t, ρ => .trm a (t.rename ρ)
  | _, _, .and d e, ρ => .and (d.rename ρ) (e.rename ρ)
termination_by structural _ _ d => d
end

/-- Weakening of an annotated term, under one new binder. -/
def ATm.weaken (t : ATm s) : ATm (s,x) := t.rename Rename.succ

/-! ## Erasure commutes with renaming -/

mutual
/-- Erasure commutes with renaming. -/
theorem ATm.erase_rename : ∀ {s1 s2 : Sig} (t : ATm s1) (ρ : Rename s1 s2),
    (t.rename ρ).erase = t.erase.rename ρ
  | _, _, .path _, _ => rfl
  | _, _, .lam T t, ρ => by
      show Tm.val (.lam (T.rename ρ) (t.rename ρ.lift).erase) = _
      rw [ATm.erase_rename t ρ.lift]; rfl
  | _, _, .obj _ d, ρ => by
      show Tm.val (.obj (d.rename ρ.lift).erase) = _
      rw [ADefs.erase_rename d ρ.lift]; rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .proj _ _, _ => rfl
  | _, _, .let _ t u, ρ => by
      show Tm.let (t.rename ρ).erase (u.rename ρ.lift).erase = _
      rw [ATm.erase_rename t ρ, ATm.erase_rename u ρ.lift]; rfl
/-- Erasure commutes with renaming, on definitions. -/
theorem ADefs.erase_rename : ∀ {s1 s2 : Sig} (d : ADefs s1) (ρ : Rename s1 s2),
    (d.rename ρ).erase = d.erase.rename ρ
  | _, _, .typ _ _, _ => rfl
  | _, _, .trm a t, ρ => by
      show Defs.trm a (t.rename ρ).erase = _
      rw [ATm.erase_rename t ρ]; rfl
  | _, _, .and d e, ρ => by
      show Defs.and (d.rename ρ).erase (e.rename ρ).erase = _
      rw [ADefs.erase_rename d ρ, ADefs.erase_rename e ρ]; rfl
end

/-! ## Size

The node count of a term.  Types do not count. -/

mutual
/-- The node count of an annotated term. -/
def sizeATm : {s : Sig} → ATm s → Nat
  | _, .path _ => 1
  | _, .lam _ t => sizeATm t + 1
  | _, .obj _ d => sizeADefs d + 1
  | _, .app _ _ => 1
  | _, .proj _ _ => 1
  | _, .let _ t u => sizeATm t + sizeATm u + 1
termination_by structural _ t => t
/-- The node count of an annotated definition list. -/
def sizeADefs : {s : Sig} → ADefs s → Nat
  | _, .typ _ _ => 1
  | _, .trm _ t => sizeATm t + 1
  | _, .and d e => sizeADefs d + sizeADefs e + 1
termination_by structural _ d => d
end

mutual
/-- Every term has at least one node. -/
theorem sizeATm_pos : ∀ {s : Sig} (t : ATm s), 0 < sizeATm t
  | _, .path _ => Nat.zero_lt_one
  | _, .lam _ _ => Nat.succ_pos _
  | _, .obj _ _ => Nat.succ_pos _
  | _, .app _ _ => Nat.zero_lt_one
  | _, .proj _ _ => Nat.zero_lt_one
  | _, .let _ _ _ => Nat.succ_pos _
/-- Every definition list has at least one node. -/
theorem sizeADefs_pos : ∀ {s : Sig} (d : ADefs s), 0 < sizeADefs d
  | _, .typ _ _ => Nat.zero_lt_one
  | _, .trm _ _ => Nat.succ_pos _
  | _, .and _ _ => Nat.succ_pos _
end

/-- The body of a term member is smaller than the definition list. -/
theorem sizeATm_lt_trm {s : Sig} (a : Label) (t : ATm s) :
    sizeATm t < sizeADefs (.trm a t) := Nat.lt_succ_self _

/-- The bound term of a `let` is smaller than the `let`. -/
theorem sizeATm_lt_letBound {s : Sig} (ann : Option (Ty s)) (t : ATm s) (u : ATm (s,x)) :
    sizeATm t < sizeATm (.let ann t u) := by
  show sizeATm t < sizeATm t + sizeATm u + 1
  omega

/-- The body of a `let` is smaller than the `let`. -/
theorem sizeATm_lt_letBody {s : Sig} (ann : Option (Ty s)) (t : ATm s) (u : ATm (s,x)) :
    sizeATm u < sizeATm (.let ann t u) := by
  show sizeATm u < sizeATm t + sizeATm u + 1
  omega

end PathsFrontend
