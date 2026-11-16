import Coercions.FCdot.Debruijn

/-!
# Selective DOT: syntax

The syntax of the coercive calculus for WadlerFest DOT in monadic normal form.
Only the binding infrastructure (`Sig`, `BVar`, `Rename`, `Label`) is imported.

There are two layers of types.

* `Ty` are the types of DOT, with selections `x.A` on variables. Contexts,
  binder annotations and the types in typing judgments are of this kind.
* `ATy` are the types written as the endpoints of a `step`. They have the same
  constructors, but a selection `p.A` is taken on a path, and a path is a
  variable under a stack of casts: `p ::= x | p ▷ c`.

Certificates have two forms, `step[S,T]` and `c ; d`. A certificate is the only
evidence a cast carries, on a term or on a path. `ATy.erase` removes the casts
from the paths of a type, and `Tm.erase` removes every cast from a term.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Types -/

/-- Types. Selections are on variables. -/
inductive Ty : Sig → Type where
  | top : Ty s
  | bot : Ty s
  /-- Type declaration `{A : S..T}`. Bad bounds are allowed. -/
  | typ : Label → Ty s → Ty s → Ty s
  /-- Field declaration `{a : T}`. -/
  | fld : Label → Ty s → Ty s
  /-- Type selection `x.A`. -/
  | sel : BVar s .var → Label → Ty s
  /-- Recursive self type `μ(x. T)`. -/
  | mu : Ty (s,x) → Ty s
  /-- Dependent function type `∀(x : S) T`. -/
  | all : Ty s → Ty (s,x) → Ty s
  | and : Ty s → Ty s → Ty s
deriving DecidableEq

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, ρ => .typ A (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .sel x A, ρ => .sel (ρ.var x) A
  | .mu T, ρ => .mu (T.rename ρ.lift)
  | .all S T, ρ => .all (S.rename ρ) (T.rename ρ.lift)
  | .and S T, ρ => .and (S.rename ρ) (T.rename ρ)

def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ

/-- Instantiate the innermost binder of a type by a variable. -/
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)

/-! ## Paths, endpoint types, certificates -/

mutual

/-- Paths: a variable under a stack of casts. -/
inductive Path : Sig → Type where
  | var : BVar s .var → Path s
  | cast : Path s → Cert s → Path s

/-- Endpoint types: the types written in a `step`. Selections are on paths. -/
inductive ATy : Sig → Type where
  | top : ATy s
  | bot : ATy s
  | typ : Label → ATy s → ATy s → ATy s
  | fld : Label → ATy s → ATy s
  | sel : Path s → Label → ATy s
  | mu : ATy (s,x) → ATy s
  | all : ATy s → ATy (s,x) → ATy s
  | and : ATy s → ATy s → ATy s

/-- Certificates: a primitive step between two written endpoints, and composition. -/
inductive Cert : Sig → Type where
  | step : ATy s → ATy s → Cert s
  | seq : Cert s → Cert s → Cert s

end

deriving instance DecidableEq for Path, ATy, Cert

/-- The variable under the casts of a path. -/
def Path.root : Path s → BVar s .var
  | .var x => x
  | .cast p _ => p.root

mutual

def Path.rename : Path s1 → Rename s1 s2 → Path s2
  | .var x, ρ => .var (ρ.var x)
  | .cast p c, ρ => .cast (p.rename ρ) (c.rename ρ)

def ATy.rename : ATy s1 → Rename s1 s2 → ATy s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, ρ => .typ A (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu T, ρ => .mu (T.rename ρ.lift)
  | .all S T, ρ => .all (S.rename ρ) (T.rename ρ.lift)
  | .and S T, ρ => .and (S.rename ρ) (T.rename ρ)

def Cert.rename : Cert s1 → Rename s1 s2 → Cert s2
  | .step S T, ρ => .step (S.rename ρ) (T.rename ρ)
  | .seq c d, ρ => .seq (c.rename ρ) (d.rename ρ)

end

def Path.weaken (p : Path s) : Path (s,,k) := p.rename Rename.succ
def ATy.weaken (T : ATy s) : ATy (s,,k) := T.rename Rename.succ
def Cert.weaken (c : Cert s) : Cert (s,,k) := c.rename Rename.succ

/-- Erasure of an endpoint type: every path is replaced by its root. -/
def ATy.erase : ATy s → Ty s
  | .top => .top
  | .bot => .bot
  | .typ A S T => .typ A S.erase T.erase
  | .fld a T => .fld a T.erase
  | .sel p A => .sel p.root A
  | .mu T => .mu T.erase
  | .all S T => .all S.erase T.erase
  | .and S T => .and S.erase T.erase

/-- A type as an endpoint whose paths carry no cast. -/
def Ty.embed : Ty s → ATy s
  | .top => .top
  | .bot => .bot
  | .typ A S T => .typ A S.embed T.embed
  | .fld a T => .fld a T.embed
  | .sel x A => .sel (.var x) A
  | .mu T => .mu T.embed
  | .all S T => .all S.embed T.embed
  | .and S T => .and S.embed T.embed

/-! ## Terms, values, definitions -/

mutual

/-- Terms. Application and projection take paths, and any term can be cast. -/
inductive Tm : Sig → Type where
  | path : Path s → Tm s
  | val : Value s → Tm s
  | app : Path s → Path s → Tm s
  | proj : Path s → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s
  | cast : Tm s → Cert s → Tm s

/-- Values. -/
inductive Value : Sig → Type where
  | obj : Defs (s,x) → Value s
  | lam : Ty s → Tm (s,x) → Value s

/-- Definitions of an object literal. -/
inductive Defs : Sig → Type where
  | typ : Label → Ty s → Defs s
  | trm : Label → Tm s → Defs s
  | and : Defs s → Defs s → Defs s

end

deriving instance DecidableEq for Tm, Value, Defs

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .path p, ρ => .path (p.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app p q, ρ => .app (p.rename ρ) (q.rename ρ)
  | .proj p a, ρ => .proj (p.rename ρ) a
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .cast t c, ρ => .cast (t.rename ρ) (c.rename ρ)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .obj d, ρ => .obj (d.rename ρ.lift)
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)

def Defs.rename : Defs s1 → Rename s1 s2 → Defs s2
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d1 d2, ρ => .and (d1.rename ρ) (d2.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,x) := v.rename Rename.succ
def Defs.weaken (d : Defs s) : Defs (s,x) := d.rename Rename.succ

/-- Instantiate the innermost binder of a term by a variable. -/
def Tm.substVar (t : Tm (s,x)) (y : BVar s .var) : Tm s := t.rename (Rename.subst y)

/-! ## Erasure of terms

Every cast is removed, on terms and on paths. The result is a term of the same
syntax in which every path is a variable. -/

mutual

def Tm.erase : Tm s → Tm s
  | .path p => .path (.var p.root)
  | .val v => .val v.erase
  | .app p q => .app (.var p.root) (.var q.root)
  | .proj p a => .proj (.var p.root) a
  | .let t u => .let t.erase u.erase
  | .cast t _ => t.erase

def Value.erase : Value s → Value s
  | .obj d => .obj d.erase
  | .lam S t => .lam S t.erase

def Defs.erase : Defs s → Defs s
  | .typ A T => .typ A T
  | .trm a t => .trm a t.erase
  | .and d1 d2 => .and d1.erase d2.erase

end

/-! ## Definition lookup -/

/-- The labels defined by a definition list. -/
def Defs.labels : Defs s → List Label
  | .typ A _ => [A]
  | .trm a _ => [a]
  | .and d1 d2 => d1.labels ++ d2.labels

/-- The term member at a label, if any. The right conjunct shadows. -/
def Defs.lookupTrm : Defs s → Label → Option (Tm s)
  | .typ _ _, _ => none
  | .trm a t, ℓ => if ℓ = a then some t else none
  | .and d1 d2, ℓ => (d2.lookupTrm ℓ).or (d1.lookupTrm ℓ)

/-- The labels of a definition list are pairwise distinct. -/
inductive Defs.Distinct : {s : Sig} → Defs s → Prop where
  | typ : Defs.Distinct (.typ A T)
  | trm : Defs.Distinct (.trm a t)
  | and :
      Defs.Distinct d1 → Defs.Distinct d2 →
      (∀ ℓ, ℓ ∈ d1.labels → ℓ ∉ d2.labels) →
      Defs.Distinct (.and d1 d2)

end SelDot
