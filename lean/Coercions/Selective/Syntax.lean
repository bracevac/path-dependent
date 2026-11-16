import Coercions.Selective.Prim

/-!
# Syntax of `H`: atoms, certificates, positioned steps, annotated terms

Types and contexts are `DotMNF.Ty` and `DotMNF.Ctx`, unchanged.

* **Atoms** (root-preserving variable evidence) `a ::= x | a ▷ c | unfold a |
  fold[T] a | ⟨a, b⟩`, with `root a` the variable at the bottom.
* **Certificates** `c ::= step[S,T] | c ; d | pos k`.
* **Positioned member steps** `k`: an explicit one-hole context (`fld`,
  `typL`, `typU`, `allD`, `allC`, `andL`, `andR`) around a leaf `selU a A U`
  or `selL a A L`, whose receiver atom `a` is scoped at the hole: under
  `allC S k` the hole `k` lives at the extended signature.
* **Terms** `t ::= a | v | a b | a.ℓ | let x = t in u | t ▷ c`, values
  `ν(x : T) d | λ(x : S). t`, definitions `{A = T} | {a = t} | d ∧ d`.

`HTm.erase` is the agreed erased program: atoms go to their roots, casts and
object annotations are dropped, and no `let` is inserted.

Renaming acts on every stored type and atom; `Atom.root_rename` says that the
root of a renamed atom is the renamed root.  The size functions and `BEq`
instances serve the measurements of the evidence (expanded size, shared
size).
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

/-! ## Evidence -/

mutual
/-- Root-preserving variable evidence. -/
inductive Atom : Sig → Type where
  | var : BVar s .var → Atom s
  | cast : Atom s → Cert s → Atom s
  | unfold : Atom s → Atom s
  | fold : Ty (s,x) → Atom s → Atom s
  | both : Atom s → Atom s → Atom s
/-- Coercion certificates. -/
inductive Cert : Sig → Type where
  | step : Ty s → Ty s → Cert s
  | seq : Cert s → Cert s → Cert s
  | pos : Pos s → Cert s
/-- A positioned member step: an explicit one-hole context around a leaf. -/
inductive Pos : Sig → Type where
  | selU : Atom s → Label → Ty s → Pos s
  | selL : Atom s → Label → Ty s → Pos s
  | fld : Label → Pos s → Pos s
  | typL : Label → Pos s → Ty s → Pos s
  | typU : Label → Ty s → Pos s → Pos s
  | allD : Pos s → Ty (s,x) → Pos s
  | allC : Ty s → Pos (s,x) → Pos s
  | andL : Pos s → Ty s → Pos s
  | andR : Ty s → Pos s → Pos s
end

deriving instance DecidableEq for Atom, Cert, Pos

/-- The variable an atom is evidence about. -/
def Atom.root : Atom s → BVar s .var
  | .var x => x
  | .cast a _ => a.root
  | .unfold a => a.root
  | .fold _ a => a.root
  | .both a _ => a.root

/-! ## Terms -/

mutual
inductive HTm : Sig → Type where
  | atom : Atom s → HTm s
  | val : HVal s → HTm s
  /-- `a b`: callee and argument are atoms; the result is instantiated at `root b`. -/
  | app : Atom s → Atom s → HTm s
  /-- `a.ℓ`: the receiver is an atom; the field is read at `root a`. -/
  | proj : Atom s → Label → HTm s
  | «let» : HTm s → HTm (s,x) → HTm s
  | cast : HTm s → Cert s → HTm s
inductive HVal : Sig → Type where
  /-- `ν(x : T) d`: the self type's body is annotated (erased). -/
  | obj : Ty (s,x) → HDefs (s,x) → HVal s
  | lam : Ty s → HTm (s,x) → HVal s
inductive HDefs : Sig → Type where
  | typ : Label → Ty s → HDefs s
  | trm : Label → HTm s → HDefs s
  | and : HDefs s → HDefs s → HDefs s
end

deriving instance DecidableEq for HTm, HVal, HDefs

/-! ## Erasure -/

mutual
def HTm.erase : HTm s → DotMNF.Tm s
  | .atom a => .path (.var a.root)
  | .val v => .val v.erase
  | .app a b => .app a.root b.root
  | .proj a ℓ => .proj a.root ℓ
  | .let t u => .let t.erase u.erase
  | .cast t _ => t.erase
def HVal.erase : HVal s → DotMNF.Value s
  | .obj _ d => .obj d.erase
  | .lam S t => .lam S t.erase
def HDefs.erase : HDefs s → DotMNF.Defs s
  | .typ A T => .typ A T
  | .trm a t => .trm a t.erase
  | .and d1 d2 => .and d1.erase d2.erase
end

/-! ## Renaming -/

mutual
def Atom.rename : Atom s1 → Rename s1 s2 → Atom s2
  | .var x, ρ => .var (ρ.var x)
  | .cast a c, ρ => .cast (a.rename ρ) (c.rename ρ)
  | .unfold a, ρ => .unfold (a.rename ρ)
  | .fold T a, ρ => .fold (T.rename ρ.lift) (a.rename ρ)
  | .both a b, ρ => .both (a.rename ρ) (b.rename ρ)
def Cert.rename : Cert s1 → Rename s1 s2 → Cert s2
  | .step S T, ρ => .step (S.rename ρ) (T.rename ρ)
  | .seq c d, ρ => .seq (c.rename ρ) (d.rename ρ)
  | .pos k, ρ => .pos (k.rename ρ)
def Pos.rename : Pos s1 → Rename s1 s2 → Pos s2
  | .selU a A U, ρ => .selU (a.rename ρ) A (U.rename ρ)
  | .selL a A L, ρ => .selL (a.rename ρ) A (L.rename ρ)
  | .fld ℓ k, ρ => .fld ℓ (k.rename ρ)
  | .typL A k U, ρ => .typL A (k.rename ρ) (U.rename ρ)
  | .typU A L k, ρ => .typU A (L.rename ρ) (k.rename ρ)
  | .allD k T, ρ => .allD (k.rename ρ) (T.rename ρ.lift)
  | .allC S k, ρ => .allC (S.rename ρ) (k.rename ρ.lift)
  | .andL k U, ρ => .andL (k.rename ρ) (U.rename ρ)
  | .andR U k, ρ => .andR (U.rename ρ) (k.rename ρ)
end

@[simp] theorem Atom.root_rename {s1 s2 : Sig} :
    (a : Atom s1) → (ρ : Rename s1 s2) → (a.rename ρ).root = ρ.var a.root
  | .var _, _ => rfl
  | .cast a _, ρ => by simp only [Atom.rename, Atom.root]; exact Atom.root_rename a ρ
  | .unfold a, ρ => by simp only [Atom.rename, Atom.root]; exact Atom.root_rename a ρ
  | .fold _ a, ρ => by simp only [Atom.rename, Atom.root]; exact Atom.root_rename a ρ
  | .both a _, ρ => by simp only [Atom.rename, Atom.root]; exact Atom.root_rename a ρ

mutual
def HTm.rename : HTm s1 → Rename s1 s2 → HTm s2
  | .atom a, ρ => .atom (a.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app a b, ρ => .app (a.rename ρ) (b.rename ρ)
  | .proj a ℓ, ρ => .proj (a.rename ρ) ℓ
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .cast t c, ρ => .cast (t.rename ρ) (c.rename ρ)
def HVal.rename : HVal s1 → Rename s1 s2 → HVal s2
  | .obj T d, ρ => .obj (T.rename ρ.lift) (d.rename ρ.lift)
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)
def HDefs.rename : HDefs s1 → Rename s1 s2 → HDefs s2
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d1 d2, ρ => .and (d1.rename ρ) (d2.rename ρ)
end

mutual
/-- Erasure commutes with renaming. -/
theorem HTm.erase_rename {s1 s2 : Sig} :
    (t : HTm s1) → (ρ : Rename s1 s2) → (t.rename ρ).erase = t.erase.rename ρ
  | .atom a, ρ => by simp [HTm.rename, HTm.erase, DotMNF.Tm.rename, DotMNF.Path.rename]
  | .val v, ρ => by
      simp only [HTm.rename, HTm.erase, DotMNF.Tm.rename]; rw [HVal.erase_rename v ρ]
  | .app a b, ρ => by simp [HTm.rename, HTm.erase, DotMNF.Tm.rename]
  | .proj a ℓ, ρ => by simp [HTm.rename, HTm.erase, DotMNF.Tm.rename]
  | .let t u, ρ => by
      simp only [HTm.rename, HTm.erase, DotMNF.Tm.rename]
      rw [HTm.erase_rename t ρ, HTm.erase_rename u ρ.lift]
  | .cast t c, ρ => by simp only [HTm.rename, HTm.erase]; exact HTm.erase_rename t ρ
theorem HVal.erase_rename {s1 s2 : Sig} :
    (v : HVal s1) → (ρ : Rename s1 s2) → (v.rename ρ).erase = v.erase.rename ρ
  | .obj T d, ρ => by
      simp only [HVal.rename, HVal.erase, DotMNF.Value.rename]; rw [HDefs.erase_rename d ρ.lift]
  | .lam S t, ρ => by
      simp only [HVal.rename, HVal.erase, DotMNF.Value.rename]; rw [HTm.erase_rename t ρ.lift]
theorem HDefs.erase_rename {s1 s2 : Sig} :
    (d : HDefs s1) → (ρ : Rename s1 s2) → (d.rename ρ).erase = d.erase.rename ρ
  | .typ A T, ρ => rfl
  | .trm a t, ρ => by
      simp only [HDefs.rename, HDefs.erase, DotMNF.Defs.rename]; rw [HTm.erase_rename t ρ]
  | .and d1 d2, ρ => by
      simp only [HDefs.rename, HDefs.erase, DotMNF.Defs.rename]
      rw [HDefs.erase_rename d1 ρ, HDefs.erase_rename d2 ρ]
end

/-! ## Sizes of stored evidence

One per node plus `sz` of every stored type (the expanded tree size). -/

mutual
def Atom.size : Atom s → Nat
  | .var _ => 1
  | .cast a c => a.size + c.size + 1
  | .unfold a => a.size + 1
  | .fold T a => sz T + a.size + 1
  | .both a b => a.size + b.size + 1
def Cert.size : Cert s → Nat
  | .step S T => sz S + sz T + 1
  | .seq c d => c.size + d.size + 1
  | .pos k => k.size + 1
def Pos.size : Pos s → Nat
  | .selU a _ U => a.size + sz U + 1
  | .selL a _ L => a.size + sz L + 1
  | .fld _ k => k.size + 1
  | .typL _ k U => k.size + sz U + 1
  | .typU _ L k => sz L + k.size + 1
  | .allD k T => k.size + sz T + 1
  | .allC S k => sz S + k.size + 1
  | .andL k U => k.size + sz U + 1
  | .andR U k => sz U + k.size + 1
end

end Selective
