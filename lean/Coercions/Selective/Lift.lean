import Coercions.Selective.Check

/-!
# Certificate-level lifts

A lift maps each `step` to a `step` between the lifted types (one `Prim`
congruence), each `pos k` to the navigation constructor around `k`, and each
`;` componentwise, reversed in the contravariant positions (lower bounds,
domains).  The lifts are functions on certificates, not constructors: the
structural rules of DOT-MNF subtyping are admissible for certificates.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

def Cert.liftFld (ℓ : Label) : Cert s → Cert s
  | .step S T => .step (.fld ℓ S) (.fld ℓ T)
  | .seq c d => .seq (c.liftFld ℓ) (d.liftFld ℓ)
  | .pos k => .pos (.fld ℓ k)

def Cert.liftTypU (A : Label) (L : Ty s) : Cert s → Cert s
  | .step S T => .step (.typ A L S) (.typ A L T)
  | .seq c d => .seq (c.liftTypU A L) (d.liftTypU A L)
  | .pos k => .pos (.typU A L k)

/-- Contravariant: `c : L2 ⇒ L1` lifts to `{A:L1..U} ⇒ {A:L2..U}`. -/
def Cert.liftTypL (A : Label) (U : Ty s) : Cert s → Cert s
  | .step S T => .step (.typ A T U) (.typ A S U)
  | .seq c d => .seq (d.liftTypL A U) (c.liftTypL A U)
  | .pos k => .pos (.typL A k U)

/-- Contravariant: `c : S2 ⇒ S1` lifts to `∀(S1) T ⇒ ∀(S2) T`. -/
def Cert.liftAllD (T : Ty (s,x)) : Cert s → Cert s
  | .step S S' => .step (.all S' T) (.all S T)
  | .seq c d => .seq (d.liftAllD T) (c.liftAllD T)
  | .pos k => .pos (.allD k T)

/-- Under the binder: `Γ, x : S ⊢ c : T1 ⇒ T2` lifts to `∀(S) T1 ⇒ ∀(S) T2`. -/
def Cert.liftAllC (S : Ty s) : Cert (s,x) → Cert s
  | .step T1 T2 => .step (.all S T1) (.all S T2)
  | .seq c d => .seq (c.liftAllC S) (d.liftAllC S)
  | .pos k => .pos (.allC S k)

def Cert.liftAndL (U : Ty s) : Cert s → Cert s
  | .step S M => .step (.and S U) (.and M U)
  | .seq c d => .seq (c.liftAndL U) (d.liftAndL U)
  | .pos k => .pos (.andL k U)

def Cert.liftAndR (U : Ty s) : Cert s → Cert s
  | .step S M => .step (.and U S) (.and U M)
  | .seq c d => .seq (c.liftAndR U) (d.liftAndR U)
  | .pos k => .pos (.andR U k)

theorem CTy.liftFld {s : Sig} {Γ : Ctx s} {ℓ : Label} :
    {c : Cert s} → {S T : Ty s} → CTy Γ c S T → CTy Γ (c.liftFld ℓ) (.fld ℓ S) (.fld ℓ T)
  | _, _, _, .step p => .step (.fld p)
  | _, _, _, .seq h1 h2 => .seq h1.liftFld h2.liftFld
  | _, _, _, .pos h => .pos (.fld h)

theorem CTy.liftTypU {s : Sig} {Γ : Ctx s} {A : Label} {L : Ty s} :
    {c : Cert s} → {S T : Ty s} → CTy Γ c S T → CTy Γ (c.liftTypU A L) (.typ A L S) (.typ A L T)
  | _, _, _, .step p => .step (.typ .refl p)
  | _, _, _, .seq h1 h2 => .seq h1.liftTypU h2.liftTypU
  | _, _, _, .pos h => .pos (.typU h)

theorem CTy.liftTypL {s : Sig} {Γ : Ctx s} {A : Label} {U : Ty s} :
    {c : Cert s} → {S T : Ty s} → CTy Γ c S T → CTy Γ (c.liftTypL A U) (.typ A T U) (.typ A S U)
  | _, _, _, .step p => .step (.typ p .refl)
  | _, _, _, .seq h1 h2 => .seq h2.liftTypL h1.liftTypL
  | _, _, _, .pos h => .pos (.typL h)

theorem CTy.liftAllD {s : Sig} {Γ : Ctx s} {T : Ty (s,x)} :
    {c : Cert s} → {S S' : Ty s} → CTy Γ c S S' → CTy Γ (c.liftAllD T) (.all S' T) (.all S T)
  | _, _, _, .step p => .step (.all p .refl)
  | _, _, _, .seq h1 h2 => .seq h2.liftAllD h1.liftAllD
  | _, _, _, .pos h => .pos (.allD h)

/-- The codomain lift, stated for an arbitrary context so that the recursion
has variable indices (as `RevB.AllCodGoal`). -/
def AllCGoal : {s' : Sig} → Ctx s' → Cert s' → Ty s' → Ty s' → Prop
  | _, .cons Γ S, c, T1, T2 => CTy Γ (c.liftAllC S) (.all S T1) (.all S T2)
  | _, _, _, _, _ => True

theorem CTy.liftAllCG {s' : Sig} {Γ' : Ctx s'} :
    {c : Cert s'} → {T1 T2 : Ty s'} → CTy Γ' c T1 T2 → AllCGoal Γ' c T1 T2
  | _, _, _, .step p => by
      cases Γ' with
      | cons Γ S => simp only [AllCGoal, Cert.liftAllC]; exact .step (.all .refl p)
      | _ => simp only [AllCGoal]
  | _, _, _, .seq h1 h2 => by
      have ih1 := CTy.liftAllCG h1; have ih2 := CTy.liftAllCG h2
      cases Γ' with
      | cons Γ S =>
          simp only [AllCGoal, Cert.liftAllC] at ih1 ih2 ⊢; exact .seq ih1 ih2
      | _ => simp only [AllCGoal]
  | _, _, _, .pos h => by
      cases Γ' with
      | cons Γ S => simp only [AllCGoal, Cert.liftAllC]; exact .pos (.allC h)
      | _ => simp only [AllCGoal]

theorem CTy.liftAllC {s : Sig} {Γ : Ctx s} {S : Ty s} {c : Cert (s,x)} {T1 T2 : Ty (s,x)}
    (h : CTy (Γ.cons S) c T1 T2) : CTy Γ (c.liftAllC S) (.all S T1) (.all S T2) :=
  CTy.liftAllCG h

theorem CTy.liftAndL {s : Sig} {Γ : Ctx s} {U : Ty s} :
    {c : Cert s} → {S M : Ty s} → CTy Γ c S M → CTy Γ (c.liftAndL U) (.and S U) (.and M U)
  | _, _, _, .step p => .step (.andR (.andL1 p) (.andL2 .refl))
  | _, _, _, .seq h1 h2 => .seq h1.liftAndL h2.liftAndL
  | _, _, _, .pos h => .pos (.andL h)

theorem CTy.liftAndR {s : Sig} {Γ : Ctx s} {U : Ty s} :
    {c : Cert s} → {S M : Ty s} → CTy Γ c S M → CTy Γ (c.liftAndR U) (.and U S) (.and U M)
  | _, _, _, .step p => .step (.andR (.andL1 .refl) (.andL2 p))
  | _, _, _, .seq h1 h2 => .seq h1.liftAndR h2.liftAndR
  | _, _, _, .pos h => .pos (.andR h)

end Selective
