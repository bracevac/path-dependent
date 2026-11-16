import Coercions.Selective.Dot.Syntax

/-!
# Selective DOT: typing

The judgments of the calculus.

```text
Γ ⊢ p : T          PathTy    a path has a type
Γ ⊢ S wf           Wf        the casts stored in an endpoint are valid
Γ ⊢ S ≤₀ T         Prim      primitive subtyping, between written endpoints
Γ ⊢ c : S ⇒ T      CertTy    a certificate converts S to T
Γ ⊢ t : T          HasTy     a term has a type
Γ ⊢ d : T          DefsTy    definitions have a type
```

The types in contexts and judgments are `Ty`. A `step[S,T]` writes two
endpoints `S T : ATy`; the certificate converts the erasure of `S` to the
erasure of `T`. So a cast or a composition matches the endpoint it is given up
to the casts written in paths, and those casts are checked: `Prim` holds only
of endpoints whose stored casts are all valid.

`Prim` has no transitivity rule. A selection step reads a bound from the type
of the receiver that is written in the endpoint: `p.A ≤₀ T` needs
`Γ ⊢ p : {A : L..U}` with `U` the erasure of `T`. Path typing has DOT's
`Rec-I`, `Rec-E` and `And-I` as ordinary rules, the rule for a cast, and the
rule `keep`, by which a cast path retains the types of the path under the
cast. It has no subsumption rule.

Term typing has no subsumption rule either. One primitive comparison, between
types without casts, is implicit at the argument of an application. Every
other conversion is a cast with a certificate.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Contexts -/

/-- A context is a list of types, newest binder first. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Ty s → Ctx (s,x)

/-- The type of a variable, weakened into the current scope. -/
def Ctx.lookup : Ctx s → BVar s .var → Ty s
  | .cons _ T, .here => T.weaken
  | .cons Γ _, .there y => (Γ.lookup y).weaken

/-! ## Paths, endpoints, primitive subtyping, certificates -/

mutual

/-- Path typing. -/
inductive PathTy : {s : Sig} → Ctx s → Path s → Ty s → Prop where
  | var : PathTy Γ (.var x) (Γ.lookup x)
  /-- A cast path has the target of its certificate. -/
  | cast : PathTy Γ p S → CertTy Γ c S T → PathTy Γ (.cast p c) T
  /-- A cast path keeps every type of the path under the cast. The cast is
  checked all the same. -/
  | keep : PathTy Γ p S → CertTy Γ c S T → PathTy Γ p U → PathTy Γ (.cast p c) U
  /-- `Rec-I`. -/
  | recI : PathTy Γ p (T.substVar p.root) → PathTy Γ p (.mu T)
  /-- `Rec-E`. -/
  | recE : PathTy Γ p (.mu T) → PathTy Γ p (T.substVar p.root)
  /-- `And-I`. -/
  | andI : PathTy Γ p T → PathTy Γ p U → PathTy Γ p (.and T U)

/-- Validity of an endpoint: every path in it has a type, so every cast stored
in it is checked. Paths under a binder are checked under that binder. -/
inductive Wf : {s : Sig} → Ctx s → ATy s → Prop where
  | top : Wf Γ .top
  | bot : Wf Γ .bot
  | typ : Wf Γ S → Wf Γ T → Wf Γ (.typ A S T)
  | fld : Wf Γ T → Wf Γ (.fld a T)
  | sel : PathTy Γ p T → Wf Γ (.sel p A)
  | mu : Wf (Γ.cons (.mu T.erase)) T → Wf Γ (.mu T)
  | all : Wf Γ S → Wf (Γ.cons S.erase) T → Wf Γ (.all S T)
  | and : Wf Γ S → Wf Γ T → Wf Γ (.and S T)

/-- Primitive subtyping between endpoints. There is no transitivity rule.
Every rule that does not compare a part of an endpoint checks that part with
`Wf`, so a derivation checks every cast stored in its two endpoints, in the
context in which the part is compared. For two function types that context has
the smaller domain. -/
inductive Prim : {s : Sig} → Ctx s → ATy s → ATy s → Prop where
  | top : Wf Γ S → Prim Γ S .top
  | bot : Wf Γ T → Prim Γ .bot T
  /-- Endpoints that differ only in the casts of their paths. -/
  | refl : Wf Γ S → Wf Γ T → S.erase = T.erase → Prim Γ S T
  | andL1 : Prim Γ S U → Wf Γ T → Prim Γ (.and S T) U
  | andL2 : Wf Γ S → Prim Γ T U → Prim Γ (.and S T) U
  | andR : Prim Γ S T → Prim Γ S U → Prim Γ S (.and T U)
  | fld : Prim Γ T U → Prim Γ (.fld a T) (.fld a U)
  | typ : Prim Γ S2 S1 → Prim Γ T1 T2 → Prim Γ (.typ A S1 T1) (.typ A S2 T2)
  | all : Prim Γ S2 S1 → Prim (Γ.cons S2.erase) T1 T2 → Prim Γ (.all S1 T1) (.all S2 T2)
  /-- `Sel-<:`, at the written receiver. -/
  | selU : PathTy Γ p (.typ A L U) → Wf Γ T → U = T.erase → Prim Γ (.sel p A) T
  /-- `<:-Sel`, at the written receiver. -/
  | selL : PathTy Γ p (.typ A L U) → Wf Γ S → L = S.erase → Prim Γ S (.sel p A)

/-- Certificate typing. -/
inductive CertTy : {s : Sig} → Ctx s → Cert s → Ty s → Ty s → Prop where
  | step : Prim Γ S T → CertTy Γ (.step S T) S.erase T.erase
  | seq : CertTy Γ c S M → CertTy Γ d M T → CertTy Γ (.seq c d) S T

end

/-- An endpoint without casts is valid. -/
theorem Wf.embed : ∀ {s : Sig} (Γ : Ctx s) (T : Ty s), Wf Γ T.embed
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, Γ, .typ _ S T => .typ (Wf.embed Γ S) (Wf.embed Γ T)
  | _, Γ, .fld _ T => .fld (Wf.embed Γ T)
  | _, _, .sel _ _ => .sel .var
  | _, _, .mu T => .mu (Wf.embed _ T)
  | _, Γ, .all S T => .all (Wf.embed Γ S) (Wf.embed _ T)
  | _, Γ, .and S T => .and (Wf.embed Γ S) (Wf.embed Γ T)

/-- Primitive subtyping between types, with every receiver a variable. This is
the comparison that term typing applies without a certificate. -/
def Prim₀ (Γ : Ctx s) (S T : Ty s) : Prop := Prim Γ S.embed T.embed

/-! ## Terms and definitions -/

mutual

/-- Term typing. There is no subsumption rule. -/
inductive HasTy : {s : Sig} → Ctx s → Tm s → Ty s → Prop where
  | path : PathTy Γ p T → HasTy Γ (.path p) T
  /-- `All-I`. -/
  | lam : HasTy (Γ.cons S) t T → HasTy Γ (.val (.lam S t)) (.all S T)
  /-- `All-E`, with one primitive comparison at the argument. -/
  | app :
      PathTy Γ p (.all S T) → PathTy Γ q S' → Prim₀ Γ S' S →
      HasTy Γ (.app p q) (T.substVar q.root)
  /-- `{}-I`. -/
  | obj : DefsTy (Γ.cons (.mu T)) d T → d.Distinct → HasTy Γ (.val (.obj d)) (.mu T)
  /-- `{}-E`. -/
  | proj : PathTy Γ p (.fld a T) → HasTy Γ (.proj p a) T
  | «let» : HasTy Γ t T → HasTy (Γ.cons T) u U.weaken → HasTy Γ (.let t u) U
  /-- A cast applies its certificate. -/
  | cast : HasTy Γ t S → CertTy Γ c S T → HasTy Γ (.cast t c) T

/-- Definition typing. -/
inductive DefsTy : {s : Sig} → Ctx s → Defs s → Ty s → Prop where
  | typ : DefsTy Γ (.typ A T) (.typ A T T)
  | trm : HasTy Γ t T → DefsTy Γ (.trm a t) (.fld a T)
  | and : DefsTy Γ d1 T1 → DefsTy Γ d2 T2 → DefsTy Γ (.and d1 d2) (.and T1 T2)

end

end SelDot
