import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.RenameTy

/-!
# Selective DOT: certificate constructions

Certificates built from `step` and `seq` only, with their typing lemmas: the
reflexive step, the single steps for `⊤`, `⊥` and the two projections of an
intersection, and the lifts of a certificate through every type constructor
that subtyping is congruent for.

A lift maps every step `step[X, Y]` of a certificate to a step whose two
endpoints place `X` and `Y` in the same position of a larger endpoint; the
parts the lift adds are cast-free (`Ty.embed`) and so are valid by `Wf.embed`.
A contravariant lift reverses the chain.

The lifts through an intersection use `andL2`/`andL1`, whose premise checks
the endpoint `X` of the step; it is valid because `X` is an endpoint of a
primitive step (`Prim.wf_left`).
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

namespace Lift

/-- Erasure undoes the embedding of a cast-free type. -/
@[simp] theorem Ty.erase_embed' : ∀ {s : Sig} (T : Ty s), T.embed.erase = T
  | _, .top => rfl
  | _, .bot => rfl
  | _, .typ _ S T => by simp only [Ty.embed, ATy.erase, Ty.erase_embed' S, Ty.erase_embed' T]
  | _, .fld _ T => by simp only [Ty.embed, ATy.erase, Ty.erase_embed' T]
  | _, .sel _ _ => rfl
  | _, .mu T => by simp only [Ty.embed, ATy.erase, Ty.erase_embed' T]
  | _, .all S T => by simp only [Ty.embed, ATy.erase, Ty.erase_embed' S, Ty.erase_embed' T]
  | _, .and S T => by simp only [Ty.embed, ATy.erase, Ty.erase_embed' S, Ty.erase_embed' T]

end Lift

open Lift (Ty.erase_embed')

/-- A step typed by `CertTy.step`, with the erasures of embedded endpoints
rewritten away. -/
theorem CertTy.stepEmbed {Γ : Ctx s} {S T : Ty s} (h : Prim Γ S.embed T.embed) :
    CertTy Γ (.step S.embed T.embed) S T := by
  have h' := CertTy.step h
  rwa [Ty.erase_embed', Ty.erase_embed'] at h'

/-! ## Single steps -/

/-- The reflexive step `step[T, T]`. -/
def Cert.refl (T : Ty s) : Cert s := .step T.embed T.embed

theorem CertTy.refl {Γ : Ctx s} {T : Ty s} : CertTy Γ (.step T.embed T.embed) T T :=
  CertTy.stepEmbed (.refl (Wf.embed Γ T) (Wf.embed Γ T) rfl)

theorem CertTy.refl' {Γ : Ctx s} {T : Ty s} : CertTy Γ (Cert.refl T) T T := CertTy.refl

/-- `T ⇒ ⊤`. -/
def Cert.top (T : Ty s) : Cert s := .step T.embed .top

theorem CertTy.top {Γ : Ctx s} {T : Ty s} : CertTy Γ (Cert.top T) T .top :=
  CertTy.stepEmbed (T := .top) (.top (Wf.embed Γ T))

/-- `⊥ ⇒ T`. -/
def Cert.bot (T : Ty s) : Cert s := .step .bot T.embed

theorem CertTy.bot {Γ : Ctx s} {T : Ty s} : CertTy Γ (Cert.bot T) .bot T :=
  CertTy.stepEmbed (S := .bot) (.bot (Wf.embed Γ T))

/-- `S ∧ T ⇒ S`. -/
def Cert.and1 (S T : Ty s) : Cert s := .step (Ty.and S T).embed S.embed

theorem CertTy.and1 {Γ : Ctx s} {S T : Ty s} : CertTy Γ (Cert.and1 S T) (.and S T) S :=
  CertTy.stepEmbed (.andL1 (.refl (Wf.embed Γ S) (Wf.embed Γ S) rfl) (Wf.embed Γ T))

/-- `S ∧ T ⇒ T`. -/
def Cert.and2 (S T : Ty s) : Cert s := .step (Ty.and S T).embed T.embed

theorem CertTy.and2 {Γ : Ctx s} {S T : Ty s} : CertTy Γ (Cert.and2 S T) (.and S T) T :=
  CertTy.stepEmbed (.andL2 (Wf.embed Γ S) (.refl (Wf.embed Γ T) (Wf.embed Γ T) rfl))

/-- `S ⇒ S ∧ S`. -/
def Cert.dup (S : Ty s) : Cert s := .step S.embed (Ty.and S S).embed

theorem CertTy.dup {Γ : Ctx s} {S : Ty s} : CertTy Γ (Cert.dup S) S (.and S S) :=
  CertTy.stepEmbed (.andR (.refl (Wf.embed Γ S) (Wf.embed Γ S) rfl)
    (.refl (Wf.embed Γ S) (Wf.embed Γ S) rfl))

/-! ## Lifts -/

/-- Lift through a field declaration. -/
def Cert.fld : Cert s → Label → Cert s
  | .step X Y, a => .step (.fld a X) (.fld a Y)
  | .seq c d, a => .seq (c.fld a) (d.fld a)

/-- Lift through the lower bound of a type declaration (contravariant). -/
def Cert.typLo : Cert s → Label → Ty s → Cert s
  | .step X Y, A, T => .step (.typ A Y T.embed) (.typ A X T.embed)
  | .seq c d, A, T => .seq (d.typLo A T) (c.typLo A T)

/-- Lift through the upper bound of a type declaration. -/
def Cert.typHi : Cert s → Label → Ty s → Cert s
  | .step X Y, A, S => .step (.typ A S.embed X) (.typ A S.embed Y)
  | .seq c d, A, S => .seq (c.typHi A S) (d.typHi A S)

/-- Lift through the domain of a function type (contravariant). -/
def Cert.allDom : Cert s → Ty (s,x) → Cert s
  | .step X Y, T => .step (.all Y T.embed) (.all X T.embed)
  | .seq c d, T => .seq (d.allDom T) (c.allDom T)

/-- Lift through the body of a function type. -/
def Cert.allBody : Cert (s,x) → Ty s → Cert s
  | .step X Y, S => .step (.all S.embed X) (.all S.embed Y)
  | .seq c d, S => .seq (c.allBody S) (d.allBody S)

/-- Lift through the left operand of an intersection. -/
def Cert.andLeft : Cert s → Ty s → Cert s
  | .step X Y, U => .step (.and X U.embed) (.and Y U.embed)
  | .seq c d, U => .seq (c.andLeft U) (d.andLeft U)

/-- Lift through the right operand of an intersection. -/
def Cert.andRight : Cert s → Ty s → Cert s
  | .step X Y, T => .step (.and T.embed X) (.and T.embed Y)
  | .seq c d, T => .seq (c.andRight T) (d.andRight T)

/-- The target a certificate writes: the erasure of the last endpoint. -/
def Cert.tgt : Cert s → Ty s
  | .step _ Y => Y.erase
  | .seq _ d => d.tgt

/-- Both conversions of one type: `S ⇒ S ∧ S`, then `c` on the left, then `d`
on the right. -/
def Cert.andI (S : Ty s) (c d : Cert s) : Cert s :=
  .seq (Cert.dup S) (.seq (c.andLeft S) (d.andRight c.tgt))

/-! ## Typing of the lifts -/

theorem CertTy.tgt_eq {Γ : Ctx s} : ∀ {c : Cert s} {S T : Ty s}, CertTy Γ c S T → c.tgt = T
  | _, _, _, .step _ => rfl
  | _, _, _, CertTy.seq _ h2 => by unfold Cert.tgt; exact CertTy.tgt_eq h2

theorem CertTy.fld {Γ : Ctx s} {a : Label} :
    ∀ {c : Cert s} {T U : Ty s}, CertTy Γ c T U → CertTy Γ (c.fld a) (.fld a T) (.fld a U)
  | _, _, _, .step h => .step (.fld h)
  | _, _, _, .seq h1 h2 => .seq (CertTy.fld h1) (CertTy.fld h2)

theorem CertTy.typLo {Γ : Ctx s} {A : Label} {T : Ty s} :
    ∀ {c : Cert s} {S2 S1 : Ty s}, CertTy Γ c S2 S1 →
      CertTy Γ (c.typLo A T) (.typ A S1 T) (.typ A S2 T)
  | _, _, _, @CertTy.step _ _ X Y h => by
      have h' := CertTy.step (Prim.typ (A := A) h
        (.refl (Wf.embed Γ T) (Wf.embed Γ T) rfl))
      simp only [ATy.erase, Ty.erase_embed'] at h'
      exact h'
  | _, _, _, .seq h1 h2 => .seq (CertTy.typLo h2) (CertTy.typLo h1)

theorem CertTy.typHi {Γ : Ctx s} {A : Label} {S : Ty s} :
    ∀ {c : Cert s} {T1 T2 : Ty s}, CertTy Γ c T1 T2 →
      CertTy Γ (c.typHi A S) (.typ A S T1) (.typ A S T2)
  | _, _, _, @CertTy.step _ _ X Y h => by
      have h' := CertTy.step (Prim.typ (A := A)
        (.refl (Wf.embed Γ S) (Wf.embed Γ S) rfl) h)
      simp only [ATy.erase, Ty.erase_embed'] at h'
      exact h'
  | _, _, _, .seq h1 h2 => .seq (CertTy.typHi h1) (CertTy.typHi h2)

theorem CertTy.allDom {Γ : Ctx s} {T : Ty (s,x)} :
    ∀ {c : Cert s} {S2 S1 : Ty s}, CertTy Γ c S2 S1 →
      CertTy Γ (c.allDom T) (.all S1 T) (.all S2 T)
  | _, _, _, @CertTy.step _ _ X Y h => by
      have h' := CertTy.step (Prim.all h (Wf.embed _ T)
        (.refl (Wf.embed _ T) (Wf.embed _ T) rfl))
      simp only [ATy.erase, Ty.erase_embed'] at h'
      exact h'
  | _, _, _, .seq h1 h2 => .seq (CertTy.allDom h2) (CertTy.allDom h1)

theorem CertTy.allBody_aux {Γ : Ctx s} {S : Ty s} :
    ∀ {Δ : Ctx (s,x)} {c : Cert (s,x)} {T1 T2 : Ty (s,x)}, CertTy Δ c T1 T2 →
      Δ = Γ.cons S → CertTy Γ (c.allBody S) (.all S T1) (.all S T2)
  | _, _, _, _, @CertTy.step _ _ X Y h, e => by
      subst e
      have hS : S.embed.erase = S := Ty.erase_embed' S
      have h1 : Prim (Γ.cons S.embed.erase) X Y := by rw [hS]; exact h
      have h' := CertTy.step (Prim.all (.refl (Wf.embed Γ S) (Wf.embed Γ S) rfl) h1.wf_left h1)
      simp only [ATy.erase, Ty.erase_embed'] at h'
      simp only [Cert.allBody]
      exact h'
  | _, _, _, _, .seq h1 h2, e => by
      simp only [Cert.allBody]
      exact .seq (CertTy.allBody_aux h1 e) (CertTy.allBody_aux h2 e)

theorem CertTy.allBody {Γ : Ctx s} {S : Ty s} {c : Cert (s,x)} {T1 T2 : Ty (s,x)}
    (h : CertTy (Γ.cons S) c T1 T2) : CertTy Γ (c.allBody S) (.all S T1) (.all S T2) :=
  CertTy.allBody_aux h rfl

theorem CertTy.andLeft {Γ : Ctx s} {U : Ty s} :
    ∀ {c : Cert s} {T T' : Ty s}, CertTy Γ c T T' →
      CertTy Γ (c.andLeft U) (.and T U) (.and T' U)
  | _, _, _, @CertTy.step _ _ X Y h => by
      have h' := CertTy.step (Prim.andR (Prim.andL1 h (Wf.embed Γ U))
        (Prim.andL2 h.wf_left (.refl (Wf.embed Γ U) (Wf.embed Γ U) rfl)))
      simp only [ATy.erase, Ty.erase_embed'] at h'
      exact h'
  | _, _, _, .seq h1 h2 => .seq (CertTy.andLeft h1) (CertTy.andLeft h2)

theorem CertTy.andRight {Γ : Ctx s} {T : Ty s} :
    ∀ {c : Cert s} {U U' : Ty s}, CertTy Γ c U U' →
      CertTy Γ (c.andRight T) (.and T U) (.and T U')
  | _, _, _, @CertTy.step _ _ X Y h => by
      have h' := CertTy.step (Prim.andR
        (Prim.andL1 (.refl (Wf.embed Γ T) (Wf.embed Γ T) rfl) h.wf_left)
        (Prim.andL2 (Wf.embed Γ T) h))
      simp only [ATy.erase, Ty.erase_embed'] at h'
      exact h'
  | _, _, _, .seq h1 h2 => .seq (CertTy.andRight h1) (CertTy.andRight h2)

/-- `And-I` for certificates. -/
theorem CertTy.andI {Γ : Ctx s} {S T U : Ty s} {c d : Cert s}
    (hc : CertTy Γ c S T) (hd : CertTy Γ d S U) :
    CertTy Γ (Cert.andI S c d) S (.and T U) := by
  unfold Cert.andI
  rw [CertTy.tgt_eq hc]
  exact .seq CertTy.dup (.seq (CertTy.andLeft hc) (CertTy.andRight hd))

theorem CertTy.andI_exists {Γ : Ctx s} {S T U : Ty s} {c d : Cert s}
    (hc : CertTy Γ c S T) (hd : CertTy Γ d S U) :
    ∃ e, CertTy Γ e S (.and T U) := ⟨_, CertTy.andI hc hd⟩

end SelDot
