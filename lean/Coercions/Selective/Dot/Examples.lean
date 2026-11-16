import Coercions.Selective.Dot.Typing

/-!
# Selective DOT: examples

Derivations in the calculus of `Typing.lean`, written out.

1. `≤₀` is not transitive, in a context with a closed realization.
2. A type selection whose receiver needs a conversion: the cast on the
   receiver is written in the path of the endpoint.
3. Two casts on the same variable: the cast path keeps both views and has
   their intersection by `And-I`. An invalid cast is rejected wherever it is
   stored.
4. A receiver that is cast under the binder of a dependent function type.
5. A function type is checked under its own domain.
-/

namespace SelDot.Examples

open FCdot (Kind Sig BVar Rename Label)

def lA : Label := .typ 0
def lB : Label := .typ 1
def lC : Label := .typ 2
def la : Label := .trm 0

/-! ## The types of a variable path

A path without a cast has the declared type of its variable, closed under
`Rec-I`, `Rec-E` and `And-I`. -/

/-- The closure of a declared type `D` of `x` under the three implicit rules. -/
inductive VarCl (D : Ty s) (x : BVar s .var) : Ty s → Prop where
  | base : VarCl D x D
  | recI : VarCl D x (T.substVar x) → VarCl D x (.mu T)
  | recE : VarCl D x (.mu T) → VarCl D x (T.substVar x)
  | andI : VarCl D x T → VarCl D x U → VarCl D x (.and T U)

theorem var_inv_aux {Γ : Ctx s} : ∀ {p : Path s} {T : Ty s},
    PathTy Γ p T → ∀ x, p = .var x → VarCl (Γ.lookup x) x T
  | _, _, .var, _, e => by cases e; exact .base
  | _, _, .cast _ _, _, e => by cases e
  | _, _, .keep _ _ _, _, e => by cases e
  | _, _, .recI h, x, e => by have ih := var_inv_aux h x e; subst e; exact .recI ih
  | _, _, .recE h, x, e => by have ih := var_inv_aux h x e; subst e; exact .recE ih
  | _, _, .andI h1 h2, x, e => .andI (var_inv_aux h1 x e) (var_inv_aux h2 x e)

theorem var_inv {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : PathTy Γ (.var x) T) : VarCl (Γ.lookup x) x T := var_inv_aux h x rfl

/-- A path whose outermost cast has no type has no type: no rule skips the
check of a cast. -/
theorem cast_untyped_aux {Γ : Ctx s} {c : Cert s} (hc : ∀ S T, ¬ CertTy Γ c S T) :
    ∀ {q : Path s} {T : Ty s}, PathTy Γ q T → ∀ p, q = .cast p c → False
  | _, _, .var, _, e => by cases e
  | _, _, .cast _ h, _, e => by cases e; exact hc _ _ h
  | _, _, .keep _ h _, _, e => by cases e; exact hc _ _ h
  | _, _, .recI h, p, e => cast_untyped_aux hc h p e
  | _, _, .recE h, p, e => cast_untyped_aux hc h p e
  | _, _, .andI h _, p, e => cast_untyped_aux hc h p e

theorem cast_untyped {Γ : Ctx s} {c : Cert s} (hc : ∀ S T, ¬ CertTy Γ c S T)
    {p : Path s} {T : Ty s} : ¬ PathTy Γ (.cast p c) T :=
  fun h => cast_untyped_aux hc h p rfl

/-- The same closure without `Rec-E`. -/
inductive VarCl' (D : Ty s) (x : BVar s .var) : Ty s → Prop where
  | base : VarCl' D x D
  | recI : VarCl' D x (T.substVar x) → VarCl' D x (.mu T)
  | andI : VarCl' D x T → VarCl' D x U → VarCl' D x (.and T U)

/-- When the declared type is not recursive, `Rec-E` only undoes a `Rec-I`. -/
theorem VarCl.noRecE {D : Ty s} {x : BVar s .var} (hD : ∀ M, D ≠ .mu M) {T : Ty s}
    (h : VarCl D x T) : VarCl' D x T := by
  induction h with
  | base => exact .base
  | recI _ ih => exact .recI ih
  | recE _ ih =>
      cases ih with
      | base => exact absurd rfl (hD _)
      | recI h => exact h
  | andI _ _ ih1 ih2 => exact .andI ih1 ih2

/-- A variable whose declared type is a type declaration has no other type
declaration among its types. -/
theorem var_typ_inv {Γ : Ctx s} {x : BVar s .var} {A A' : Label} {L U L' U' : Ty s}
    (hD : Γ.lookup x = .typ A' L' U') (h : PathTy Γ (.var x) (.typ A L U)) :
    A = A' ∧ L = L' ∧ U = U' := by
  have h1 := (var_inv h).noRecE (by rw [hD]; intro M e; cases e)
  rw [hD] at h1
  cases h1
  exact ⟨rfl, rfl, rfl⟩

/-- A variable whose declared type is a selection has no type declaration
among its types. -/
theorem var_sel_no_typ {Γ : Ctx s} {x y : BVar s .var} {A B : Label} {L U : Ty s}
    (hD : Γ.lookup x = .sel y B) : ¬ PathTy Γ (.var x) (.typ A L U) := by
  intro h
  have h1 := (var_inv h).noRecE (by rw [hD]; intro M e; cases e)
  rw [hD] at h1
  cases h1

/-! ## `≤₀` is not transitive

`b : {B : ⊥..⊤}, c : {C : ⊥..⊤}, x : {A : b.B..c.C}`. Then `b.B ≤₀ x.A` and
`x.A ≤₀ c.C`, and `b.B ≤₀ c.C` fails. The context has a closed realization:
take `⊤` for all three members. -/

abbrev S3 : Sig := [],x,x,x

def Γr : Ctx S3 :=
  .cons (.cons (.cons .nil (.typ lB .bot .top)) (.typ lC .bot .top))
    (.typ lA (.sel (.there .here) lB) (.sel .here lC))

def rb : BVar S3 .var := .there (.there .here)
def rc : BVar S3 .var := .there .here
def rx : BVar S3 .var := .here

def bB : Ty S3 := .sel rb lB
def cC : Ty S3 := .sel rc lC
def xA : Ty S3 := .sel rx lA

theorem Γr_x : Γr.lookup rx = .typ lA bB cC := rfl
theorem Γr_b : Γr.lookup rb = .typ lB .bot .top := rfl
theorem Γr_c : Γr.lookup rc = .typ lC .bot .top := rfl

theorem half1 : Prim₀ Γr bB xA := .selL (Γr_x ▸ PathTy.var) (.sel .var) rfl
theorem half2 : Prim₀ Γr xA cC := .selU (Γr_x ▸ PathTy.var) (.sel .var) rfl

theorem gap : ¬ Prim₀ Γr bB cC := by
  intro h
  change Prim Γr (.sel (.var rb) lB) (.sel (.var rc) lC) at h
  cases h with
  | refl _ _ e => cases e
  | selU hp _ e =>
      obtain ⟨_, _, rfl⟩ := var_typ_inv Γr_b hp
      cases e
  | selL hp _ e =>
      obtain ⟨_, rfl, _⟩ := var_typ_inv Γr_c hp
      cases e

/-- The written composite. -/
def wit : Cert S3 := .seq (.step bB.embed xA.embed) (.step xA.embed cC.embed)

theorem wit_typed : CertTy Γr wit bB cC :=
  .seq (.step half1) (.step half2)

/-- Primitive subtyping is not transitive. -/
theorem primitive_nontrans :
    ¬ ∀ {s : Sig} (Γ : Ctx s) (S M T : Ty s), Prim₀ Γ S M → Prim₀ Γ M T → Prim₀ Γ S T :=
  fun h => gap (h Γr bB xA cC half1 half2)

/-- Primitive subtyping between written endpoints is not transitive: the three
endpoints of the witness are fixed, and `Prim₀` is `Prim` on them. -/
theorem prim_nontrans :
    ¬ ∀ {s : Sig} (Γ : Ctx s) (S M T : ATy s), Prim Γ S M → Prim Γ M T → Prim Γ S T :=
  fun h => gap (h Γr bB.embed xA.embed cC.embed half1 half2)

/-! ## A selection whose receiver needs a conversion

```text
R = {A : ⊥..{a : ⊤}}
w : {B : ⊥..R}, y : w.B, u : y.A
r = y ▷ step[w.B, R]
(u ▷ step[r.A, {a : ⊤}]).a
```

The declared type of `y` is `w.B`, which has no member `A`. The cast that gives
`y` the type `R` is written in the path `r` of the endpoint `r.A`. The
certificate converts `y.A`, the erasure of `r.A`, so it applies to `u`. -/

def R : Ty s := .typ lA .bot (.fld la .top)

def Γ2 : Ctx S3 :=
  .cons (.cons (.cons .nil (.typ lB .bot R)) (.sel .here lB)) (.sel .here lA)

def rw : BVar S3 .var := .there (.there .here)
def ry : BVar S3 .var := .there .here
def ru : BVar S3 .var := .here

theorem Γ2_w : Γ2.lookup rw = .typ lB .bot R := rfl
theorem Γ2_y : Γ2.lookup ry = .sel rw lB := rfl
theorem Γ2_u : Γ2.lookup ru = .sel ry lA := rfl

/-- `step[w.B, R]`. -/
def cRecv : Cert S3 := .step (.sel (.var rw) lB) R.embed

theorem cRecv_typed : CertTy Γ2 cRecv (.sel rw lB) R :=
  .step (.selU (Γ2_w ▸ PathTy.var) (.typ .bot (.fld .top)) rfl)

/-- The receiver `r = y ▷ step[w.B, R]`. -/
def r : Path S3 := .cast (.var ry) cRecv

theorem r_typed : PathTy Γ2 r R := .cast (Γ2_y ▸ PathTy.var) cRecv_typed

/-- `step[r.A, {a : ⊤}]`. -/
def cSel : Cert S3 := .step (.sel r lA) (.fld la .top)

/-- The step converts `y.A`: the cast in `r` is not part of the type. -/
theorem cSel_typed : CertTy Γ2 cSel (.sel ry lA) (.fld la .top) :=
  .step (.selU r_typed (.fld .top) rfl)

/-- `(u ▷ step[r.A, {a : ⊤}]).a`. -/
def ex2 : Tm S3 := .proj (.cast (.var ru) cSel) la

theorem ex2_typed : HasTy Γ2 ex2 .top :=
  .proj (.cast (Γ2_u ▸ PathTy.var) cSel_typed)

theorem ex2_erase : ex2.erase = .proj (.var ru) la := rfl

/-- Without the cast on the receiver the step is not primitive. -/
theorem ex2_bare_gap : ¬ Prim₀ Γ2 (.sel ry lA) (.fld la .top) := by
  intro h
  change Prim Γ2 (.sel (.var ry) lA) (.fld la .top) at h
  cases h with
  | refl _ _ e => cases e
  | selU hp _ _ => exact var_sel_no_typ Γ2_y hp

/-! ## Two casts on one variable

`x : {A : ⊥..⊥} ∧ {B : ⊥..⊥}`, with `c₁ : _ ⇒ {A : ⊥..⊤}` and
`c₂ : _ ⇒ {B : ⊥..⊤}`. The path `(x ▷ c₁) ▷ c₂` has the target of `c₂`, keeps
the target of `c₁`, and so has their intersection by `And-I`. -/

abbrev S1 : Sig := [],x

def D3 : Ty S1 := .and (.typ lA .bot .bot) (.typ lB .bot .bot)
def Γ3 : Ctx S1 := .cons .nil (.and (.typ lA .bot .bot) (.typ lB .bot .bot))
def x3 : BVar S1 .var := .here

theorem Γ3_x : Γ3.lookup x3 = D3 := rfl

def V1 : Ty S1 := .typ lA .bot .top
def V2 : Ty S1 := .typ lB .bot .top

def c1 : Cert S1 := .step D3.embed V1.embed
def c2 : Cert S1 := .step D3.embed V2.embed

theorem c1_typed : CertTy Γ3 c1 D3 V1 :=
  .step (.andL1 (.typ (.refl .bot .bot rfl) (.top .bot)) (.typ .bot .bot))

theorem c2_typed : CertTy Γ3 c2 D3 V2 :=
  .step (.andL2 (.typ .bot .bot) (.typ (.refl .bot .bot rfl) (.top .bot)))

def p3 : Path S1 := .cast (.cast (.var x3) c1) c2

/-- The path under the second cast still has the declared type. -/
theorem p3_inner_decl : PathTy Γ3 (.cast (.var x3) c1) D3 :=
  .keep (Γ3_x ▸ PathTy.var) c1_typed (Γ3_x ▸ PathTy.var)

theorem p3_new : PathTy Γ3 p3 V2 := .cast p3_inner_decl c2_typed

theorem p3_kept : PathTy Γ3 p3 V1 :=
  .keep p3_inner_decl c2_typed (.cast (Γ3_x ▸ PathTy.var) c1_typed)

/-- Both views, combined by `And-I`. -/
theorem p3_both : PathTy Γ3 p3 (.and V1 V2) := .andI p3_kept p3_new

/-! ### An invalid cast is rejected wherever it is stored -/

/-- `step[⊤, ⊥]` is not a certificate. -/
def cBad : Cert S1 := .step .top .bot

theorem cBad_untyped {S T : Ty S1} : ¬ CertTy Γ3 cBad S T := by
  intro h
  cases h with
  | step hp =>
      cases hp with
      | refl _ _ e => cases e

def pBad : Path S1 := .cast (.var x3) cBad

/-- The path `x ▷ step[⊤, ⊥]` has no type: `keep` does not hide the cast. -/
theorem pBad_untyped {T : Ty S1} : ¬ PathTy Γ3 pBad T :=
  cast_untyped (fun _ _ => cBad_untyped)

/-- `step[S, S]` is rejected when `S` stores the invalid cast, although its
two endpoints have the same erasure. -/
theorem step_refl_validates {S T : Ty S1} :
    ¬ CertTy Γ3 (.step (.sel pBad lA) (.sel pBad lA)) S T := by
  intro h
  cases h with
  | step hp =>
      cases hp with
      | refl hw _ _ =>
          cases hw with
          | sel hp => exact pBad_untyped hp
      | selU hp _ _ => exact pBad_untyped hp
      | selL hp _ _ => exact pBad_untyped hp

/-- `step[⊤, ⊥]` is not a certificate in any context. -/
theorem cBad_weaken_untyped {Γ : Ctx (S1,x)} {S T : Ty (S1,x)} : ¬ CertTy Γ cBad.weaken S T := by
  intro h
  cases h with
  | step hp =>
      cases hp with
      | refl _ _ e => cases e

/-- The same under a binder: the body of a function type is checked too. -/
theorem step_refl_validates_under_binder {S T : Ty S1} :
    ¬ CertTy Γ3 (.step (.all .top (.sel pBad.weaken lA)) (.all .top (.sel pBad.weaken lA))) S T := by
  intro h
  have bad : ∀ {Γ : Ctx (S1,x)} {T : Ty (S1,x)}, ¬ PathTy Γ pBad.weaken T :=
    cast_untyped (c := cBad.weaken) (fun _ _ => cBad_weaken_untyped)
  cases h with
  | step hp =>
      cases hp with
      | refl hw _ _ =>
          cases hw with
          | all _ hb =>
              cases hb with
              | sel hp => exact bad hp
      | all _ _ hb =>
          cases hb with
          | refl hw _ _ =>
              cases hw with
              | sel hp => exact bad hp
          | selU hp _ _ => exact bad hp
          | selL hp _ _ => exact bad hp

/-! ## A receiver cast under a dependent binder

```text
RB = {B : ⊥..{a : ⊤}},  D = {A : ⊤..RB},  y : ⊤
under x : D:   r = y ▷ (step[⊤, x.A] ; step[x.A, RB])
step[∀(x : D) r.B, ∀(x : D) {a : ⊤}]  :  ∀(x : D) y.B  ⇒  ∀(x : D) {a : ⊤}
```

The cast on `y` uses the bound variable `x`, so it can only be written under
the binder. It is written in the path of the selection in the endpoint. -/

def RB : Ty s := .typ lB .bot (.fld la .top)
def D4 : Ty s := .typ lA .top RB

def Γ4 : Ctx S1 := .cons .nil .top

abbrev S2 : Sig := [],x,x

/-- The context under the binder. -/
def Γ4x : Ctx S2 := Γ4.cons D4

def y4 : BVar S2 .var := .there .here
def x4 : BVar S2 .var := .here

theorem Γ4x_y : Γ4x.lookup y4 = .top := rfl
theorem Γ4x_x : Γ4x.lookup x4 = .typ lA .top RB := rfl

/-- `step[⊤, x.A] ; step[x.A, RB]`. -/
def cY : Cert S2 :=
  .seq (.step .top (.sel (.var x4) lA)) (.step (.sel (.var x4) lA) RB.embed)

theorem cY_typed : CertTy Γ4x cY .top RB :=
  .seq (.step (.selL (Γ4x_x ▸ PathTy.var) .top rfl))
    (.step (.selU (Γ4x_x ▸ PathTy.var) (.typ .bot (.fld .top)) rfl))

/-- The receiver under the binder. -/
def r4 : Path S2 := .cast (.var y4) cY

theorem r4_typed : PathTy Γ4x r4 RB := .cast (Γ4x_y ▸ PathTy.var) cY_typed

/-- `step[∀(x : D) r.B, ∀(x : D) {a : ⊤}]`. -/
def certY : Cert S1 :=
  .step (.all D4.embed (.sel r4 lB)) (.all D4.embed (.fld la .top))

theorem certY_typed :
    CertTy Γ4 certY (.all D4 (.sel y4 lB)) (.all D4 (.fld la .top)) :=
  .step (.all (.refl (Wf.embed _ D4) (Wf.embed _ D4) rfl) (.sel r4_typed)
    (.selU r4_typed (.fld .top) rfl))

/-- With the receiver left as the variable `y`, the step is not primitive. -/
theorem certY_bare_gap :
    ¬ Prim₀ Γ4 (.all D4 (.sel y4 lB)) (.all D4 (.fld la .top)) := by
  intro h
  change Prim Γ4 (.all D4.embed (.sel (.var y4) lB)) (.all D4.embed (.fld la .top)) at h
  cases h with
  | refl _ _ e => cases e
  | all _ _ hb =>
      cases hb with
      | refl _ _ e => cases e
      | selU hp _ _ =>
          have h1 := (var_inv hp).noRecE (by intro M e; cases e)
          cases h1

/-! ## A function type is checked under its own domain

`D = {A : ⊤..⊤}` and `p = x ▷ step[D, ⊤]`. The cast in `p` is valid under
`x : D` and invalid under `x : ⊤`, where `x` does not have the type `D`. So
`∀(x : ⊤) p.B` is not a valid endpoint, and the step from it to `∀(x : D) p.B`
is rejected although the two bodies are compared under `x : D`. -/

/-- The path under a cast has the source of the cast among its types. -/
theorem cast_inv_aux {Γ : Ctx s} : ∀ {q : Path s} {T : Ty s}, PathTy Γ q T →
    ∀ p c, q = .cast p c → ∃ S U, PathTy Γ p S ∧ CertTy Γ c S U
  | _, _, .var, _, _, e => by cases e
  | _, _, .cast hp hc, _, _, e => by cases e; exact ⟨_, _, hp, hc⟩
  | _, _, .keep hp hc _, _, _, e => by cases e; exact ⟨_, _, hp, hc⟩
  | _, _, .recI h, p, c, e => cast_inv_aux h p c e
  | _, _, .recE h, p, c, e => cast_inv_aux h p c e
  | _, _, .andI h _, p, c, e => cast_inv_aux h p c e

theorem cast_inv {Γ : Ctx s} {p : Path s} {c : Cert s} {T : Ty s}
    (h : PathTy Γ (.cast p c) T) : ∃ S U, PathTy Γ p S ∧ CertTy Γ c S U :=
  cast_inv_aux h p c rfl

def D5 : Ty s := .typ lA .top .top

/-- `p = x ▷ step[D, ⊤]`, under the binder. -/
def p5 : Path S1 := .cast (.var .here) (.step D5.embed .top)

/-- Under `x : D` the path has a type. -/
theorem p5_typed_under_D : PathTy (.cons .nil D5) p5 .top :=
  .cast (.var (x := .here)) (.step (.top (Wf.embed _ D5)))

/-- Under `x : ⊤` it has none: `x` does not have the source of the cast. -/
theorem p5_untyped_under_top {T : Ty S1} : ¬ PathTy (.cons .nil .top) p5 T := by
  intro h
  obtain ⟨S, U, hp, hc⟩ := cast_inv h
  cases hc with
  | step _ =>
      have h1 := (var_inv hp).noRecE (by intro M e; cases e)
      cases h1

theorem step_checks_source_body {S T : Ty []} :
    ¬ CertTy .nil (.step (.all .top (.sel p5 lB)) (.all D5.embed (.sel p5 lB))) S T := by
  intro h
  cases h with
  | step hp =>
      cases hp with
      | refl _ _ e => cases e
      | all _ hw _ =>
          cases hw with
          | sel hq => exact p5_untyped_under_top hq

end SelDot.Examples
