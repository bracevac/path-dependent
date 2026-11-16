import Coercions.Selective.Negative
import Coercions.Selective.Annotate

/-!
# Selective subtyping for DOT-MNF: the main statements and two examples

Read this file first; the introduction is `README.md` in this directory.

The calculus `H` has DOT-MNF's types, contexts and programs (`DotMNF.Ty`,
`DotMNF.Ctx`, `DotMNF.Tm`), unchanged. On top of them it has

* a primitive subtyping relation `≤₀` (`Prim`) that is decidable and has no
  transitivity rule, and for which transitivity is not admissible;
* annotated terms (`HTm`) with no subsumption rule. A primitive step is
  applied without being written at an application argument and at the
  subject of a cast, and nowhere else. Every further step is written in the
  term, as a certificate `step[S,T]`, `c ; d` or a positioned member step.

The file has three parts: the main statements, each a reference to the
theorem that proves it; a program with a conversion that `≤₀` rejects and
its written certificates; and a program whose member step carries receiver
evidence.

The discipline is one primitive check at each allowed boundary, with every
further step guided by what is written. A use of DOT-MNF's transitivity rule
is translated to a written `;` (`trans_is_seq`), but an accepted annotation
of a program need not contain a `;`: example 1 is also accepted with one
written step, the application boundary supplying the other.
-/

namespace Selective.Hybrid

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path HasTy Sub)

/-! ## The target: DOT-MNF, unchanged

Nothing is restricted: `HTy` is stated over `DotMNF.Ty` and `DotMNF.Ctx`
(recursive types `μ`, dependent functions `∀(x : S) T`, type members with
both bounds `{A : L..U}`, fields, intersections, `⊤`, `⊥`), and the erasure
`HTm.erase` lands in `DotMNF.Tm`. Coverage of every DOT-MNF typing is
stated under exactness below. -/

/-! ## The discipline: one primitive step per boundary, the rest written -/

/-- `≤₀` is decided by `prim?`. -/
theorem prim_decided {s : Sig} {Γ : Ctx s} {S T : Ty s} : prim? Γ S T = true ↔ Prim Γ S T :=
  prim?_iff

/-- Transitivity of `≤₀` is not admissible. The witness is a realizable
context, `b : {B:⊥..⊤}, c : {C:⊥..⊤}, x : {A : b.B..c.C}`; its closed
realization is `realization` (`realization_typed`). -/
theorem prim_not_transitive :
    ¬ ∀ {s : Sig} (Γ : Ctx s) (S M T : Ty s), Prim Γ S M → Prim Γ M T → Prim Γ S T :=
  primitive_nontrans

/-- No subsumption: a variable used as a term has its declared type and no other. -/
theorem var_exact {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} :
    HTy Γ (.atom (.var x)) T ↔ T = Γ.lookup x :=
  HTy.atom_iff.trans ⟨fun h => by cases h; rfl, fun e => e ▸ .var⟩

/-- A written `step[A,B]` is one primitive step between exactly `A` and `B`. -/
theorem step_rule {s : Sig} {Γ : Ctx s} {A B S T : Ty s} :
    CTy Γ (.step A B) S T ↔ A = S ∧ B = T ∧ Prim Γ S T :=
  ⟨fun h => by cases h with | step p => exact ⟨rfl, rfl, p⟩,
   fun ⟨e1, e2, p⟩ => by subst e1; subst e2; exact .step p⟩

/-- The composition rule checks the written `c ; d`: both parts, meeting at one middle type. -/
theorem seq_rule {s : Sig} {Γ : Ctx s} {c d : Cert s} {S T : Ty s} :
    CTy Γ (.seq c d) S T ↔ ∃ M, CTy Γ c S M ∧ CTy Γ d M T :=
  ⟨fun h => by cases h with | seq hc hd => exact ⟨_, hc, hd⟩, fun ⟨_, hc, hd⟩ => .seq hc hd⟩

/-- A cast `t ▷ c`: one implicit `≤₀` step at the subject, then the written certificate. -/
theorem cast_rule {s : Sig} {Γ : Ctx s} {t : HTm s} {c : Cert s} {T : Ty s} :
    HTy Γ (.cast t c) T ↔ ∃ S0 S, HTy Γ t S0 ∧ Prim Γ S0 S ∧ CTy Γ c S T :=
  HTy.cast_iff

/-- An application `a b`: one implicit `≤₀` step at the argument, none at the callee. -/
theorem app_rule {s : Sig} {Γ : Ctx s} {a b : Atom s} {U : Ty s} :
    HTy Γ (.app a b) U ↔
      ∃ S T V, U = T.substVar b.root ∧ ATy Γ a (.all S T) ∧ ATy Γ b V ∧ Prim Γ V S :=
  HTy.app_iff

/-- A term cast by a written composite has the composed endpoint. -/
theorem cast_seq {s : Sig} {Γ : Ctx s} {t : HTm s} {c d : Cert s} {S M T : Ty s}
    (ht : HTy Γ t S) (hc : CTy Γ c S M) (hd : CTy Γ d M T) : HTy Γ (.cast t (.seq c d)) T :=
  .cast ht .refl (.seq hc hd)

/-- A cast erases to its subject. -/
theorem cast_erases {s : Sig} (t : HTm s) (c : Cert s) : (HTm.cast t c).erase = t.erase := rfl

/-- Stored evidence determines the type of a variable occurrence. -/
theorem atom_type_unique {s : Sig} {Γ : Ctx s} {a : Atom s} {T T' : Ty s}
    (h : ATy Γ a T) (h' : ATy Γ a T') : T = T' :=
  ATy.unique h h'

/-! ## Exactness and checking -/

/-- The certificate checker is sound and complete. -/
theorem cert_checker {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} :
    checkC Γ c S T = true ↔ CTy Γ c S T :=
  checkC_iff

/-- The term checker is sound and complete. It reads the stored evidence and searches for none. -/
theorem term_checker {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} :
    T ∈ synthTm Γ t ↔ HTy Γ t T :=
  synthTm_iff

/-- Coercion existence is DOT-MNF subtyping. -/
theorem coercion_exact {s : Sig} {Γ : Ctx s} {S T : Ty s} :
    (∃ c, CTy Γ c S T) ↔ Nonempty (Sub Γ S T) :=
  coercion_iff

/-- Typability of erased programs is DOT-MNF typability, at the same type. -/
theorem typability_exact {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    (∃ h : HTm s, h.erase = t ∧ HTy Γ h T) ↔ Nonempty (HasTy Γ t T) :=
  typability_iff

/-- Every DOT-MNF typing derivation has a computed annotation, with the same
erased program and the same type. -/
theorem annotation {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} (d : HasTy Γ t T) :
    d.toH.erase = t ∧ HTy Γ d.toH T :=
  d.toH_typed

/-- The term checker accepts the computed annotation. -/
theorem annotation_checks {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} (d : HasTy Γ t T) :
    T ∈ synthTm Γ d.toH :=
  synthTm_iff.mpr d.toH_typed.2

/-- A use of DOT-MNF's transitivity rule becomes a written `;`. -/
theorem trans_is_seq {s : Sig} {Γ : Ctx s} {S M T : Ty s} (d1 : Sub Γ S M) (d2 : Sub Γ M T) :
    (Sub.trans d1 d2).toCert = .seq d1.toCert d2.toCert := rfl

/-! ## Safety of the erased program

The erased program of a closed typed term runs safely on DOT-MNF's machine.
The proof reuses `DotMNF.dot_safety`; `H` has no machine of its own. -/

theorem safety {t : HTm []} {T : Ty []} (h : HTy .nil t T)
    {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, t.erase⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety h run

theorem not_stuck {t : HTm []} {T : Ty []} (h : HTy .nil t T)
    {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, t.erase⟩ : DotMNF.State []) st) : ¬ st.Stuck :=
  compiled_not_stuck h run

/-! ## Example 1: a conversion that `≤₀` rejects, written in the term

The context `Γgap` is

    b : {B : ⊥..⊤},  c : {C : ⊥..⊤},  x : {A : b.B..c.C},  k : ∀(_ : c.C) ⊤,  z : b.B

and the program is the application `k z`. The argument has type `b.B`, the
parameter type is `c.C`, and the way from one to the other used here goes
through `x.A`: two bound steps. The bare program is rejected. Three
annotations are accepted: the composite written in full, the same two steps
as nested casts, and the first step alone, where the implicit step at the
argument supplies the second. -/

/-- The variables of `Γgap`. -/
def gb : BVar Sg .var := .there (.there (.there (.there .here)))
def gc : BVar Sg .var := .there (.there (.there .here))
def gx : BVar Sg .var := .there (.there .here)
def gk : BVar Sg .var := .there .here
def gz : BVar Sg .var := .here

/-- `b.B`, `x.A` and `c.C`. -/
def gbB : Ty Sg := .sel (.var gb) lB
def gxA : Ty Sg := .sel (.var gx) lA
def gcC : Ty Sg := .sel (.var gc) lC

/-- The written certificate is `step[b.B, x.A] ; step[x.A, c.C]`. -/
theorem ex1_cert : (witG : Cert Sg) = .seq (.step gbB gxA) (.step gxA gcC) := rfl

/-- Each half is primitive; the composite is not. -/
theorem ex1_gap : Prim Γgap gbB gxA ∧ Prim Γgap gxA gcC ∧ ¬ Prim Γgap gbB gcC :=
  ⟨prim?_sound (by decide), prim?_sound (by decide), not_prim_of (by decide)⟩

/-- The bare program `k z` has no type in `H`. -/
theorem ex1_bare_rejected : ∀ U, ¬ HTy Γgap (.app (.var gk) (.var gz)) U :=
  gapNeeded_bare_untypable

/-- The direct certificate `step[b.B, c.C]` is rejected: it is not one primitive step.
This rules out that one certificate, not every annotation with one written step
(`ex1_one_written_step`). -/
theorem ex1_one_step_rejected :
    ∀ U, ¬ HTy Γgap (.app (.var gk) (.cast (.var gz) (.step gbB gcC))) U :=
  untypable_of_synthTm (by decide)

/-- `k (z ▷ (step[b.B, x.A] ; step[x.A, c.C]))` has type `⊤`. -/
theorem ex1_typed : HTy Γgap (.app (.var gk) (.cast (.var gz) witG)) .top :=
  gapBody_typed

/-- The term checker computes that type. -/
theorem ex1_checked : .top ∈ synthTm Γgap (.app (.var gk) (.cast (.var gz) witG)) := by decide

/-- The same two steps as nested casts, `k ((z ▷ step[b.B, x.A]) ▷ step[x.A, c.C])`,
with the same erasure. -/
theorem ex1_nested_casts :
    HTy Γgap (.app (.var gk) (.cast (.cast (.var gz) (.step gbB gxA)) (.step gxA gcC))) .top ∧
    (HTm.app (.var gk) (.cast (.cast (.var gz) (.step gbB gxA)) (.step gxA gcC)) : HTm Sg).erase =
      .app gk gz :=
  ⟨by decide, rfl⟩

/-- One written step suffices here: in `k (z ▷ step[b.B, x.A])` the cast gives
`z` the type `x.A`, and the application supplies `x.A ≤₀ c.C` as its one
implicit step. No `;` is written, and the erasure is the same. -/
theorem ex1_one_written_step :
    HTy Γgap (.app (.var gk) (.cast (.var gz) (.step gbB gxA))) .top ∧
    (HTm.app (.var gk) (.cast (.var gz) (.step gbB gxA)) : HTm Sg).erase = .app gk gz :=
  ⟨by decide, rfl⟩

/-- The annotated program erases to `k z`. -/
theorem ex1_erases :
    (HTm.app (.var gk) (.cast (.var gz) witG) : HTm Sg).erase = .app gk gz := rfl

/-- DOT-MNF types `k z` (by subsumption and transitivity), as exactness says it must. -/
theorem ex1_source_typed : Nonempty (HasTy Γgap (.app gk gz) .top) :=
  elaboration_typed gapBody_typed

/-- The same composite as a cast on a term: `z ▷ (step[b.B, x.A] ; step[x.A, c.C]) : c.C`,
erasing to `z`. Without the cast `z` has the type `b.B` only (`var_exact`). -/
theorem ex1_term_cast :
    HTy Γgap (.cast (.atom (.var gz)) witG) gcC ∧
    (HTm.cast (.atom (.var gz)) witG : HTm Sg).erase = .path (.var gz) :=
  ⟨by decide, rfl⟩

/-- The term cast with one written step, `z ▷ step[x.A, c.C] : c.C`: the
implicit step at the subject supplies `b.B ≤₀ x.A`. -/
theorem ex1_term_cast_one_step : HTy Γgap (.cast (.atom (.var gz)) (.step gxA gcC)) gcC := by
  decide

/-- The closed program around `k z`: three object literals for `b`, `c`,
`x`, the function `gapFn` whose body is example 1, and its five arguments.
This is its erased form, an ordinary DOT-MNF program. -/
def gapNeededTm : DotMNF.Tm [] :=
  .let (.val (.obj (.typ lB .top)))
  (.let (.val (.obj (.typ lC .top)))
  (.let (.val (.obj (.typ lA .top)))
  (.let (.val (.lam (.typ lB .bot .top) (.val (.lam (.typ lC .bot .top) (.val (.lam
      (.typ lA (.sel (.var (.there .here)) lB) (.sel (.var .here) lC))
      (.val (.lam (.all (.sel (.var (.there .here)) lC) .top)
        (.val (.lam (.sel (.var (.there (.there (.there .here)))) lB)
          (.app (.there .here) .here)))))))))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.app .here (.there (.there (.there .here))))
  (.let (.val (.lam (.sel (.var (.there (.there (.there (.there (.there .here)))))) lC)
      (.path (.var .here))))
  (.let (.app (.there .here) .here)
  (.app .here (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))

theorem ex1_closed_erases : gapNeeded.erase = gapNeededTm := rfl

theorem ex1_closed_typed : HTy .nil gapNeeded .top := gapNeeded_typed

theorem ex1_closed_safe {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, gapNeededTm⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  gapNeeded_safe run

/-! ## Example 2: a type selection that needs receiver evidence

The context `ΓR2` is

    w : {B : ⊥..{A : ⊥..{a:⊤}}},  y : w.B,  u : y.A

and the program is the projection `u.a`. The receiver `u` has the declared
type `y.A`, which declares no field. DOT-MNF derives `y.A <: {a:⊤}` by first
retyping `y` from `w.B` to `{A : ⊥..{a:⊤}}` and then reading the upper bound
of `A`. In `H` the bound step has to say how its receiver `y` gets a type
that declares `A`: the evidence is the receiver atom
`y ▷ step[w.B, {A : ⊥..{a:⊤}}]`, stored in the positioned member step
`selU`. For this `≤₀`, no certificate built from `step` and `;` does the
same (`ex2_no_step_only`). This is the part of `H` that plain F-sub does not
need. -/

def ru : BVar ([],x,x,x) .var := .here
def ry : BVar ([],x,x,x) .var := .there .here
def rw : BVar ([],x,x,x) .var := .there (.there .here)

/-- The receiver atom `y ▷ step[w.B, {A : ⊥..{a:⊤}}]`. -/
def recv : Atom ([],x,x,x) := .cast (.var ry) (.step (.sel (.var rw) lB) RInner)

/-- The annotated program is `(u ▷ selU(recv, A, {a:⊤})).a`. -/
theorem ex2_term : uProjH = .proj (.cast (.var ru) (.pos (.selU recv lA T1))) la := rfl

/-- The bare program `u.a` has no type in `H`. -/
theorem ex2_bare_rejected : ∀ U, ¬ HTy ΓR2 (.proj (.var ru) la) U :=
  untypable_of_synthTm (by decide)

/-- The bound step `y.A ≤₀ {a:⊤}` is not primitive: `y`'s declared type is `w.B`. -/
theorem ex2_not_primitive : ¬ Prim ΓR2 (.sel (.var ry) lA) T1 := not_prim_of (by decide)

/-- A member step whose receiver is the bare `y` is rejected. -/
theorem ex2_bare_receiver_rejected : ∀ S T, ¬ CTy ΓR2 (.pos (.selU (.var ry) lA T1)) S T :=
  fun S T h => by
    have e : synthC ΓR2 (.pos (.selU (.var ry) lA T1)) = some (S, T) := synthC_iff.mpr h
    have n : synthC ΓR2 (.pos (.selU (.var ry) lA T1)) = none := by decide
    rw [n] at e; cases e

/-- The types reachable from `y.A` by `≤₀` steps in `ΓR2`. -/
inductive Reach : Ty ([],x,x,x) → Prop where
  | sel : Reach (.sel (.var (.there .here)) lA)
  | top : Reach .top
  | and : Reach S → Reach T → Reach (.and S T)

theorem reach_step : {S T : Ty ([],x,x,x)} → Prim ΓR2 S T → Reach S → Reach T
  | _, _, .refl, h => h
  | _, _, .top, _ => .top
  | _, _, .bot, h => by cases h
  | _, _, .andR h1 h2, h => .and (reach_step h1 h) (reach_step h2 h)
  | _, _, .andL1 h1, h => by cases h with | and h' _ => exact reach_step h1 h'
  | _, _, .andL2 h1, h => by cases h with | and _ h' => exact reach_step h1 h'
  | _, _, .fld _, h => by cases h
  | _, _, .typ _ _, h => by cases h
  | _, _, .all _ _, h => by cases h
  | _, _, .selU e, h => by
      cases h
      have e' : Exp (.there .here) (.sel (.var (.there (.there .here))) lB) _ _ _ := e
      cases e'
  | _, _, .selL (x := x) e, h => by
      cases x with
      | here =>
          have e' : Exp .here (.sel (.var (.there .here)) lA) _ _ _ := e
          cases e'
      | there x =>
          cases x with
          | here =>
              have e' : Exp (.there .here) (.sel (.var (.there (.there .here))) lB) _ _ _ := e
              cases e'
          | there x =>
              cases x with
              | here =>
                  have e' : Exp (.there (.there .here)) (.typ lB .bot RInner) _ _ _ := e
                  cases e'; cases h
              | there v => cases v

theorem reach_chain {S T : Ty ([],x,x,x)} (h : Chain ΓR2 S T) (hS : Reach S) : Reach T := by
  induction h with
  | refl => exact hS
  | cons p _ ih => exact ih (reach_step p hS)

/-- No certificate built from `step` and `;` only relates `y.A` to `{a:⊤}` in `ΓR2`. -/
theorem ex2_no_step_only :
    ¬ ∃ c : Cert ([],x,x,x), c.StepOnly ∧ CTy ΓR2 c (.sel (.var ry) lA) T1 :=
  fun hc => by
    have h := reach_chain (stepOnly_iff_chain.mp hc) .sel
    cases h

/-- The receiver atom has the type that declares `A`, and still stands for `y`. -/
theorem ex2_receiver : ATy ΓR2 recv RInner ∧ recv.root = ry := ⟨synthA_iff.mp (by decide), rfl⟩

/-- With the receiver evidence, `u.a` has type `⊤`. -/
theorem ex2_typed : HTy ΓR2 uProjH .top := uProjH_typed

/-- The annotated program erases to `u.a`: receiver evidence leaves no trace. -/
theorem ex2_erases : uProjH.erase = .proj ru la := uProjH_erase

/-- The closed form: `λ(w : {B : ⊥..{A : ⊥..{a:⊤}}}). λ(y : w.B). λ(u : y.A). u.a`, annotated. -/
def receiverProgram : HTm [] :=
  .val (.lam (.typ lB .bot RInner) (.val (.lam wB (.val (.lam yA uProjH)))))

def receiverProgramTm : DotMNF.Tm [] :=
  .val (.lam (.typ lB .bot RInner) (.val (.lam wB (.val (.lam yA (.proj .here la))))))

def receiverProgramTy : Ty [] := .all (.typ lB .bot RInner) (.all wB (.all yA .top))

theorem ex2_closed_erases : receiverProgram.erase = receiverProgramTm := rfl

theorem ex2_closed_typed : HTy .nil receiverProgram receiverProgramTy := by decide

theorem ex2_closed_safe {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, receiverProgramTm⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' :=
  compiled_safety ex2_closed_typed run

/-! ## Receiver evidence is needed for this `≤₀`

Over the relation `Prim` fixed in `Prim.lean`, `step` and `;` alone do not
cover DOT-MNF subtyping. Nothing is claimed about other choices of the
primitive relation. For the endpoints of
`certY` (`y : ⊤ ⊢ ∀(x : {A : ⊤..{B : ⊥..{a:⊤}}}) y.B ⇒ ∀(x : …) {a:⊤}`) a
certificate exists, with a receiver that mentions the bound `x`, and no
certificate built from `step` and `;` only relates them. -/

theorem receiver_evidence_needed :
    CTy Γ0 certY SrcY DstY ∧ ¬ ∃ c : Cert ([],x), c.StepOnly ∧ CTy Γ0 c SrcY DstY :=
  ⟨certY_typed, Y_no_receiver_free_coercion⟩

/-! ## The other two annotation forms: recursive views and intersections

`unfold a` and `fold[T] a` open and close a recursive type at the variable
`a` stands for; `⟨a, b⟩` joins two views of the same variable. In
`f ⟨fold(unfold x ▷ _), unfold x ▷ _⟩` the argument `x : μ(s. {A:⊥..⊤} ∧ {a : s.A})`
is passed at `μ(s. {a : s.A}) ∧ {A:⊥..⊤}`. All three erase to `x`. -/

theorem views_typed : HTy ΓAnd bothApp .top ∧ bothApp.erase = .app (.there .here) .here :=
  ⟨bothApp_typed, bothApp_erase⟩

end Selective.Hybrid
