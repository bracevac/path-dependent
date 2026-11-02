import Coercions.Nominal.Source.Derived

/-!
# The nominal vocabulary of the source

Plan XII, section "The nominal vocabulary of the source".  The relations that say how a type reaches a
class type `p.C` in pDOT-C, and the three theorems of the plan's Head about them.

`ops(T)` is the list of operands of a nested intersection.  `IsView G q T` (IV-Var to IV-And2) reads a
type of the path `q` off the context: a binder, a field, a singleton, an upper bound, an unfolded `μ`,
an operand.  `Up G S S'` (Up-Upper to Up-ReplQP) is one step up from `S`: an operand of `∧`, the upper
bound of a member read off a view, or a replacement along an alias.  `UpStar` is its reflexive
transitive closure.  `AliasStep` and `AliasEq` are one replacement step on a path and its equivalence
closure.  `ClassReach G (q, D) (p, C)` is the class order: the declared parents of a class body, up to
aliases of paths.  `Factor G S p C` holds when an `Up` path from `S` arrives at `⊥` or at `q.C` with `q`
an alias of `p`.

The three theorems:

- `Factor.sub`: a factorization is a subtyping, `Factor G S p C → G ⊢ S <: p.C`.
- `Ty.Structural.not_factor`: no structural type factors through a class type.
- `class_order`: under `G.ClassDecls K`, for class labels `D` and `C`, `q.D` factors through `p.C`
  exactly when `(q, D)` reaches `(p, C)` in the class order.

The proofs follow the plan's section "Proof route", with its three lemmas.  L1 (`Repl.sngl_inv`,
`Repl.sel_inv`, `Repl.into_sel`, `Repl.sel_of_sngl`): a replacement keeps a selection a selection at the
same label, and replaces in `p.A` as in `p.type`.  L2 (`AliasEq.trans`, `AliasEq.symm`): `AliasEq` is
an equivalence.  L3 (`Repl.structural`, `Up.structural`): from a structural type every `Up` step stays
structural.
-/

namespace Nominal.Source
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The vocabulary -/

/-- `ops(T)`, the operands of a nested intersection: `ops(T ∧ U) = ops(T) ++ ops(U)` and `ops(X) = [X]`
for every other former. -/
def Ty.ops : Ty s → List (Ty s)
  | .and T U => T.ops ++ U.ops
  | .top => [.top]
  | .bot => [.bot]
  | .rcd D => [.rcd D]
  | .sel p A => [.sel p A]
  | .mu T => [.mu T]
  | .all S T => [.all S T]
  | .sngl p => [.sngl p]

/-- `T` is structural: `⊤`, a record `{D}`, a `μ(z. T)`, a `∀(z : S) T`, a singleton `p.type`, or an
intersection `T ∧ U` of two structural types.  Neither `⊥` nor a selection `p.A` is. -/
def Ty.Structural : Ty s → Prop
  | .top => True
  | .rcd _ => True
  | .mu _ => True
  | .all _ _ => True
  | .sngl _ => True
  | .and T U => T.Structural ∧ U.Structural
  | .bot => False
  | .sel _ _ => False

/-- `IsView G q T`: `T` is a view of the path `q` in `G`, the rules IV-Var to IV-And2. -/
inductive IsView (G : Ctx s) : Path s → Ty s → Prop where
  -- IV-Var        binders G x T
  | var {x : BVar s .var} {T : Ty s} : G.lookup x = T → IsView G (.var x) T
  -- IV-Fld        binders G q a T U
  | fld {q : Path s} {a : Label} {T U : Ty s} : IsView G q T → .rcd (.trm a U) ∈ T.ops → IsView G (q.sel a) U
  -- IV-PathElim   binders G q r a T
  | pathElim {q r : Path s} {a : Label} {T : Ty s} : IsView G q (.sngl r) → IsView G (r.sel a) T →
      IsView G (q.sel a) (.sngl (r.sel a))
  -- IV-Sngl       binders G p r T
  | sngl {p r : Path s} {T : Ty s} : IsView G p (.sngl r) → IsView G r T → IsView G p T
  -- IV-Upper      binders G p q A T L U
  | upper {p q : Path s} {A : Label} {T L U : Ty s} : IsView G p (.sel q A) → IsView G q T →
      .rcd (.typ A L U) ∈ T.ops → IsView G p U
  -- IV-Unfold     binders G p T, z of T
  | unfold {p : Path s} {T : Ty (s,x)} : IsView G p (.mu T) → IsView G p (T.substPath p)
  -- IV-And1       binders G p T U
  | and1 {p : Path s} {T U : Ty s} : IsView G p (.and T U) → IsView G p T
  -- IV-And2       binders G p T U
  | and2 {p : Path s} {T U : Ty s} : IsView G p (.and T U) → IsView G p U

/-- `Up G S S'`: one step up from `S`, an operand of `∧`, the upper bound of a member read off a view,
or a replacement, the rules Up-Upper to Up-ReplQP. -/
inductive Up (G : Ctx s) : Ty s → Ty s → Prop where
  -- Up-Upper      binders G q T A L U
  | upper {q : Path s} {T : Ty s} {A : Label} {L U : Ty s} : IsView G q T → .rcd (.typ A L U) ∈ T.ops → Up G (.sel q A) U
  -- Up-And1       binders G S₁ S₂
  | and1 {S₁ S₂ : Ty s} : Up G (.and S₁ S₂) S₁
  -- Up-And2       binders G S₁ S₂
  | and2 {S₁ S₂ : Ty s} : Up G (.and S₁ S₂) S₂
  -- Up-ReplPQ     binders G r r' V S S'
  | replPQ {r r' : Path s} {V S S' : Ty s} : IsView G r (.sngl r') → Nonempty (HasTy G (.path r') V) →
      Nonempty (Repl r r' S S') → Up G S S'
  -- Up-ReplQP     binders G r r' V S S'
  | replQP {r r' : Path s} {V S S' : Ty s} : IsView G r (.sngl r') → Nonempty (HasTy G (.path r') V) →
      Nonempty (Repl r' r S S') → Up G S S'

/-- `UpStar G S S'`: the reflexive transitive closure of `Up`, the rules Up*-Refl and Up*-Step. -/
inductive UpStar (G : Ctx s) : Ty s → Ty s → Prop where
  -- Up*-Refl      binders G S
  | refl {S : Ty s} : UpStar G S S
  -- Up*-Step      binders G S M S'
  | step {S M S' : Ty s} : Up G S M → UpStar G M S' → UpStar G S S'

/-- `AliasStep G p p'`: one replacement step on a path, `r ↦ r' ⊢ p.type ⇝ p'.type` or its reverse at
a view `r'.type` of `r`, the rules AS-PQ and AS-QP. -/
inductive AliasStep (G : Ctx s) : Path s → Path s → Prop where
  -- AS-PQ         binders G r r' V p p'
  | pq {r r' : Path s} {V : Ty s} {p p' : Path s} : IsView G r (.sngl r') → Nonempty (HasTy G (.path r') V) →
      Nonempty (Repl r r' (.sngl p) (.sngl p')) → AliasStep G p p'
  -- AS-QP         binders G r r' V p p'
  | qp {r r' : Path s} {V : Ty s} {p p' : Path s} : IsView G r (.sngl r') → Nonempty (HasTy G (.path r') V) →
      Nonempty (Repl r' r (.sngl p) (.sngl p')) → AliasStep G p p'

/-- `AliasEq G p p'`: the equivalence closure of `AliasStep`, the rules AE-Refl, AE-Step, AE-Back. -/
inductive AliasEq (G : Ctx s) : Path s → Path s → Prop where
  -- AE-Refl       binders G p
  | refl {p : Path s} : AliasEq G p p
  -- AE-Step       binders G p p' p''
  | step {p p' p'' : Path s} : AliasStep G p p' → AliasEq G p' p'' → AliasEq G p p''
  -- AE-Back       binders G p p' p''
  | back {p p' p'' : Path s} : AliasStep G p' p → AliasEq G p' p'' → AliasEq G p p''

/-- `ClassReach G (q, D) (p, C)`: the class order, the declared parents `q'.B` of a class body
`{D : ⊥..U}` up to aliases of paths, the rules CR-Refl, CR-Parent, CR-Alias. -/
inductive ClassReach (G : Ctx s) : Path s × Label → Path s × Label → Prop where
  -- CR-Refl       binders G q D
  | refl {q : Path s} {D : Label} : ClassReach G (q, D) (q, D)
  -- CR-Parent     binders G q T D U q' B p C
  | parent {q : Path s} {T : Ty s} {D : Label} {U : Ty s} {q' : Path s} {B : Label} {p : Path s} {C : Label} :
      IsView G q T → .rcd (.typ D .bot U) ∈ T.ops → .sel q' B ∈ U.ops → ClassReach G (q', B) (p, C) →
      ClassReach G (q, D) (p, C)
  -- CR-Alias      binders G q q' D p C
  | alias {q q' : Path s} {D : Label} {p : Path s} {C : Label} : AliasEq G q q' → ClassReach G (q', D) (p, C) →
      ClassReach G (q, D) (p, C)

/-- `ClassBody K U`: `U = μ(z. T₀) ∧ Ps` with every operand of `Ps` a selection `q.B` with `B ∈ K`, or
`⊤`. -/
def ClassBody (K : List Label) (U : Ty s) : Prop :=
  ∃ (T₀ : Ty (s,x)) (Ps : Ty s), U = .and (.mu T₀) Ps ∧
    ∀ X ∈ Ps.ops, (∃ (q : Path s) (B : Label), X = .sel q B ∧ B ∈ K) ∨ X = .top

/-- `G.ClassDecls K`: every view `IsView G q T` with an operand `{D : L..U}`, `D ∈ K`, has `L = ⊥` and
`ClassBody K U`. -/
def Ctx.ClassDecls (G : Ctx s) (K : List Label) : Prop :=
  ∀ (q : Path s) (T : Ty s) (D : Label) (L U : Ty s), IsView G q T → .rcd (.typ D L U) ∈ T.ops → D ∈ K →
    L = .bot ∧ ClassBody K U

/-- `Factor G S p C`: an `Up` path from `S` arrives at `⊥`, or at `q.C` with `q` an alias of `p`. -/
def Factor (G : Ctx s) (S : Ty s) (p : Path s) (C : Label) : Prop :=
  ∃ S', UpStar G S S' ∧ (S' = .bot ∨ ∃ q, S' = .sel q C ∧ AliasEq G q p)

/-! ## Lemmas -/

/-- A type that is no intersection is its own operand, `X ∈ ops(X)`. -/
theorem Ty.mem_ops_self_of_not_and : ∀ (T : Ty s), (∀ T₁ T₂, T ≠ .and T₁ T₂) → T ∈ T.ops
  | .and T₁ T₂, h => absurd rfl (h T₁ T₂)
  | .top, _ => List.mem_singleton_self _
  | .bot, _ => List.mem_singleton_self _
  | .rcd _, _ => List.mem_singleton_self _
  | .sel _ _, _ => List.mem_singleton_self _
  | .mu _, _ => List.mem_singleton_self _
  | .all _ _, _ => List.mem_singleton_self _
  | .sngl _, _ => List.mem_singleton_self _

/-- A type is a subtype of each of its operands: `X ∈ ops(T) → G ⊢ T <: X`. -/
theorem Sub.of_ops {G : Ctx s} : ∀ {T X : Ty s}, X ∈ T.ops → Nonempty (Sub G T X)
  | .and T₁ T₂, X, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨e⟩ := Sub.of_ops (G := G) h; exact ⟨.subtyp_trans .subtyp_and11 e⟩
      · obtain ⟨e⟩ := Sub.of_ops (G := G) h; exact ⟨.subtyp_trans .subtyp_and12 e⟩
  | .top, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .bot, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .rcd _, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .sel _ _, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .mu _, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .all _ _, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩
  | .sngl _, X, h => by cases List.mem_singleton.mp h; exact ⟨.subtyp_refl⟩

/-- Every operand is reached by Up-And1 and Up-And2 steps: `X ∈ ops(T) → UpStar G T X`. -/
theorem UpStar.of_ops {G : Ctx s} : ∀ {T X : Ty s}, X ∈ T.ops → UpStar G T X
  | .and T₁ T₂, X, h => by
      rcases List.mem_append.mp h with h | h
      · exact .step .and1 (UpStar.of_ops h)
      · exact .step .and2 (UpStar.of_ops h)
  | .top, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .bot, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .rcd _, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .sel _ _, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .mu _, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .all _ _, X, h => by cases List.mem_singleton.mp h; exact .refl
  | .sngl _, X, h => by cases List.mem_singleton.mp h; exact .refl

/-- `UpStar` is transitive: `UpStar G S M → UpStar G M S' → UpStar G S S'`. -/
theorem UpStar.trans {G : Ctx s} {S M S' : Ty s} (h₁ : UpStar G S M) (h₂ : UpStar G M S') : UpStar G S S' := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- `IsView.sound`: a view of a path is a typing of it, `IsView G q T → G ⊢ q : T`. -/
theorem IsView.sound {G : Ctx s} {q : Path s} {T : Ty s} (h : IsView G q T) : Nonempty (HasTy G (.path q) T) := by
  induction h with
  | var e => exact ⟨.ty_var e⟩
  | fld _ hm ih =>
      obtain ⟨d⟩ := ih; obtain ⟨e⟩ := Sub.of_ops (G := G) hm
      exact ⟨.ty_new_elim (.ty_sub d e)⟩
  | pathElim _ _ ih₁ ih₂ => obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂; exact ⟨.ty_path_elim d₁ d₂⟩
  | sngl _ _ ih₁ ih₂ => obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂; exact ⟨.ty_sngl d₁ d₂⟩
  | upper _ _ hm ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂; obtain ⟨e⟩ := Sub.of_ops (G := G) hm
      exact ⟨.ty_sub d₁ (.subtyp_sel1 (.ty_sub d₂ e))⟩
  | unfold _ ih => obtain ⟨d⟩ := ih; exact ⟨.ty_rec_elim d⟩
  | and1 _ ih => obtain ⟨d⟩ := ih; exact ⟨.ty_sub d .subtyp_and11⟩
  | and2 _ ih => obtain ⟨d⟩ := ih; exact ⟨.ty_sub d .subtyp_and12⟩

/-- L1: a replacement `r ↦ r' ⊢ q.type ⇝ X` is one of the same path rule, `q = r.bs` and
`X = (r'.bs).type`. -/
theorem Repl.sngl_inv {r r' q : Path s} {X : Ty s} (h : Repl r r' (.sngl q) X) :
    ∃ bs, q = r.nomExt bs ∧ X = .sngl (r'.nomExt bs) := by
  cases h with
  | rsngl => exact ⟨_, rfl, rfl⟩

/-- L1: a replacement `r ↦ r' ⊢ q.A ⇝ X` is one of the same path rule at the same label, `q = r.bs`
and `X = (r'.bs).A`. -/
theorem Repl.sel_inv {r r' q : Path s} {A : Label} {X : Ty s} (h : Repl r r' (.sel q A) X) :
    ∃ bs, q = r.nomExt bs ∧ X = .sel (r'.nomExt bs) A := by
  cases h with
  | rpath => exact ⟨_, rfl, rfl⟩

/-- L1: a replacement `r ↦ r' ⊢ X ⇝ q'.A` comes from a selection at the same label, `X = (r.bs).A`
and `q' = r'.bs`. -/
theorem Repl.into_sel {r r' q' : Path s} {A : Label} {X : Ty s} (h : Repl r r' X (.sel q' A)) :
    ∃ bs, X = .sel (r.nomExt bs) A ∧ q' = r'.nomExt bs := by
  cases h with
  | rpath => exact ⟨_, rfl, rfl⟩

/-- L1: `r ↦ r' ⊢ q.type ⇝ q'.type` gives `r ↦ r' ⊢ q.A ⇝ q'.A`. -/
def Repl.sel_of_sngl {r r' q q' : Path s} (A : Label) (h : Repl r r' (.sngl q) (.sngl q')) :
    Repl r r' (.sel q A) (.sel q' A) := by
  cases h with
  | rsngl => exact .rpath

/-- L2: `AliasEq` is transitive. -/
theorem AliasEq.trans {G : Ctx s} {p q r : Path s} (h₁ : AliasEq G p q) (h₂ : AliasEq G q r) : AliasEq G p r := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)
  | back h _ ih => exact .back h (ih h₂)

/-- L2: `AliasEq` is symmetric. -/
theorem AliasEq.symm {G : Ctx s} {p q : Path s} (h : AliasEq G p q) : AliasEq G q p := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact ih.trans (.back h .refl)
  | back h _ ih => exact ih.trans (.step h .refl)

/-- An alias step `AliasStep G p p'` gives `G ⊢ p.C <: p'.C` and `G ⊢ p'.C <: p.C` at every label `C`. -/
theorem AliasStep.sub {G : Ctx s} {p p' : Path s} (h : AliasStep G p p') (C : Label) :
    Nonempty (Sub G (.sel p C) (.sel p' C)) ∧ Nonempty (Sub G (.sel p' C) (.sel p C)) := by
  cases h with
  | pq hv hr hp =>
      obtain ⟨dv⟩ := hv.sound; obtain ⟨dr⟩ := hr; obtain ⟨rp⟩ := hp
      have rs := Repl.sel_of_sngl C rp
      exact ⟨⟨.subtyp_sngl_pq dv dr rs⟩, ⟨.subtyp_sngl_qp dv dr rs.swap⟩⟩
  | qp hv hr hp =>
      obtain ⟨dv⟩ := hv.sound; obtain ⟨dr⟩ := hr; obtain ⟨rp⟩ := hp
      have rs := Repl.sel_of_sngl C rp
      exact ⟨⟨.subtyp_sngl_qp dv dr rs⟩, ⟨.subtyp_sngl_pq dv dr rs.swap⟩⟩

/-- An alias equivalence `AliasEq G p p'` gives `G ⊢ p.C <: p'.C` at every label `C`. -/
theorem AliasEq.sub {G : Ctx s} {p p' : Path s} (h : AliasEq G p p') (C : Label) : Nonempty (Sub G (.sel p C) (.sel p' C)) := by
  induction h with
  | refl => exact ⟨.subtyp_refl⟩
  | step h _ ih => obtain ⟨e₁⟩ := (h.sub C).1; obtain ⟨e₂⟩ := ih; exact ⟨.subtyp_trans e₁ e₂⟩
  | back h _ ih => obtain ⟨e₁⟩ := (h.sub C).2; obtain ⟨e₂⟩ := ih; exact ⟨.subtyp_trans e₁ e₂⟩

/-- One step up is a subtyping: `Up G S S' → G ⊢ S <: S'`. -/
theorem Up.sub {G : Ctx s} {S S' : Ty s} (h : Up G S S') : Nonempty (Sub G S S') := by
  cases h with
  | upper hv hm =>
      obtain ⟨d⟩ := hv.sound; obtain ⟨e⟩ := Sub.of_ops (G := G) hm
      exact ⟨.subtyp_sel1 (.ty_sub d e)⟩
  | and1 => exact ⟨.subtyp_and11⟩
  | and2 => exact ⟨.subtyp_and12⟩
  | replPQ hv hr hp => obtain ⟨dv⟩ := hv.sound; obtain ⟨dr⟩ := hr; obtain ⟨rp⟩ := hp; exact ⟨.subtyp_sngl_pq dv dr rp⟩
  | replQP hv hr hp => obtain ⟨dv⟩ := hv.sound; obtain ⟨dr⟩ := hr; obtain ⟨rp⟩ := hp; exact ⟨.subtyp_sngl_qp dv dr rp⟩

/-- A path up is a subtyping: `UpStar G S S' → G ⊢ S <: S'`. -/
theorem UpStar.sub {G : Ctx s} {S S' : Ty s} (h : UpStar G S S') : Nonempty (Sub G S S') := by
  induction h with
  | refl => exact ⟨.subtyp_refl⟩
  | step h _ ih => obtain ⟨e₁⟩ := h.sub; obtain ⟨e₂⟩ := ih; exact ⟨.subtyp_trans e₁ e₂⟩

/-- `Factor.sub`: a factorization is a subtyping, `Factor G S p C → G ⊢ S <: p.C`. -/
theorem Factor.sub {G : Ctx s} {S : Ty s} {p : Path s} {C : Label} (h : Factor G S p C) : Nonempty (Sub G S (.sel p C)) := by
  obtain ⟨S', hu, hS'⟩ := h
  obtain ⟨e₁⟩ := hu.sub
  rcases hS' with rfl | ⟨q, rfl, hq⟩
  · exact ⟨.subtyp_trans e₁ .subtyp_bot⟩
  · obtain ⟨e₂⟩ := hq.sub C; exact ⟨.subtyp_trans e₁ e₂⟩

/-- L3: a replacement `r ↦ r' ⊢ S ⇝ S'` keeps a structural type structural. -/
theorem Repl.structural {r r' : Path s} : ∀ {S S' : Ty s}, Repl r r' S S' → S.Structural → S'.Structural
  | _, _, .rrcd _, _ => trivial
  | _, _, .rand1 h, hS => ⟨Repl.structural h hS.1, hS.2⟩
  | _, _, .rand2 h, hS => ⟨hS.1, Repl.structural h hS.2⟩
  | _, _, .rpath, hS => hS
  | _, _, .rbnd _, _ => trivial
  | _, _, .rall1 _, _ => trivial
  | _, _, .rall2 _, _ => trivial
  | _, _, .rsngl, _ => trivial

/-- L3: from a structural type every `Up` step stays structural. -/
theorem Up.structural {G : Ctx s} {S S' : Ty s} (h : Up G S S') (hS : S.Structural) : S'.Structural := by
  cases h with
  | upper _ _ => exact hS.elim
  | and1 => exact hS.1
  | and2 => exact hS.2
  | replPQ _ _ hp => obtain ⟨rp⟩ := hp; exact Repl.structural rp hS
  | replQP _ _ hp => obtain ⟨rp⟩ := hp; exact Repl.structural rp hS

/-- `not_factor`: no structural type factors through a class type, `S.Structural → ¬ Factor G S p C`. -/
theorem Ty.Structural.not_factor {G : Ctx s} {S : Ty s} {p : Path s} {C : Label} (hS : S.Structural) : ¬ Factor G S p C := by
  rintro ⟨S', hu, hS'⟩
  have hst : S'.Structural := by
    clear hS'
    induction hu with
    | refl => exact hS
    | step h _ ih => exact ih (h.structural hS)
  rcases hS' with rfl | ⟨q, rfl, _⟩ <;> exact hst

/-! ## The class order -/

/-- `T.ClsShape K`: every operand of `T` is structural or a class selection `q.B` with `B ∈ K`, and none
is `⊥`. -/
def Ty.ClsShape (K : List Label) : Ty s → Prop
  | .and T U => T.ClsShape K ∧ U.ClsShape K
  | .sel _ B => B ∈ K
  | .top => True
  | .rcd _ => True
  | .mu _ => True
  | .all _ _ => True
  | .sngl _ => True
  | .bot => False

/-- A type whose operands are all `⊤` or class selections `q.B`, `B ∈ K`, has class shape. -/
theorem Ty.ClsShape.of_ops {K : List Label} : ∀ {T : Ty s}, (∀ X ∈ T.ops, (∃ (q : Path s) (B : Label), X = .sel q B ∧ B ∈ K) ∨ X = .top) → T.ClsShape K
  | .and T U, h => ⟨Ty.ClsShape.of_ops (fun X hX => h X (List.mem_append_left _ hX)),
                    Ty.ClsShape.of_ops (fun X hX => h X (List.mem_append_right _ hX))⟩
  | .top, _ => trivial
  | .bot, h => by rcases h .bot (List.mem_singleton_self _) with ⟨_, _, e, _⟩ | e <;> cases e
  | .rcd _, _ => trivial
  | .sel q B, h => by
      rcases h (.sel q B) (List.mem_singleton_self _) with ⟨_, _, e, hB⟩ | e
      · cases e; exact hB
      · cases e
  | .mu _, _ => trivial
  | .all _ _, _ => trivial
  | .sngl _, _ => trivial

/-- A class body `μ(z. T₀) ∧ Ps` has class shape. -/
theorem ClassBody.shape {K : List Label} {U : Ty s} (h : ClassBody K U) : U.ClsShape K := by
  obtain ⟨T₀, Ps, rfl, hPs⟩ := h
  exact ⟨trivial, Ty.ClsShape.of_ops hPs⟩

/-- A replacement `r ↦ r' ⊢ S ⇝ S'` keeps class shape. -/
theorem Repl.clsShape {K : List Label} {r r' : Path s} : ∀ {S S' : Ty s}, Repl r r' S S' → S.ClsShape K → S'.ClsShape K
  | _, _, .rrcd _, _ => trivial
  | _, _, .rand1 h, hS => ⟨Repl.clsShape h hS.1, hS.2⟩
  | _, _, .rand2 h, hS => ⟨hS.1, Repl.clsShape h hS.2⟩
  | _, _, .rpath, hS => hS
  | _, _, .rbnd _, _ => trivial
  | _, _, .rall1 _, _ => trivial
  | _, _, .rall2 _, _ => trivial
  | _, _, .rsngl, _ => trivial

/-- An operand `Y ∈ ops(S')` of a replaced type `r ↦ r' ⊢ S ⇝ S'` is an operand of `S`, or the
replacement `r ↦ r' ⊢ Y₀ ⇝ Y` of an operand `Y₀ ∈ ops(S)`. -/
theorem Repl.ops_mem {r r' : Path s} : ∀ {S S' : Ty s}, Repl r r' S S' → ∀ {Y : Ty s}, Y ∈ S'.ops →
    Y ∈ S.ops ∨ ∃ Y₀ ∈ S.ops, Nonempty (Repl r r' Y₀ Y)
  | _, _, .rrcd h, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rrcd h⟩⟩
  | _, _, .rand1 (U := U) h, Y, hY => by
      rcases List.mem_append.mp hY with hY | hY
      · rcases Repl.ops_mem h hY with h' | ⟨Y₀, hm, hr⟩
        · exact .inl (List.mem_append_left _ h')
        · exact .inr ⟨Y₀, List.mem_append_left _ hm, hr⟩
      · exact .inl (List.mem_append_right _ hY)
  | _, _, .rand2 (U := U) h, Y, hY => by
      rcases List.mem_append.mp hY with hY | hY
      · exact .inl (List.mem_append_left _ hY)
      · rcases Repl.ops_mem h hY with h' | ⟨Y₀, hm, hr⟩
        · exact .inl (List.mem_append_right _ h')
        · exact .inr ⟨Y₀, List.mem_append_right _ hm, hr⟩
  | _, _, .rpath, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rpath⟩⟩
  | _, _, .rbnd h, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rbnd h⟩⟩
  | _, _, .rall1 h, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rall1 h⟩⟩
  | _, _, .rall2 h, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rall2 h⟩⟩
  | _, _, .rsngl, Y, hY => by
      cases List.mem_singleton.mp hY; exact .inr ⟨_, List.mem_singleton_self _, ⟨.rsngl⟩⟩

/-- CR-Alias at one label: `AliasEq G q q' → ClassReach G (q', C) (p, C) → ClassReach G (q, C) (p, C)`. -/
theorem ClassReach.of_alias {G : Ctx s} {q q' p : Path s} {C : Label} (h : AliasEq G q q') (h' : ClassReach G (q', C) (p, C)) : ClassReach G (q, C) (p, C) :=
  .alias h h'

/-- The `→` half of `class_order`, for a type `X` of class shape: an `Up` path from `X` to `⊥` or to
`q.C` with `q` an alias of `p` starts at an operand `q'.B ∈ ops(X)` with `(q', B)` below `(p, C)`. -/
theorem UpStar.classReach {G : Ctx s} {K : List Label} {p : Path s} {C : Label} (hK : G.ClassDecls K) :
    ∀ {X S' : Ty s}, UpStar G X S' → X.ClsShape K → (S' = .bot ∨ ∃ q, S' = .sel q C ∧ AliasEq G q p) →
      ∃ (q' : Path s) (B : Label), .sel q' B ∈ X.ops ∧ ClassReach G (q', B) (p, C) := by
  intro X S' hu
  induction hu with
  | refl =>
      intro hX hS'
      rcases hS' with rfl | ⟨q, rfl, hq⟩
      · exact hX.elim
      · exact ⟨q, C, List.mem_singleton_self _, .alias hq .refl⟩
  | @step X M S' h _ ih =>
      intro hX hS'
      cases h with
      | and1 =>
          obtain ⟨q', B, hm, hr⟩ := ih hX.1 hS'
          exact ⟨q', B, List.mem_append_left _ hm, hr⟩
      | and2 =>
          obtain ⟨q', B, hm, hr⟩ := ih hX.2 hS'
          exact ⟨q', B, List.mem_append_right _ hm, hr⟩
      | upper hv hm =>
          obtain ⟨hL, hb⟩ := hK _ _ _ _ _ hv hm hX
          subst hL
          obtain ⟨q', B, hm', hr⟩ := ih hb.shape hS'
          exact ⟨_, _, List.mem_singleton_self _, .parent hv hm hm' hr⟩
      | replPQ hv hr hp =>
          obtain ⟨rp⟩ := hp
          obtain ⟨q', B, hm', hr'⟩ := ih (Repl.clsShape rp hX) hS'
          rcases Repl.ops_mem rp hm' with h₀ | ⟨Y₀, hm₀, ⟨r₀⟩⟩
          · exact ⟨q', B, h₀, hr'⟩
          · obtain ⟨bs, rfl, rfl⟩ := Repl.into_sel r₀
            exact ⟨_, B, hm₀, .alias (.step (.pq hv hr ⟨.rsngl⟩) .refl) hr'⟩
      | replQP hv hr hp =>
          obtain ⟨rp⟩ := hp
          obtain ⟨q', B, hm', hr'⟩ := ih (Repl.clsShape rp hX) hS'
          rcases Repl.ops_mem rp hm' with h₀ | ⟨Y₀, hm₀, ⟨r₀⟩⟩
          · exact ⟨q', B, h₀, hr'⟩
          · obtain ⟨bs, rfl, rfl⟩ := Repl.into_sel r₀
            exact ⟨_, B, hm₀, .alias (.step (.qp hv hr ⟨.rsngl⟩) .refl) hr'⟩

/-- An alias equivalence lifts to `Up` steps on a selection: `AliasEq G q q' → UpStar G (q.D) (q'.D)`. -/
theorem AliasEq.upStar {G : Ctx s} {q q' : Path s} (D : Label) (h : AliasEq G q q') : UpStar G (.sel q D) (.sel q' D) := by
  induction h with
  | refl => exact .refl
  | step h _ ih =>
      cases h with
      | pq hv hr hp => obtain ⟨rp⟩ := hp; exact .step (.replPQ hv hr ⟨Repl.sel_of_sngl D rp⟩) ih
      | qp hv hr hp => obtain ⟨rp⟩ := hp; exact .step (.replQP hv hr ⟨Repl.sel_of_sngl D rp⟩) ih
  | back h _ ih =>
      cases h with
      | pq hv hr hp => obtain ⟨rp⟩ := hp; exact .step (.replQP hv hr ⟨(Repl.sel_of_sngl D rp).swap⟩) ih
      | qp hv hr hp => obtain ⟨rp⟩ := hp; exact .step (.replPQ hv hr ⟨(Repl.sel_of_sngl D rp).swap⟩) ih

/-- The `←` half of `class_order`: `ClassReach G (q, D) (p, C) → Factor G (q.D) p C`. -/
theorem ClassReach.factor {G : Ctx s} : ∀ {a b : Path s × Label}, ClassReach G a b → Factor G (.sel a.1 a.2) b.1 b.2 := by
  intro a b h
  induction h with
  | refl => exact ⟨_, .refl, .inr ⟨_, rfl, .refl⟩⟩
  | parent hv hm hm' _ ih =>
      obtain ⟨S', hu, hS'⟩ := ih
      exact ⟨S', .step (.upper hv hm) ((UpStar.of_ops hm').trans hu), hS'⟩
  | @alias q q' D p C ha _ ih =>
      obtain ⟨S', hu, hS'⟩ := ih
      exact ⟨S', (ha.upStar D).trans hu, hS'⟩

/-- `class_order`: under `G.ClassDecls K`, for class labels `D, C ∈ K`, `q.D` factors through `p.C`
exactly when `(q, D)` reaches `(p, C)` in the class order. -/
theorem class_order {G : Ctx s} {K : List Label} {q p : Path s} {D C : Label} (hK : G.ClassDecls K) (hD : D ∈ K) (hC : C ∈ K) :
    Factor G (.sel q D) p C ↔ ClassReach G (q, D) (p, C) := by
  have _ := hC
  constructor
  · rintro ⟨S', hu, hS'⟩
    obtain ⟨q', B, hm, hr⟩ := UpStar.classReach hK hu hD hS'
    cases List.mem_singleton.mp hm
    exact hr
  · exact ClassReach.factor

/-! ## Tests -/

namespace NominalTests
/-- The first class label `K₁`. -/
abbrev K₁ : Label := .typ 0
/-- The second class label `K₂`. -/
abbrev K₂ : Label := .typ 1
/-- A field label `a`. -/
abbrev a : Label := .trm 0
/-- The body of `K₁`, `μ(z. {a : ⊤}) ∧ ⊤`. -/
abbrev B₁ : Ty ([],x) := .and (.mu (.rcd (.trm a .top))) .top
/-- The body of `K₂`, `μ(z. {a : ⊤}) ∧ (x.K₁ ∧ ⊤)`, with the parent `x.K₁`. -/
abbrev B₂ : Ty ([],x) := .and (.mu (.rcd (.trm a .top))) (.and (.sel (.var .here) K₁) .top)
/-- `x :ˢ {K₁ : ⊥..B₁} ∧ {K₂ : ⊥..B₂}`, a self that declares two classes, `K₂` below `K₁`. -/
abbrev G₁ : Ctx ([],x) := Ctx.nil.consSelf (.and (.rcd (.typ K₁ .bot B₁)) (.rcd (.typ K₂ .bot B₂)))
/-- `(x, K₂)` reaches `(x, K₁)` in the class order, by CR-Parent and CR-Refl. -/
theorem cr₁ : ClassReach G₁ (.var .here, K₂) (.var .here, K₁) :=
  .parent (U := B₂) (q' := .var .here) (B := K₁) (IsView.var rfl) (by decide) (by decide) .refl
example : Nonempty (Sub G₁ (.sel (.var .here) K₂) (.sel (.var .here) K₁)) := Factor.sub (ClassReach.factor cr₁)
example : ¬ Factor G₁ (.rcd (.trm a .top)) (.var .here) K₁ := Ty.Structural.not_factor trivial
end NominalTests

end Nominal.Source
