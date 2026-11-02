import Coercions.Nominal.Frontend.Decide
import Coercions.Nominal.Frontend.Ann
import Coercions.Nominal.Source.Nominal
import Coercions.Nominal.Source.Examples
import Coercions.Frontend.Fuel

/-!
# The views of a path on the tank

`views Γ p` lists the types of the path `p` in the context `Γ`, each with its
`HasTy` derivation.  This is plan XI (`plan-11-pdot-frontends.md`), its parts
"Shape" and "Views of a path, in order".  The model is
`lean/Coercions/Paths/Frontend/Look.lean`.

A view comes from one of seven rules.

- V1.  At a variable `x`, its entry `Γ.lookup x`, by `ty_var`.
- V2.  At `q.a`, the type `U` of a field `{a : U}` among the operands of `∧`
  of a view of `q`, by `ty_new_elim` over `ty_sub`.
- V3.  At `q.a`, the singleton `(r.a).type` for a view `r.type` of `q`, by
  `ty_path_elim` with the first view of `r.a`.
- V4.  For a view `r.type` of `p`, each view of `r`, by `ty_sngl`.
- V5.  For a view `q.A` of `p`, the upper bound `U` of each member
  `{A : L..U}` among the views of `q`, by `ty_sub` and `subtyp_sel1`.
- V6.  For a view `μ(z. T)` of `p`, the opened body `T⟨p⟩`, by `ty_rec_elim`.
- V7.  For a view `S₁ ∧ S₂` of `p`, both operands, by `ty_sub` with
  `subtyp_and11` and `subtyp_and12`.

V1 to V3 give the base.  Then the views close in rounds.  Each round applies
V4 to V7 to the views the last round found, and keeps the ones whose type is
new.  The rounds stop when a round finds nothing new.  Out of rounds, the tank
is marked.

A view that V4 brings from `r` is tagged closed.  A closed view gets V6 only.
V4, V5 and V7 are not applied to it again, since the closure of `r` already
holds what they give.  Without the tag, the views of `x12.a` in a chain of
twelve singletons recompute the views of every `xk.a` once per singleton they
meet, which is exponential.  The tag loses a view only when the run of `r` was
cut short by its pending paths.

A path is pending while its views are computed.  A pending path met again on
the same branch has no views.  This is the cut, and it leaves the tank
unmarked.  Each path drawn costs `cost` of the number of paths pending.  A view
`⊥` gives no member, since `fieldsOf` and `boundsOf` find none in `⊥`.

Every answer carries its derivation, so there is no soundness theorem.  The
frame lemmas say that a run that ends with the tank unmarked gives the same
views with more fuel.  Every definition is structural, and the tests at the
end run by `decide +kernel`.

Plan XII (N3) gives each view its certificates (D-17).  A view of `p` at `T`
carries `IsView Γ p T` beside its derivation, and the proof that the
derivation has no seal.  A bound of `q.A` carries a view of `q` with the
member among its operands.  The certificate vocabulary comes first, in
`NominalFrontend`: the seal-free derivations, `HasTy.SealsAt` (every seal is
the evidence of a `ty_sub` at a tagged variable), `NomSub`, `SealAt` and
`NomPath` of the plan's Head, and one lemma per alternative of the search.
-/

namespace NominalFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Tm Ctx HasTy DefTy DefsTy Sub Repl IsView Up UpStar AliasStep AliasEq
  Factor)

/-! ## Seal-free derivations and the seal sites -/

/-- The term is a tagged variable: `x` with `tg.get x ≠ none`. -/
def TaggedAt (tg : Tags s) : Tm s → Prop
  | .path (.var x) => tg.get x ≠ none
  | _ => False

/-- The subtyping is one step of `subtyp_seal`, `G ⊢ p.C <: T` read off `G.selfCls p C = some T`. -/
def Sub.IsSeal : Sub Γ S T → Prop
  | .subtyp_seal _ => True
  | _ => False

mutual
/-- No `subtyp_seal` in the derivation, at any depth.  One clause per rule, a rule with two premises
the conjunction. -/
def HasTy.SealFree : {s : Sig} → {G : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy G t T → Prop
  | _, _, _, _, .ty_var _ => True
  | _, _, _, _, .ty_all_intro d => HasTy.SealFree d
  | _, _, _, _, .ty_all_elim d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .ty_new_intro d => DefsTy.SealFree d
  | _, _, _, _, .ty_new_elim d => HasTy.SealFree d
  | _, _, _, _, .ty_rcd_intro d => HasTy.SealFree d
  | _, _, _, _, .ty_let d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .ty_sngl d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .ty_path_elim d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .ty_rec_intro d => HasTy.SealFree d
  | _, _, _, _, .ty_rec_elim d => HasTy.SealFree d
  | _, _, _, _, .ty_and_intro d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .ty_sub d e => HasTy.SealFree d ∧ Sub.SealFree e
termination_by structural _ _ _ _ d => d
/-- No `subtyp_seal` in the typing of a definition. -/
def DefTy.SealFree : {s : Sig} → {G : Ctx s} → {r : Path s} → {d : Nominal.Source.Def s} → {D : Dec s} → DefTy G r d D → Prop
  | _, _, _, _, _, .ty_def_typ => True
  | _, _, _, _, _, .ty_def_all d => HasTy.SealFree d
  | _, _, _, _, _, .ty_def_new _ d => DefsTy.SealFree d
  | _, _, _, _, _, .ty_def_path d => HasTy.SealFree d
  | _, _, _, _, _, .ty_def_cls _ => True
termination_by structural _ _ _ _ _ d => d
/-- No `subtyp_seal` in the typing of a list of definitions. -/
def DefsTy.SealFree : {s : Sig} → {G : Ctx s} → {r : Path s} → {ds : Nominal.Source.Defs s} → {T : Ty s} → DefsTy G r ds T → Prop
  | _, _, _, _, _, .ty_defs_one d => DefTy.SealFree d
  | _, _, _, _, _, .ty_defs_cons d₁ d₂ _ => DefsTy.SealFree d₁ ∧ DefTy.SealFree d₂
termination_by structural _ _ _ _ _ d => d
/-- No `subtyp_seal` in the subtyping: `subtyp_seal` is `False`, every other rule asks its premises. -/
def Sub.SealFree : {s : Sig} → {G : Ctx s} → {S T : Ty s} → Sub G S T → Prop
  | _, _, _, _, .subtyp_top => True
  | _, _, _, _, .subtyp_bot => True
  | _, _, _, _, .subtyp_refl => True
  | _, _, _, _, .subtyp_trans e₁ e₂ => Sub.SealFree e₁ ∧ Sub.SealFree e₂
  | _, _, _, _, .subtyp_and11 => True
  | _, _, _, _, .subtyp_and12 => True
  | _, _, _, _, .subtyp_and2 e₁ e₂ => Sub.SealFree e₁ ∧ Sub.SealFree e₂
  | _, _, _, _, .subtyp_fld e => Sub.SealFree e
  | _, _, _, _, .subtyp_typ e₁ e₂ => Sub.SealFree e₁ ∧ Sub.SealFree e₂
  | _, _, _, _, .subtyp_sngl_pq d₁ d₂ _ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .subtyp_sngl_qp d₁ d₂ _ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, _, .subtyp_sel2 d => HasTy.SealFree d
  | _, _, _, _, .subtyp_sel1 d => HasTy.SealFree d
  | _, _, _, _, .subtyp_all e₁ e₂ => Sub.SealFree e₁ ∧ Sub.SealFree e₂
  | _, _, _, _, .subtyp_seal _ => False
termination_by structural _ _ _ _ e => e
end
/-- Every seal of a derivation is the last step of a path answer at a tagged variable: a `subtyp_seal`
is allowed only as the evidence of a `ty_sub` whose term is `x` with `tg.get x ≠ none`.  Under a binder
and in a premise of another family the derivation is seal-free. -/
def HasTy.SealsAt (tg : Tags s) : {G : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy G t T → Prop
  | _, _, _, .ty_var _ => True
  | _, _, _, .ty_all_intro d => HasTy.SealFree d
  | _, _, _, .ty_all_elim d₁ d₂ => HasTy.SealsAt tg d₁ ∧ HasTy.SealsAt tg d₂
  | _, _, _, .ty_new_intro d => DefsTy.SealFree d
  | _, _, _, .ty_new_elim d => HasTy.SealsAt tg d
  | _, _, _, .ty_rcd_intro d => HasTy.SealsAt tg d
  | _, _, _, .ty_let d₁ d₂ => HasTy.SealFree d₁ ∧ HasTy.SealFree d₂
  | _, _, _, .ty_sngl d₁ d₂ => HasTy.SealsAt tg d₁ ∧ HasTy.SealsAt tg d₂
  | _, _, _, .ty_path_elim d₁ d₂ => HasTy.SealsAt tg d₁ ∧ HasTy.SealsAt tg d₂
  | _, _, _, .ty_rec_intro d => HasTy.SealsAt tg d
  | _, _, _, .ty_rec_elim d => HasTy.SealsAt tg d
  | _, _, _, .ty_and_intro d₁ d₂ => HasTy.SealsAt tg d₁ ∧ HasTy.SealsAt tg d₂
  | _, t, _, .ty_sub d e => HasTy.SealsAt tg d ∧ (Sub.SealFree e ∨ (Sub.IsSeal e ∧ TaggedAt tg t))
termination_by structural _ _ _ d => d

/-- A seal-free derivation has its seals at tagged variables, for every `tg`. -/
theorem HasTy.sealsAt_of_sealFree (tg : Tags s) : {G : Ctx s} → {t : Tm s} → {T : Ty s} → (d : HasTy G t T) →
    HasTy.SealFree d → HasTy.SealsAt tg d
  | _, _, _, .ty_var _, _ => trivial
  | _, _, _, .ty_all_intro _, h => h
  | _, _, _, .ty_all_elim d₁ d₂, h => ⟨HasTy.sealsAt_of_sealFree tg d₁ h.1, HasTy.sealsAt_of_sealFree tg d₂ h.2⟩
  | _, _, _, .ty_new_intro _, h => h
  | _, _, _, .ty_new_elim d, h => HasTy.sealsAt_of_sealFree tg d h
  | _, _, _, .ty_rcd_intro d, h => HasTy.sealsAt_of_sealFree tg d h
  | _, _, _, .ty_let _ _, h => h
  | _, _, _, .ty_sngl d₁ d₂, h => ⟨HasTy.sealsAt_of_sealFree tg d₁ h.1, HasTy.sealsAt_of_sealFree tg d₂ h.2⟩
  | _, _, _, .ty_path_elim d₁ d₂, h => ⟨HasTy.sealsAt_of_sealFree tg d₁ h.1, HasTy.sealsAt_of_sealFree tg d₂ h.2⟩
  | _, _, _, .ty_rec_intro d, h => HasTy.sealsAt_of_sealFree tg d h
  | _, _, _, .ty_rec_elim d, h => HasTy.sealsAt_of_sealFree tg d h
  | _, _, _, .ty_and_intro d₁ d₂, h => ⟨HasTy.sealsAt_of_sealFree tg d₁ h.1, HasTy.sealsAt_of_sealFree tg d₂ h.2⟩
  | _, _, _, .ty_sub d _, h => ⟨HasTy.sealsAt_of_sealFree tg d h.1, .inl h.2⟩

/-! ## The certificates of the plan's Head -/

/-- `S <: T` into a class type factors (plan XII, the Head): at `T = p.C` with `C ∈ K`, `Factor Γ S p C`. -/
def NomSub (K : List Label) (Γ : Ctx s) (S T : Ty s) : Prop :=
  ∀ p C, T = .sel p C → C ∈ K → Factor Γ S p C
/-- `q` is a tagged instance `x` of `r.K₀`, and `r.K₀` factors through `p.C`. -/
def SealAt (tags : Tags s) (Γ : Ctx s) (q p : Path s) (C : Label) : Prop :=
  ∃ x r K₀, q = .var x ∧ tags.get x = some (r, K₀) ∧ Factor Γ (.sel r K₀) p C
/-- `q : T` into a class type `p.C` with `C ∈ K`: a view of `q` factors through `p.C`, or `q` is a seal
site (`SealAt`). -/
def NomPath (K : List Label) (tags : Tags s) (Γ : Ctx s) (q : Path s) (T : Ty s) : Prop :=
  ∀ p C, T = .sel p C → C ∈ K → (∃ U, IsView Γ q U ∧ Factor Γ U p C) ∨ SealAt tags Γ q p C

/-! ## The lemmas, one per alternative of the search -/

section CertLemmas
variable {K : List Label} {s : Sig} {Γ : Ctx s}
/-- S1 and G1, reflexivity: `T` factors through itself by `AliasEq.refl`. -/
theorem NomSub.refl {T : Ty s} : NomSub K Γ T T := by
  intro p C h _; subst h; exact ⟨_, .refl, .inr ⟨p, rfl, .refl⟩⟩
/-- S3, `⊥ <: T`: `⊥` factors through every class type. -/
theorem NomSub.bot {T : Ty s} : NomSub K Γ .bot T := fun _ _ _ _ => ⟨_, .refl, .inl rfl⟩
/-- `S <: ⊤` (among S2, S4, S5, S6c): no selection, vacuous. -/
theorem NomSub.top {S : Ty s} : NomSub K Γ S .top := fun _ _ h _ => nomatch h
/-- `S <: T₁ ∧ T₂` (among S2, S4, S5, S6c): no selection, vacuous. -/
theorem NomSub.and {S T₁ T₂ : Ty s} : NomSub K Γ S (.and T₁ T₂) := fun _ _ h _ => nomatch h
/-- A record target (among S2, S4, S5, S6c): no selection, vacuous. -/
theorem NomSub.rcd {S : Ty s} {D : Dec s} : NomSub K Γ S (.rcd D) := fun _ _ h _ => nomatch h
/-- A function type target (among S2, S4, S5, S6c): no selection, vacuous. -/
theorem NomSub.all {S S₂ : Ty s} {T₂ : Ty (s,x)} : NomSub K Γ S (.all S₂ T₂) := fun _ _ h _ => nomatch h
/-- A `μ` target (among S2, S4, S5, S6c): no selection, vacuous. -/
theorem NomSub.mu {S : Ty s} {T : Ty (s,x)} : NomSub K Γ S (.mu T) := fun _ _ h _ => nomatch h
/-- S7 at a label outside `K`: nothing to prove. -/
theorem NomSub.of_not_mem {S : Ty s} {q : Path s} {A : Label} (hA : A ∉ K) : NomSub K Γ S (.sel q A) := by
  intro p C h hC; cases h; exact absurd hC hA
/-- S9, one `Up` step before the sub-answer's certificate, Up-And1 and Up-And2 among them. -/
theorem NomSub.up {S M T : Ty s} (hu : Up Γ S M) (h : NomSub K Γ M T) : NomSub K Γ S T := by
  intro p C hT hC; obtain ⟨S', h₁, h₂⟩ := h p C hT hC; exact ⟨S', .step hu h₁, h₂⟩
/-- An `UpStar` chain before the rest, the alias chains of avoidance. -/
theorem NomSub.ofUpStar {S M T : Ty s} (hu : UpStar Γ S M) (h : NomSub K Γ M T) : NomSub K Γ S T := by
  intro p C hT hC; obtain ⟨S', h₁, h₂⟩ := h p C hT hC; exact ⟨S', hu.trans h₁, h₂⟩
/-- S8, `q.A <: T` through the upper bound `U` of a member `{A : L..U}` of a view of `q` (Up-Upper). -/
theorem NomSub.upper {q : Path s} {A : Label} {L U T : Ty s}
    (hv : ∃ V, IsView Γ q V ∧ .rcd (.typ A L U) ∈ V.ops) (h : NomSub K Γ U T) : NomSub K Γ (.sel q A) T := by
  obtain ⟨V, hV, hm⟩ := hv; exact NomSub.up (.upper hV hm) h
/-- S6a, a replacement of `l` by `m` on the left, for a view `m.type` of `l` (Up-ReplPQ). -/
theorem NomSub.replL {l m : Path s} {V S S' T : Ty s} (hv : IsView Γ l (.sngl m)) (hu : HasTy Γ (.path m) V)
    (ρ : Repl l m S S') (h : NomSub K Γ S' T) : NomSub K Γ S T :=
  NomSub.up (.replPQ hv ⟨hu⟩ ⟨ρ⟩) h
/-- S6b, a replacement on the right: the selection's path moves by one alias step (L1 by
`Repl.into_sel`, then AS-QP and AE-Step). -/
theorem NomSub.replR {l m : Path s} {V S T T' : Ty s} (hv : IsView Γ l (.sngl m)) (hu : HasTy Γ (.path m) V)
    (ρ : Repl m l T' T) (h : NomSub K Γ S T') : NomSub K Γ S T := by
  intro p C hT hC
  subst hT
  obtain ⟨bs, rfl, rfl⟩ := Nominal.Source.Repl.into_sel ρ
  obtain ⟨S', h₁, h₂⟩ := h _ C rfl hC
  have ha : AliasStep Γ (m.nomExt bs) (l.nomExt bs) := .qp hv ⟨hu⟩ ⟨.rsngl⟩
  rcases h₂ with h₂ | ⟨q, hq, he⟩
  · exact ⟨S', h₁, .inl h₂⟩
  · exact ⟨S', h₁, .inr ⟨q, hq, he.trans (.step ha .refl)⟩⟩
/-- G4, a view `U` of `q` and `U <: T`. -/
theorem NomPath.ofSub {tg : Tags s} {q : Path s} {U T : Ty s} (hv : IsView Γ q U) (h : NomSub K Γ U T) :
    NomPath K tg Γ q T := fun p C hT hC => .inl ⟨U, hv, h p C hT hC⟩
/-- G1, `T` is a view of `q`. -/
theorem NomPath.ofView {tg : Tags s} {q : Path s} {T : Ty s} (hv : IsView Γ q T) : NomPath K tg Γ q T :=
  NomPath.ofSub hv NomSub.refl
/-- An intersection target (among G2, G3, G5): no selection, vacuous. -/
theorem NomPath.and {tg : Tags s} {q : Path s} {T₁ T₂ : Ty s} : NomPath K tg Γ q (.and T₁ T₂) := fun _ _ h _ => nomatch h
/-- A record target (among G2, G3, G5): no selection, vacuous. -/
theorem NomPath.rcd {tg : Tags s} {q : Path s} {D : Dec s} : NomPath K tg Γ q (.rcd D) := fun _ _ h _ => nomatch h
/-- A `μ` target (among G2, G3, G5): no selection, vacuous. -/
theorem NomPath.mu {tg : Tags s} {q : Path s} {T : Ty (s,x)} : NomPath K tg Γ q (.mu T) := fun _ _ h _ => nomatch h
/-- G6 at a label outside `K`: nothing to prove. -/
theorem NomPath.of_not_mem {tg : Tags s} {q r : Path s} {A : Label} (hA : A ∉ K) : NomPath K tg Γ q (.sel r A) := by
  intro p C h hC; cases h; exact absurd hC hA
/-- G7', the seal at a tagged variable `x` of `r.K₀`, with `r.K₀ <: q.D` certified. -/
theorem NomPath.seal {tg : Tags s} {x : BVar s .var} {r q : Path s} {K₀ D : Label}
    (ht : tg.get x = some (r, K₀)) (h : NomSub K Γ (.sel r K₀) (.sel q D)) : NomPath K tg Γ (.var x) (.sel q D) := by
  intro p C hT hC; exact .inr ⟨x, r, K₀, rfl, ht, h p C hT hC⟩
/-- V5 by IV-Upper: the upper bound of a member of a view of `q`, for a view `q.A` of `p`. -/
theorem IsView.ofBound {p q : Path s} {A : Label} {L U : Ty s} (hp : IsView Γ p (.sel q A))
    (hb : ∃ V, IsView Γ q V ∧ .rcd (.typ A L U) ∈ V.ops) : IsView Γ p U :=
  match hb with
  | ⟨_, hV, hm⟩ => .upper hp hV hm
end CertLemmas

end NominalFrontend

namespace NominalFrontend.Core

open Frontend.Fuel
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Ctx HasTy Sub IsView)

/-- The cost of a path drawn with `k` paths pending. -/
def cost (k : Nat) : Nat := k + 1
theorem costOk : CostOk cost := costOk_succ
/-- The fuel every entry point starts from (decision 14 of plan XI). -/
def defaultFuel : Nat := 2 ^ 15

/-! ## Views and bounds -/

/-- A typing of `p` at `T` read off the context, with its certificates: the view `IsView Γ p T`, no seal. -/
structure Viewed (Γ : Ctx s) (p : Path s) (T : Ty s) where
  d : HasTy Γ (.path p) T
  iv : IsView Γ p T
  sf : HasTy.SealFree d
/-- A type of the path `p`, with its derivation and certificates. -/
abbrev View (Γ : Ctx s) (p : Path s) := (T : Ty s) × Viewed Γ p T
/-- The views of every path, one index down. -/
abbrev Vw (Γ : Ctx s) := (q : Path s) → Fu (List (View Γ q))

/-- A member `{A : lo..hi}` of `q`, with the premise of `subtyp_sel1` and `subtyp_sel2` and its certificates:
a view of `q` with the member among its operands, no seal. -/
structure Bound (Γ : Ctx s) (q : Path s) (A : Label) where
  lo : Ty s
  hi : Ty s
  d : HasTy Γ (.path q) (.rcd (.typ A lo hi))
  iv : ∃ V, IsView Γ q V ∧ .rcd (.typ A lo hi) ∈ V.ops
  sf : HasTy.SealFree d
/-- A field `{a : ty}` among the operands of `T`, with the subtyping that reaches it. -/
structure Field (Γ : Ctx s) (a : Label) (T : Ty s) where
  ty : Ty s
  e : Sub Γ T (.rcd (.trm a ty))
  mem : .rcd (.trm a ty) ∈ T.ops
  sf : Sub.SealFree e
/-- A member `{A : lo..hi}` among the operands of `T`, with the subtyping that reaches it. -/
structure Member (Γ : Ctx s) (A : Label) (T : Ty s) where
  lo : Ty s
  hi : Ty s
  e : Sub Γ T (.rcd (.typ A lo hi))
  mem : .rcd (.typ A lo hi) ∈ T.ops
  sf : Sub.SealFree e

/-- The fields `{a : U}` among the operands of `∧` of `T`, each with the subtyping that reaches it. -/
def fieldsOf (Γ : Ctx s) (a : Label) : (T : Ty s) → List (Field Γ a T)
  | .rcd (.trm b U) => if h : b = a then [by subst h; exact ⟨U, .subtyp_refl, List.mem_singleton_self _, trivial⟩] else []     -- the member
  | .and T₁ T₂ =>
      (fieldsOf Γ a T₁).map (fun e => ⟨e.ty, .subtyp_trans .subtyp_and11 e.e, List.mem_append_left _ e.mem, (by exact ⟨trivial, e.sf⟩)⟩) ++   -- left operand
      (fieldsOf Γ a T₂).map (fun e => ⟨e.ty, .subtyp_trans .subtyp_and12 e.e, List.mem_append_right _ e.mem, (by exact ⟨trivial, e.sf⟩)⟩)     -- right operand
  | _ => []

/-- The type members `{A : L..U}` among the operands of `∧` of `T`, each with its subtyping. -/
def boundsOf (Γ : Ctx s) (A : Label) : (T : Ty s) → List (Member Γ A T)
  | .rcd (.typ B L U) => if h : B = A then [by subst h; exact ⟨L, U, .subtyp_refl, List.mem_singleton_self _, trivial⟩] else []
  | .and T₁ T₂ =>
      (boundsOf Γ A T₁).map (fun e => ⟨e.lo, e.hi, .subtyp_trans .subtyp_and11 e.e, List.mem_append_left _ e.mem, (by exact ⟨trivial, e.sf⟩)⟩) ++
      (boundsOf Γ A T₂).map (fun e => ⟨e.lo, e.hi, .subtyp_trans .subtyp_and12 e.e, List.mem_append_right _ e.mem, (by exact ⟨trivial, e.sf⟩)⟩)
  | _ => []

/-- The members `{A : L..U}` among the views of `q`. -/
def boundsAt {Γ : Ctx s} (vw : Vw Γ) (q : Path s) (A : Label) : Fu (List (Bound Γ q A)) :=
  Fu.bind (vw q) fun vs =>
    Fu.ret (vs.flatMap fun v => (boundsOf Γ A v.1).map fun e => ⟨e.lo, e.hi, .ty_sub v.2.d e.e, ⟨v.1, v.2.iv, e.mem⟩, (by exact ⟨v.2.sf, e.sf⟩)⟩)

/-! ## The rounds -/

/-- The base views of `p`: V1 at a variable, V2 and V3 at a selection. -/
def baseOf {Γ : Ctx s} (vw : Vw Γ) : (p : Path s) → Fu (List (View Γ p))
  | .var x => Fu.ret [⟨Γ.lookup x, .ty_var rfl, .var rfl, trivial⟩]                               -- V1
  | .sel q a => Fu.bind (vw q) (Fu.flatMapL fun v =>
      let v2 : List (View Γ (q.sel a)) :=
        (fieldsOf Γ a v.1).map fun e => ⟨e.ty, .ty_new_elim (.ty_sub v.2.d e.e), .fld v.2.iv e.mem, (by exact ⟨v.2.sf, e.sf⟩)⟩ -- V2
      match v with
      | ⟨.sngl r, d⟩ => Fu.bind (vw (r.sel a)) fun ws =>
          Fu.ret (v2 ++ match ws with
            | [] => []
            | w :: _ => [⟨.sngl (r.sel a), .ty_path_elim d.d w.2.d, .pathElim d.iv w.2.iv, (by exact ⟨d.sf, w.2.sf⟩)⟩]) -- V3
      | _ => Fu.ret v2)

/-- V4 to V7 on one view.  A view tagged `true` came by V4 and gets V6 only. -/
def nextOf {Γ : Ctx s} (vw : Vw Γ) (p : Path s) (v : View Γ p × Bool) : Fu (List (View Γ p × Bool)) :=
  match v with
  | (⟨.sngl r, d⟩, false) => Fu.bind (vw r) fun ws =>
      Fu.ret (ws.map fun w => (⟨w.1, .ty_sngl d.d w.2.d, .sngl d.iv w.2.iv, (by exact ⟨d.sf, w.2.sf⟩)⟩, true))          -- V4
  | (⟨.sel q A, d⟩, false) => Fu.bind (boundsAt vw q A) fun bs =>
      Fu.ret (bs.map fun b => (⟨b.hi, .ty_sub d.d (.subtyp_sel1 b.d), IsView.ofBound d.iv b.iv, (by exact ⟨d.sf, b.sf⟩)⟩, false)) -- V5
  | (⟨.mu T, d⟩, _) => Fu.ret [(⟨T.substPath p, .ty_rec_elim d.d, .unfold d.iv, d.sf⟩, false)]          -- V6
  | (⟨.and T₁ T₂, d⟩, false) =>
      Fu.ret [(⟨T₁, .ty_sub d.d .subtyp_and11, .and1 d.iv, (by exact ⟨d.sf, trivial⟩)⟩, false),
        (⟨T₂, .ty_sub d.d .subtyp_and12, .and2 d.iv, (by exact ⟨d.sf, trivial⟩)⟩, false)]                            -- V7
  | _ => Fu.ret []

/-- The views of a list whose types are neither in `all` nor earlier in the list. -/
def fresh {Γ : Ctx s} {p : Path s} (all : List (View Γ p)) : List (View Γ p × Bool) → List (View Γ p × Bool)
  | [] => []
  | v :: vs => if all.any (fun w => decide (w.1 = v.1.1)) then fresh all vs else v :: fresh (all ++ [v.1]) vs

/-- Rounds until no new view.  `all` holds every view so far, `front` the new ones.  Out of rounds, the tank is marked. -/
def rounds {Γ : Ctx s} (vw : Vw Γ) (p : Path s) :
    Nat → List (View Γ p) → List (View Γ p × Bool) → Fu (List (View Γ p))
  | _, all, [] => Fu.ret all
  | 0, all, _ :: _ => fun t => (all, { t with out := true })
  | k + 1, all, v :: vs => Fu.bind (Fu.flatMapL (nextOf vw p) (v :: vs)) fun ns =>
      let nw := fresh all ns
      rounds vw p k (all ++ nw.map (·.1)) nw

/-- The views of `p`, at index `d`, with the paths pending along the branch.  A pending path has no views. -/
def viewsP (Γ : Ctx s) : Nat → List (Path s) → (p : Path s) → Fu (List (View Γ p))
  | 0, _, _ => fun t => ([], { t with out := true })
  | d + 1, P, p => Fu.bind (draw (cost P.length)) fun
      | false => Fu.ret []
      | true =>
        if p ∈ P then Fu.ret [] else
        Fu.bind (baseOf (viewsP Γ d (p :: P)) p) fun b =>
          let b' := fresh [] (b.map (·, false))
          rounds (viewsP Γ d (p :: P)) p d (b'.map (·.1)) b'
termination_by structural d _ _ => d

/-! ## Entry points -/

/-- The views of `p`, at the tank's own index, with no path pending. -/
def views (Γ : Ctx s) (p : Path s) : Fu (List (View Γ p)) := fun t => viewsP Γ t.left [] p t
/-- The members `{A : L..U}` among the views of `q`, at the tank's own index. -/
def bounds (Γ : Ctx s) (q : Path s) (A : Label) : Fu (List (Bound Γ q A)) :=
  fun t => boundsAt (viewsP Γ t.left []) q A t
/-- The first view of `m`, the "any view" of `ty_def_path`, `ty_path_elim` and replacement. -/
def firstView (Γ : Ctx s) (m : Path s) : Fu (Option (View Γ m)) :=
  Fu.bind (views Γ m) fun ws => Fu.ret ws.head?
/-- A view of `p` equal to `T` (G1), with its certificates. -/
def viewAt (Γ : Ctx s) (p : Path s) (T : Ty s) : Fu (Option (Viewed Γ p T)) :=
  Fu.bind (views Γ p) fun vs => Fu.ret (vs.findSome? fun v => if h : v.1 = T then some (h ▸ v.2) else none)
/-- The singleton views of a list, with their paths and certificates. -/
def sngls {Γ : Ctx s} {p : Path s} (vs : List (View Γ p)) : List ((m : Path s) × Viewed Γ p (.sngl m)) :=
  vs.filterMap fun v => match v with
    | ⟨.sngl m, d⟩ => some ⟨m, d⟩
    | _ => none

/-! ## Generic combinators

These are restated from the Paths front end, which this library does not import. -/

/-- Map an optional answer. -/
def mapO {α β : Type} (c : Fu (Option α)) (f : α → β) : Fu (Option β) :=
  Fu.bind c fun o => Fu.ret (o.map f)
/-- Continue an optional answer, or stop with none. -/
def bindO {α β : Type} (c : Fu (Option α)) (f : α → Fu (Option β)) : Fu (Option β) :=
  Fu.bind c fun
    | none => Fu.ret none
    | some a => f a

/-- A run that marks the tank is framed. -/
theorem mark_framed {β : Type} (a : β) : Framed (fun t : Tank => (a, { t with out := true })) where
  absorbs t ht := by cases t; simp_all
  spends _ := Nat.le_refl _
  shift := by
    intro t r t' h ho _
    simp only [Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
/-- Agreement through `if`. -/
theorem ite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' b b' : Fu α} (ha : Agree a a')
    (hb : Agree b b') : Agree (if p then a else b) (if p then a' else b') := by
  cases hp
  · exact hb
  · exact ha
/-- Agreement through a dependent `if`. -/
theorem dite_agree {α : Type} {p : Prop} [hp : Decidable p] {a a' : p → Fu α} {b b' : ¬p → Fu α}
    (ha : ∀ h, Agree (a h) (a' h)) (hb : ∀ h, Agree (b h) (b' h)) :
    Agree (dite p a b) (dite p a' b') := by
  cases hp with
  | isFalse h => exact hb h
  | isTrue h => exact ha h
/-- A run at the tank's own index is framed when the runs at two indices agree. -/
theorem atLeft_framed {α : Type} {c : Nat → Fu α} (hc : ∀ d d', d ≤ d' → Agree (c d) (c d')) :
    Framed (fun t => c t.left t) where
  absorbs t ht := (hc t.left t.left (Nat.le_refl _)).left.absorbs t ht
  spends t := (hc t.left t.left (Nat.le_refl _)).left.spends t
  shift := by
    intro t r t' h ho j
    exact (hc t.left (t.left + j) (Nat.le_add_right _ _)).sim t r t' h ho j
theorem mapO_framed {α β : Type} {c : Fu (Option α)} (f : α → β) (hc : Framed c) : Framed (mapO c f) :=
  bind_framed hc fun _ => ret_framed _
theorem mapO_agree {α β : Type} {c c' : Fu (Option α)} (f : α → β) (hc : Agree c c') :
    Agree (mapO c f) (mapO c' f) :=
  bind_agree hc fun _ => ret_agree _
theorem bindO_framed {α β : Type} {c : Fu (Option α)} {f : α → Fu (Option β)}
    (hc : Framed c) (hf : ∀ a, Framed (f a)) : Framed (bindO c f) :=
  bind_framed hc fun r => by
    cases r
    · exact ret_framed _
    · exact hf _
theorem bindO_agree {α β : Type} {c c' : Fu (Option α)} {f f' : α → Fu (Option β)}
    (hc : Agree c c') (hf : ∀ a, Agree (f a) (f' a)) : Agree (bindO c f) (bindO c' f') :=
  bind_agree hc fun r => by
    cases r
    · exact ret_agree _
    · exact hf _

/-! ## Frame lemmas of the views -/

section Frames
variable {s : Sig} {Γ : Ctx s} {vw vw' : Vw Γ}
theorem boundsAt_agree (h : ∀ q, Agree (vw q) (vw' q)) (q : Path s) (A : Label) :
    Agree (boundsAt vw q A) (boundsAt vw' q A) :=
  bind_agree (h q) fun _ => ret_agree _
theorem baseOf_agree (h : ∀ q, Agree (vw q) (vw' q)) : ∀ p, Agree (baseOf vw p) (baseOf vw' p)
  | .var _ => ret_agree _
  | .sel q a => bind_agree (h q) (flatMapL_agree fun v => by
      rcases v with ⟨T, d⟩
      cases T <;> first
        | exact ret_agree _
        | exact bind_agree (h _) fun _ => ret_agree _)
theorem nextOf_agree (h : ∀ q, Agree (vw q) (vw' q)) (p : Path s) (v : View Γ p × Bool) :
    Agree (nextOf vw p v) (nextOf vw' p v) := by
  rcases v with ⟨⟨T, d⟩, b⟩
  cases T <;> cases b <;> first
    | exact ret_agree _
    | exact bind_agree (h _) fun _ => ret_agree _
    | exact bind_agree (boundsAt_agree h _ _) fun _ => ret_agree _
theorem rounds_framed (h : ∀ q, Framed (vw q)) (p : Path s) :
    ∀ k all front, Framed (rounds vw p k all front)
  | _, all, [] => by simp only [rounds]; exact ret_framed _
  | 0, all, v :: vs => by simp only [rounds]; exact mark_framed _
  | k + 1, all, v :: vs => by
      simp only [rounds]
      exact bind_framed (flatMapL_framed (fun w => (nextOf_agree (fun q => Agree.refl (h q)) p w).left) _)
        fun _ => rounds_framed h p k _ _
theorem rounds_agree (h : ∀ q, Agree (vw q) (vw' q)) (p : Path s) :
    ∀ k k', k ≤ k' → ∀ all front, Agree (rounds vw p k all front) (rounds vw' p k' all front)
  | _, _, _, all, [] => by simp only [rounds]; exact ret_agree _
  | 0, k', _, all, v :: vs => by
      refine ⟨?_, ?_, ?_⟩
      · exact mark_framed _
      · exact rounds_framed (fun q => (h q).right) p k' all (v :: vs)
      · intro t r t' e ho _
        simp only [rounds, Prod.mk.injEq] at e
        rw [← e.2] at ho; simp at ho
  | k + 1, k', hk, all, v :: vs => by
      obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
      simp only [rounds]
      exact bind_agree (flatMapL_agree (nextOf_agree h p) _) fun _ =>
        rounds_agree h p k j (by omega) _ _

end Frames
theorem viewsP_framed {s : Sig} (Γ : Ctx s) : ∀ d (P : List (Path s)) (p : Path s), Framed (viewsP Γ d P p)
  | 0, P, p => mark_framed _
  | d + 1, P, p => by
    have ih := fun q => viewsP_framed Γ d (p :: P) q
    simp only [viewsP]
    apply bind_framed (draw_framed _)
    intro ok
    cases ok
    · exact ret_framed _
    · exact (ite_agree (ret_agree _) (bind_agree (baseOf_agree (fun q => Agree.refl (ih q)) p) fun _ =>
        Agree.refl (rounds_framed ih p d _ _))).left
theorem viewsP_agree {s : Sig} (Γ : Ctx s) :
    ∀ d d', d ≤ d' → ∀ (P : List (Path s)) (p : Path s), Agree (viewsP Γ d P p) (viewsP Γ d' P p)
  | 0, d', _, P, p => by
    refine ⟨mark_framed _, viewsP_framed Γ d' P p, ?_⟩
    intro t r t' h ho _
    simp only [viewsP, Prod.mk.injEq] at h
    rw [← h.2] at ho
    simp at ho
  | d + 1, d', hd, P, p => by
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    have ih := viewsP_agree Γ d e (by omega) (p :: P)
    simp only [viewsP]
    apply bind_agree (draw_agree _)
    intro ok
    cases ok
    · exact ret_agree _
    · apply ite_agree (ret_agree _)
      exact bind_agree (baseOf_agree ih p) fun _ => rounds_agree ih p d e (by omega) _ _
theorem views_framed {s : Sig} (Γ : Ctx s) (p : Path s) : Framed (views Γ p) :=
  atLeft_framed fun d d' hd => viewsP_agree Γ d d' hd [] p
theorem bounds_framed {s : Sig} (Γ : Ctx s) (q : Path s) (A : Label) : Framed (bounds Γ q A) :=
  atLeft_framed fun d d' hd => boundsAt_agree (viewsP_agree Γ d d' hd []) q A
theorem firstView_framed {s : Sig} (Γ : Ctx s) (m : Path s) : Framed (firstView Γ m) :=
  bind_framed (views_framed Γ m) fun _ => ret_framed _
theorem viewAt_framed {s : Sig} (Γ : Ctx s) (p : Path s) (T : Ty s) : Framed (viewAt Γ p T) :=
  bind_framed (views_framed Γ p) fun _ => ret_framed _

/-! ## Tests

V2, V3 and V4 on E9.  The cut on the cyclic path of E13, which ends unmarked.
V5 on a variable at a type selection.  A member of `⊥`, which is none and
unmarked.  And `bounds`. -/

section Tests
open Nominal.Source (e9_G e9_x e9_a e9_b e13_T e13_a)
/-- `x : μ(z. {a : z.a.type})`, the type of E13's literal. -/
abbrev lk13G : Ctx ([],x) := Ctx.nil.cons (.mu e13_T)
abbrev lkA : Label := .typ 0
abbrev lka : Label := .trm 0
/-- `x : {A : ⊥..{a : ⊤}}`, `y : x.A`. -/
abbrev lkSelG : Ctx (([],x),x) :=
  (Ctx.nil.cons (.rcd (.typ lkA .bot (.rcd (.trm lka .top))))).cons (.sel (.var .here) lkA)
/-- `x : ⊥`. -/
abbrev lkBotG : Ctx ([],x) := Ctx.nil.cons .bot
/-- The types of the views a run gave. -/
def tys {Γ : Ctx s} {p : Path s} (r : List (View Γ p) × Tank) : List (Ty s) := r.1.map (·.1)

example : (tys (views e9_G (e9_x.sel e9_a) ⟨defaultFuel, false⟩)).head? = some (.sngl e9_x) := by decide +kernel
example : (views e9_G (e9_x.sel e9_a) ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : (tys (views e9_G ((e9_x.sel e9_a).sel e9_b) ⟨defaultFuel, false⟩)).contains (.sngl (e9_x.sel e9_b)) = true := by decide +kernel
example : (tys (views e9_G ((e9_x.sel e9_a).sel e9_b) ⟨defaultFuel, false⟩)).contains .top = true := by decide +kernel
example : (tys (views lk13G ((Path.var .here).sel e13_a) ⟨defaultFuel, false⟩)) = [.sngl ((Path.var .here).sel e13_a)] := by decide +kernel
example : (views lk13G ((Path.var .here).sel e13_a) ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : (tys (views lkSelG (.var .here) ⟨defaultFuel, false⟩)) = [.sel (.var (.there .here)) lkA, .rcd (.trm lka .top)] := by decide +kernel
example : (tys (views lkBotG ((Path.var .here).sel lka) ⟨defaultFuel, false⟩)) = [] := by decide +kernel
example : (views lkBotG ((Path.var .here).sel lka) ⟨defaultFuel, false⟩).2.out = false := by decide +kernel
example : ((bounds lkSelG (.var (.there .here)) lkA ⟨defaultFuel, false⟩).1.map (fun b => (b.lo, b.hi))) = [(.bot, .rcd (.trm lka .top))] := by decide +kernel
/-- Seal-freedom of `ty_sub` is the conjunction of its premises'. -/
example (d : HasTy G t T) (e : Sub G T U) : HasTy.SealFree (.ty_sub d e) = (HasTy.SealFree d ∧ Sub.SealFree e) := rfl
/-- A seal is never seal-free. -/
example (G : Ctx s) (p : Path s) (C : Label) (T : Ty s) (h : G.selfCls p C = some T) : Sub.SealFree (.subtyp_seal h) = False := rfl
end Tests
end NominalFrontend.Core
