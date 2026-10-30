import Coercions.Nominal.Source.Typing

/-!
# Derived lemmas and rules of the typing

Inversion lemmas, and the derived rules that the examples use.

The inversion of a value typing runs through `ty_sub`, the only rule other than the introduction
that can conclude a typing of a value.  So `HasTy.val_new_inv` and `HasTy.val_lam_inv` are proved by
recursion on the derivation, with the term index generalized to an equation.  The inversions of a
definition typing read the one rule that fits the definition: a definition typing has no
subsumption.  So a path field is declared at its singleton and nothing else (`DefTy.path_decl`), a
function field at a `∀` (`DefTy.lam_decl`), an object field at its own `μ` (`DefTy.new_decl`), and a
type member at equal bounds (`DefTy.typ_decl`), and a class definition at `{C : ⊥..T}`
(`DefTy.cls_decl`).  `DefsTy.cons_inv` reads the last definition's declaration off the type of a list
of definitions.  Every type a list of definitions is typed at is tight in the sense of `Ty.tightC`
(`DefsTy.tightC`), since `ty_def_new` asks it of each nested literal.

The derived rules are `def`s from the constructors: `HasTy.sub'`, `HasTy.andL`, `HasTy.andR`,
`HasTy.fieldOfRec` and `Sub.andProj`.

The last section shows that plan X's pDOT is the class-free restriction of pDOT-C
(`HasTy.plain_of_clsFree`).
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Inversion of value typings -/

/-- The inversion of an object typing, with the term generalized: every typing of `ν(z : T) ds`
comes from `ty_new_intro`, below some `ty_sub`. -/
theorem HasTy.val_new_inv_of_eq : ∀ {G : Ctx s} {t : Tm s} {U : Ty s}, HasTy G t U →
    ∀ (T : Ty (s,x)) (ds : Defs (s,x)), t = .val (.new T ds) →
      Nonempty (DefsTy (G.consSelf T) (.var .here) ds T)
  | _, _, _, .ty_new_intro d, _, _, e => by
      cases e
      exact ⟨d⟩
  | _, _, _, .ty_sub h _, T, ds, e => HasTy.val_new_inv_of_eq h T ds e
  | _, _, _, .ty_var _, _, _, e => nomatch e
  | _, _, _, .ty_all_intro _, _, _, e => nomatch e
  | _, _, _, .ty_all_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_new_elim _, _, _, e => nomatch e
  | _, _, _, .ty_rcd_intro _, _, _, e => nomatch e
  | _, _, _, .ty_let _ _, _, _, e => nomatch e
  | _, _, _, .ty_sngl _ _, _, _, e => nomatch e
  | _, _, _, .ty_path_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_rec_intro _, _, _, e => nomatch e
  | _, _, _, .ty_rec_elim _, _, _, e => nomatch e
  | _, _, _, .ty_and_intro _ _, _, _, e => nomatch e

/-- A typed object literal `ν(z : T) ds` has its definitions typed at its annotation, in the context
extended by its self `z :ˢ T`. -/
theorem HasTy.val_new_inv : HasTy G (.val (.new T ds)) U → Nonempty (DefsTy (G.consSelf T) (.var .here) ds T) :=
  fun h => h.val_new_inv_of_eq T ds rfl

/-- The inversion of a function typing, with the term generalized: every typing of `λ(z : S) t`
comes from `ty_all_intro`, below some `ty_sub`. -/
theorem HasTy.val_lam_inv_of_eq : ∀ {G : Ctx s} {t : Tm s} {U : Ty s}, HasTy G t U →
    ∀ (S : Ty s) (t₀ : Tm (s,x)), t = .val (.lam S t₀) → ∃ U₀, Nonempty (HasTy (G.cons S) t₀ U₀)
  | _, _, _, .ty_all_intro (U := U₀) h, _, _, e => by
      cases e
      exact ⟨U₀, ⟨h⟩⟩
  | _, _, _, .ty_sub h _, S, t₀, e => HasTy.val_lam_inv_of_eq h S t₀ e
  | _, _, _, .ty_var _, _, _, e => nomatch e
  | _, _, _, .ty_all_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_new_intro _, _, _, e => nomatch e
  | _, _, _, .ty_new_elim _, _, _, e => nomatch e
  | _, _, _, .ty_rcd_intro _, _, _, e => nomatch e
  | _, _, _, .ty_let _ _, _, _, e => nomatch e
  | _, _, _, .ty_sngl _ _, _, _, e => nomatch e
  | _, _, _, .ty_path_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_rec_intro _, _, _, e => nomatch e
  | _, _, _, .ty_rec_elim _, _, _, e => nomatch e
  | _, _, _, .ty_and_intro _ _, _, _, e => nomatch e

/-- A typed function `λ(z : S) t` has its body typed in the context extended by `z : S`. -/
theorem HasTy.val_lam_inv : HasTy G (.val (.lam S t)) U → ∃ U₀, Nonempty (HasTy (G.cons S) t U₀) :=
  fun h => h.val_lam_inv_of_eq S t rfl

/-! ## Inversion of definition typings -/

/-- A path field `{b = defp q}` is declared at `{b : q.type}` and at nothing else (`ty_def_path`). -/
theorem DefTy.path_decl : DefTy G r (.trm b (.defp q)) D → D = .trm b (.sngl q)
  | .ty_def_path _ => rfl

/-- The premise of `ty_def_path`: the path of a path field is typed. -/
theorem DefTy.path_inv : DefTy G r (.trm b (.defp q)) D → ∃ T, Nonempty (HasTy G (.path q) T)
  | .ty_def_path (T := T) h => ⟨T, ⟨h⟩⟩

/-- A function field is declared at a `∀` (`ty_def_all`). -/
theorem DefTy.lam_decl : DefTy G r (.trm b (.defv (.lam T t))) D → ∃ U V, D = .trm b (.all U V)
  | .ty_def_all (U := U) (V := V) _ => ⟨U, V, rfl⟩

/-- An object field `{b = defv ν(z : T) ds}` is declared at `{b : μ(z. T)}` (`ty_def_new`). -/
theorem DefTy.new_decl : DefTy G r (.trm b (.defv (.new T ds))) D → D = .trm b (.mu T)
  | .ty_def_new _ _ => rfl

/-- A type member `{A = T}` is declared at `{A : T..T}` (`ty_def_typ`). -/
theorem DefTy.typ_decl : DefTy G r (.typ A T) D → D = .typ A T T
  | .ty_def_typ => rfl

/-- A class definition `{class C = T}` is declared at `{C : ⊥..T}` (`ty_def_cls`). -/
theorem DefTy.cls_decl : DefTy G r (.cls C T) D → D = .typ C .bot T
  | .ty_def_cls _ => rfl

/-- The type of a non-empty list of definitions: `{D}` for one definition, `T' ∧ {D}` otherwise, with
`D` the declaration of the last definition. -/
theorem DefsTy.cons_inv : DefsTy G r (.cons ds d) T →
    (ds = .nil ∧ ∃ D, T = .rcd D ∧ Nonempty (DefTy G r d D)) ∨
    ∃ T' D, T = .and T' (.rcd D) ∧ Nonempty (DefTy G r d D) ∧ Nonempty (DefsTy G r ds T')
  | .ty_defs_one hd => .inl ⟨rfl, _, rfl, ⟨hd⟩⟩
  | .ty_defs_cons hds hd _ => .inr ⟨_, _, rfl, ⟨hd⟩, ⟨hds⟩⟩

/-! ## Tight bounds of a typed list of definitions -/

/-- Every declaration a definition is typed at is tight in the sense of `tightC`.  `ty_def_typ`
declares equal bounds, `ty_def_new` asks `tightC` of the nested annotation, and `ty_def_cls` declares
`{C : ⊥..T}` with `T` a class body. -/
theorem DefTy.tightC : DefTy G r d D → D.tightC = true
  | .ty_def_typ => by simp [Dec.tightC]
  | .ty_def_all _ => rfl
  | .ty_def_new h _ => h
  | .ty_def_path _ => rfl
  | .ty_def_cls h => by simp [Dec.tightC, h]

/-- Every type a list of definitions is typed at is tight in the sense of `tightC`. -/
theorem DefsTy.tightC : DefsTy G r ds T → T.tightC = true
  | .ty_defs_one hd => hd.tightC
  | .ty_defs_cons hds hd _ => by
      show (_ && Dec.tightC _) = true
      rw [hds.tightC, hd.tightC]
      rfl

/-- The annotation of a typed literal is tight in the sense of `tightC`. -/
theorem DefsTy.tightC_at_self {G : Ctx s} : DefsTy (G.consSelf T) (.var .here) ds T → T.tightC = true :=
  DefsTy.tightC

/-! ## Derived rules -/

/-- Two subsumptions in a row, as one `ty_sub` by `subtyp_trans`. -/
def HasTy.sub' (h : HasTy G t T) (h₁ : Sub G T U) (h₂ : Sub G U V) : HasTy G t V :=
  .ty_sub h (.subtyp_trans h₁ h₂)

/-- A path typed at `T ∧ U` is typed at `T`. -/
def HasTy.andL (h : HasTy G (.path p) (.and T U)) : HasTy G (.path p) T :=
  .ty_sub h .subtyp_and11

/-- A path typed at `T ∧ U` is typed at `U`. -/
def HasTy.andR (h : HasTy G (.path p) (.and T U)) : HasTy G (.path p) U :=
  .ty_sub h .subtyp_and12

/-- A field of a path typed at `μ(z. T)`: `ty_rec_elim`, then `ty_sub` from `T⟨p⟩` to the record
`{a : U}`, then `ty_new_elim`. -/
def HasTy.fieldOfRec (h : HasTy G (.path p) (.mu T)) (hs : Sub G (T.substPath p) (.rcd (.trm a U))) :
    HasTy G (.path (p.sel a)) U :=
  .ty_new_elim (.ty_sub (.ty_rec_elim h) hs)

/-- The `n`-th component of a left-nested intersection, counted from the right, so that
`((T₁ ∧ T₂) ∧ T₃).andComp 0 = T₃`, `… 1 = T₂` and `… 2 = T₁`.  A type that is not an intersection
is its own only component. -/
def Ty.andComp : Ty s → Nat → Ty s
  | .and _ U, 0 => U                             -- (T ∧ U).andComp 0 = U
  | .and T _, n + 1 => T.andComp n               -- (T ∧ U).andComp (n+1) = T.andComp n
  | .top, _ => .top                              -- ⊤.andComp n = ⊤
  | .bot, _ => .bot                              -- ⊥.andComp n = ⊥
  | .rcd D, _ => .rcd D                          -- {D}.andComp n = {D}
  | .sel p A, _ => .sel p A                      -- (p.A).andComp n = p.A
  | .mu T, _ => .mu T                            -- (μ(z. T)).andComp n = μ(z. T)
  | .all S T, _ => .all S T                      -- (∀(z : S) T).andComp n = ∀(z : S) T
  | .sngl p, _ => .sngl p                        -- (p.type).andComp n = p.type

/-- A left-nested intersection is a subtype of each of its components, by `subtyp_and12` at the
component and `subtyp_and11` for each intersection to its right. -/
def Sub.andProj {G : Ctx s} : (T : Ty s) → (n : Nat) → Sub G T (T.andComp n)
  | .and _ _, 0 => .subtyp_and12
  | .and T _, n + 1 => .subtyp_trans .subtyp_and11 (Sub.andProj T n)
  | .top, _ => .subtyp_refl
  | .bot, _ => .subtyp_refl
  | .rcd _, _ => .subtyp_refl
  | .sel _ _, _ => .subtyp_refl
  | .mu _, _ => .subtyp_refl
  | .all _ _, _ => .subtyp_refl
  | .sngl _, _ => .subtyp_refl

/-! ## The class-free restriction (plan XII)

Plan X's pDOT is the class-free restriction of pDOT-C.  In a context whose self types declare no
class (`Ctx.clsFree`), a term with no class definition (`Tm.clsFree`) has only derivations that use
neither `ty_def_cls` nor `subtyp_seal` (`HasTy.plain_of_clsFree`, `Sub.plain_of_clsFree`).  A self
binder enters the context only at `ty_new_intro`, at the type of its definitions, and that type is
class-free when the definitions are (`DefsTy.clsFree_ty`).  `subtyp_seal` is ruled out by
`Ctx.selfCls_none_of_classFree`.
-/

mutual
/-- `t` holds no class definition `{class C = T}`, at any depth of nested literals and lambdas. -/
def Tm.clsFree : Tm s → Bool
  | .val v => v.clsFree
  | .app _ _ => true
  | .lett t u => t.clsFree && u.clsFree
  | .path _ => true
/-- `ν(z : T) ds` is class-free when `ds` is, `λ(z : T) t` when `t` is. -/
def Val.clsFree : Val s → Bool
  | .new _ ds => ds.clsFree
  | .lam _ t => t.clsFree
/-- `{A = T}` is class-free, `{a = rhs}` when `rhs` is, and `{class C = T}` is not. -/
def Def.clsFree : Def s → Bool
  | .typ _ _ => true
  | .trm _ r => r.clsFree
  | .cls _ _ => false
/-- Every definition of the list is class-free. -/
def Defs.clsFree : Defs s → Bool
  | .nil => true
  | .cons ds d => ds.clsFree && d.clsFree
/-- A path right side is class-free, a value one when the value is. -/
def Rhs.clsFree : Rhs s → Bool
  | .defp _ => true
  | .defv v => v.clsFree
end

mutual
/-- A substitution of paths keeps class-freedom: it substitutes no definition. -/
theorem Tm.clsFree_subst : ∀ (t : Tm s₁) (σ : PathSubst s₁ s₂), (t.subst σ).clsFree = t.clsFree
  | .val v, σ => Val.clsFree_subst v σ
  | .app _ _, _ => rfl
  | .lett t u, σ => by simp only [Tm.subst, Tm.clsFree, Tm.clsFree_subst t σ, Tm.clsFree_subst u σ.lift]
  | .path _, _ => rfl
theorem Val.clsFree_subst : ∀ (v : Val s₁) (σ : PathSubst s₁ s₂), (v.subst σ).clsFree = v.clsFree
  | .new _ ds, σ => Defs.clsFree_subst ds σ.lift
  | .lam _ t, σ => Tm.clsFree_subst t σ.lift
theorem Def.clsFree_subst : ∀ (d : Def s₁) (σ : PathSubst s₁ s₂), (d.subst σ).clsFree = d.clsFree
  | .typ _ _, _ => rfl
  | .trm _ r, σ => Rhs.clsFree_subst r σ
  | .cls _ _, _ => rfl
theorem Defs.clsFree_subst : ∀ (ds : Defs s₁) (σ : PathSubst s₁ s₂), (ds.subst σ).clsFree = ds.clsFree
  | .nil, _ => rfl
  | .cons ds d, σ => by simp only [Defs.subst, Defs.clsFree, Defs.clsFree_subst ds σ, Def.clsFree_subst d σ]
theorem Rhs.clsFree_subst : ∀ (r : Rhs s₁) (σ : PathSubst s₁ s₂), (r.subst σ).clsFree = r.clsFree
  | .defp _, _ => rfl
  | .defv v, σ => Val.clsFree_subst v σ
end

mutual
/-- A class-free definition is typed at a class-free declaration.  `{A : T..T}` is class-free since `⊥`
is no class body, and `ty_def_new` reads the nested literal's type. -/
theorem DefTy.clsFree_dec : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s}, DefTy G r d D → d.clsFree = true → D.clsFree = true
  | _, _, _, _, .ty_def_typ (T := T), _ => by
      cases T <;> simp [Dec.clsFree, Ty.clsBody]
  | _, _, _, _, .ty_def_all _, _ => rfl
  | _, r, _, _, .ty_def_new (b := b) (T := T) (ds := ds) _ dds, h => by
      have h' : (ds.substPath (r.sel b)).clsFree = true := by
        rw [Defs.substPath, Defs.clsFree_subst]; exact h
      have := DefsTy.clsFree_ty dds h'
      rw [Ty.substPath, Ty.clsFree_subst] at this
      exact this
  | _, _, _, _, .ty_def_path _, _ => rfl
  | _, _, _, _, .ty_def_cls _, h => nomatch h
/-- A class-free list of definitions is typed at a class-free type. -/
theorem DefsTy.clsFree_ty : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s}, DefsTy G r ds T → ds.clsFree = true → T.clsFree = true
  | _, _, _, _, .ty_defs_one dd, h => by
      simp only [Defs.clsFree, Bool.true_and] at h
      exact DefTy.clsFree_dec dd h
  | _, _, _, _, .ty_defs_cons dds dd _, h => by
      simp only [Defs.clsFree, Bool.and_eq_true] at h
      simp only [Ty.clsFree, Bool.and_eq_true]
      exact ⟨DefsTy.clsFree_ty dds h.1, DefTy.clsFree_dec dd h.2⟩
end

mutual
/-- `d.Plain`: the derivation `d` uses neither `ty_def_cls` nor `subtyp_seal`, at any depth.  One
clause per rule: `True` at a rule with no derivation premise, the conjunction of the premises'
`Plain` otherwise (a `Repl` premise is not read), `False` at `ty_def_cls` and `subtyp_seal`. -/
def HasTy.Plain : {G : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy G t T → Prop
  | _, _, _, .ty_var _ => True
  | _, _, _, .ty_all_intro d => d.Plain
  | _, _, _, .ty_all_elim d₁ d₂ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .ty_new_intro d => d.Plain
  | _, _, _, .ty_new_elim d => d.Plain
  | _, _, _, .ty_rcd_intro d => d.Plain
  | _, _, _, .ty_let d₁ d₂ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .ty_sngl d₁ d₂ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .ty_path_elim d₁ d₂ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .ty_rec_intro d => d.Plain
  | _, _, _, .ty_rec_elim d => d.Plain
  | _, _, _, .ty_and_intro d₁ d₂ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .ty_sub d e => d.Plain ∧ e.Plain
/-- `Plain` of a definition typing, as `HasTy.Plain`. -/
def DefTy.Plain : {G : Ctx s} → {r : Path s} → {d : Def s} → {D : Dec s} → DefTy G r d D → Prop
  | _, _, _, _, .ty_def_typ => True
  | _, _, _, _, .ty_def_all d => d.Plain
  | _, _, _, _, .ty_def_new _ d => d.Plain
  | _, _, _, _, .ty_def_path d => d.Plain
  | _, _, _, _, .ty_def_cls _ => False
/-- `Plain` of a typing of a list of definitions, as `HasTy.Plain`. -/
def DefsTy.Plain : {G : Ctx s} → {r : Path s} → {ds : Defs s} → {T : Ty s} → DefsTy G r ds T → Prop
  | _, _, _, _, .ty_defs_one d => d.Plain
  | _, _, _, _, .ty_defs_cons d₁ d₂ _ => d₁.Plain ∧ d₂.Plain
/-- `Plain` of a subtyping, as `HasTy.Plain`. -/
def Sub.Plain : {G : Ctx s} → {S T : Ty s} → Sub G S T → Prop
  | _, _, _, .subtyp_top => True
  | _, _, _, .subtyp_bot => True
  | _, _, _, .subtyp_refl => True
  | _, _, _, .subtyp_trans e₁ e₂ => e₁.Plain ∧ e₂.Plain
  | _, _, _, .subtyp_and11 => True
  | _, _, _, .subtyp_and12 => True
  | _, _, _, .subtyp_and2 e₁ e₂ => e₁.Plain ∧ e₂.Plain
  | _, _, _, .subtyp_fld e => e.Plain
  | _, _, _, .subtyp_typ e₁ e₂ => e₁.Plain ∧ e₂.Plain
  | _, _, _, .subtyp_sngl_pq d₁ d₂ _ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .subtyp_sngl_qp d₁ d₂ _ => d₁.Plain ∧ d₂.Plain
  | _, _, _, .subtyp_sel2 d => d.Plain
  | _, _, _, .subtyp_sel1 d => d.Plain
  | _, _, _, .subtyp_all e₁ e₂ => e₁.Plain ∧ e₂.Plain
  | _, _, _, .subtyp_seal _ => False
end

mutual
/-- In a class-free context, every typing of a class-free term is plain: it uses neither
`ty_def_cls` nor `subtyp_seal`.  So plan X's pDOT is the class-free restriction of pDOT-C. -/
theorem HasTy.plain_of_clsFree : ∀ {G : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy G t T), G.clsFree = true → t.clsFree = true → d.Plain
  | _, _, _, .ty_var _, _, _ => trivial
  | _, _, _, .ty_all_intro d, hG, ht => HasTy.plain_of_clsFree d hG ht
  | _, _, _, .ty_all_elim d₁ d₂, hG, _ => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .ty_new_intro d, hG, ht => by
      have hT := DefsTy.clsFree_ty d ht
      exact DefsTy.plain_of_clsFree d (by simp only [Ctx.clsFree, hG, hT, Bool.and_self]) ht
  | _, _, _, .ty_new_elim d, hG, _ => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .ty_rcd_intro d, hG, _ => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .ty_let d₁ d₂, hG, ht => by
      simp only [Tm.clsFree, Bool.and_eq_true] at ht
      exact ⟨HasTy.plain_of_clsFree d₁ hG ht.1, HasTy.plain_of_clsFree d₂ hG ht.2⟩
  | _, _, _, .ty_sngl d₁ d₂, hG, _ => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .ty_path_elim d₁ d₂, hG, _ => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .ty_rec_intro d, hG, _ => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .ty_rec_elim d, hG, _ => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .ty_and_intro d₁ d₂, hG, _ => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .ty_sub d e, hG, ht => ⟨HasTy.plain_of_clsFree d hG ht, Sub.plain_of_clsFree e hG⟩
/-- In a class-free context, every typing of a class-free definition is plain. -/
theorem DefTy.plain_of_clsFree : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D), G.clsFree = true → d.clsFree = true → dd.Plain
  | _, _, _, _, .ty_def_typ, _, _ => trivial
  | _, _, _, _, .ty_def_all d, hG, h => HasTy.plain_of_clsFree d hG h
  | _, r, _, _, .ty_def_new (b := b) (ds := ds) _ d, hG, h => by
      have h' : (ds.substPath (r.sel b)).clsFree = true := by
        rw [Defs.substPath, Defs.clsFree_subst]; exact h
      exact DefsTy.plain_of_clsFree d hG h'
  | _, _, _, _, .ty_def_path d, hG, _ => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, _, .ty_def_cls _, _, h => nomatch h
/-- In a class-free context, every typing of a class-free list of definitions is plain. -/
theorem DefsTy.plain_of_clsFree : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T), G.clsFree = true → ds.clsFree = true → d.Plain
  | _, _, _, _, .ty_defs_one d, hG, h => by
      simp only [Defs.clsFree, Bool.true_and] at h
      exact DefTy.plain_of_clsFree d hG h
  | _, _, _, _, .ty_defs_cons d₁ d₂ _, hG, h => by
      simp only [Defs.clsFree, Bool.and_eq_true] at h
      exact ⟨DefsTy.plain_of_clsFree d₁ hG h.1, DefTy.plain_of_clsFree d₂ hG h.2⟩
/-- In a class-free context, every subtyping is plain: `subtyp_seal` reads `G.selfCls p C = some T`,
which `Ctx.selfCls_none_of_classFree` denies. -/
theorem Sub.plain_of_clsFree : ∀ {G : Ctx s} {S T : Ty s} (e : Sub G S T), G.clsFree = true → e.Plain
  | _, _, _, .subtyp_top, _ => trivial
  | _, _, _, .subtyp_bot, _ => trivial
  | _, _, _, .subtyp_refl, _ => trivial
  | _, _, _, .subtyp_trans e₁ e₂, hG => ⟨Sub.plain_of_clsFree e₁ hG, Sub.plain_of_clsFree e₂ hG⟩
  | _, _, _, .subtyp_and11, _ => trivial
  | _, _, _, .subtyp_and12, _ => trivial
  | _, _, _, .subtyp_and2 e₁ e₂, hG => ⟨Sub.plain_of_clsFree e₁ hG, Sub.plain_of_clsFree e₂ hG⟩
  | _, _, _, .subtyp_fld e, hG => Sub.plain_of_clsFree e hG
  | _, _, _, .subtyp_typ e₁ e₂, hG => ⟨Sub.plain_of_clsFree e₁ hG, Sub.plain_of_clsFree e₂ hG⟩
  | _, _, _, .subtyp_sngl_pq d₁ d₂ _, hG => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .subtyp_sngl_qp d₁ d₂ _, hG => ⟨HasTy.plain_of_clsFree d₁ hG rfl, HasTy.plain_of_clsFree d₂ hG rfl⟩
  | _, _, _, .subtyp_sel2 d, hG => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .subtyp_sel1 d, hG => HasTy.plain_of_clsFree d hG rfl
  | _, _, _, .subtyp_all e₁ e₂, hG => ⟨Sub.plain_of_clsFree e₁ hG, Sub.plain_of_clsFree e₂ hG⟩
  | _, _, _, .subtyp_seal (p := p) (C := C) h, hG => by
      rw [Ctx.selfCls_none_of_classFree hG p C] at h
      cases h
end

end Nominal.Source
