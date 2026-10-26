import Coercions.PDot.Source.Typing

/-!
# Derived lemmas and rules of the typing

Inversion lemmas, and the derived rules that the examples use.

The inversion of a value typing runs through `ty_sub`, the only rule other than the introduction
that can conclude a typing of a value.  So `HasTy.val_new_inv` and `HasTy.val_lam_inv` are proved by
recursion on the derivation, with the term index generalized to an equation.  The inversions of a
definition typing read the one rule that fits the definition: a definition typing has no
subsumption.  So a path field is declared at its singleton and nothing else (`DefTy.path_decl`), a
function field at a `∀` (`DefTy.lam_decl`), an object field at its own `μ` (`DefTy.new_decl`), and a
type member at equal bounds (`DefTy.typ_decl`).  `DefsTy.cons_inv` reads the last definition's
declaration off the type of a list of definitions.  Every type a list of definitions is typed at is
tight (`DefsTy.tight`), since `ty_def_new` asks it of each nested literal.

The derived rules are `def`s from the constructors: `HasTy.sub'`, `HasTy.andL`, `HasTy.andR`,
`HasTy.fieldOfRec` and `Sub.andProj`.
-/

namespace PDot.Source

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

/-- The type of a non-empty list of definitions: `{D}` for one definition, `T' ∧ {D}` otherwise, with
`D` the declaration of the last definition. -/
theorem DefsTy.cons_inv : DefsTy G r (.cons ds d) T →
    (ds = .nil ∧ ∃ D, T = .rcd D ∧ Nonempty (DefTy G r d D)) ∨
    ∃ T' D, T = .and T' (.rcd D) ∧ Nonempty (DefTy G r d D) ∧ Nonempty (DefsTy G r ds T')
  | .ty_defs_one hd => .inl ⟨rfl, _, rfl, ⟨hd⟩⟩
  | .ty_defs_cons hds hd _ => .inr ⟨_, _, rfl, ⟨hd⟩, ⟨hds⟩⟩

/-! ## Tight bounds of a typed list of definitions -/

/-- Every declaration a definition is typed at is tight.  `ty_def_typ` declares equal bounds, and
`ty_def_new` asks `tight_bounds` of the nested annotation. -/
theorem DefTy.tight : DefTy G r d D → D.tight = true
  | .ty_def_typ => decide_eq_true rfl
  | .ty_def_all _ => rfl
  | .ty_def_new h _ => h
  | .ty_def_path _ => rfl

/-- Every type a list of definitions is typed at is tight. -/
theorem DefsTy.tight : DefsTy G r ds T → T.tight = true
  | .ty_defs_one hd => hd.tight
  | .ty_defs_cons hds hd _ => by
      show (_ && Dec.tight _) = true
      rw [hds.tight, hd.tight]
      rfl

/-- The annotation of a typed literal is tight. -/
theorem DefsTy.tight_at_self {G : Ctx s} : DefsTy (G.consSelf T) (.var .here) ds T → T.tight = true :=
  DefsTy.tight

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

end PDot.Source
