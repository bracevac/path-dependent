import Coercions.PDot.Source.Derived

/-!
# Path models of a fixed context

A tool for the negative examples.  A model of a context `G` reads every type as a set of paths,
`sem T p`, and asks one closure property per typing rule whose conclusion is a path typing in `G`,
and one per subtyping rule in `G`.  `Model.sound_path` and `Model.sound_sub` then read a path typing
in `G` as membership and a subtyping in `G` as inclusion.  A path that is in no set of the model has
no type in `G`.

The model reads nothing in any other context.  Four rules have a premise in a context extended by a
binder: `ty_all_intro`, `ty_let`, `ty_new_intro` and `subtyp_all`.  The first three conclude a typing
of a term that is not a path, which the model does not read.  `subtyp_all` concludes a subtyping of
two function types, and the field `all` asks the model to include one function type in another with
no premise.  So the soundness proof never recurses into a premise outside `G`.  It is one structural
recursion on `HasTy` and `Sub` at the fixed `G`.

A model is built by recursion on the type with a closing substitution for the selves that `μ` binds,
as `sem (μ(z. T)) p := sem T⟨z := p⟩ p`.  `PathSubst.extend` adds the binding of the self, and
`PathSubst.lift_comp_extend` and `PathSubst.one_comp_ofRename_id` are the two equations that make
`rec_i` and `rec_e` hold by the substitution lemma of such a model.

Binders are named in comments only.  `.here` is the newest variable of a signature.
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Models -/

/-- A path model of the context `G`: a set of paths for each type, closed under every rule that
concludes a path typing or a subtyping in `G`. -/
structure Model (G : Ctx s) where
  sem : Ty s → Path s → Prop
  -- ty_var        G.lookup x ∋ x
  var : ∀ x, sem (G.lookup x) (.var x)
  -- ty_new_elim   p ∈ {a : T}  ⟹  p.a ∈ T
  fld_e : ∀ p a T, sem (.rcd (.trm a T)) p → sem T (p.sel a)
  -- ty_rcd_intro  p.a ∈ T  ⟹  p ∈ {a : T}
  fld_i : ∀ p a T, sem T (p.sel a) → sem (.rcd (.trm a T)) p
  -- ty_sngl       p ∈ q.type,  q ∈ T  ⟹  p ∈ T
  sngl : ∀ p q T, sem (.sngl q) p → sem T q → sem T p
  -- ty_path_elim  p ∈ q.type,  q.a ∈ T  ⟹  p.a ∈ (q.a).type
  path_elim : ∀ p q a T, sem (.sngl q) p → sem T (q.sel a) → sem (.sngl (q.sel a)) (p.sel a)
  -- ty_rec_intro  p ∈ T⟨p⟩  ⟹  p ∈ μ(z. T)
  rec_i : ∀ p T, sem (T.substPath p) p → sem (.mu T) p
  -- ty_rec_elim   p ∈ μ(z. T)  ⟹  p ∈ T⟨p⟩
  rec_e : ∀ p T, sem (.mu T) p → sem (T.substPath p) p
  -- ty_and_intro  p ∈ T,  p ∈ U  ⟹  p ∈ T ∧ U
  and_i : ∀ p T U, sem T p → sem U p → sem (.and T U) p
  -- subtyp_top    T ⊆ ⊤
  top : ∀ T p, sem T p → sem .top p
  -- subtyp_bot    ⊥ ⊆ T
  bot : ∀ T p, sem .bot p → sem T p
  -- subtyp_and11  T ∧ U ⊆ T
  and1 : ∀ T U p, sem (.and T U) p → sem T p
  -- subtyp_and12  T ∧ U ⊆ U
  and2 : ∀ T U p, sem (.and T U) p → sem U p
  -- subtyp_fld    T ⊆ U  ⟹  {a : T} ⊆ {a : U}
  fld : ∀ a T U, (∀ p, sem T p → sem U p) → ∀ p, sem (.rcd (.trm a T)) p → sem (.rcd (.trm a U)) p
  -- subtyp_typ    S₂ ⊆ S₁,  T₁ ⊆ T₂  ⟹  {A : S₁..T₁} ⊆ {A : S₂..T₂}
  typ : ∀ A S₁ T₁ S₂ T₂, (∀ p, sem S₂ p → sem S₁ p) → (∀ p, sem T₁ p → sem T₂ p) →
      ∀ p, sem (.rcd (.typ A S₁ T₁)) p → sem (.rcd (.typ A S₂ T₂)) p
  -- subtyp_sngl_pq, subtyp_sngl_qp
  --               p ∈ q.type,  q ∈ U,  p ↦ q ⊢ T ⇝ T' or q ↦ p ⊢ T ⇝ T'  ⟹  T ⊆ T'
  repl : ∀ p q U T T', sem (.sngl q) p → sem U q → (Repl p q T T' ⊕ Repl q p T T') → ∀ r, sem T r → sem T' r
  -- subtyp_sel2   p ∈ {A : S..T}  ⟹  S ⊆ p.A
  sel2 : ∀ p A S T, sem (.rcd (.typ A S T)) p → ∀ r, sem S r → sem (.sel p A) r
  -- subtyp_sel1   p ∈ {A : S..T}  ⟹  p.A ⊆ T
  sel1 : ∀ p A S T, sem (.rcd (.typ A S T)) p → ∀ r, sem (.sel p A) r → sem T r
  -- subtyp_all    ∀(z : S₁) T₁ ⊆ ∀(z : S₂) T₂, with no premise read
  all : ∀ S₁ T₁ S₂ T₂ r, sem (.all S₁ T₁) r → sem (.all S₂ T₂) r

/-! ## Soundness -/

mutual
/-- A typing in `G` of a term that is a path puts the path in the set of its type.  The term is
generalized to an equation, so that the cases of terms that are not paths close by `nomatch`. -/
theorem Model.sound_of_eq {G : Ctx s} (M : Model G) :
    ∀ {t : Tm s} {T : Ty s}, HasTy G t T → ∀ p, t = .path p → M.sem T p
  | _, _, .ty_var h, _, e => by
      cases e
      subst h
      exact M.var _
  | _, _, .ty_all_intro _, _, e => nomatch e
  | _, _, .ty_all_elim _ _, _, e => nomatch e
  | _, _, .ty_new_intro _, _, e => nomatch e
  | _, _, .ty_new_elim h, _, e => by
      cases e
      exact M.fld_e _ _ _ (Model.sound_of_eq M h _ rfl)
  | _, _, .ty_rcd_intro h, _, e => by
      cases e
      exact M.fld_i _ _ _ (Model.sound_of_eq M h _ rfl)
  | _, _, .ty_let _ _, _, e => nomatch e
  | _, _, .ty_sngl h₁ h₂, _, e => by
      cases e
      exact M.sngl _ _ _ (Model.sound_of_eq M h₁ _ rfl) (Model.sound_of_eq M h₂ _ rfl)
  | _, _, .ty_path_elim h₁ h₂, _, e => by
      cases e
      exact M.path_elim _ _ _ _ (Model.sound_of_eq M h₁ _ rfl) (Model.sound_of_eq M h₂ _ rfl)
  | _, _, .ty_rec_intro h, _, e => by
      cases e
      exact M.rec_i _ _ (Model.sound_of_eq M h _ rfl)
  | _, _, .ty_rec_elim h, _, e => by
      cases e
      exact M.rec_e _ _ (Model.sound_of_eq M h _ rfl)
  | _, _, .ty_and_intro h₁ h₂, _, e => by
      cases e
      exact M.and_i _ _ _ (Model.sound_of_eq M h₁ _ rfl) (Model.sound_of_eq M h₂ _ rfl)
  | _, _, .ty_sub h hs, p, e => Model.sound_sub_at M hs p (Model.sound_of_eq M h p e)

/-- A subtyping in `G` is an inclusion of the sets of the model. -/
theorem Model.sound_sub_at {G : Ctx s} (M : Model G) :
    ∀ {S T : Ty s}, Sub G S T → ∀ p, M.sem S p → M.sem T p
  | _, _, .subtyp_top, p, h => M.top _ p h
  | _, _, .subtyp_bot, p, h => M.bot _ p h
  | _, _, .subtyp_refl, _, h => h
  | _, _, .subtyp_trans h₁ h₂, p, h => Model.sound_sub_at M h₂ p (Model.sound_sub_at M h₁ p h)
  | _, _, .subtyp_and11, p, h => M.and1 _ _ p h
  | _, _, .subtyp_and12, p, h => M.and2 _ _ p h
  | _, _, .subtyp_and2 h₁ h₂, p, h =>
      M.and_i p _ _ (Model.sound_sub_at M h₁ p h) (Model.sound_sub_at M h₂ p h)
  | _, _, .subtyp_fld h₁, p, h => M.fld _ _ _ (fun q => Model.sound_sub_at M h₁ q) p h
  | _, _, .subtyp_typ h₁ h₂, p, h =>
      M.typ _ _ _ _ _ (fun q => Model.sound_sub_at M h₁ q) (fun q => Model.sound_sub_at M h₂ q) p h
  | _, _, .subtyp_sngl_pq h₁ h₂ r, p, h =>
      M.repl _ _ _ _ _ (Model.sound_of_eq M h₁ _ rfl) (Model.sound_of_eq M h₂ _ rfl) (.inl r) p h
  | _, _, .subtyp_sngl_qp h₁ h₂ r, p, h =>
      M.repl _ _ _ _ _ (Model.sound_of_eq M h₁ _ rfl) (Model.sound_of_eq M h₂ _ rfl) (.inr r) p h
  | _, _, .subtyp_sel2 h₁, p, h => M.sel2 _ _ _ _ (Model.sound_of_eq M h₁ _ rfl) p h
  | _, _, .subtyp_sel1 h₁, p, h => M.sel1 _ _ _ _ (Model.sound_of_eq M h₁ _ rfl) p h
  | _, _, .subtyp_all _ _, p, h => M.all _ _ _ _ p h
end

/-- A path typing in `G` is membership in the model. -/
theorem Model.sound_path (M : Model G) : HasTy G (.path p) T → M.sem T p :=
  fun h => M.sound_of_eq h p rfl

/-- A subtyping in `G` is inclusion in the model. -/
theorem Model.sound_sub (M : Model G) : Sub G S T → ∀ p, M.sem S p → M.sem T p :=
  M.sound_sub_at

/-! ## Closing substitutions for the selves of `μ` -/

/-- `τ` extended by one more variable, the newest, sent to the path `p`.  It closes the self of a
`μ` at the path the model reads it at. -/
def _root_.Paths.FCdot.PathSubst.extend (τ : PathSubst s₁ s₂) (p : Path s₂) : PathSubst (s₁,x) s₂ where
  var := fun
    | .here => p                                 -- (τ, z ↦ p) z = p
    | .there y => τ.var y                        -- (τ, z ↦ p) y↑ = τ y

/-- Substituting under the binder and then closing it at `p` is closing it at `p` after
substituting. -/
theorem PathSubst.lift_comp_extend (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃) (p : Path s₃) :
    σ.lift.comp (τ.extend p) = (σ.comp τ).extend p := by
  apply PathSubst.funext'
  intro y
  cases y with
  | here => rfl
  | there y =>
      show ((σ.var y).rename Rename.succ).subst (τ.extend p) = (σ.var y).subst τ
      rw [Path.rename_subst]
      rfl

/-- Opening at `p` and reading in the identity closing is reading with the self closed at `p`. -/
theorem PathSubst.one_comp_ofRename_id (p : Path s) :
    (PathSubst.one p).comp (PathSubst.ofRename Rename.id) = (PathSubst.ofRename Rename.id).extend p := by
  apply PathSubst.funext'
  intro y
  cases y with
  | here =>
      show p.subst (PathSubst.ofRename Rename.id) = p
      rw [Path.subst_ofRename, Path.rename_id]
  | there y => rfl

end PDot.Source
