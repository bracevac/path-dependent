import Coercions.Nominal.FCn.Context

/-!
# FCn typing (plan T.3)

The typing rules of T.3 in full, as two mutual blocks of `Prop`-valued judgments (decision D2 of
the groups file).  The first block types evidence: path equality `Γ ⊢ π : p ≃ q`, path typing
`Γ ⊢ᵖ P : T`, inclusion `Γ ⊢ e : S ≤ T`, type equality `Γ ⊢ φ : S ≡ T`, morphisms
`Γ ⊢ m : src ⇒ Tel` and sides `Γ ⊢ˢ sd : X ≤ Y`.  The second types terms `Γ ⊢ t : T`, values
`Γ ⊢ᵥ v : T` and definitions `Γ ⊢ᵈ[p] ds : Tel`.

Every rule is a constructor named after the evidence or term constructor it types, with its
premises in the plan's order.  So `LE-Eq` is `eqToLe`, `EQ-Def` is `defP`, `DF-Fun` is `fn` and
`TM-Let` is `lett`.  The comment above each rule carries the plan's name and the binders the rule
introduces.  `src`, `Tel` and `Tel'` of a morphism are under one self `w`, and the types of a side
are under it too.

The inversions go through equation forms that generalize the index, X0's route
(`PDot/Source/Derived.lean`).  The last two theorems are Z9 for FCn morphisms: a singleton
telescope proves no bound and no other alias.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Evidence -/

mutual
inductive PEq.HasType : Ctx s → PEq s → Path s → Path s → Prop where              -- Γ ⊢ π : p ≃ q
  -- PE-Refl     binders p
  | refl : PEq.HasType Γ (.refl p) p p
  -- PE-Symm     binders π p q
  | symm : PEq.HasType Γ π p q → PEq.HasType Γ (.symm π) q p
  -- PE-Trans    binders π π' p q r
  | trans : PEq.HasType Γ π p q → PEq.HasType Γ π' q r → PEq.HasType Γ (.trans π π') p r
  -- PE-Sel      binders π p q a
  | sel : PEq.HasType Γ π p q → PEq.HasType Γ (.sel π a) (.sel p a) (.sel q a)
  -- PE-Member   binders P S e Tel i, q under the self w
  | member : PathCo.HasType Γ P S → LeCo.HasType Γ e S (.mu Tel) → Tel.At i (.alias q) → PEq.HasType Γ (.member P e i) P.path (q.substPath P.path)
inductive PathCo.HasType : Ctx s → PathCo s → Ty s → Prop where                    -- Γ ⊢ᵖ P : T
  -- PA-Var      binders x T
  | var : Γ.ty x = T → PathCo.HasType Γ (.var x) T
  -- PA-Sel      binders P Tel i a, T under the self w
  | sel : PathCo.HasType Γ P (.mu Tel) → Tel.At i (.fld a T) → PathCo.HasType Γ (.sel P a i) (T.substPath P.path)
  -- PA-Cast     binders P S e T
  | cast : PathCo.HasType Γ P S → LeCo.HasType Γ e S T → PathCo.HasType Γ (.cast P e) T
  -- PA-Alias    binders P₀ S π Q T, the new path P₀.path typed first (decision 8)
  | alias : PathCo.HasType Γ P₀ S → PEq.HasType Γ π P₀.path Q.path → PathCo.HasType Γ Q T → PathCo.HasType Γ (.alias P₀ π Q) T
  -- PA-Sngl     binders P S π q
  | sngl : PathCo.HasType Γ P S → PEq.HasType Γ π P.path q → PathCo.HasType Γ (.sngl P q π) (Ty.sngl q)
  -- PA-FldI     binders Q T p a
  | fldI : PathCo.HasType Γ Q T → Q.path = .sel p a → PathCo.HasType Γ (.fldI p a Q) (.mu (.cons .nil (.fld a T.weaken)))
  -- PA-Unfold   binders P Tel
  | unfold : PathCo.HasType Γ P (.mu Tel) → PathCo.HasType Γ (.unfold P) (.mu (Tel.substPath P.path).weaken)
  -- PA-Fold     binders P Tel
  | fold : PathCo.HasType Γ P (.mu (Tel.substPath P.path).weaken) → PathCo.HasType Γ (.fold Tel P) (.mu Tel)
  -- PA-Both     binders P Q Tel Tel'
  | both : PathCo.HasType Γ P (.mu Tel) → PathCo.HasType Γ Q (.mu Tel') → Q.path = P.path → PathCo.HasType Γ (.both Tel Tel' P Q) (.mu (Tel ++ Tel'))
inductive LeCo.HasType : Ctx s → LeCo s → Ty s → Ty s → Prop where                 -- Γ ⊢ e : S ≤ T
  -- LE-Refl     binders T
  | refl : LeCo.HasType Γ (.refl T) T T
  -- LE-Trans    binders e f S M T
  | trans : LeCo.HasType Γ e S M → LeCo.HasType Γ f M T → LeCo.HasType Γ (.trans e f) S T
  -- LE-Top      binders T
  | top : LeCo.HasType Γ (.top T) T .top
  -- LE-Bot      binders T
  | bot : LeCo.HasType Γ (.bot T) .bot T
  -- LE-Eq       binders φ S T
  | eqToLe : EqCo.HasType Γ φ S T → LeCo.HasType Γ (.eqToLe φ) S T
  -- LE-Pi       binders e S₁ S₂, z of f T₁ T₂
  | pi : LeCo.HasType Γ e S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) f T₁ T₂ → LeCo.HasType Γ (.pi e f) (.pi S₁ T₁) (.pi S₂ T₂)
  -- LE-Obj      binders m, w of Tel Tel'
  | obj : Morphism.HasType Γ Tel m Tel' → LeCo.HasType Γ (.obj Tel m) (.mu Tel) (.mu Tel')
  -- LE-Pair     binders e f S, w of Tel Tel'
  | pair : LeCo.HasType Γ e S (.mu Tel) → LeCo.HasType Γ f S (.mu Tel') → LeCo.HasType Γ (.pair Tel Tel' e f) S (.mu (Tel ++ Tel'))
  -- LE-Bound    binders i T, w of Tel
  | bound : Tel.At i (.is T.weaken) → LeCo.HasType Γ (.bound Tel i) (.mu Tel) T
  -- LE-IntoBnd  binders e S T
  | intoBnd : LeCo.HasType Γ e S T → LeCo.HasType Γ (.intoBnd e) S (.mu (.cons .nil (.is T.weaken)))
  -- LE-Member   binders P S e Tel i, S' T' under the self w
  | member : PathCo.HasType Γ P S → LeCo.HasType Γ e S (.mu Tel) → Tel.At i (.le S' T') → LeCo.HasType Γ (.member P e i) (S'.substPath P.path) (T'.substPath P.path)
  -- LE-Seal     binders p C U
  | seal : Γ.clsAt p C = some U → LeCo.HasType Γ (.seal p C) U (.sel p C)
inductive EqCo.HasType : Ctx s → EqCo s → Ty s → Ty s → Prop where                 -- Γ ⊢ φ : S ≡ T
  -- EQ-Refl     binders T
  | refl : EqCo.HasType Γ (.refl T) T T
  -- EQ-Symm     binders φ S T
  | symm : EqCo.HasType Γ φ S T → EqCo.HasType Γ (.symm φ) T S
  -- EQ-Trans    binders φ ψ S M T
  | trans : EqCo.HasType Γ φ S M → EqCo.HasType Γ ψ M T → EqCo.HasType Γ (.trans φ ψ) S T
  -- EQ-Def      binders p A W
  | defP : Γ.defAt p A = some W → EqCo.HasType Γ (.defP p A) (.sel p A) W
  -- EQ-Lift     binders π p q, h of T
  | lift : PEq.HasType Γ π p q → EqCo.HasType Γ (.lift T π) (T.substPath p) (T.substPath q)
  -- EQ-Dom      binders φ S₁ S₂, z of T₁ T₂
  | dom : EqCo.HasType Γ φ (.pi S₁ T₁) (.pi S₂ T₂) → EqCo.HasType Γ (.dom φ) S₁ S₂
  -- EQ-Cod      binders φ S₁ S₂ p, z of T₁ T₂
  | cod : EqCo.HasType Γ φ (.pi S₁ T₁) (.pi S₂ T₂) → EqCo.HasType Γ (.cod φ p) (T₁.substPath p) (T₂.substPath p)
inductive Morphism.HasType : Ctx s → Telescope (s,x) → Morphism s → Telescope (s,x) → Prop where   -- Γ ⊢ m : src ⇒ Tel
  -- MO-Nil      binders, w of src
  | nil : Morphism.HasType Γ src .nil .nil
  -- MO-Le       binders m j pre post, w of src Tel X Y S T
  | le : Morphism.HasType Γ src m Tel → src.At j (.le X Y) → Side.HasType Γ pre S X → Side.HasType Γ post Y T → Morphism.HasType Γ src (.le m pre j post) (.cons Tel (.le S T))
  -- MO-Fld      binders m j sd a, w of src Tel X T
  | fld : Morphism.HasType Γ src m Tel → src.At j (.fld a X) → Side.HasType Γ sd X T → Morphism.HasType Γ src (.fld m j sd) (.cons Tel (.fld a T))
  -- MO-Alias    binders m j, w of src Tel q
  | alias : Morphism.HasType Γ src m Tel → src.At j (.alias q) → Morphism.HasType Γ src (.alias m j) (.cons Tel (.alias q))
  -- MO-Is       binders m e T, w of src Tel
  | is : Morphism.HasType Γ src m Tel → LeCo.HasType Γ e (.mu src) T → Morphism.HasType Γ src (.is m e) (.cons Tel (.is T.weaken))
inductive Side.HasType : Ctx s → Side s → Ty (s,x) → Ty (s,x) → Prop where         -- Γ ⊢ˢ sd : X ≤ Y, under the self
  -- SD-None     binders X
  | none : Side.HasType Γ .none X X
  -- SD-Some     binders e X Y
  | some : LeCo.HasType Γ e X Y → Side.HasType Γ (.some e) X.weaken Y.weaken
  -- SD-Bot      binders X
  | bot : Side.HasType Γ (.bot X) .bot X
  -- SD-Top      binders X
  | top : Side.HasType Γ (.top X) X .top
end

/-! ## Terms, values, definitions -/

mutual
inductive Tm.HasType : Ctx s → Tm s → Ty s → Prop where                            -- Γ ⊢ t : T
  -- TM-Path     binders P T
  | path : PathCo.HasType Γ P T → Tm.HasType Γ (.path P) T
  -- TM-Val      binders v T
  | val : Value.HasType Γ v T → Tm.HasType Γ (.val v) T
  -- TM-App      binders P Q S, z of T
  | app : PathCo.HasType Γ P (.pi S T) → PathCo.HasType Γ Q S → Tm.HasType Γ (.app P Q) (T.substPath Q.path)
  -- TM-Let      binders t T U, z of u
  | lett : Tm.HasType Γ t T → Tm.HasType (Γ.cons (.opaque T)) u U.weaken → Tm.HasType Γ (.lett t u) U
  -- TM-Cast     binders t e S T
  | cast : Tm.HasType Γ t S → LeCo.HasType Γ e S T → Tm.HasType Γ (.cast t e) T
inductive Value.HasType : Ctx s → Value s → Ty s → Prop where                     -- Γ ⊢ᵥ v : T
  -- VA-Lam      binders S, z of t T
  | lam : Tm.HasType (Γ.cons (.opaque S)) t T → Value.HasType Γ (.lam S t) (.pi S T)
  -- VA-Obj      binders, z of ds, w of Tel, the self bound transparent at the literal's own block (D3, D4)
  | obj : Defs.HasType (Γ.cons (.transparent (.mu Tel) ds.block)) (.var .here) ds (Tel.rename Rename.succ.lift) → Value.HasType Γ (.obj Tel ds) (.mu Tel)
  -- VA-Cast     binders v e S T
  | cast : Value.HasType Γ v S → LeCo.HasType Γ e S T → Value.HasType Γ (.cast v e) T
inductive Defs.HasType : Ctx s → Path s → Defs s → Telescope (s,x) → Prop where    -- Γ ⊢ᵈ[p] ds : Tel
  -- DF-Nil      binders p
  | nil : Defs.HasType Γ p .nil .nil
  -- DF-Typ      binders p ds A U, w of Tel W
  | typ : Defs.HasType Γ p ds Tel → A ∉ ds.labels → U = W.substPath p → Defs.HasType Γ p (.typ ds A U) (.cons (.cons Tel (.le W (.sel (.var .here) A))) (.le (.sel (.var .here) A) W))
  -- DF-Path     binders p ds a P T, w of Tel q
  | path : Defs.HasType Γ p ds Tel → a ∉ ds.labels → PathCo.HasType Γ P T → P.path = q.substPath p → Defs.HasType Γ p (.fld ds a (.path P)) (.cons Tel (.fld a (Ty.sngl q)))
  -- DF-Fun      binders p ds a v, w of Tel S, y of T
  | fn : Defs.HasType Γ p ds Tel → a ∉ ds.labels → v.isLam = true → Value.HasType Γ v ((Ty.pi S T).substPath p) → Defs.HasType Γ p (.fld ds a (.fn v)) (.cons Tel (.fld a (.pi S T)))
  -- DF-Nest     binders p ds a ds', w of Tel, w and v of Tel'
  | nest : Defs.HasType Γ p ds Tel → a ∉ ds.labels → Defs.HasType Γ (.sel p a) ds' (Tel'.subst (PathSubst.one p).lift) → Defs.HasType Γ p (.fld ds a (.nest (Tel'.subst (PathSubst.one p).lift) ds')) (.cons Tel (.fld a (.mu Tel')))
  -- DF-Cls      binders p ds C U, w of Tel and TelB, o the own self of TelB
  | cls : Defs.HasType Γ p ds Tel → C ∉ ds.labels → U = (Ty.mu TelB).substPath p → Defs.HasType Γ p (.cls ds C U) (.cons (.cons Tel (.le .bot (.sel (.var .here) C))) (.le (.sel (.var .here) C) (.mu TelB)))
end

/-! ## Inversions

Each inversion lemma is proved through its equation form, which generalizes the index of the
judgment by an equation (the route of `PDot/Source/Derived.lean`). -/

theorem Value.HasType.obj_inv_of_eq : ∀ {Γ : Ctx s} {v : Value s} {U : Ty s}, Value.HasType Γ v U → ∀ (Tel : Telescope (s,x)) (ds : Defs (s,x)), v = .obj Tel ds → U = .mu Tel ∧ Defs.HasType (Γ.cons (.transparent (.mu Tel) ds.block)) (.var .here) ds (Tel.rename Rename.succ.lift)
  | _, _, _, .obj h, _, _, e => by cases e; exact ⟨rfl, h⟩
  | _, _, _, .lam _, _, _, e => nomatch e
  | _, _, _, .cast _ _, _, _, e => nomatch e

theorem Value.HasType.obj_inv {Γ : Ctx s} {Tel : Telescope (s,x)} {ds : Defs (s,x)} {U : Ty s} : Value.HasType Γ (.obj Tel ds) U → U = .mu Tel ∧ Defs.HasType (Γ.cons (.transparent (.mu Tel) ds.block)) (.var .here) ds (Tel.rename Rename.succ.lift) :=
  fun h => h.obj_inv_of_eq Tel ds rfl

theorem Defs.HasType.path_inv_of_eq : ∀ {Γ : Ctx s} {p : Path s} {ds' : Defs s} {Tel' : Telescope (s,x)}, Defs.HasType Γ p ds' Tel' → ∀ (ds : Defs s) (a : Label) (P : PathCo s), ds' = .fld ds a (.path P) → ∃ Tel q T, Tel' = .cons Tel (.fld a (Ty.sngl q)) ∧ P.path = q.substPath p ∧ Defs.HasType Γ p ds Tel ∧ PathCo.HasType Γ P T
  | _, _, _, _, .path (Tel := Tel) (q := q) (T := T) hds _ hP hq, _, _, _, e => by
      cases e; exact ⟨Tel, q, T, rfl, hq, hds, hP⟩
  | _, _, _, _, .nil, _, _, _, e => nomatch e
  | _, _, _, _, .typ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .fn _ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .nest _ _ _, _, _, _, e => nomatch e

theorem Defs.HasType.path_inv {Γ : Ctx s} {p : Path s} {ds : Defs s} {a : Label} {P : PathCo s} {Tel' : Telescope (s,x)} : Defs.HasType Γ p (.fld ds a (.path P)) Tel' → ∃ Tel q T, Tel' = .cons Tel (.fld a (Ty.sngl q)) ∧ P.path = q.substPath p ∧ Defs.HasType Γ p ds Tel ∧ PathCo.HasType Γ P T :=
  fun h => h.path_inv_of_eq ds a P rfl

theorem Defs.HasType.fn_inv_of_eq : ∀ {Γ : Ctx s} {p : Path s} {ds' : Defs s} {Tel' : Telescope (s,x)}, Defs.HasType Γ p ds' Tel' → ∀ (ds : Defs s) (a : Label) (v : Value s), ds' = .fld ds a (.fn v) → ∃ Tel S T, Tel' = .cons Tel (.fld a (.pi S T)) ∧ v.isLam = true ∧ Value.HasType Γ v ((Ty.pi S T).substPath p) ∧ Defs.HasType Γ p ds Tel
  | _, _, _, _, .fn (Tel := Tel) (S := S) (T := T) hds _ hl hv, _, _, _, e => by
      cases e; exact ⟨Tel, S, T, rfl, hl, hv, hds⟩
  | _, _, _, _, .nil, _, _, _, e => nomatch e
  | _, _, _, _, .typ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .path _ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .nest _ _ _, _, _, _, e => nomatch e

theorem Defs.HasType.fn_inv {Γ : Ctx s} {p : Path s} {ds : Defs s} {a : Label} {v : Value s} {Tel' : Telescope (s,x)} : Defs.HasType Γ p (.fld ds a (.fn v)) Tel' → ∃ Tel S T, Tel' = .cons Tel (.fld a (.pi S T)) ∧ v.isLam = true ∧ Value.HasType Γ v ((Ty.pi S T).substPath p) ∧ Defs.HasType Γ p ds Tel :=
  fun h => h.fn_inv_of_eq ds a v rfl

/-- (I3) of the plan: the labels of typed definitions are distinct. -/
theorem Defs.HasType.labels_nodup {Γ : Ctx s} {p : Path s} {ds : Defs s} {Tel : Telescope (s,x)} : Defs.HasType Γ p ds Tel → ds.labels.Nodup
  | .nil => List.Pairwise.nil
  | .typ h hA _ => List.Pairwise.cons (fun _ h' e => hA (e ▸ h')) h.labels_nodup
  | .path h ha _ _ => List.Pairwise.cons (fun _ h' e => ha (e ▸ h')) h.labels_nodup
  | .fn h ha _ _ => List.Pairwise.cons (fun _ h' e => ha (e ▸ h')) h.labels_nodup
  | .nest h ha _ => List.Pairwise.cons (fun _ h' e => ha (e ▸ h')) h.labels_nodup
  | .cls h hC _ => List.Pairwise.cons (fun _ h' e => hC (e ▸ h')) h.labels_nodup

/-! ## Z9 for FCn morphisms -/

theorem no_le_out_of_sngl {s : Sig} {Γ : Ctx s} {q : Path (s,x)} {m : Morphism s} {Tel : Telescope (s,x)} {S T : Ty (s,x)} : ¬ Morphism.HasType Γ (.cons .nil (.alias q)) m (.cons Tel (.le S T)) := by
  intro h
  cases h with
  | le _ hj _ _ => cases hj with | there h' => cases h'

theorem alias_template_fixed {s : Sig} {Γ : Ctx s} {q q' : Path (s,x)} {m : Morphism s} {Tel : Telescope (s,x)} : Morphism.HasType Γ (.cons .nil (.alias q)) m (.cons Tel (.alias q')) → q' = q := by
  intro h
  cases h with
  | alias _ hj => cases hj with
    | here => rfl
    | there h' => cases h'

end Nominal.FCn
