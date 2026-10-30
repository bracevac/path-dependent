import Coercions.Nominal.Translation.Hole
import Coercions.Nominal.Translation.Rel

/-!
# Evidence: path typings and subtyping (plan X, Parts TR.3 and TR.4, stage X6 group g2)

A source derivation of a path typing translates to an FCn path evidence `PathCo`, and a source
subtyping derivation to an FCn subtyping coercion `LeCo`.  `HasTy.pathImage` and `Sub.translate` are
one structural recursion over the two families `HasTy` and `Sub`, one equation per source rule.

Path images through `Option` (decision D2 of the groups file).  A function on `HasTy G (.path p) T`
alone cannot recurse structurally, since its index `.path p` is not a variable.  A function from
every `HasTy` derivation into `FCn.PathCo s` does not exist either: `FCn.PathCo []` is empty, and
`ty_all_intro` types a value in the empty context.  So `HasTy.pathImage` is `none` exactly at the
derivations whose term is not a path.  `HasTy.translatePath` reads it with the fallback
`Translation.ofPath p`, and `HasTy.pathImage_path` shows the fallback is never read.

The helpers.  `Ty.intoPath` and `Ty.into` are `into` and `into'` of TR.3 and TR.4.  `Ty.recElimCo`
and `Ty.recIntroCo` are the two images of `ty_rec_elim` and `ty_rec_intro` (decision D7), each a case
split on `telLike`.  Both are the fold after unfold of the Paths line
(`Paths/DotToFCdot/Evidence.lean:286-288`).  A variable at a self binder takes `Ty.recElimCo` too
(decision D6).  `Translation.aliasEv` is `π(d₁)` of TR.3.  `Ty.projL` and `Ty.projR` are the images of
`subtyp_and11` and `subtyp_and12`, an `obj` over identity templates at a tel-like component, a
`bound` at any other.

Telescope indices count from the oldest proposition (decision D4).  In `[S ⊑ w∙A, w∙A ⊑ U]` index 0
is the lower bound.  So `subtyp_sel2` reads index 0, `subtyp_sel1` index 1, and `subtyp_typ` relates
the lower bounds at index 0 and the upper bounds at index 1.  The plan counts from the newest
proposition (`plan-10-pdot.md:777-778`).

The second premise of the replacement rules is not visited (decision D13).  The paths of the images
are the last part: every image's path is the path its derivation types.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The fallback of D2, never read: the path evidence that names a path's own steps, each field
selection at index 0. -/
def _root_.Nominal.Translation.ofPath : Path s → FCn.PathCo s    -- the fallback of D2, never read
  | .var x => .var x                                          -- x ↦ var x
  | .sel p a => .sel (Translation.ofPath p) a 0               -- p.a ↦ sel (ofPath p) a 0

-- identity templates of the propositions of Tel, read at positions off, off + 1, … of src
-- (the Paths line's identityMorphism, Paths/DotToFCdot/Evidence.lean:93, at any signature s', so that it is structural)
/-- The identity template of `Tel`: each proposition of `Tel` read from position `off + i` of `src`,
with no coercion on either side.  It is the Paths line's `identityMorphism`
(`Paths/DotToFCdot/Evidence.lean:93`) at any signature `s'`, so that it is structural. -/
def _root_.Nominal.Translation.identityMorphism (src : FCn.Telescope (s,x)) (off : Nat) : {s' : Sig} → FCn.Telescope s' → FCn.Morphism s
  | _, .nil => .nil                                                                                    -- [] ↦ nil
  | _, .cons Tel (.le _ _) => .le (Translation.identityMorphism src off Tel) .none (off + Tel.length) .none        -- Tel, X ⊑ Y ↦ le m none j none
  | _, .cons Tel (.fld _ _) => .fld (Translation.identityMorphism src off Tel) (off + Tel.length) .none             -- Tel, fld a X ↦ fld m j none
  | _, .cons Tel (.alias _) => .alias (Translation.identityMorphism src off Tel) (off + Tel.length)                -- Tel, ≈ q ↦ alias m j
  | _, .cons Tel (.is _) => .is (Translation.identityMorphism src off Tel) (.bound src (off + Tel.length))          -- Tel, is T ↦ is m (bound src j)

/-- `into'` of TR.4: a coercion into `⟦T⟧` read as a coercion into `μ(w : tel⁺ T)`. -/
def Ty.into (T : Ty s) (e : FCn.LeCo s) : FCn.LeCo s := if T.telLike then e else .intoBnd e              -- into' of TR.4

/-- `into` of TR.3: a path evidence at `⟦T⟧` read at `μ(w : tel⁺ T)`. -/
def Ty.intoPath (T : Ty s) (P : FCn.PathCo s) : FCn.PathCo s :=                                       -- into of TR.3
  if T.telLike then P else .cast P (.intoBnd (.refl T.translate))

/-- The image of `ty_rec_elim` and of a variable at a self binder: for `T = T₀⟨p⟩` and `P` at
`μ(w : tel T₀)`, an evidence at `⟦T⟧`.  At a tel-like `T` it folds the unfolding at `tel⁺ T`.  At
any other `T` it reads the one proposition `is ⟦T⟧` by `bound`. -/
def Ty.recElimCo (T : Ty s) (P : FCn.PathCo s) : FCn.PathCo s :=                                      -- T = T₀⟨p⟩, P : μ(w : tel T₀)
  if T.telLike then .fold T.telP (.unfold P) else .cast (.unfold P) (.bound T.telP 0)

/-- The image of `ty_rec_intro`: for `P` at `⟦T⟨p⟩⟧`, an evidence at `⟦μ(z. T)⟧`.  It folds at
`tel T`, through the unfolding at a tel-like `T` and through `intoBnd` at any other. -/
def Ty.recIntroCo (T : Ty (s,x)) (p : Path s) (P : FCn.PathCo s) : FCn.PathCo s :=                    -- P : ⟦T⟨p⟩⟧
  if T.telLike then .fold T.tel (.unfold P) else .fold T.tel (.cast P (.intoBnd (.refl (T.substPath p).translate)))

/-- `π(d₁)` of TR.3: for `P` at `⟦q.type⟧`, the path equality `P.path ≃ q` read from the alias
proposition at index 0. -/
def _root_.Nominal.Translation.aliasEv (P : FCn.PathCo s) (q : Path s) : FCn.PEq s := .member P (.refl (FCn.Ty.sngl q)) 0   -- π(d₁) of TR.3

/-- The image of `subtyp_and11`, `T ∧ U <: T`: the identity template of the first `|tel⁺ T|`
propositions at a tel-like `T`, the proposition `is ⟦T⟧↑` at index 0 otherwise. -/
def Ty.projL (T U : Ty s) : FCn.LeCo s :=                                                              -- subtyp_and11
  if T.telLike then .obj (Ty.and T U).telP (Translation.identityMorphism (Ty.and T U).telP 0 T.telP) else .bound (Ty.and T U).telP 0

/-- The image of `subtyp_and12`, `T ∧ U <: U`: the identity template of the last `|tel⁺ U|`
propositions at a tel-like `U`, the proposition `is ⟦U⟧↑` at index `|tel⁺ T|` otherwise. -/
def Ty.projR (T U : Ty s) : FCn.LeCo s :=                                                              -- subtyp_and12
  if U.telLike then .obj (Ty.and T U).telP (Translation.identityMorphism (Ty.and T U).telP T.telP.length U.telP)
  else .bound (Ty.and T U).telP T.telP.length

mutual
/-- The image `⟦d⟧` of a typing derivation at a path term, `none` at any other term (D2).  One
equation per source rule of TR.3. -/
def HasTy.pathImage : {G : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy G t T → Option (FCn.PathCo s)
  -- ty_var       x, T = G.lookup x: var x at a plain binder, the fold after unfold at a self binder (D6)
  | G, _, T, .ty_var (x := x) _ => some (if G.isSelf x then T.recElimCo (.var x) else .var x)
  -- ty_all_intro, ty_all_elim, ty_new_intro, ty_let conclude no path
  | _, _, _, .ty_all_intro _ => none
  | _, _, _, .ty_all_elim _ _ => none
  | _, _, _, .ty_new_intro _ => none
  -- ty_new_elim  d : p : {a : T}  ↦  sel ⟦d⟧ a 0
  | _, _, _, .ty_new_elim (a := a) d => d.pathImage.map (FCn.PathCo.sel · a 0)
  -- ty_rcd_intro d : p.a : T  ↦  fldI p a ⟦d⟧
  | _, _, _, .ty_rcd_intro (p := p) (a := a) d => d.pathImage.map (FCn.PathCo.fldI p a)
  -- ty_let       t, u: a let is not a path
  | _, _, _, .ty_let _ _ => none
  -- ty_sngl      d₁ : p : q.type, d₂ : q : T  ↦  alias ⟦d₁⟧ π(d₁) ⟦d₂⟧
  | _, _, _, .ty_sngl (q := q) d₁ d₂ =>
      match d₁.pathImage, d₂.pathImage with
      | some P, some Q => some (.alias P (Translation.aliasEv P q) Q)
      | _, _ => none
  -- ty_path_elim d₁ : p : q.type, d₂ : q.a : T  ↦  sngl (sel (alias ⟦d₁⟧ π(d₁) (fldI q a ⟦d₂⟧)) a 0) (q.a) (sel π(d₁) a)
  | _, _, _, .ty_path_elim (q := q) (a := a) d₁ d₂ =>
      match d₁.pathImage, d₂.pathImage with
      | some P, some Q => some (.sngl (.sel (.alias P (Translation.aliasEv P q) (.fldI q a Q)) a 0) (q.sel a) (.sel (Translation.aliasEv P q) a))
      | _, _ => none
  -- ty_rec_intro d : p : T⟨p⟩, T over (s,z)  ↦  the two images of TR.3 (D7)
  | _, _, _, .ty_rec_intro (p := p) (T := T) d => d.pathImage.map (T.recIntroCo p)
  -- ty_rec_elim  d : p : μ(z. T)  ↦  the two images of TR.3 (D7)
  | _, _, _, .ty_rec_elim (p := p) (T := T) d => d.pathImage.map ((T.substPath p).recElimCo)
  -- ty_and_intro d₁ : p : T, d₂ : p : U  ↦  both (tel⁺ T) (tel⁺ U) (into T ⟦d₁⟧) (into U ⟦d₂⟧)
  | _, _, _, .ty_and_intro (T := T) (U := U) d₁ d₂ =>
      match d₁.pathImage, d₂.pathImage with
      | some P, some Q => some (.both T.telP U.telP (T.intoPath P) (U.intoPath Q))
      | _, _ => none
  -- ty_sub       d : t : T, e : T <: U  ↦  cast ⟦d⟧ ⟦e⟧ at a path
  | _, _, _, .ty_sub d e => d.pathImage.map (FCn.PathCo.cast · e.translate)
/-- The image `⟦e⟧` of a subtyping derivation, one equation per source rule of TR.4. -/
def Sub.translate : {G : Ctx s} → {S T : Ty s} → Sub G S T → FCn.LeCo s
  | _, T, _, .subtyp_top => .top T.translate                  -- T <: ⊤
  | _, _, T, .subtyp_bot => .bot T.translate                  -- ⊥ <: T
  | _, T, _, .subtyp_refl => .refl T.translate                -- T <: T
  | _, _, _, .subtyp_trans e₁ e₂ => .trans e₁.translate e₂.translate          -- e₁ : S <: T, e₂ : T <: U
  | _, _, _, .subtyp_and11 (T := T) (U := U) => Ty.projL T U  -- T ∧ U <: T
  | _, _, _, .subtyp_and12 (T := T) (U := U) => Ty.projR T U  -- T ∧ U <: U
  | _, _, _, .subtyp_and2 (T := T) (U := U) e₁ e₂ => .pair T.telP U.telP (T.into e₁.translate) (U.into e₂.translate)   -- e₁ : S <: T, e₂ : S <: U
  | _, _, _, .subtyp_fld (a := a) (T := T) e => .obj (Ty.rcd (.trm a T)).telP (.fld .nil 0 (.some e.translate))      -- e : T <: U
  -- subtyp_typ   e₁ : S₂ <: S₁, e₂ : T₁ <: T₂, indices from the oldest (D4)
  | _, _, _, .subtyp_typ (A := A) (S₁ := S₁) (T₁ := T₁) e₁ e₂ =>
      .obj (Ty.rcd (.typ A S₁ T₁)).telP (.le (.le .nil (.some e₁.translate) 0 .none) .none 1 (.some e₂.translate))
  -- subtyp_sngl_pq d₁ : p : q.type, d₂ : q : U (not visited, D13), r : p ↦ q ⊢ T ⇝ T'  ↦  eqToLe (lift (h. ⟦hole r⟧) π(d₁))
  | _, _, _, .subtyp_sngl_pq (p := p) (q := q) d₁ _ r =>
      .eqToLe (.lift r.hole.translate (Translation.aliasEv (d₁.pathImage.getD (Translation.ofPath p)) q))
  -- subtyp_sngl_qp d₁ : p : q.type, d₂ : q : U (not visited), r : q ↦ p ⊢ T ⇝ T'  ↦  eqToLe (lift (h. ⟦hole r⟧) (symm π(d₁)))
  | _, _, _, .subtyp_sngl_qp (p := p) (q := q) d₁ _ r =>
      .eqToLe (.lift r.hole.translate (.symm (Translation.aliasEv (d₁.pathImage.getD (Translation.ofPath p)) q)))
  -- subtyp_sel2  d : p : {A : S..T}  ↦  member ⟦d⟧ (refl ⟦{A : S..T}⟧) 0, the lower bound (D4)
  | _, _, _, .subtyp_sel2 (p := p) (A := A) (S := S) (T := T) d =>
      .member (d.pathImage.getD (Translation.ofPath p)) (.refl (Ty.rcd (.typ A S T)).translate) 0
  -- subtyp_sel1  d : p : {A : S..T}  ↦  member ⟦d⟧ (refl ⟦{A : S..T}⟧) 1, the upper bound (D4)
  | _, _, _, .subtyp_sel1 (p := p) (A := A) (S := S) (T := T) d =>
      .member (d.pathImage.getD (Translation.ofPath p)) (.refl (Ty.rcd (.typ A S T)).translate) 1
  | _, _, _, .subtyp_all e₁ e₂ => .pi e₁.translate e₂.translate              -- e₁ : S₂ <: S₁, z of e₂ : T₁ <: T₂
end

/-- `⟦d⟧` at a path term.  The fallback is never read (`HasTy.pathImage_path`). -/
def HasTy.translatePath {G : Ctx s} {p : Path s} {T : Ty s} (d : HasTy G (.path p) T) : FCn.PathCo s :=
  d.pathImage.getD (Translation.ofPath p)                     -- ⟦d⟧ at a path term

/-- The image of `ty_rec_elim` keeps the path of its evidence. -/
theorem Ty.recElimCo_path (T : Ty s) (P : FCn.PathCo s) : (T.recElimCo P).path = P.path := by
  unfold Ty.recElimCo; split <;> rfl

/-- The image of `ty_rec_intro` keeps the path of its evidence. -/
theorem Ty.recIntroCo_path (T : Ty (s,x)) (p : Path s) (P : FCn.PathCo s) : (T.recIntroCo p P).path = P.path := by
  unfold Ty.recIntroCo; split <;> rfl

/-- `into` keeps the path of its evidence. -/
theorem Ty.intoPath_path (T : Ty s) (P : FCn.PathCo s) : (T.intoPath P).path = P.path := by
  unfold Ty.intoPath; split <;> rfl

/-- A derivation at a path term has an image, and the image's path is that path.  An equation form
(D12): the term is generalized by `t = .path p`. -/
theorem HasTy.pathImage_path : ∀ {G : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy G t T) (p : Path s),
    t = .path p → ∃ P, d.pathImage = some P ∧ P.path = p
  | _, _, _, .ty_var (x := x) _, p, e => by
      cases e
      refine ⟨_, rfl, ?_⟩
      split
      · exact Ty.recElimCo_path _ _
      · rfl
  | _, _, _, .ty_all_intro _, _, e => nomatch e
  | _, _, _, .ty_all_elim _ _, _, e => nomatch e
  | _, _, _, .ty_new_intro _, _, e => nomatch e
  | _, _, _, .ty_let _ _, _, e => nomatch e
  | _, _, _, .ty_new_elim (p := p') (a := a) d, p, e => by
      obtain ⟨P, hd, hp⟩ := HasTy.pathImage_path d p' rfl
      cases e
      exact ⟨.sel P a 0, by simp only [HasTy.pathImage, hd]; rfl, by simp only [FCn.PathCo.path, hp]⟩
  | _, _, _, .ty_rcd_intro (p := p') (a := a) d, p, e => by
      obtain ⟨P, hd, _⟩ := HasTy.pathImage_path d (p'.sel a) rfl
      cases e
      exact ⟨.fldI p' a P, by simp only [HasTy.pathImage, hd]; rfl, rfl⟩
  | _, _, _, .ty_sngl (p := p') (q := q) d₁ d₂, p, e => by
      obtain ⟨P, hd₁, hp⟩ := HasTy.pathImage_path d₁ p' rfl
      obtain ⟨Q, hd₂, _⟩ := HasTy.pathImage_path d₂ q rfl
      cases e
      exact ⟨.alias P (Translation.aliasEv P q) Q, by simp only [HasTy.pathImage, hd₁, hd₂], hp⟩
  | _, _, _, .ty_path_elim (p := p') (q := q) (a := a) d₁ d₂, p, e => by
      obtain ⟨P, hd₁, hp⟩ := HasTy.pathImage_path d₁ p' rfl
      obtain ⟨Q, hd₂, _⟩ := HasTy.pathImage_path d₂ (q.sel a) rfl
      cases e
      exact ⟨.sngl (.sel (.alias P (Translation.aliasEv P q) (.fldI q a Q)) a 0) (q.sel a) (.sel (Translation.aliasEv P q) a),
        by simp only [HasTy.pathImage, hd₁, hd₂], by simp only [FCn.PathCo.path, hp]⟩
  | _, _, _, .ty_rec_intro (p := p') (T := T) d, p, e => by
      obtain ⟨P, hd, hp⟩ := HasTy.pathImage_path d p' rfl
      cases e
      exact ⟨T.recIntroCo p' P, by simp only [HasTy.pathImage, hd]; rfl, by rw [Ty.recIntroCo_path, hp]⟩
  | _, _, _, .ty_rec_elim (p := p') (T := T) d, p, e => by
      obtain ⟨P, hd, hp⟩ := HasTy.pathImage_path d p' rfl
      cases e
      exact ⟨(T.substPath p').recElimCo P, by simp only [HasTy.pathImage, hd]; rfl, by rw [Ty.recElimCo_path, hp]⟩
  | _, _, _, .ty_and_intro (p := p') (T := T) (U := U) d₁ d₂, p, e => by
      obtain ⟨P, hd₁, hp⟩ := HasTy.pathImage_path d₁ p' rfl
      obtain ⟨Q, hd₂, _⟩ := HasTy.pathImage_path d₂ p' rfl
      cases e
      exact ⟨.both T.telP U.telP (T.intoPath P) (U.intoPath Q), by simp only [HasTy.pathImage, hd₁, hd₂],
        by rw [FCn.PathCo.path, Ty.intoPath_path, hp]⟩
  | _, _, _, .ty_sub d e', p, e => by
      obtain ⟨P, hd, hp⟩ := HasTy.pathImage_path d p e
      exact ⟨.cast P e'.translate, by simp only [HasTy.pathImage, hd]; rfl, hp⟩

/-- The image of a derivation at a path term has that path. -/
theorem HasTy.translatePath_path {G : Ctx s} {p : Path s} {T : Ty s} (d : HasTy G (.path p) T) :
    d.translatePath.path = p := by
  obtain ⟨P, hd, hp⟩ := HasTy.pathImage_path d p rfl
  unfold HasTy.translatePath; rw [hd]; exact hp

end Nominal.Source
