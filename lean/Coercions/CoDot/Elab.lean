import Coercions.CoDot.Term

/-!
# Elaboration: every DOT-MNF derivation is annotated at the same type

Erasure deletes all coercions. The source is `DotMNF/Typing.lean`, unchanged:
subsumption on every term, unrestricted intersections, `Rec-I`/`Rec-E`/`And-I`
on variables with arbitrary bodies, contexts with bad bounds. There is no
side condition on the source derivation.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-! ## Erasure -/

mutual

def Tm.erase : Tm s → DotMNF.Tm s
  | .ref x _ => .path (.var x)
  | .val v _ => .val v.erase
  | .app x _ y _ => .app x y
  | .proj x _ a => .proj x a
  | .let t u => .let t.erase u.erase
  | .cast t _ => t.erase

def Value.erase : Value s → DotMNF.Value s
  | .obj d => .obj d.erase
  | .lam S t => .lam S t.erase

def Defs.erase : Defs s → DotMNF.Defs s
  | .typ A T => .typ A T
  | .trm a t => .trm a t.erase
  | .and d1 d2 => .and d1.erase d2.erase

end

/-- A DOT-MNF context as a context of the coercion calculus: the same type
for every variable. A self binder of an object literal is at `μ(T)`. -/
def ofDot (Γ : DotMNF.Ctx s) : Ctx s := ⟨Γ.lookup⟩

/-! ## Elaboration -/

theorem ofDot_cons (Γ : DotMNF.Ctx s) (S : Ty s) :
    ofDot (Γ.cons S) = (ofDot Γ).cons S := by
  unfold ofDot Ctx.cons
  congr 1
  funext y
  cases y <;> rfl

theorem ofDot_consSelf (Γ : DotMNF.Ctx s) (d : DotMNF.Defs (s,x)) (T : Ty (s,x)) :
    ofDot (Γ.consSelf d T) = (ofDot Γ).cons (.mu T) := by
  unfold ofDot Ctx.cons
  congr 1
  funext y
  cases y <;> rfl

theorem Defs.erase_labels : (d : Defs s) → d.erase.labels = d.labels
  | .typ _ _ | .trm _ _ => rfl
  | .and d1 d2 => by
    show d1.erase.labels ++ d2.erase.labels = d1.labels ++ d2.labels
    rw [Defs.erase_labels d1, Defs.erase_labels d2]

mutual

theorem elab_sub_aux {Γ : DotMNF.Ctx s} {S T : Ty s} :
    DotMNF.Sub Γ S T → ∃ c, CoTy (ofDot Γ) none c S T
  | .top => ⟨_, .top⟩
  | .bot => ⟨_, .bot⟩
  | .refl => ⟨_, .id⟩
  | .trans h1 h2 =>
    let ⟨c1, k1⟩ := elab_sub_aux h1
    let ⟨c2, k2⟩ := elab_sub_aux h2
    ⟨_, .seq k1 k2⟩
  | .and1 => ⟨_, .andL .id⟩
  | .and2 => ⟨_, .andR .id⟩
  | .and h1 h2 =>
    let ⟨c1, k1⟩ := elab_sub_aux h1
    let ⟨c2, k2⟩ := elab_sub_aux h2
    ⟨_, .pair k1 k2⟩
  | .fld h =>
    let ⟨c, k⟩ := elab_sub_aux h
    ⟨_, .fld k⟩
  | .typ h1 h2 =>
    let ⟨c1, k1⟩ := elab_sub_aux h1
    let ⟨c2, k2⟩ := elab_sub_aux h2
    ⟨_, .typ k1 k2⟩
  | .selUpper h =>
    let ⟨c, k⟩ := elab_var_aux h _ rfl
    ⟨_, .up k⟩
  | .selLower h =>
    let ⟨c, k⟩ := elab_var_aux h _ rfl
    ⟨_, .down k⟩
  | .all h1 h2 => by
    obtain ⟨c1, k1⟩ := elab_sub_aux h1
    obtain ⟨c2, k2⟩ := elab_sub_aux h2
    rw [ofDot_cons] at k2
    exact ⟨_, .all k1 k2⟩

theorem elab_var_aux {Γ : DotMNF.Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    DotMNF.HasTy Γ t T → ∀ x, t = .path (.var x) →
      ∃ c, CoTy (ofDot Γ) (some x) c ((ofDot Γ).lookup x) T
  | .var, _, e => by cases e; exact ⟨_, .id⟩
  | .lam _, _, e => by cases e
  | .app _ _, _, e => by cases e
  | .obj _ _, _, e => by cases e
  | .proj _, _, e => by cases e
  | .let _ _, _, e => by cases e
  | .recI h, _, e => by
    cases e
    obtain ⟨c, k⟩ := elab_var_aux h _ rfl
    exact ⟨_, .seq k .fold⟩
  | .recE h, _, e => by
    cases e
    obtain ⟨c, k⟩ := elab_var_aux h _ rfl
    exact ⟨_, .seq k .unfold⟩
  | .andI h1 h2, _, e => by
    cases e
    obtain ⟨c1, k1⟩ := elab_var_aux h1 _ rfl
    obtain ⟨c2, k2⟩ := elab_var_aux h2 _ rfl
    exact ⟨_, .pair k1 k2⟩
  | .sub h hs, x, e => by
    obtain ⟨c1, k1⟩ := elab_var_aux h x e
    obtain ⟨c2, k2⟩ := elab_sub_aux hs
    exact ⟨_, .seq k1 (k2.anySubject _)⟩

theorem elab_tm_aux {Γ : DotMNF.Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    DotMNF.HasTy Γ t T → ∃ t', Typed (ofDot Γ) (.tm t' T) ∧ t'.erase = t
  | .var => ⟨_, .ref .id, rfl⟩
  | .recI h => by
    obtain ⟨c, k⟩ := elab_var_aux h _ rfl
    exact ⟨_, .ref (.seq k .fold), rfl⟩
  | .recE h => by
    obtain ⟨c, k⟩ := elab_var_aux h _ rfl
    exact ⟨_, .ref (.seq k .unfold), rfl⟩
  | .andI h1 h2 => by
    obtain ⟨c1, k1⟩ := elab_var_aux h1 _ rfl
    obtain ⟨c2, k2⟩ := elab_var_aux h2 _ rfl
    exact ⟨_, .ref (.pair k1 k2), rfl⟩
  | .lam h => by
    obtain ⟨t', ht, he⟩ := elab_tm_aux h
    rw [ofDot_cons] at ht
    exact ⟨.val (.lam _ t') .id, .val (.lam ht) .id, by simp [Tm.erase, Value.erase, he]⟩
  | .obj h hd => by
    obtain ⟨d', ht, he⟩ := elab_defs_aux h hd
    rw [ofDot_consSelf] at ht
    exact ⟨.val (.obj d') .id, .val (.obj ht) .id, by simp [Tm.erase, Value.erase, he]⟩
  | .app hx hy => by
    obtain ⟨c1, k1⟩ := elab_var_aux hx _ rfl
    obtain ⟨c2, k2⟩ := elab_var_aux hy _ rfl
    exact ⟨_, .app k1 k2, rfl⟩
  | .proj hx => by
    obtain ⟨c, k⟩ := elab_var_aux hx _ rfl
    exact ⟨_, .proj k, rfl⟩
  | .let h1 h2 => by
    obtain ⟨t', ht, he⟩ := elab_tm_aux h1
    obtain ⟨u', hu, hue⟩ := elab_tm_aux h2
    rw [ofDot_cons] at hu
    exact ⟨.let t' u', .let ht hu, by simp [Tm.erase, he, hue]⟩
  | .sub h hs => by
    obtain ⟨t', ht, he⟩ := elab_tm_aux h
    obtain ⟨c, k⟩ := elab_sub_aux hs
    exact ⟨.cast t' c, .cast ht k, by simp [Tm.erase, he]⟩

theorem elab_defs_aux {Γ : DotMNF.Ctx s} {d : DotMNF.Defs s} {T : Ty s} :
    DotMNF.DefsTy Γ d T → DotMNF.Defs.Distinct d →
      ∃ d', Typed (ofDot Γ) (.defs d' T) ∧ d'.erase = d
  | .typ, _ => ⟨.typ _ _, .dtyp, rfl⟩
  | .trm h, _ => by
    obtain ⟨t', ht, he⟩ := elab_tm_aux h
    exact ⟨.trm _ t', .dtrm ht, by simp [Defs.erase, he]⟩
  | .and h1 h2, hd => by
    cases hd with
    | and hd1 hd2 hdis =>
    obtain ⟨d1', ht1, he1⟩ := elab_defs_aux h1 hd1
    obtain ⟨d2', ht2, he2⟩ := elab_defs_aux h2 hd2
    refine ⟨.and d1' d2', .dand ht1 ht2 ?_, by simp [Defs.erase, he1, he2]⟩
    intro ℓ h1 h2
    rw [← Defs.erase_labels, he1] at h1
    rw [← Defs.erase_labels, he2] at h2
    exact hdis ℓ h1 h2

end

/-- A subtyping derivation is a coercion for any subject. -/
theorem elab_sub {Γ : DotMNF.Ctx s} {S T : Ty s} (h : DotMNF.Sub Γ S T) :
    ∃ c, CoTy (ofDot Γ) none c S T :=
  elab_sub_aux h

/-- A typing derivation of a variable is a coercion on its context type, with
that variable as subject. `And-I` is `pair`, `Rec-I`/`Rec-E` are
`fold`/`unfold`, subsumption is `seq`. -/
theorem elab_var {Γ : DotMNF.Ctx s} {x : BVar s .var} {T : Ty s}
    (h : DotMNF.HasTy Γ (.path (.var x)) T) :
    ∃ c, CoTy (ofDot Γ) (some x) c ((ofDot Γ).lookup x) T :=
  elab_var_aux h x rfl

/-- Every typing derivation has an annotation at the same type that erases to
the same term. -/
theorem elab_tm {Γ : DotMNF.Ctx s} {t : DotMNF.Tm s} {T : Ty s} (h : DotMNF.HasTy Γ t T) :
    ∃ t', Typed (ofDot Γ) (.tm t' T) ∧ t'.erase = t :=
  elab_tm_aux h

/-- Definition typing, for definitions with distinct labels (the premise of
`{}-I` in DOT-MNF). -/
theorem elab_defs {Γ : DotMNF.Ctx s} {d : DotMNF.Defs s} {T : Ty s}
    (h : DotMNF.DefsTy Γ d T) (hd : DotMNF.Defs.Distinct d) :
    ∃ d', Typed (ofDot Γ) (.defs d' T) ∧ d'.erase = d :=
  elab_defs_aux h hd

/-- Closed programs. -/
theorem elaboration {t : DotMNF.Tm []} {T : Ty []} (h : DotMNF.HasTy .nil t T) :
    ∃ t', Typed (ofDot .nil) (.tm t' T) ∧ t'.erase = t :=
  elab_tm h

end CoDot
