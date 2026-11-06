import Coercions.Nominal.FCn.Consistency

/-!
# Canonical forms of the class primitive (`class_view`, `le_below`, `nominal_literal`, `seal_scope`)

The canonical forms of `seal`, `unseal` and the instance view over a typed store.  They are N1 to
N4 of design d3, as stage NT states them.

N1, `class_view`: a closed path at a class selection has an instance view, whose content is a view
at the class body.  N2, `le_below`: closed inclusion evidence into a type below a class either starts
below the class or holds a seal of a class below it (`Below`, `FormT.witness`).  N3,
`le_below_sealFree` and `nominal_literal`: a seal-free form reflects `Below`, so an inclusion from a
literal's type into a class selection holds a seal.  N4, `seal_scope`: in a context of opaque binders
every seal of a typed term names the self of a literal that encloses it.

A forged instance meets every conclusion: LE-Seal holds at every class of a stored literal, so a path
at a class body extends by the seal to a path at the class.  These are canonical forms, not
nominality, which plan XII states at the source (NOM-A and NOM-B).  `seal_scope` is a property of a
closed program before it runs: its hypothesis fails once the store holds a literal
(`Store.Typed.allOpaque_iff`), and its conclusion is not preserved by a step (`ClassEx.Forge`).
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## N1, the instance view at a class -/

/-- A closed path at a class selection has an instance view, whose content is a view at the body. -/
theorem class_view {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {p : Path s} {C : Label}
    {U : Ty s} (h : PathCo.HasType Γ P (.sel p C)) (hc : Γ.clsOf (.sel p C) = some U) :
    ∃ W, PV σ Γ P (.sel p C) (.inst W) ∧ ViewT Γ σ.erase P.path (Γ.res U) W := by
  obtain ⟨W, hPV, hW⟩ := h.view hσ
  unfold PViewT at hW
  rw [Ctx.res_cls hc] at hW
  obtain ⟨W', rfl, hW'⟩ := ViewT.cls_inv hW hc
  exact ⟨W', hPV, hW'⟩

/-- The same at a type that resolves to a class selection, an alias of the class among them. -/
theorem class_view_res {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {T : Ty s} {p : Path s}
    {C : Label} {U : Ty s} (h : PathCo.HasType Γ P T) (hT : Γ.res T = .sel p C)
    (hc : Γ.clsOf (.sel p C) = some U) :
    ∃ W, PV σ Γ P T (.inst W) ∧ ViewT Γ σ.erase P.path (Γ.res U) W := by
  obtain ⟨W, hPV, hW⟩ := h.view hσ
  unfold PViewT at hW
  rw [hT] at hW
  obtain ⟨W', rfl, hW'⟩ := ViewT.cls_inv hW hc
  exact ⟨W', hPV, hW'⟩

/-! ## Seals in a form -/

mutual
def Atom.seals : Atom s → List (Path s × Label)
  | .seal p C => [(p, C)]
  | .obj Es => Entries.seals Es
  | .pair F G => Form.seals F ++ Form.seals G
  | .into F => Form.seals F
  | .eqv _ => []
  | .pi _ _ => []
  | .top => []
  | .bot => []
  | .bnd _ => []
  | .unseal _ _ => []
def Form.seals : Form s → List (Path s × Label)
  | .nil => []
  | .cons A F => Atom.seals A ++ Form.seals F
def Entry.seals : Entry s → List (Path s × Label)
  | .le pre _ post => SideF.seals pre ++ SideF.seals post
  | .fld _ sd => SideF.seals sd
  | .alias _ => []
  | .is F => Form.seals F
def Entries.seals : Entries s → List (Path s × Label)
  | .nil => []
  | .cons Es e => Entries.seals Es ++ Entry.seals e
def SideF.seals : SideF s → List (Path s × Label)
  | .some F => Form.seals F
  | .none => []
  | .bot => []
  | .top => []
end

/-- The atom `seal q D` occurs in `F`, at any depth. -/
def Form.HasSeal (F : Form s) (q : Path s) (D : Label) : Prop := (q, D) ∈ Form.seals F
/-- No seal occurs in `F`. -/
def Form.sealFree (F : Form s) : Prop := Form.seals F = []

/-! ## `Below`: nominally below a class -/

/-- `Below Γ c C T`: `T` is nominally below the class `C` declared at the canonical path `c`. -/
inductive Below (Γ : Ctx s) (c : Path s) (C : Label) : Ty s → Prop
  | bot : Γ.res T = .bot → Below Γ c C T                                                    -- BL-Bot
  | self : Γ.res T = .sel q C → Γ.canon q = some c → Below Γ c C T                          -- BL-Self
  | up : Γ.res T = .sel q D → Γ.clsOf (.sel q D) = some U → Below Γ c C U → Below Γ c C T  -- BL-Up
  | is : Γ.res T = .mu Tel → Tel.At i (.is X.weaken) → Below Γ c C X → Below Γ c C T      -- BL-Is

section Below
variable {Γ : Ctx s} {c : Path s} {C : Label}

/-- `Below` moves backward along type equality evidence: at a selection by one normal type, at an
object type component by component (`SoundEq.res_mu`). -/
theorem Below.eqv {γ : PDot.Runtime.Store s} : ∀ {T : Ty s}, Below Γ c C T →
    ∀ {S : Ty s} {φ : EqCo s}, SoundEq Γ γ φ S T → Below Γ c C S
  | _, .bot hT, _, _, h => .bot (Γ.norm_res_bot h.norm hT)
  | _, .self hT hq, _, _, h => by
      obtain ⟨q', hS, hc⟩ := Γ.norm_res_sel h.norm hT
      exact .self hS (hc.trans hq)
  | _, .up hT hcl hU, _, _, h => by
      obtain ⟨q', hS, hc⟩ := Γ.norm_res_sel h.norm hT
      exact .up hS ((Γ.clsOf_sel_congr hc _).trans hcl) hU
  | _, .is hT hi hX, _, _, h => by
      obtain ⟨Tel₁, hS, r⟩ := (SoundEq.symm h).res_mu hT
      obtain ⟨pr', h₁, _, h₃⟩ := r.2 _ _ hi
      obtain ⟨X', ψ, e, hψ⟩ := h₃ _ rfl
      subst e
      exact .is hS h₁ (Below.eqv hX (SoundEq.symm hψ))

theorem Below.res_mu_inv {T : Ty s} {Tel : Telescope (s,x)} (h : Below Γ c C T) (hT : Γ.res T = .mu Tel) :
    ∃ i X, Tel.At i (.is X.weaken) ∧ Below Γ c C X := by
  cases h with
  | bot h' => rw [hT] at h'; cases h'
  | self h' _ => rw [hT] at h'; cases h'
  | up h' _ _ => rw [hT] at h'; cases h'
  | is h' hi hX => rw [hT] at h'; cases h'; exact ⟨_, _, hi, hX⟩

theorem Below.mu_inv {Tel : Telescope (s,x)} (h : Below Γ c C (.mu Tel)) :
    ∃ i X, Tel.At i (.is X.weaken) ∧ Below Γ c C X := h.res_mu_inv (Γ.res_mu Tel)

theorem Below.not_pi {S : Ty s} {T : Ty (s,x)} (h : Below Γ c C (.pi S T)) : False := by
  cases h with
  | bot h' => rw [Γ.res_pi] at h'; cases h'
  | self h' _ => rw [Γ.res_pi] at h'; cases h'
  | up h' _ _ => rw [Γ.res_pi] at h'; cases h'
  | is h' _ _ => rw [Γ.res_pi] at h'; cases h'

theorem not_below_top : ¬ Below Γ c C .top := fun h => by
  obtain ⟨_, _, hi, _⟩ := h.mu_inv
  exact Telescope.At.nil_of_eq hi rfl

/-- The self bounds `is X` of a telescope. -/
def Telescope.selfBounds : Telescope s → List (Pr s)
  | .nil => []
  | .cons Tel (.is X) => .is X :: Telescope.selfBounds Tel
  | .cons Tel (.le _ _) => Telescope.selfBounds Tel
  | .cons Tel (.fld _ _) => Telescope.selfBounds Tel
  | .cons Tel (.alias _) => Telescope.selfBounds Tel

theorem Telescope.not_at_is : ∀ {Tel : Telescope s}, Telescope.selfBounds Tel = [] →
    ∀ {i : Nat} {X : Ty s}, ¬ Tel.At i (.is X)
  | .nil, _, _, _, hi => Telescope.At.nil_of_eq hi rfl
  | .cons Tel pr, h, i, X, hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · subst e; simp [Telescope.selfBounds] at h
      · cases pr with
        | is _ => simp [Telescope.selfBounds] at h
        | le _ _ => exact Telescope.not_at_is (Tel := Tel) h hi'
        | fld _ _ => exact Telescope.not_at_is (Tel := Tel) h hi'
        | alias _ => exact Telescope.not_at_is (Tel := Tel) h hi'

/-- A type that resolves to an object type with no self bound is below no class. -/
theorem not_below_literal {S : Ty s} {Tel : Telescope (s,x)} (hS : Γ.res S = .mu Tel)
    (hTel : Telescope.selfBounds Tel = []) : ¬ Below Γ c C S := fun h => by
  obtain ⟨_, _, hi, _⟩ := h.res_mu_inv hS
  exact Telescope.not_at_is hTel hi

end Below

/-! ## N2, the witness theorem by induction on forms -/

section Witness
variable {Γ : Ctx s} {γ : PDot.Runtime.Store s} {c : Path s} {C : Label}

mutual
theorem AtomT.witness : ∀ {A : Atom s} {S M : Ty s}, AtomT Γ γ A S M → Below Γ c C M →
    Below Γ c C S ∨ ∃ q D, (q, D) ∈ Atom.seals A ∧ Below Γ c C (.sel q D)
  | _, _, _, .eqv h, hM => .inl (hM.eqv h)
  | _, _, _, .pi _ _, hM => hM.not_pi.elim
  | _, _, _, .obj hEs, hM => by
      obtain ⟨i, X, hi, hX⟩ := hM.mu_inv
      rcases EntriesT.witness hEs i X hi hX with h | ⟨q, D, hm, hb⟩
      · exact .inl h
      · exact .inr ⟨q, D, by simpa [Atom.seals] using hm, hb⟩
  | _, _, _, .top, hM => (not_below_top hM).elim
  | _, _, _, .bot, _ => .inl (.bot (Γ.res_bot))
  | _, _, _, .pair (Tel := Tel) (Tel' := Tel') hF hG, hM => by
      obtain ⟨i, X, hi, hX⟩ := hM.mu_inv
      rcases Telescope.At.of_append Tel Tel' hi with hi | ⟨j, _, hj⟩
      · rcases FormT.witness hF (.is (Γ.res_mu _) hi hX) with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Atom.seals, hm], hb⟩
      · rcases FormT.witness hG (.is (Γ.res_mu _) hj hX) with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Atom.seals, hm], hb⟩
  | _, _, _, .bnd hi, hM => .inl (.is (Γ.res_mu _) hi hM)
  | _, _, _, .into hF, hM => by
      obtain ⟨i, X, hi, hX⟩ := hM.mu_inv
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · rw [Ty.weaken_inj (Pr.is_inj e)] at hX
        rcases FormT.witness hF hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simpa [Atom.seals] using hm, hb⟩
      · exact (Telescope.At.nil_of_eq hi' rfl).elim
  | _, _, _, .seal (p := p) (C := D) _, hM => .inr ⟨p, D, by simp [Atom.seals], hM⟩
  | _, _, _, .unseal hc, hM => .inl (.up (Ctx.res_cls hc) hc hM)
theorem FormT.witness : ∀ {F : Form s} {S T : Ty s}, FormT Γ γ F S T → Below Γ c C T →
    Below Γ c C S ∨ ∃ q D, (q, D) ∈ Form.seals F ∧ Below Γ c C (.sel q D)
  | _, _, _, .nil, hT => .inl hT
  | _, _, _, .cons hA hF, hT => by
      rcases FormT.witness hF hT with hM | ⟨q, D, hm, hb⟩
      · rcases AtomT.witness hA hM with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Form.seals, hm], hb⟩
      · exact .inr ⟨q, D, by simp [Form.seals, hm], hb⟩
theorem EntriesT.witness : ∀ {src : Telescope (s,x)} {Es : Entries s} {Tel : Telescope (s,x)},
    EntriesT Γ γ src Es Tel → ∀ i X, Tel.At i (.is X.weaken) → Below Γ c C X →
    Below Γ c C (.mu src) ∨ ∃ q D, (q, D) ∈ Entries.seals Es ∧ Below Γ c C (.sel q D)
  | _, _, _, .nil, _, _, hi, _ => (Telescope.At.nil_of_eq hi rfl).elim
  | _, _, _, .le hEs _ _ _, i, X, hi, hX => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · rcases EntriesT.witness hEs i X hi' hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Entries.seals, hm], hb⟩
  | _, _, _, .fld hEs _ _, i, X, hi, hX => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · rcases EntriesT.witness hEs i X hi' hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Entries.seals, hm], hb⟩
  | _, _, _, .alias hEs _, i, X, hi, hX => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · rcases EntriesT.witness hEs i X hi' hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Entries.seals, hm], hb⟩
  | _, _, _, .is hEs hF, i, X, hi, hX => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · rw [Ty.weaken_inj (Pr.is_inj e)] at hX
        rcases FormT.witness hF hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Entries.seals, Entry.seals, hm], hb⟩
      · rcases EntriesT.witness hEs i X hi' hX with h | ⟨q, D, hm, hb⟩
        · exact .inl h
        · exact .inr ⟨q, D, by simp [Entries.seals, hm], hb⟩
end

/-- A seal-free typed form reflects `Below`. -/
theorem FormT.reflect {F : Form s} {S T : Ty s} (h : FormT Γ γ F S T) (hs : Form.sealFree F)
    (hT : Below Γ c C T) : Below Γ c C S := by
  rcases h.witness hT with h' | ⟨q, D, hm, _⟩
  · exact h'
  · unfold Form.sealFree at hs
    rw [hs] at hm
    cases hm

end Witness

/-! ## N2 and N3 over closed evidence -/

/-- N2: closed inclusion into a type below a class has a head normal form, and either the source is
below the class or the form holds a seal of a class below it. -/
theorem le_below {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {e : LeCo s} {S T : Ty s} {c : Path s}
    {C : Label} (h : LeCo.HasType Γ e S T) (hT : Below Γ c C T) :
    ∃ F, Hnf σ Γ e S T F ∧ (Below Γ c C S ∨ ∃ q D, Form.HasSeal F q D ∧ Below Γ c C (.sel q D)) := by
  obtain ⟨F, hH, hF⟩ := le_canon hσ h
  exact ⟨F, hH, hF.witness hT⟩

/-- N3: a seal-free closed inclusion reflects `Below`.  The form is the normalizer's, one per
evidence (`Hnf.det`). -/
theorem le_below_sealFree {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {e : LeCo s} {S T : Ty s} {F : Form s}
    {c : Path s} {C : Label} (h : LeCo.HasType Γ e S T) (hF : Hnf σ Γ e S T F) (hs : Form.sealFree F)
    (hT : Below Γ c C T) : Below Γ c C S := by
  obtain ⟨F', hH, hF'⟩ := le_canon hσ h
  cases Hnf.det hH hF
  exact hF'.reflect hs hT

/-- N3: a closed inclusion from a literal's type (an object type with no self bound) into a class
selection holds a seal of the class or of a class below it. -/
theorem nominal_literal {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {e : LeCo s} {S : Ty s} {p c : Path s}
    {C : Label} {Tel : Telescope (s,x)} (h : LeCo.HasType Γ e S (.sel p C)) (hc : Γ.canon p = some c)
    (hcl : (Γ.clsAt c C).isSome) (hS : Γ.res S = .mu Tel) (hTel : Telescope.selfBounds Tel = []) :
    ∃ F q D, Hnf σ Γ e S (.sel p C) F ∧ Form.HasSeal F q D ∧ Below Γ c C (.sel q D) := by
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 hcl
  have hcls : Γ.clsOf (.sel p C) = some U := by
    show (Γ.canon p).bind (fun c => Γ.clsAt c C) = some U
    rw [hc]; exact hU
  obtain ⟨F, hH, hb⟩ := le_below hσ h (.self (Ctx.res_cls hcls) hc)
  rcases hb with hb | ⟨q, D, hm, hqD⟩
  · exact absurd hb (not_below_literal hS hTel)
  · exact ⟨F, q, D, hH, hm, hqD⟩

/-! ## N4, seals in scope

A scope `ξ` marks the variables that are selves of enclosing literals.  `obj` adds its self in
scope.  `lam`, `let` and the codomain of `pi` add theirs out of scope.  `Tm.SealsScoped ξ t` says
that every `seal p C` in `t` has `ξ p.root = true`. -/

/-- Which variables are selves of literals that enclose the position. -/
abbrev Scope (s : Sig) := BVar s .var → Bool

def Scope.cons (ξ : Scope s) (b : Bool) : Scope (s,x)
  | .here => b
  | .there y => ξ y

mutual
def PEq.SealsScoped : Scope s → PEq s → Prop
  | _, .refl _ => True
  | ξ, .symm π => PEq.SealsScoped ξ π
  | ξ, .trans π π' => PEq.SealsScoped ξ π ∧ PEq.SealsScoped ξ π'
  | ξ, .sel π _ => PEq.SealsScoped ξ π
  | ξ, .member P e _ => PathCo.SealsScoped ξ P ∧ LeCo.SealsScoped ξ e
def PathCo.SealsScoped : Scope s → PathCo s → Prop
  | _, .var _ => True
  | ξ, .sel P _ _ => PathCo.SealsScoped ξ P
  | ξ, .cast P e => PathCo.SealsScoped ξ P ∧ LeCo.SealsScoped ξ e
  | ξ, .alias P₀ π Q => PathCo.SealsScoped ξ P₀ ∧ PEq.SealsScoped ξ π ∧ PathCo.SealsScoped ξ Q
  | ξ, .sngl P _ π => PathCo.SealsScoped ξ P ∧ PEq.SealsScoped ξ π
  | ξ, .fldI _ _ Q => PathCo.SealsScoped ξ Q
  | ξ, .fold _ P => PathCo.SealsScoped ξ P
  | ξ, .unfold P => PathCo.SealsScoped ξ P
  | ξ, .both _ _ P Q => PathCo.SealsScoped ξ P ∧ PathCo.SealsScoped ξ Q
def LeCo.SealsScoped : Scope s → LeCo s → Prop
  | _, .refl _ => True
  | ξ, .trans e f => LeCo.SealsScoped ξ e ∧ LeCo.SealsScoped ξ f
  | _, .top _ => True
  | _, .bot _ => True
  | ξ, .eqToLe φ => EqCo.SealsScoped ξ φ
  | ξ, .pi e f => LeCo.SealsScoped ξ e ∧ LeCo.SealsScoped (Scope.cons ξ false) f
  | ξ, .obj _ m => Morphism.SealsScoped ξ m
  | ξ, .pair _ _ e f => LeCo.SealsScoped ξ e ∧ LeCo.SealsScoped ξ f
  | _, .bound _ _ => True
  | ξ, .intoBnd e => LeCo.SealsScoped ξ e
  | ξ, .member P e _ => PathCo.SealsScoped ξ P ∧ LeCo.SealsScoped ξ e
  | ξ, .seal p _ => ξ p.root = true
def EqCo.SealsScoped : Scope s → EqCo s → Prop
  | _, .refl _ => True
  | ξ, .symm φ => EqCo.SealsScoped ξ φ
  | ξ, .trans φ ψ => EqCo.SealsScoped ξ φ ∧ EqCo.SealsScoped ξ ψ
  | _, .defP _ _ => True
  | ξ, .lift _ π => PEq.SealsScoped ξ π
  | ξ, .dom φ => EqCo.SealsScoped ξ φ
  | ξ, .cod φ _ => EqCo.SealsScoped ξ φ
def Morphism.SealsScoped : Scope s → Morphism s → Prop
  | _, .nil => True
  | ξ, .le m pre _ post => Morphism.SealsScoped ξ m ∧ Side.SealsScoped ξ pre ∧ Side.SealsScoped ξ post
  | ξ, .fld m _ sd => Morphism.SealsScoped ξ m ∧ Side.SealsScoped ξ sd
  | ξ, .alias m _ => Morphism.SealsScoped ξ m
  | ξ, .is m e => Morphism.SealsScoped ξ m ∧ LeCo.SealsScoped ξ e
def Side.SealsScoped : Scope s → Side s → Prop
  | _, .none => True
  | ξ, .some e => LeCo.SealsScoped ξ e
  | _, .bot _ => True
  | _, .top _ => True
end

mutual
def Tm.SealsScoped : Scope s → Tm s → Prop
  | ξ, .path P => PathCo.SealsScoped ξ P
  | ξ, .val v => Value.SealsScoped ξ v
  | ξ, .app P Q => PathCo.SealsScoped ξ P ∧ PathCo.SealsScoped ξ Q
  | ξ, .lett t u => Tm.SealsScoped ξ t ∧ Tm.SealsScoped (Scope.cons ξ false) u
  | ξ, .cast t e => Tm.SealsScoped ξ t ∧ LeCo.SealsScoped ξ e
def Value.SealsScoped : Scope s → Value s → Prop
  | ξ, .lam _ t => Tm.SealsScoped (Scope.cons ξ false) t
  | ξ, .obj _ ds => Defs.SealsScoped (Scope.cons ξ true) ds
  | ξ, .cast v e => Value.SealsScoped ξ v ∧ LeCo.SealsScoped ξ e
def Defs.SealsScoped : Scope s → Defs s → Prop
  | _, .nil => True
  | ξ, .typ ds _ _ => Defs.SealsScoped ξ ds
  | ξ, .fld ds _ rhs => Defs.SealsScoped ξ ds ∧ Rhs.SealsScoped ξ rhs
  | ξ, .cls ds _ _ => Defs.SealsScoped ξ ds
def Rhs.SealsScoped : Scope s → Rhs s → Prop
  | ξ, .path P => PathCo.SealsScoped ξ P
  | ξ, .fn v => Value.SealsScoped ξ v
  | ξ, .nest _ ds => Defs.SealsScoped ξ ds
end

/-- No binder of `Γ` has a block. -/
def Ctx.AllOpaque (Γ : Ctx s) : Prop := ∀ x, Γ.blockAt x = none

/-- The scope covers the context: every variable with a block is in scope. -/
def Scope.Covers (ξ : Scope s) (Γ : Ctx s) : Prop := ∀ x, Γ.blockAt x ≠ none → ξ x = true

theorem Scope.Covers.opaque {ξ : Scope s} {Γ : Ctx s} (h : Scope.Covers ξ Γ) (T : Ty s) :
    Scope.Covers (Scope.cons ξ false) (Γ.cons (.opaque T)) := fun
  | .here, hb => (hb rfl).elim
  | .there y, hb => h y (fun e => hb (by show (Γ.blockAt y).map _ = none; rw [e]; rfl))

theorem Scope.Covers.transparent {ξ : Scope s} {Γ : Ctx s} (h : Scope.Covers ξ Γ) (T : Ty s) (B : Block (s,x)) :
    Scope.Covers (Scope.cons ξ true) (Γ.cons (.transparent T B)) := fun
  | .here, _ => rfl
  | .there y, hb => h y (fun e => hb (by show (Γ.blockAt y).map _ = none; rw [e]; rfl))

theorem Ctx.nodeAt_root (Γ : Ctx s) : ∀ (p : Path s) (B : Block s), Γ.nodeAt p = some B → Γ.blockAt p.root ≠ none
  | .var y, B, h, e => by
      have h' : Γ.blockAt y = some B := h
      have e' : Γ.blockAt y = none := e
      rw [h'] at e'; cases e'
  | .sel p a, B, h, e => by
      have h' : (Γ.nodeAt p).bind (·.child a) = some B := h
      cases hp : Γ.nodeAt p with
      | none => rw [hp] at h'; cases h'
      | some B₀ => exact Ctx.nodeAt_root Γ p B₀ hp e

theorem Ctx.clsAt_root {Γ : Ctx s} {p : Path s} {C : Label} {U : Ty s} (h : Γ.clsAt p C = some U) :
    Γ.blockAt p.root ≠ none := by
  have h' : (Γ.nodeAt p).bind (·.cls C) = some U := h
  cases hp : Γ.nodeAt p with
  | none => rw [hp] at h'; cases h'
  | some B => exact Ctx.nodeAt_root Γ p B hp

mutual
theorem scoped_peq {Γ : Ctx s} : PEq.HasType Γ π p q → ∀ ξ, Scope.Covers ξ Γ → PEq.SealsScoped ξ π
  | .refl, _, _ => trivial
  | .symm h, ξ, hξ => scoped_peq h ξ hξ
  | .trans h₁ h₂, ξ, hξ => ⟨scoped_peq h₁ ξ hξ, scoped_peq h₂ ξ hξ⟩
  | .sel h, ξ, hξ => scoped_peq h ξ hξ
  | .member hP he _, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_le he ξ hξ⟩
theorem scoped_path {Γ : Ctx s} : PathCo.HasType Γ P T → ∀ ξ, Scope.Covers ξ Γ → PathCo.SealsScoped ξ P
  | .var _, _, _ => trivial
  | .sel hP _, ξ, hξ => scoped_path hP ξ hξ
  | .cast hP he, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_le he ξ hξ⟩
  | .alias h₀ hπ hQ, ξ, hξ => ⟨scoped_path h₀ ξ hξ, scoped_peq hπ ξ hξ, scoped_path hQ ξ hξ⟩
  | .sngl hP hπ, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_peq hπ ξ hξ⟩
  | .fldI hQ _, ξ, hξ => scoped_path hQ ξ hξ
  | .unfold hP, ξ, hξ => scoped_path hP ξ hξ
  | .fold hP, ξ, hξ => scoped_path hP ξ hξ
  | .both hP hQ _, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_path hQ ξ hξ⟩
theorem scoped_le {Γ : Ctx s} : LeCo.HasType Γ e S T → ∀ ξ, Scope.Covers ξ Γ → LeCo.SealsScoped ξ e
  | .refl, _, _ => trivial
  | .trans h₁ h₂, ξ, hξ => ⟨scoped_le h₁ ξ hξ, scoped_le h₂ ξ hξ⟩
  | .top, _, _ => trivial
  | .bot, _, _ => trivial
  | .eqToLe h, ξ, hξ => scoped_eq h ξ hξ
  | .pi (S₂ := S₂) he hf, ξ, hξ => ⟨scoped_le he ξ hξ, scoped_le hf _ (hξ.opaque S₂)⟩
  | .obj hm, ξ, hξ => scoped_mor hm ξ hξ
  | .pair h₁ h₂, ξ, hξ => ⟨scoped_le h₁ ξ hξ, scoped_le h₂ ξ hξ⟩
  | .bound _, _, _ => trivial
  | .intoBnd h, ξ, hξ => scoped_le h ξ hξ
  | .member hP he _, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_le he ξ hξ⟩
  | .seal h, _, hξ => hξ _ (Ctx.clsAt_root h)
theorem scoped_eq {Γ : Ctx s} : EqCo.HasType Γ φ S T → ∀ ξ, Scope.Covers ξ Γ → EqCo.SealsScoped ξ φ
  | .refl, _, _ => trivial
  | .symm h, ξ, hξ => scoped_eq h ξ hξ
  | .trans h₁ h₂, ξ, hξ => ⟨scoped_eq h₁ ξ hξ, scoped_eq h₂ ξ hξ⟩
  | .defP _, _, _ => trivial
  | .lift hπ, ξ, hξ => scoped_peq hπ ξ hξ
  | .dom h, ξ, hξ => scoped_eq h ξ hξ
  | .cod h, ξ, hξ => scoped_eq h ξ hξ
theorem scoped_mor {Γ : Ctx s} : Morphism.HasType Γ src m Tel → ∀ ξ, Scope.Covers ξ Γ →
    Morphism.SealsScoped ξ m
  | .nil, _, _ => trivial
  | .le hm _ hpre hpost, ξ, hξ => ⟨scoped_mor hm ξ hξ, scoped_side hpre ξ hξ, scoped_side hpost ξ hξ⟩
  | .fld hm _ hsd, ξ, hξ => ⟨scoped_mor hm ξ hξ, scoped_side hsd ξ hξ⟩
  | .alias hm _, ξ, hξ => scoped_mor hm ξ hξ
  | .is hm he, ξ, hξ => ⟨scoped_mor hm ξ hξ, scoped_le he ξ hξ⟩
theorem scoped_side {Γ : Ctx s} : Side.HasType Γ sd X Y → ∀ ξ, Scope.Covers ξ Γ → Side.SealsScoped ξ sd
  | .none, _, _ => trivial
  | .some he, ξ, hξ => scoped_le he ξ hξ
  | .bot, _, _ => trivial
  | .top, _, _ => trivial
end

mutual
theorem scoped_tm {Γ : Ctx s} : Tm.HasType Γ t T → ∀ ξ, Scope.Covers ξ Γ → Tm.SealsScoped ξ t
  | .path hP, ξ, hξ => scoped_path hP ξ hξ
  | .val hv, ξ, hξ => scoped_val hv ξ hξ
  | .app hP hQ, ξ, hξ => ⟨scoped_path hP ξ hξ, scoped_path hQ ξ hξ⟩
  | .lett (T := T₀) ht hu, ξ, hξ => ⟨scoped_tm ht ξ hξ, scoped_tm hu _ (hξ.opaque T₀)⟩
  | .cast ht he, ξ, hξ => ⟨scoped_tm ht ξ hξ, scoped_le he ξ hξ⟩
theorem scoped_val {Γ : Ctx s} : Value.HasType Γ v T → ∀ ξ, Scope.Covers ξ Γ → Value.SealsScoped ξ v
  | .lam (S := S) ht, ξ, hξ => scoped_tm ht _ (hξ.opaque S)
  | .obj (Tel := Tel) (ds := ds) hds, ξ, hξ => scoped_defs hds _ (hξ.transparent (.mu Tel) ds.block)
  | .cast hv he, ξ, hξ => ⟨scoped_val hv ξ hξ, scoped_le he ξ hξ⟩
theorem scoped_defs {Γ : Ctx s} : Defs.HasType Γ p ds Tel → ∀ ξ, Scope.Covers ξ Γ → Defs.SealsScoped ξ ds
  | .nil, _, _ => trivial
  | .typ hds _ _, ξ, hξ => scoped_defs hds ξ hξ
  | .path hds _ hP _, ξ, hξ => ⟨scoped_defs hds ξ hξ, scoped_path hP ξ hξ⟩
  | .fn hds _ _ hv, ξ, hξ => ⟨scoped_defs hds ξ hξ, scoped_val hv ξ hξ⟩
  | .nest hds _ hds', ξ, hξ => ⟨scoped_defs hds ξ hξ, scoped_defs hds' ξ hξ⟩
  | .cls hds _ _, ξ, hξ => scoped_defs hds ξ hξ
end

/-- N4: in a context of opaque binders every seal of a typed term reads the self of a literal that
encloses it. -/
theorem seal_scope {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : Tm.HasType Γ t T) (hΓ : Ctx.AllOpaque Γ) :
    Tm.SealsScoped (fun _ => false) t :=
  scoped_tm h _ (fun x hb => (hb (hΓ x)).elim)

/-- Over a typed store the context is all opaque exactly when the store holds no literal. -/
theorem Store.Typed.allOpaque_iff {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    Ctx.AllOpaque Γ ↔ ∀ x, ∃ S t, σ.get x = .lam S t := by
  constructor
  · intro hA x
    rcases hσ.get_shape x with ⟨S, t, _, e, _, _⟩ | ⟨_, _, _, _, hb⟩
    · exact ⟨S, t, e⟩
    · rw [hA x] at hb; cases hb
  · intro hL x
    rcases hσ.get_shape x with ⟨_, _, _, _, _, hb⟩ | ⟨_, _, e, _, _⟩
    · exact hb
    · obtain ⟨_, _, e'⟩ := hL x
      rw [e] at e'; cases e'

end Nominal.FCn
