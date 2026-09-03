import Coercions.FCdot.CanonicalDepth
import Coercions.FCdot.CanonicalMono

/-!
# Typedness of `Form.combine`

`Form.combine` composes the head forms of two composable coercions.  This
file proves that composition preserves typedness at every depth: if `F` is
typed from `S` to `M` and `G` from `M` to `T`, then `F.combine G` is typed
from `S` to `T`.

The interesting cases are the object ones.  Concatenating chains is
`ChainWellTyped_append` syntactically and `applyChain_append_of`
operationally; the bookkeeping is in the threshold and the fuel bound of the
applicative clause.  Running `cs₁ ++ cs₂` on an input of depth `j'` runs
`cs₁` at `j'` and then `cs₂` at `j' - fuelLoss n₁`, so the composite
threshold must clear the *worst* loss of the first half: `t := max t₁ (t₂ +
fuelLoss N₁)`.  The composite fuel bound is `N₁ + N₂ + cs₁.length`, and the
composite loss is absorbed because `fuelLoss` is superadditive
(`fuelLoss_add_le'`).

One pair of forms is *not* composed soundly by `Form.combine`: an equality
form followed by `bot`.  The equation `| F, _ => F` keeps the equality
`φ : S = M`, which is evidence for the wrong endpoints — the composite must
go from `S` to `T`, and nothing constrains `T`.  `Form.Combinable` excludes
exactly that pair; `Form.combine_eqv_bot_resolve` shows that the form
`Form.combine` *should* return there (`.bot`) is typed, so adding the arm
`| .eqv _, .bot => .bot` to `Form.combine` would make the hypothesis
unnecessary.
-/

namespace FCdot

section

variable {s : Sig}

/-! ## Equations of `Form.combine` -/

@[simp] theorem Form.combine_top_left (G : Form s) :
    (Form.top : Form s).combine G = .top := by
  cases G <;> rfl

@[simp] theorem Form.combine_eqv_top (φ : EqCo s) :
    (Form.eqv φ).combine .top = .top := rfl

@[simp] theorem Form.combine_pi_top (d : LeCo s) (c : LeCo (s,x)) :
    (Form.pi d c).combine .top = .top := rfl

@[simp] theorem Form.combine_obj_top (cs : List (ChainStep s)) :
    (Form.obj cs).combine .top = .top := rfl

@[simp] theorem Form.combine_eqv_eqv (φ ψ : EqCo s) :
    (Form.eqv φ).combine (.eqv ψ) = .eqv (.trans φ ψ) := rfl

@[simp] theorem Form.combine_eqv_pi (φ : EqCo s) (d : LeCo s) (c : LeCo (s,x)) :
    (Form.eqv φ).combine (.pi d c) = .pi d c := rfl

@[simp] theorem Form.combine_pi_eqv (d : LeCo s) (c : LeCo (s,x)) (ψ : EqCo s) :
    (Form.pi d c).combine (.eqv ψ) = .pi d c := rfl

@[simp] theorem Form.combine_eqv_obj (φ : EqCo s) (cs : List (ChainStep s)) :
    (Form.eqv φ).combine (.obj cs) = .obj (.conv φ :: cs) := rfl

@[simp] theorem Form.combine_obj_eqv (cs : List (ChainStep s)) (ψ : EqCo s) :
    (Form.obj cs).combine (.eqv ψ) = .obj (cs ++ [.conv ψ]) := rfl

@[simp] theorem Form.combine_pi_pi (d₁ : LeCo s) (c₁ : LeCo (s,x))
    (d₂ : LeCo s) (c₂ : LeCo (s,x)) :
    (Form.pi d₁ c₁).combine (.pi d₂ c₂)
      = .pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂.weaken)) c₂) := rfl

@[simp] theorem Form.combine_obj_obj (cs₁ cs₂ : List (ChainStep s)) :
    (Form.obj cs₁).combine (.obj cs₂) = .obj (cs₁ ++ cs₂) := rfl

@[simp] theorem Form.combine_eqv_bot (φ : EqCo s) :
    (Form.eqv φ).combine .bot = .bot := rfl

@[simp] theorem Form.combine_pi_bot (d : LeCo s) (c : LeCo (s,x)) :
    (Form.pi d c).combine .bot = .pi d c := rfl

@[simp] theorem Form.combine_obj_bot (cs : List (ChainStep s)) :
    (Form.obj cs).combine .bot = .obj cs := rfl

@[simp] theorem Form.combine_pi_obj (d : LeCo s) (c : LeCo (s,x)) (cs : List (ChainStep s)) :
    (Form.pi d c).combine (.obj cs) = .pi d c := rfl

@[simp] theorem Form.combine_obj_pi (cs : List (ChainStep s)) (d : LeCo s) (c : LeCo (s,x)) :
    (Form.obj cs).combine (.pi d c) = .obj cs := rfl

/-! ## Atoms under a chain -/

@[simp] theorem Atom.root_cast (a : Atom s) (e : LeCo s) :
    (Atom.cast a e).root = a.root := rfl

/-- `chainAtom` (`CanonicalMono`) and `chainAtom'` (`CanonicalDepth`) are the
same function. -/
theorem ChainStep.chainAtom_eq_chainAtom' :
    ∀ (cs : List (ChainStep s)) (a : Atom s),
      ChainStep.chainAtom cs a = ChainStep.chainAtom' cs a
  | [], _ => rfl
  | c :: cs, a => by
      simp [ChainStep.chainAtom_eq_chainAtom' cs]

/-- Casting through a chain never changes the root. -/
@[simp] theorem ChainStep.chainAtom_root :
    ∀ (cs : List (ChainStep s)) (a : Atom s),
      (ChainStep.chainAtom cs a).root = a.root
  | [], _ => rfl
  | c :: cs, a => by
      simp [ChainStep.chainAtom_root cs]

/-! ## Views only see the root of their atom -/

theorem ViewTypedWith_root {σ : Store s} {Γ : Ctx s} {FT : Form s → Ty s → Ty s → Prop}
    {V : View s} {Tel : Telescope (s,x)} {a b : Atom s} (h : a.root = b.root)
    (hV : ViewTypedWith σ Γ FT V Tel a) : ViewTypedWith σ Γ FT V Tel b := by
  intro i P hP
  rw [← h]
  exact hV i P hP

/-- Typedness of a view transfers along a cast of its self atom. -/
theorem ViewTypedWith_cast {σ : Store s} {Γ : Ctx s} {FT : Form s → Ty s → Ty s → Prop}
    {V : View s} {Tel : Telescope (s,x)} {a : Atom s} {e : LeCo s}
    (hV : ViewTypedWith σ Γ FT V Tel a) : ViewTypedWith σ Γ FT V Tel (.cast a e) :=
  ViewTypedWith_root rfl hV

/-! ## The fuel-loss budget is superadditive -/

/-- Splitting an application in two never loses more depth than doing it in
one go: `(2^a - 1) + (2^b - 1) ≤ 2^(a+b) - 1`. -/
theorem fuelLoss_add_le' : ∀ (a b : Nat), fuelLoss a + fuelLoss b ≤ fuelLoss (a + b)
  | _, 0 => by simp
  | a, b + 1 => by
      have ih := fuelLoss_add_le' a b
      have h1 := fuelLoss_succ b
      have h2 := fuelLoss_succ (a + b)
      have h3 : a + (b + 1) = (a + b) + 1 := rfl
      rw [h3]
      omega

/-! ## The one pair `Form.combine` does not compose -/

/-- `Form.combine` composes soundly on every pair of forms except an
equality form followed by `bot`. -/
def Form.Combinable : Form s → Form s → Prop
  | .eqv _, .bot => False
  | _, _ => True

theorem Form.combinable_of_ne_bot {F G : Form s} (h : G ≠ .bot) : F.Combinable G := by
  cases F <;> cases G <;> first | trivial | exact absurd rfl h

theorem Form.combinable_bot_left (G : Form s) : (Form.bot : Form s).Combinable G := by
  cases G <;> trivial

theorem Form.combinable_id_left (G : Form s) : (Form.id : Form s).Combinable G := by
  cases G <;> trivial

theorem Form.combinable_top_left (G : Form s) : (Form.top : Form s).Combinable G := by
  cases G <;> trivial

theorem Form.combinable_pi_left (d : LeCo s) (c : LeCo (s,x)) (G : Form s) :
    (Form.pi d c).Combinable G := by
  cases G <;> trivial

theorem Form.combinable_obj_left (cs : List (ChainStep s)) (G : Form s) :
    (Form.obj cs).Combinable G := by
  cases G <;> trivial

end

/-! ## A self-cast substitution between opaque binders

`Form.combine` on two function forms retypes the first codomain evidence
under the *second* source's domain binder, by casting the binder through the
composite domain evidence.  `Subst.Typed.selfCast` (`Preservation.lean`)
does this for a transparent target binder; the version needed here has an
opaque one. -/

theorem Subst.Typed.selfCastOpaque {s : Sig} {Γ : Ctx s} {S₀ T : Ty s} {E : LeCo s}
    (hE : LeCo.HasType Γ E S₀ T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.selfCast E.weaken) (Γ.cons (.opaque S₀)) where
  var := by
    intro y
    cases y with
    | here =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.cast (.var .here) E.weaken)
          (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.selfCast E.weaken).root)
        have hE' : LeCo.HasType (Γ.cons (.opaque S₀)) E.weaken S₀.weaken T.weaken :=
          hE.weaken _
        have hvar : Atom.HasType (Γ.cons (.opaque S₀)) (.var .here) S₀.weaken := by
          simpa [Binding.ty] using
            Atom.HasType.var (Γ := Γ.cons (.opaque S₀)) (x := .here)
        simpa [Binding.ty] using Atom.HasType.cast hvar hE'
    | there z =>
        show Atom.HasType (Γ.cons (.opaque S₀)) (.var (.there z))
          (((Γ.cons (.opaque T)).lookupTy (.there z)).rename (Subst.selfCast E.weaken).root)
        simpa using Atom.HasType.var (Γ := Γ.cons (.opaque S₀)) (x := .there z)
  ty := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simp
  transparent := by
    intro y ht
    cases y with
    | here => simp at ht
    | there z => simpa using (Ctx.isTransparent_there Γ _ z).mp ht
  def_ := by
    intro y l W hW
    cases y with
    | here => simp at hW
    | there z =>
        rw [Ctx.lookupDef_there] at hW
        simpa using hW
  fields := by
    intro y Fs hFs
    cases y with
    | here => simp at hFs
    | there z =>
        rw [Ctx.lookupFields_there] at hFs
        simpa using hFs

/-! ## Typedness of `Form.combine` -/

section

variable {s : Sig} {σ : Store s} {Γ : Ctx s}

/-- The excluded pair: an equality form followed by `bot` composes to `bot`,
the form `Form.combine` does not currently return. -/
theorem Form.combine_eqv_bot_resolve {k : Nat} {φ : EqCo s} {S M T : Ty s}
    (hF : FormTyped σ Γ k (.eqv φ) S M) (hG : FormTyped σ Γ k .bot M T) :
    FormTyped σ Γ k .bot S T := by
  rw [FormTyped] at hF
  rw [FormTyped] at hG
  rw [FormTyped]
  exact hF.2.trans hG

/-- Composition of head forms preserves typedness at every depth. -/
theorem Form.combine_typed {k : Nat} {F G : Form s} {S M T : Ty s}
    (hF : FormTyped σ Γ k F S M) (hG : FormTyped σ Γ k G M T) :
    FormTyped σ Γ k (F.combine G) S T := by
  cases F with
  | bot =>
      rw [Form.combine_bot, FormTyped]
      rw [FormTyped] at hF
      exact hF
  | id =>
      rw [FormTyped] at hF
      subst hF
      rw [Form.combine_id_left]
      exact hG
  | top =>
      rw [Form.combine_top_left, FormTyped]
      rw [FormTyped] at hF
      have hG0 := FormTyped_shape_mono hG
      cases G with
      | bot =>
          rw [FormTyped] at hG0
          rw [hF] at hG0
          exact absurd hG0 (by simp)
      | top => rw [FormTyped] at hG0; exact hG0
      | id => rw [FormTyped] at hG0; subst hG0; exact hF
      | eqv ψ =>
          rw [FormTyped] at hG0
          rw [← hG0.2]
          exact hF
      | pi d c =>
          rw [FormTyped] at hG0
          obtain ⟨_, _, _, _, hM, _, _, _⟩ := hG0
          rw [hF] at hM
          exact absurd hM (by simp)
      | obj cs =>
          rw [FormTyped] at hG0
          obtain ⟨_, _, hM, _, _⟩ := hG0
          rw [hF] at hM
          exact absurd hM (by simp)
  | eqv φ =>
      rw [FormTyped] at hF
      obtain ⟨hφ, hres⟩ := hF
      cases G with
      | bot =>
          rw [Form.combine_eqv_bot, FormTyped]
          rw [FormTyped] at hG
          exact hres.trans hG
      | top =>
          rw [Form.combine_eqv_top, FormTyped]
          rw [FormTyped] at hG
          exact hG
      | id =>
          rw [FormTyped] at hG
          subst hG
          rw [Form.combine_id_right, FormTyped]
          exact ⟨hφ, hres⟩
      | eqv ψ =>
          rw [FormTyped] at hG
          rw [Form.combine_eqv_eqv, FormTyped]
          exact ⟨.trans hφ hG.1, hres.trans hG.2⟩
      | pi d c =>
          rw [FormTyped] at hG
          obtain ⟨S₁, T₁, S₂, T₂, hM, hT, hd, hcod⟩ := hG
          rw [Form.combine_eqv_pi, FormTyped]
          exact ⟨S₁, T₁, S₂, T₂, hres.trans hM, hT, hd, hcod⟩
      | obj cs =>
          rw [Form.combine_eqv_obj]
          cases k with
          | zero =>
              rw [FormTyped] at hG
              obtain ⟨Tel₁, Tel₂, hM, hT, hchain⟩ := hG
              rw [FormTyped]
              exact ⟨Tel₁, Tel₂, hres.trans hM, hT, M, hφ, hres, hchain⟩
          | succ j =>
              rw [FormTyped] at hG
              obtain ⟨Tel₁, Tel₂, hM, hT, hchain, hcl⟩ := hG
              rw [FormTyped]
              refine ⟨Tel₁, Tel₂, hres.trans hM, hT, ⟨M, hφ, hres, hchain⟩, fun a ha V => ?_⟩
              have ha' : Atom.HasType Γ (.cast a (.eqToLe φ)) M :=
                Atom.HasType.cast ha (.eqToLe hφ)
              obtain ⟨t, L, hcl'⟩ := hcl _ ha' V
              refine ⟨t, L, fun j' ht hj hV => ?_⟩
              obtain ⟨n, V', happ, hV'⟩ := hcl' j' ht hj (ViewTypedWith_cast hV)
              refine ⟨n + 1, V', ?_, ViewTypedWith_root rfl hV'⟩
              rw [applyChain_cons_conv]
              exact happ
  | pi d c =>
      rw [FormTyped] at hF
      obtain ⟨S₁, T₁, S₂, T₂, hS, hM, hd, hcod⟩ := hF
      have hG0 := FormTyped_shape_mono hG
      cases G with
      | bot =>
          rw [FormTyped] at hG0
          rw [hM] at hG0
          exact absurd hG0 (by simp)
      | top =>
          rw [Form.combine_pi_top, FormTyped]
          rw [FormTyped] at hG
          exact hG
      | id =>
          rw [FormTyped] at hG
          subst hG
          rw [Form.combine_id_right, FormTyped]
          exact ⟨S₁, T₁, S₂, T₂, hS, hM, hd, hcod⟩
      | eqv ψ =>
          rw [FormTyped] at hG
          rw [Form.combine_pi_eqv, FormTyped]
          exact ⟨S₁, T₁, S₂, T₂, hS, hG.2.symm.trans hM, hd, hcod⟩
      | obj cs =>
          rw [FormTyped] at hG0
          obtain ⟨_, _, hM', _, _⟩ := hG0
          rw [hM] at hM'
          exact absurd hM' (by simp)
      | pi d₂ c₂ =>
          rw [FormTyped] at hG
          obtain ⟨S₁', T₁', S₂', T₂', hM', hT, hd₂, hc₂⟩ := hG
          injection hM.symm.trans hM' with _ hs ht
          subst hs
          subst ht
          rw [Form.combine_pi_pi, FormTyped]
          refine ⟨S₁, T₁, S₂', T₂', hS, hT, .trans hd₂ hd, .trans ?_ hc₂⟩
          have hsub := LeCo.HasType.subst (Subst.Typed.selfCastOpaque hd₂) hcod
          simpa using hsub
  | obj cs =>
      have hF0 := FormTyped_shape_mono hF
      cases G with
      | bot =>
          rw [FormTyped] at hF0
          rw [FormTyped] at hG
          obtain ⟨_, _, _, hM, _⟩ := hF0
          rw [hM] at hG
          exact absurd hG (by simp)
      | top =>
          rw [Form.combine_obj_top, FormTyped]
          rw [FormTyped] at hG
          exact hG
      | id =>
          rw [FormTyped] at hG
          subst hG
          rw [Form.combine_id_right]
          exact hF
      | pi d₂ c₂ =>
          rw [FormTyped] at hF0
          rw [FormTyped] at hG
          obtain ⟨_, _, _, hM, _⟩ := hF0
          obtain ⟨_, _, _, _, hM', _, _, _⟩ := hG
          rw [hM] at hM'
          exact absurd hM' (by simp)
      | eqv ψ =>
          rw [FormTyped] at hG
          obtain ⟨hψ, hres⟩ := hG
          rw [Form.combine_obj_eqv]
          cases k with
          | zero =>
              rw [FormTyped] at hF ⊢
              obtain ⟨Tel₁, Tel₂, hS, hM, hchain⟩ := hF
              exact ⟨Tel₁, Tel₂, hS, hres.symm.trans hM,
                ChainWellTyped_append cs hchain ⟨T, hψ, hres, rfl⟩⟩
          | succ j =>
              rw [FormTyped] at hF ⊢
              obtain ⟨Tel₁, Tel₂, hS, hM, hchain, hcl⟩ := hF
              refine ⟨Tel₁, Tel₂, hS, hres.symm.trans hM,
                ChainWellTyped_append cs hchain ⟨T, hψ, hres, rfl⟩, fun a ha V => ?_⟩
              obtain ⟨t, L, hcl'⟩ := hcl a ha V
              refine ⟨t, L, fun j' ht hj hV => ?_⟩
              obtain ⟨n, V', happ, hV'⟩ := hcl' j' ht hj hV
              have h2 : applyChain σ 2 [ChainStep.conv ψ] (ChainStep.chainAtom cs a) V'
                  = some V' := rfl
              exact ⟨n + 2 + cs.length, V', applyChain_append_of cs happ h2, hV'⟩
      | obj cs₂ =>
          rw [Form.combine_obj_obj]
          cases k with
          | zero =>
              rw [FormTyped] at hF hG ⊢
              obtain ⟨Tel₁, TelM, hS, hM, hchain₁⟩ := hF
              obtain ⟨TelM', Tel₂, hM', hT, hchain₂⟩ := hG
              exact ⟨Tel₁, Tel₂, hS, hT, ChainWellTyped_append cs hchain₁ hchain₂⟩
          | succ j =>
              rw [FormTyped] at hF hG ⊢
              obtain ⟨Tel₁, TelM, hS, hM, hchain₁, hcl₁⟩ := hF
              obtain ⟨TelM', Tel₂, hM', hT, hchain₂, hcl₂⟩ := hG
              injection hM.symm.trans hM' with _ hTel
              subst hTel
              refine ⟨Tel₁, Tel₂, hS, hT, ChainWellTyped_append cs hchain₁ hchain₂, fun a ha V => ?_⟩
              obtain ⟨t₁, L₁, hcl₁'⟩ := hcl₁ a ha V
              have hb : Atom.HasType Γ (ChainStep.chainAtom cs a) M := by
                rw [ChainStep.chainAtom_eq_chainAtom']
                exact ChainWellTyped_chainAtom cs hchain₁ ha
              by_cases hex : ∃ j', t₁ ≤ j' ∧ j' ≤ j ∧ ViewTypedWith σ Γ (FormTyped σ Γ j') V Tel₁ a
              · obtain ⟨j₀, ht₀, hj₀, hV₀⟩ := hex
                obtain ⟨n₀, V₁, happ₀, _⟩ := hcl₁' j₀ ht₀ hj₀ hV₀
                obtain ⟨t₂, L₂, hcl₂'⟩ := hcl₂ _ hb V₁
                refine ⟨max t₁ (t₂ + L₁), L₁ + L₂, fun j' ht hj hV => ?_⟩
                have ht₁ : t₁ ≤ j' := Nat.le_trans (Nat.le_max_left _ _) ht
                have ht₂ : t₂ + L₁ ≤ j' := Nat.le_trans (Nat.le_max_right _ _) ht
                obtain ⟨n₁, V₁', happ₁, hV₁'⟩ := hcl₁' j' ht₁ hj hV
                have hV₁eq : V₁' = V₁ := by
                  have h₁ := applyChain_le (Nat.le_max_left n₁ n₀) happ₁
                  have h₂ := applyChain_le (Nat.le_max_right n₁ n₀) happ₀
                  exact Option.some.inj (h₁.symm.trans h₂)
                subst hV₁eq
                obtain ⟨n₂, V'', happ₂, hV''⟩ :=
                  hcl₂' (j' - L₁) (by omega) (by omega)
                    (ViewTypedWith_root (ChainStep.chainAtom_root cs a).symm hV₁')
                refine ⟨n₁ + n₂ + cs.length, V'', applyChain_append_of cs happ₁ happ₂, ?_⟩
                have hdepth : j' - L₁ - L₂ = j' - (L₁ + L₂) := by omega
                rw [hdepth] at hV''
                exact ViewTypedWith_root (ChainStep.chainAtom_root cs a) hV''
              · refine ⟨j + 1, 0, fun j' ht hj hV => ?_⟩
                exact absurd ⟨j', by omega, hj, hV⟩ hex

/-- Composition of head forms preserves typedness whenever the second form
is not `bot` — the common case, and the one the normalizer needs. -/
theorem Form.combine_typed_of_ne_bot {k : Nat} {F G : Form s} {S M T : Ty s}
    (hF : FormTyped σ Γ k F S M) (hG : FormTyped σ Γ k G M T) (h : G ≠ .bot) :
    FormTyped σ Γ k (F.combine G) S T :=
  Form.combine_typed hF hG

end

end FCdot
