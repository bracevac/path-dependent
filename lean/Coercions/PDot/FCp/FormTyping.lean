import Coercions.PDot.FCp.Normalizer

/-!
# The typing of forms and views of FCp (plan X, T.7 fixed by C0)

The readings over the erased store are `HasFld`, `FieldOK`, `Live`, the closed reading of a path
equality `PRead`, and `RLam`.  `SoundEq` is type equality evidence whose path equalities carry their
closed reading.  Atoms are typed between syntactic shapes by their own evidence (`AtomT`, `FormT`,
`EntriesT`, `SideT`), and the forms of a function view hold `eqv` and `pi` atoms only (`FnAtomT`,
`FnFormT`).  Views are typed against `res` (`ViewT`, `VEntriesT`, `VEntryT`, `PViewT`).
`Ctx.comp` reads a type at a position below `dom` and `cod`.  `HeadTyped` and `AccT` type the head
of the machine.  The inversions of view typing come last.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Readings over the erased store -/

/-- A right side that has a field `a`. -/
def HasFld : Runtime.Rhs s → Label → Prop
  | .defv (.new ds), a => (ds.get a).isSome = true
  | .nest ds, a => (ds.get a).isSome = true
  | _, _ => False

/-- Every lookup end of `p` that is no path has a field `a`. -/
def FieldOK (γ : Runtime.Store s) (p : Path s) (a : Label) : Prop :=
  ∀ k, Runtime.Lookups γ (.defp p) k → k.isPath = false → HasFld k a

/-- Every prefix of the path has the next field at every lookup end. -/
def Live (γ : Runtime.Store s) : Path s → Prop
  | .var _ => True
  | .sel p a => Live γ p ∧ FieldOK γ p a

/-- The closed reading of path equality: one canonical name and joinable lookups. -/
def PRead (Γ : Ctx s) (γ : Runtime.Store s) (p q : Path s) : Prop :=
  Γ.canon p = Γ.canon q ∧ Runtime.Joinable γ p q

/-- The lookup of `r` reaches the stored value `v`, whose erasure is its closure. -/
def RLam (γ : Runtime.Store s) (r : Path s) (v : Value s) : Prop :=
  Runtime.Lookups γ (.defp r) (.defv v.erase)

/-! ## Typing of forms and views -/

/-- Type equality evidence whose path equalities carry their closed reading. -/
inductive SoundEq (Γ : Ctx s) (γ : Runtime.Store s) : EqCo s → Ty s → Ty s → Prop
  | refl : SoundEq Γ γ (.refl T) T T
  | symm : SoundEq Γ γ φ S T → SoundEq Γ γ (.symm φ) T S
  | trans : SoundEq Γ γ φ S M → SoundEq Γ γ ψ M T → SoundEq Γ γ (.trans φ ψ) S T
  | defP : Γ.defAt p A = some W → SoundEq Γ γ (.defP p A) (.sel p A) W
  | lift : PEq.HasType Γ π p q → PRead Γ γ p q → SoundEq Γ γ (.lift T π) (T.substPath p) (T.substPath q)
  | dom : SoundEq Γ γ φ (.pi S₁ T₁) (.pi S₂ T₂) → SoundEq Γ γ (.dom φ) S₁ S₂
  | cod : SoundEq Γ γ φ (.pi S₁ T₁) (.pi S₂ T₂) → SoundEq Γ γ (.cod φ p) (T₁.substPath p) (T₂.substPath p)

mutual
/-- `AtomT Γ γ A S T`: the atom proves `S ≤ T`. -/
inductive AtomT (Γ : Ctx s) (γ : Runtime.Store s) : Atom s → Ty s → Ty s → Prop
  | eqv : SoundEq Γ γ φ S T → AtomT Γ γ (.eqv φ) S T
  | pi : LeCo.HasType Γ e S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) f T₁ T₂ →
      AtomT Γ γ (.pi e f) (.pi S₁ T₁) (.pi S₂ T₂)
  | obj : EntriesT Γ γ Tel₁ Es Tel₂ → AtomT Γ γ (.obj Es) (.mu Tel₁) (.mu Tel₂)
  | top : AtomT Γ γ .top T .top
  | bot : AtomT Γ γ .bot .bot T
  | pair : FormT Γ γ F S (.mu Tel) → FormT Γ γ G S (.mu Tel') → AtomT Γ γ (.pair F G) S (.mu (Tel ++ Tel'))
  | bnd : Tel.At i (.is T.weaken) → AtomT Γ γ (.bnd i) (.mu Tel) T
  | into : FormT Γ γ F S T → AtomT Γ γ (.into F) S (.mu (.cons .nil (.is T.weaken)))
inductive FormT (Γ : Ctx s) (γ : Runtime.Store s) : Form s → Ty s → Ty s → Prop
  | nil : FormT Γ γ .nil T T
  | cons : AtomT Γ γ A S M → FormT Γ γ F M T → FormT Γ γ (.cons A F) S T
inductive EntriesT (Γ : Ctx s) (γ : Runtime.Store s) : Telescope (s,x) → Entries s → Telescope (s,x) → Prop
  | nil : EntriesT Γ γ src .nil .nil
  | le : EntriesT Γ γ src Es Tel → src.At j (.le X Y) → SideT Γ γ pre S X → SideT Γ γ post Y T →
      EntriesT Γ γ src (.cons Es (.le pre j post)) (.cons Tel (.le S T))
  | fld : EntriesT Γ γ src Es Tel → src.At j (.fld a X) → SideT Γ γ sd X T →
      EntriesT Γ γ src (.cons Es (.fld j sd)) (.cons Tel (.fld a T))
  | alias : EntriesT Γ γ src Es Tel → src.At j (.alias q) →
      EntriesT Γ γ src (.cons Es (.alias j)) (.cons Tel (.alias q))
  | is : EntriesT Γ γ src Es Tel → FormT Γ γ F (.mu src) T →
      EntriesT Γ γ src (.cons Es (.is F)) (.cons Tel (.is T.weaken))
inductive SideT (Γ : Ctx s) (γ : Runtime.Store s) : SideF s → Ty (s,x) → Ty (s,x) → Prop
  | none : SideT Γ γ .none X X
  | some : FormT Γ γ F X Y → SideT Γ γ (.some F) X.weaken Y.weaken
  | bot : SideT Γ γ .bot .bot X
  | top : SideT Γ γ .top X .top
end

/-- The forms of a function view: `eqv` and `pi` atoms only. -/
inductive FnAtomT (Γ : Ctx s) (γ : Runtime.Store s) : Atom s → Ty s → Ty s → Prop
  | eqv : SoundEq Γ γ φ S T → FnAtomT Γ γ (.eqv φ) S T
  | pi : LeCo.HasType Γ e S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) f T₁ T₂ →
      FnAtomT Γ γ (.pi e f) (.pi S₁ T₁) (.pi S₂ T₂)
inductive FnFormT (Γ : Ctx s) (γ : Runtime.Store s) : Form s → Ty s → Ty s → Prop
  | nil : FnFormT Γ γ .nil T T
  | cons : FnAtomT Γ γ A S M → FnFormT Γ γ F M T → FnFormT Γ γ (.cons A F) S T

mutual
/-- `ViewT Γ γ r R W`: `W` is a view of the path `r` at the resolved type `R`. -/
inductive ViewT (Γ : Ctx s) (γ : Runtime.Store s) : Path s → Ty s → View s → Prop
  | obj : VEntriesT Γ γ r Tel V → Live γ r → ViewT Γ γ r (.mu Tel) (.obj V)
  | fn : Value.HasType Γ v X → v.isLam = true → FnFormT Γ γ F X (.pi S U) → Live γ r →
      RLam γ r v → ViewT Γ γ r (.pi S U) (.fn v F)
  | none : Γ.next (.sel p A) = none → Live γ r → ViewT Γ γ r (.sel p A) .none
inductive VEntriesT (Γ : Ctx s) (γ : Runtime.Store s) : Path s → Telescope (s,x) → VEntries s → Prop
  | nil : VEntriesT Γ γ r .nil .nil
  | cons : VEntriesT Γ γ r Tel V → VEntryT Γ γ r pr e → VEntriesT Γ γ r (.cons Tel pr) (.cons V e)
inductive VEntryT (Γ : Ctx s) (γ : Runtime.Store s) : Path s → Pr (s,x) → VEntry s → Prop
  | le : FormT Γ γ F (S.substPath r) (T.substPath r) → VEntryT Γ γ r (.le S T) (.le F)
  | fld : ViewT Γ γ (.sel r a) (Γ.res (T.substPath r)) W → VEntryT Γ γ r (.fld a T) (.fld a W)
  | alias : PRead Γ γ r (q.substPath r) → VEntryT Γ γ r (.alias q) .alias
  | is : ViewT Γ γ r (Γ.res (T.substPath r)) W → VEntryT Γ γ r (.is T) (.is W)
end

/-- `Γ ⊨ₚ[r] W : T`: a view at the resolution of `T`. -/
def PViewT (Γ : Ctx s) (γ : Runtime.Store s) (r : Path s) (T : Ty s) (W : View s) : Prop :=
  ViewT Γ γ r (Γ.res T) W

/-- The component of a type at a position below `dom` and `cod`, each step read after resolution. -/
def Ctx.comp (Γ : Ctx s) : List (Dir s) → Ty s → Option (Ty s)
  | [], T => some (Γ.res T)
  | .dom :: κ, T => match Γ.res T with
    | .pi S _ => Γ.comp κ S
    | _ => none
  | .cod p :: κ, T => match Γ.res T with
    | .pi _ U => Γ.comp κ (U.substPath p)
    | _ => none

theorem Ctx.comp_congr (Γ : Ctx s) {T T' : Ty s} (h : Γ.res T = Γ.res T') : ∀ κ, Γ.comp κ T = Γ.comp κ T'
  | [] => by simp only [Ctx.comp, h]
  | .dom :: κ => by simp only [Ctx.comp, h]
  | .cod _ :: κ => by simp only [Ctx.comp, h]

variable {Γ : Ctx s} {γ : Runtime.Store s}

/-! ## Inversions of view typing -/

theorem ViewT.live : ViewT Γ γ r R W → Live γ r
  | .obj _ h => h
  | .fn _ _ _ h _ => h
  | .none _ h => h

theorem ViewT.not_bot : ¬ ViewT Γ γ r .bot W := by
  intro h; cases h

theorem ViewT.obj_inv (h : ViewT Γ γ r R (.obj V)) : ∃ Tel, R = .mu Tel ∧ VEntriesT Γ γ r Tel V ∧ Live γ r := by
  cases h with
  | obj hV hl => exact ⟨_, rfl, hV, hl⟩

theorem ViewT.fn_inv (h : ViewT Γ γ r R (.fn v F)) :
    ∃ X S U, R = .pi S U ∧ Value.HasType Γ v X ∧ v.isLam = true ∧ FnFormT Γ γ F X (.pi S U) ∧
      Live γ r ∧ RLam γ r v := by
  cases h with
  | fn hv hl hF hli hR => exact ⟨_, _, _, rfl, hv, hl, hF, hli, hR⟩

theorem ViewT.none_inv (h : ViewT Γ γ r R .none) : ∃ p A, R = .sel p A ∧ Γ.next (.sel p A) = Option.none ∧ Live γ r := by
  cases h with
  | none hn hl => exact ⟨_, _, rfl, hn, hl⟩

theorem ViewT.mu_inv (h : ViewT Γ γ r (.mu Tel) W) : ∃ V, W = .obj V ∧ VEntriesT Γ γ r Tel V := by
  cases h with
  | obj hV _ => exact ⟨_, rfl, hV⟩

theorem ViewT.pi_inv (h : ViewT Γ γ r (.pi S U) W) :
    ∃ v F X, W = .fn v F ∧ Value.HasType Γ v X ∧ v.isLam = true ∧ FnFormT Γ γ F X (.pi S U) ∧ RLam γ r v := by
  cases h with
  | fn hv hl hF _ hR => exact ⟨_, _, _, rfl, hv, hl, hF, hR⟩

theorem VEntriesT.length_eq : VEntriesT Γ γ r Tel V → V.length = Tel.length
  | .nil => rfl
  | .cons h _ => congrArg (· + 1) h.length_eq

theorem VEntriesT.get : ∀ {Tel : Telescope (s,x)} {V : VEntries s}, VEntriesT Γ γ r Tel V →
    ∀ {j : Nat} {pr : Pr (s,x)}, Tel.At j pr → ∃ e, V.get j = some e ∧ VEntryT Γ γ r pr e
  | _, _, .nil, _, _, hj => (Telescope.At.nil_of_eq hj rfl).elim
  | _, _, .cons (Tel := Tel) (V := V) (e := e) hV he, j, pr, hj => by
      rcases Telescope.At.cons_of_eq hj rfl with ⟨rfl, rfl⟩ | hj'
      · refine ⟨e, ?_, he⟩
        simp [VEntries.get, hV.length_eq]
      · obtain ⟨e', hg, he'⟩ := VEntriesT.get hV hj'
        refine ⟨e', ?_, he'⟩
        have : j ≠ V.length := by rw [hV.length_eq]; have := hj'.lt_length; omega
        simp [VEntries.get, this, hg]

theorem FnAtomT.toAtomT {Γ : Ctx s} {γ : Runtime.Store s} : FnAtomT Γ γ A S T → AtomT Γ γ A S T
  | .eqv h => .eqv h
  | .pi he hf => .pi he hf

theorem FnFormT.toFormT {Γ : Ctx s} {γ : Runtime.Store s} : FnFormT Γ γ F S T → FormT Γ γ F S T
  | .nil => .nil
  | .cons hA hF => .cons hA.toAtomT hF.toFormT

/-- The typing of a machine head from `Π(z : S₀) T₀` to `Π(z : S) T`. -/
def HeadTyped (Γ : Ctx s) : AppHead s → Ty s → Ty (s,x) → Ty s → Ty (s,x) → Prop
  | .id, S₀, T₀, S, T => S₀ = S ∧ T₀ = T
  | .eqv φ, S₀, T₀, S, T => EqCo.HasType Γ φ (.pi S₀ T₀) (.pi S T)
  | .pi d c, S₀, T₀, S, T => LeCo.HasType Γ d S S₀ ∧ LeCo.HasType (Γ.cons (.opaque S)) c T₀ T

inductive AccT (Γ : Ctx s) (S₀ : Ty s) (T₀ : Ty (s,x)) : Acc s → Ty s → Prop
  | start : AccT Γ S₀ T₀ .start (.pi S₀ T₀)
  | eqv : EqCo.HasType Γ χ (.pi S₀ T₀) X → AccT Γ S₀ T₀ (.eqv χ) X
  | pi : LeCo.HasType Γ d S S₀ → LeCo.HasType (Γ.cons (.opaque S)) c T₀ T → AccT Γ S₀ T₀ (.pi d c) (.pi S T)
  | piEqv : LeCo.HasType Γ d S S₀ → LeCo.HasType (Γ.cons (.opaque S)) c T₀ T →
      EqCo.HasType Γ χ (.pi S T) X → AccT Γ S₀ T₀ (.piEqv d c χ) X

end PDot.FCp

