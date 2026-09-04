import Coercions.FCdot.Canonical
import Coercions.FCdot.Typing

/-!
# Typedness of forms and views

Forms are typed *syntactically*: a form is typed between two endpoints when
its pieces of evidence are typed and the endpoints resolve to the shapes the
form promises.  An object form is typed when each of its entries is typed
against the corresponding proposition of the (opened) target telescope, and
its presence entries point at presence propositions of the source.  Since
object coercions are between opened telescopes, an entry's endpoints do not
depend on the atom the coercion is applied to; the definition quantifies
over the instantiating root anyway, which also covers views of atoms at
self-mentioning telescopes.

Forms are typed *at a root*: shapes are read off the type after resolving
definitions and opening the self block at that root, so `foldSelf` and
`unfoldSelf` on an atom do not change what its chain of casts is typed at.
Forms of coercions are typed at every root; forms of atom chains at the
atom's root.

No depth index: the recursion is structural in the form.
-/

namespace FCdot

/-- Field presence in a store. -/
def Store.HasField (σ : Store s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ W F, σ.lookup x = .obj W F ∧ (F.get? ℓ).isSome

/-! ## Shapes: resolve, and optionally open the self block at a root -/

/-- Open the self block of an object type at a root; other types unchanged.
Idempotent, and invisible to `foldSelf`/`unfoldSelf`. -/
def Ty.unfoldAt (r : BVar s .var) : Ty s → Ty s
  | .obj Tel => .obj ((Tel.substVar r).weaken)
  | T => T

/-- The shape of a type: its resolution, opened at the root when one is
given.  Coercion forms and views use no root (their endpoints are closed
types unrelated to any atom); the chain of casts of an atom is typed at the
atom's root, so that folding and unfolding the self block are invisible. -/
def Ctx.resolveAt (Γ : Ctx s) : Option (BVar s .var) → Ty s → Ty s
  | none, T => Γ.resolve T
  | some r, T => (Γ.resolve T).unfoldAt r

/-! ### Notation for typed forms

`Γ ⊨ F : S ≤ T` types a coercion form with plain shapes; `Γ ⊨[r] F : S ≤ T`
types the chain of casts of an atom rooted at `r`, with shapes opened at
`r`.  `Γ ⊨ Es : Tel₁ ⇒ Tel₂` types the entries of an object form between
opened telescopes. -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ none F S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r "] " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ (some r) F S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ none Tel₁ Es Tel₂
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r "] " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ (some r) Tel₁ Es Tel₂

section

variable (Γ : Ctx s) (ρ : Option (BVar s .var))

mutual

/-- `FormTyped Γ ρ F S T`: the head form `F` is typed evidence for `S ≤ T`,
with shapes read off `Γ.resolveAt ρ`.  Object forms are between opened
telescopes. -/
inductive FormTyped : Form s → Ty s → Ty s → Prop where
  | bot {S T : Ty s} : Γ.resolve S = .bot → FormTyped .bot S T
  | top {S T : Ty s} : Γ.resolve T = .top → FormTyped .top S T
  | id {S T : Ty s} : Γ.resolveAt ρ S = Γ.resolveAt ρ T → FormTyped .id S T
  | eqv {φ : EqCo s} {S T : Ty s} : Γ.resolveAt ρ S = Γ.resolveAt ρ T → FormTyped (.eqv φ) S T
  | pi {d : LeCo s} {c : LeCo (s,x)} {S T S₁ S₂ : Ty s} {T₁ T₂ : Ty (s,x)} :
      Γ.resolve S = .pi S₁ T₁ → Γ.resolve T = .pi S₂ T₂ →
      LeCo.HasType Γ d S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) c T₁ T₂ →
      FormTyped (.pi d c) S T
  | obj {Es : List (Entry s)} {S T : Ty s} {Tel₁ Tel₂ : Telescope s} :
      Γ.resolveAt ρ S = .obj Tel₁.weaken → Γ.resolveAt ρ T = .obj Tel₂.weaken →
      EntriesTyped Tel₁ Es Tel₂ → FormTyped (.obj Es) S T

/-- `EntriesTyped Γ ρ Tel₁ Es Tel₂`: the entries `Es` are typed against the
propositions of the opened telescope `Tel₂`, with presence entries pointing
into the opened source `Tel₁`. -/
inductive EntriesTyped : Telescope s → List (Entry s) → Telescope s → Prop where
  | nil {Tel₁ : Telescope s} : EntriesTyped Tel₁ [] .nil
  | le {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {F : Form s} {S' T' : Ty s} :
      EntriesTyped Tel₁ Es Tel₂ → FormTyped F S' T' →
      EntriesTyped Tel₁ (Es ++ [.le F]) (.cons Tel₂ (.le S' T'))
  | eq {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {S' T' : Ty s} :
      EntriesTyped Tel₁ Es Tel₂ → Γ.resolve S' = Γ.resolve T' →
      EntriesTyped Tel₁ (Es ++ [.eq]) (.cons Tel₂ (.eq S' T'))
  | has {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {j : Nat} {ℓ : Label} :
      EntriesTyped Tel₁ Es Tel₂ → Tel₁.At j (.has ℓ) →
      EntriesTyped Tel₁ (Es ++ [.has j]) (.cons Tel₂ (.has ℓ))

end

end

open Lean PrettyPrinter in
@[app_unexpander FormTyped] def FormTyped.unexpand : Unexpander
  | `($_ $Γ none $F $S $T) => `($Γ ⊨ $F : $S ≤ $T)
  | `($_ $Γ (some $r) $F $S $T) => `($Γ ⊨[$r] $F : $S ≤ $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander EntriesTyped] def EntriesTyped.unexpand : Unexpander
  | `($_ $Γ none $Tel₁ $Es $Tel₂) => `($Γ ⊨ $Es : $Tel₁ ⇒ $Tel₂)
  | `($_ $Γ (some $r) $Tel₁ $Es $Tel₂) => `($Γ ⊨[$r] $Es : $Tel₁ ⇒ $Tel₂)
  | _ => throw ()

section
variable (Γ : Ctx s) (r : BVar s .var) (σ : Store s)

/-- Typedness of one proposition form against a proposition instantiated at
the root.  Forms in views are coercion forms: plain shapes. -/
def PropFormTyped : Option (PropForm s) → Proposition s → Prop
  | some (.le F), .le S T => FormTyped Γ none F S T
  | some .eq, .eq S T => Γ.resolve S = Γ.resolve T
  | some (.has x ℓ), .has ℓ' => x = r ∧ ℓ = ℓ' ∧ σ.HasField r ℓ
  | _, _ => False

/-- A view is typed against a telescope at the root. -/
def ViewTyped (V : View s) (Tel : Telescope (s,x)) : Prop :=
  V.length = Tel.length ∧
  ∀ i P, Tel.At i P → PropFormTyped Γ r σ (View.nth? V i) (P.substVar r)

end

/-- `Γ ⊨[r, σ] V : Tel`: over the store `σ`, the view `V` of an atom rooted
at `r` is typed against `Tel` instantiated at `r`. -/
scoped notation:40 Γ:51 " ⊨[" r ", " σ "] " V:51 " : " Tel:51 => ViewTyped Γ r σ V Tel

end FCdot
