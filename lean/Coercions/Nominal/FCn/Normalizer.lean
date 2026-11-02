import Coercions.Nominal.FCn.Resolution
import Coercions.Nominal.FCn.Machine
import Coercions.Nominal.FCn.CheckerCompleteness

/-!
# Forms, views and the normalizer of FCn (plan X, T.7 fixed by C0)

A form `Form` is a chain of atoms `Atom`, applied first to last.  `Entries` are the entries of an
object form, and `SideF` its sides.  A view `View` is what a path reads at its resolved type: an
object view of entries `VEntries`, a function view that names a stored value with a form, or `none`
at an abstract selection.  `View.liftAct`, `View.liftK` and `View.transport` move a view along an
equality, and `View.repath` moves it to an aliased path.  `View.applyForm` applies a form, and
`litView` and `varView` give the view of a literal at its path and of a store variable.  Each
equation that is reached only off typed inputs says so in the docstring of its definition.

The normalizer `Hnf` with `HnfM` and `HnfS`, the path view `PV` and the stored casts `NormV` are
relations indexed by the types of the evidence, one rule per evidence constructor.  `collapse` reads
the head of a function form, and `appView` is the application view `AV`, the parameter of the
machine.  Every index and every output of the relations is a function of the evidence: `Hnf.idx`,
`PV.idx`, `Hnf.det`, `PV.det`, `NormV.det` and `appView_det`, with `Store.Typed.ctx_unique` for the
context of a store.

At the end come the computable versions `Store.ctx`, `hnf`, `hnfM`, `hnfSPre`, `hnfSPost`, `pview`,
`normV` and `appViewOf`, structural on the evidence, with their graph lemmas.  Each computes the
indices of its relation with its output, so each graph lemma holds with no typing hypothesis, and
`appViewOf_iff` says that `appViewOf` computes `appView`.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.  The computable versions are new.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Forms

A form is a chain of atoms, applied first to last.  `nil` is `id`.  An atom is head normal and
typed between syntactic shapes, except `eqv φ`, which relates any two types by evidence. -/

mutual
inductive Atom : Sig → Type where
  | eqv : EqCo s → Atom s                          -- eqv φ
  | pi : LeCo s → LeCo (s,x) → Atom s              -- pi e (z. f), z the .here of f
  | obj : Entries s → Atom s                       -- obj Es
  | top : Atom s                                   -- top
  | bot : Atom s                                   -- bot
  | pair : Form s → Form s → Atom s                -- pair F G
  | bnd : Nat → Atom s                             -- bnd i
  | into : Form s → Atom s                         -- into F
inductive Form : Sig → Type where
  | nil : Form s                                   -- id
  | cons : Atom s → Form s → Form s                -- A ⨾ F, A applied first
inductive Entry : Sig → Type where
  | le : SideF s → Nat → SideF s → Entry s         -- le pre j post
  | fld : Nat → SideF s → Entry s                  -- fld j sd
  | alias : Nat → Entry s                          -- alias j
  | is : Form s → Entry s                          -- is F
inductive Entries : Sig → Type where
  | nil : Entries s
  | cons : Entries s → Entry s → Entries s         -- newest last, as Telescope
inductive SideF : Sig → Type where
  | none : SideF s
  | some : Form s → SideF s
  | bot : SideF s
  | top : SideF s
end

def Form.append : Form s → Form s → Form s
  | .nil, G => G
  | .cons A F, G => .cons A (F.append G)

def Form.single (A : Atom s) : Form s := .cons A .nil

def SideF.form : SideF s → Form s
  | .none => .nil
  | .some F => F
  | .bot => .single .bot
  | .top => .single .top

/-! ## Views

A view of a path `r` at a resolved type: an object view lists one entry per proposition, a
function view names the stored value `v` whose core is the closure the lookup of `r` reaches,
with the form from the type of `v`, and `none` is the view at an abstract selection.  A field
entry carries its label and the view of `r.a`, an `is` entry the view of `r` itself. -/

mutual
inductive View : Sig → Type where
  | obj : VEntries s → View s                      -- (V)
  | fn : Value s → Form s → View s                 -- (v, F), v.core a lambda
  | none : View s
inductive VEntry : Sig → Type where
  | le : Form s → VEntry s                         -- le F
  | fld : Label → View s → VEntry s                -- fld a W
  | alias : VEntry s                               -- alias
  | is : View s → VEntry s                         -- is W
inductive VEntries : Sig → Type where
  | nil : VEntries s
  | cons : VEntries s → VEntry s → VEntries s      -- newest last, as Telescope
end

def VEntries.length : VEntries s → Nat
  | .nil => 0
  | .cons V _ => V.length + 1

def VEntries.get : VEntries s → Nat → Option (VEntry s)
  | .nil, _ => none
  | .cons V e, i => if i = V.length then some e else V.get i

def VEntries.append : VEntries s → VEntries s → VEntries s
  | V, .nil => V
  | V, .cons V' e => .cons (V.append V') e

/-! ## Acting on views

`liftAct (h. Y) π r` moves a view of `r` at `Y⟨p⟩` to `Y⟨q⟩` along `π : p ≃ q`.  `liftK` does it at a
position below `dom` and `cod`.  `transport b φ κ r` reads a type equality as a move of views,
forward (`b = true`) or backward.  `repath R π r r'` moves a view of `r` at `R` to a view of `r'`
along `π : r' ≃ r`.  `applyForm r F` applies a form. -/

inductive Dir (s : Sig) : Type where
  | dom : Dir s
  | cod : Path s → Dir s

mutual
/-- `liftAct (h. Y) π r W` moves a view of `r` at `Y⟨p⟩` to a view at `Y⟨q⟩` along `π : p ≃ q`.  An
object view at an object type moves entry by entry, and a function view at a function type gains
the bridge `eqv (lift (h. Y) π)`.  The last equation keeps the view.  On typed inputs it is reached at
a selection, whose two instances resolve alike or stay abstract.  At `⊥`, and where the view is not of
the type's shape, it is reached only off typed inputs (`View.liftAct_typed`). -/
def View.liftAct : Ty (s,x) → PEq s → Path s → View s → View s
  | .mu Tel, π, r, .obj V => .obj (VEntries.liftAct V Tel π r)
  | .pi S T, π, _, .fn v F => .fn v (F.append (.single (.eqv (.lift (.pi S T) π))))
  | _, _, _, W => W
/-- `liftAct` entry by entry.  The last equation is reached on typed inputs at the end of both, and
only off typed inputs where the lengths differ (`VEntries.liftAct_typed`). -/
def VEntries.liftAct : VEntries s → Telescope ((s,x),x) → PEq s → Path s → VEntries s
  | .cons V e, .cons Tel pr, π, r => .cons (VEntries.liftAct V Tel π r) (VEntry.liftAct e pr π r)
  | V, _, _, _ => V
/-- A bound entry gains a bridge on each side, and a field or `is` entry moves its view.  The last
equation keeps the entry.  On typed inputs it is reached at an alias entry, and only off typed
inputs where the entry is not of the proposition's kind (`VEntry.liftAct_typed`). -/
def VEntry.liftAct : VEntry s → Pr ((s,x),x) → PEq s → Path s → VEntry s
  | .le F, .le S T, π, r =>
      .le ((Form.single (.eqv (.lift (S.substPath r.weaken) (.symm π)))).append
        (F.append (.single (.eqv (.lift (T.substPath r.weaken) π)))))
  | .fld a W, .fld _ T, π, r => .fld a (View.liftAct (T.substPath r.weaken) π (r.sel a) W)
  | .is W, .is T, π, r => .is (View.liftAct (T.substPath r.weaken) π r W)
  | e, _, _, _ => e
end

/-- `liftAct` at a position below `dom` and `cod`.  The last equation keeps the view.  On typed
inputs it is reached at a selection, whose two instances resolve alike, and only off typed inputs
at `⊥` or an object type, where no position below `dom` or `cod` resolves (`View.liftK_typed`). -/
def View.liftK : Ty (s,x) → PEq s → List (Dir s) → Path s → View s → View s
  | T, π, [], r, W => View.liftAct T π r W
  | .pi S _, π, .dom :: κ, r, W => View.liftK S π κ r W
  | .pi _ U, π, .cod p :: κ, r, W => View.liftK (U.substPath p.weaken) π κ r W
  | _, _, _ :: _, _, W => W

def View.transport : Bool → EqCo s → List (Dir s) → Path s → View s → View s
  | _, .refl _, _, _, W => W
  | b, .symm φ, κ, r, W => View.transport (!b) φ κ r W
  | true, .trans φ ψ, κ, r, W => View.transport true ψ κ r (View.transport true φ κ r W)
  | false, .trans φ ψ, κ, r, W => View.transport false φ κ r (View.transport false ψ κ r W)
  | _, .defP _ _, _, _, W => W
  | true, .lift T π, κ, r, W => View.liftK T π κ r W
  | false, .lift T π, κ, r, W => View.liftK T (.symm π) κ r W
  | b, .dom φ, κ, r, W => View.transport b φ (.dom :: κ) r W
  | b, .cod φ p, κ, r, W => View.transport b φ (.cod p :: κ) r W

mutual
/-- `repath W T π r r'` moves a view of `r` at `Γ.res T` to a view of `r'` along `π : r' ≃ r`.  A
function view or `none` is kept, on typed inputs too.  An object view at a `T` that resolves to no
object type is kept as well, and that equation is reached only off typed inputs: an object view is a
view at an object type (`View.repath_typed`). -/
def View.repath (Γ : Ctx s) : View s → Ty s → PEq s → Path s → Path s → View s
  | .obj V, T, π, r, r' =>
      match Γ.res T with
      | .mu Tel => .obj (VEntries.repath Γ V Tel π r r')
      | _ => .obj V
  | W, _, _, _, _ => W
/-- `repath` entry by entry.  The last equation is reached on typed inputs at the end of both, and
only off typed inputs where the lengths differ (`VEntries.repath_typed`). -/
def VEntries.repath (Γ : Ctx s) : VEntries s → Telescope (s,x) → PEq s → Path s → Path s → VEntries s
  | .cons V e, .cons Tel pr, π, r, r' => .cons (VEntries.repath Γ V Tel π r r') (VEntry.repath Γ e pr π r r')
  | V, _, _, _, _ => V
/-- A bound entry gains a bridge on each side, and a field or `is` entry moves its view to `r'`.
The last equation keeps the entry.  On typed inputs it is reached at an alias entry, and only off
typed inputs where the entry is not of the proposition's kind (`VEntry.repath_typed`). -/
def VEntry.repath (Γ : Ctx s) : VEntry s → Pr (s,x) → PEq s → Path s → Path s → VEntry s
  | .le F, .le S T, π, _, _ =>
      .le ((Form.single (.eqv (.lift S π))).append (F.append (.single (.eqv (.lift T (.symm π))))))
  | .fld a W, .fld _ T, π, r, r' =>
      .fld a (View.liftAct T (.symm π) (r'.sel a) (View.repath Γ W (T.substPath r) (.sel π a) (r.sel a) (r'.sel a)))
  | .is W, .is T, π, r, r' => .is (View.liftAct T (.symm π) r' (View.repath Γ W (T.substPath r) π r r'))
  | e, _, _, _, _ => e
end

mutual
/-- One atom applied to a view.  At `pair`, a side whose view is no object view, and at `bnd i`, an
entry at `i` that is no `is` entry, are reached only off typed inputs.  The last equation keeps the
view: a `pi` atom at a view that is no function view, an `obj` or `bnd` atom at a view that is no
object view, and `bot`, which has no view to apply to.  It is reached only off typed inputs
(`AtomT.apply`). -/
def View.applyAtom : Atom s → Path s → View s → View s
  | .eqv φ, r, W => View.transport true φ [] r W
  | .pi e f, _, .fn v F => .fn v (F.append (.single (.pi e f)))
  | .obj Es, r, .obj V => .obj (Entries.apply Es r V)
  | .top, _, _ => .obj .nil
  | .pair F G, r, W =>
      match View.applyForm F r W, View.applyForm G r W with
      | .obj V, .obj V' => .obj (V.append V')
      | W₁, _ => W₁
  | .bnd i, _, .obj V =>
      match V.get i with
      | some (.is W) => W
      | _ => .none
  | .into F, r, W => .obj (.cons .nil (.is (View.applyForm F r W)))
  | _, _, W => W
def View.applyForm : Form s → Path s → View s → View s
  | .nil, _, W => W
  | .cons A F, r, W => View.applyForm F r (View.applyAtom A r W)
def Entries.apply : Entries s → Path s → VEntries s → VEntries s
  | .nil, _, _ => .nil
  | .cons Es e, r, V => .cons (Entries.apply Es r V) (Entry.apply e r V)
/-- A bound entry composes its sides around the form it reads, and a field entry applies its side
to the field's view.  Where the entry read at `j` is not of the kind the morphism names, the result
is `alias`, reached only off typed inputs (`EntriesT.apply`). -/
def Entry.apply : Entry s → Path s → VEntries s → VEntry s
  | .le pre j post, _, V =>
      match V.get j with
      | some (.le F) => .le (pre.form.append (F.append post.form))
      | _ => .alias
  | .fld j sd, r, V =>
      match V.get j with
      | some (.fld a W) => .fld a (SideF.apply sd (r.sel a) W)
      | _ => .alias
  | .alias _, _, _ => .alias
  | .is F, r, V => .is (View.applyForm F r (.obj V))
/-- A side applied to a view.  `bot` keeps the view, reached only off typed inputs: there is no view
at `⊥` (`SideT.apply`). -/
def SideF.apply : SideF s → Path s → View s → View s
  | .none, _, W => W
  | .some F, r, W => View.applyForm F r W
  | .bot, _, W => W
  | .top, _, _ => .obj .nil
end

/-! ## The view of a literal at its own path -/

mutual
def litView : Path s → Defs s → VEntries s
  | _, .nil => .nil
  | l, .typ ds A _ =>
      .cons (.cons (litView l ds) (.le (.single (.eqv (.symm (.defP l A)))))) (.le (.single (.eqv (.defP l A))))
  | l, .fld ds a rhs => .cons (litView l ds) (.fld a (rhsView l a rhs))
  | l, .cls ds C _ => .cons (.cons (litView l ds) (.le (.single .bot))) (.le (.single (.eqv (.defP l C))))
def rhsView : Path s → Label → Rhs s → View s
  | _, _, .path _ => .obj (.cons .nil .alias)
  | _, _, .fn v => .fn v .nil
  | l, a, .nest _ ds => .obj (litView (l.sel a) ds)
end

/-- The view of a store variable: its closure, or the view of its literal at the variable.  A stored
cast has the view `none`, reached only off typed inputs: a typed store holds a lambda or a literal
at every variable (`Store.Typed.get_shape`, `varView_typed`). -/
def varView (σ : Store s) (x : BVar s .var) : View s :=
  match σ.get x with
  | .lam S t => .fn (.lam S t) .nil
  | .obj _ ds => .obj (litView (.var x) (ds.rename (Rename.subst x)))
  | .cast _ _ => .none

/-! ## The normalizer and the path view, as relations indexed by the types of the evidence

One rule per equation of T.7.  `Hnf σ Γ e S T F` is `σ ⊢ e ⇓ F` for `e : S ≤ T`, and
`PV σ Γ P T W` is `σ ⊢ P ⇓ₚ W` for `P : T`. -/

mutual
inductive Hnf (σ : Store s) (Γ : Ctx s) : LeCo s → Ty s → Ty s → Form s → Prop
  | refl : Hnf σ Γ (.refl T) T T .nil
  | trans : Hnf σ Γ e S M F → Hnf σ Γ f M T G → Hnf σ Γ (.trans e f) S T (F.append G)
  | top : Hnf σ Γ (.top T) T .top (.single .top)
  | bot : Hnf σ Γ (.bot T) .bot T (.single .bot)
  | eqToLe : EqCo.HasType Γ φ S T → Hnf σ Γ (.eqToLe φ) S T (.single (.eqv φ))
  | pi : LeCo.HasType Γ e S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) f T₁ T₂ →
      Hnf σ Γ (.pi e f) (.pi S₁ T₁) (.pi S₂ T₂) (.single (.pi e f))
  | obj : HnfM σ Γ Tel m Tel' Es → Hnf σ Γ (.obj Tel m) (.mu Tel) (.mu Tel') (.single (.obj Es))
  | pair : Hnf σ Γ e S (.mu Tel) F → Hnf σ Γ f S (.mu Tel') G →
      Hnf σ Γ (.pair Tel Tel' e f) S (.mu (Tel ++ Tel')) (.single (.pair F G))
  | bound : Tel.At i (.is T.weaken) → Hnf σ Γ (.bound Tel i) (.mu Tel) T (.single (.bnd i))
  | intoBnd : Hnf σ Γ e S T F → Hnf σ Γ (.intoBnd e) S (.mu (.cons .nil (.is T.weaken))) (.single (.into F))
  | member : PV σ Γ P S W → Hnf σ Γ e S (.mu Tel) F → Tel.At i (.le S' T') →
      (View.applyForm F P.path W) = .obj V → V.get i = some (.le G) →
      Hnf σ Γ (.member P e i) (S'.substPath P.path) (T'.substPath P.path) G
  | seal : Γ.clsAt p C = some U → Hnf σ Γ (.seal p C) U (.sel p C) (.single (.eqv (.symm (.defP p C))))
inductive HnfM (σ : Store s) (Γ : Ctx s) : Telescope (s,x) → Morphism s → Telescope (s,x) → Entries s → Prop
  | nil : HnfM σ Γ src .nil .nil .nil
  | le : HnfM σ Γ src m Tel Es → src.At j (.le X Y) → HnfS σ Γ pre S X pre' → HnfS σ Γ post Y T post' →
      HnfM σ Γ src (.le m pre j post) (.cons Tel (.le S T)) (.cons Es (.le pre' j post'))
  | fld : HnfM σ Γ src m Tel Es → src.At j (.fld a X) → HnfS σ Γ sd X T sd' →
      HnfM σ Γ src (.fld m j sd) (.cons Tel (.fld a T)) (.cons Es (.fld j sd'))
  | alias : HnfM σ Γ src m Tel Es → src.At j (.alias q) →
      HnfM σ Γ src (.alias m j) (.cons Tel (.alias q)) (.cons Es (.alias j))
  | is : HnfM σ Γ src m Tel Es → Hnf σ Γ e (.mu src) T F →
      HnfM σ Γ src (.is m e) (.cons Tel (.is T.weaken)) (.cons Es (.is F))
inductive HnfS (σ : Store s) (Γ : Ctx s) : Side s → Ty (s,x) → Ty (s,x) → SideF s → Prop
  | none : HnfS σ Γ .none X X .none
  | some : Hnf σ Γ e X Y F → HnfS σ Γ (.some e) X.weaken Y.weaken (.some F)
  | bot : HnfS σ Γ (.bot X) .bot X .bot
  | top : HnfS σ Γ (.top X) X .top .top
inductive PV (σ : Store s) (Γ : Ctx s) : PathCo s → Ty s → View s → Prop
  | var : Γ.ty x = T → PV σ Γ (.var x) T (varView σ x)
  | sel : PV σ Γ P (.mu Tel) (.obj V) → Tel.At i (.fld a T) → V.get i = some (.fld a W) →
      PV σ Γ (.sel P a i) (T.substPath P.path) W
  | cast : PV σ Γ P S W → Hnf σ Γ e S T F → PV σ Γ (.cast P e) T (View.applyForm F P.path W)
  | alias : PV σ Γ Q T W → PV σ Γ (.alias P₀ π Q) T (View.repath Γ W T π Q.path P₀.path)
  | sngl : PV σ Γ (.sngl P q π) (Ty.sngl q) (.obj (.cons .nil .alias))
  | fldI : PV σ Γ Q T W → PV σ Γ (.fldI p a Q) (.mu (.cons .nil (.fld a T.weaken))) (.obj (.cons .nil (.fld a W)))
  | unfold : PV σ Γ P (.mu Tel) W → PV σ Γ (.unfold P) (.mu (Tel.substPath P.path).weaken) W
  | fold : PV σ Γ P (.mu (Tel.substPath P.path).weaken) W → PV σ Γ (.fold Tel P) (.mu Tel) W
  | both : PV σ Γ P (.mu Tel) (.obj V) → PV σ Γ Q (.mu Tel') (.obj V') →
      PV σ Γ (.both Tel Tel' P Q) (.mu (Tel ++ Tel')) (.obj (V.append V'))
end

/-! ## Normalizing the stored casts of a function value -/

/-- `NormV σ Γ r v X W`: the casts of the value `v : X`, normalized and applied to the closure. -/
inductive NormV (σ : Store s) (Γ : Ctx s) (r : Path s) : Value s → Ty s → View s → Prop
  | lam : Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ → NormV σ Γ r (.lam S₀ t₀) (.pi S₀ T₀) (.fn (.lam S₀ t₀) .nil)
  | cast : NormV σ Γ r v X W → Hnf σ Γ e X Y G → NormV σ Γ r (.cast v e) Y (View.applyForm G r W)

/-! ## The machine head -/

/-- What the collapse of a function form has seen: nothing, an equality, a function inclusion, or a
function inclusion followed by an equality. -/
inductive Acc (s : Sig) : Type where
  | start : Acc s
  | eqv : EqCo s → Acc s
  | pi : LeCo s → LeCo (s,x) → Acc s
  | piEqv : LeCo s → LeCo (s,x) → EqCo s → Acc s

/-- The domain and codomain casts of `eqv χ` pushed into a following `pi e (z. f)`. -/
def pushDom (χ : EqCo s) (e : LeCo s) : LeCo s := .trans e (.eqToLe (.symm (.dom χ)))
def pushCod (χ : EqCo s) (f : LeCo (s,x)) : LeCo (s,x) := .trans (.eqToLe (.cod χ.weaken (.var .here))) f

/-- One atom pushed into the accumulator of the head.  The last equation, an atom that is neither
`eqv` nor `pi`, is reached only off typed inputs: a typed function form holds `eqv` and `pi` atoms
only (`collapse_typed`). -/
def Acc.step : Acc s → Atom s → Option (Acc s)
  | .start, .eqv φ => some (.eqv φ)
  | .eqv χ, .eqv φ => some (.eqv (.trans χ φ))
  | .pi d c, .eqv φ => some (.piEqv d c φ)
  | .piEqv d c χ, .eqv φ => some (.piEqv d c (.trans χ φ))
  | .start, .pi e f => some (.pi e f)
  | .eqv χ, .pi e f => some (.pi (pushDom χ e) (pushCod χ f))
  | .pi d c, .pi e f => some (.pi (.trans e d) (.trans (c.subst (CoSubst.selfCast e)) f))
  | .piEqv d c χ, .pi e f =>
      some (.pi (.trans (pushDom χ e) d) (.trans (c.subst (CoSubst.selfCast (pushDom χ e))) (pushCod χ f)))
  | _, _ => none

def Acc.head : Acc s → AppHead s
  | .start => .id
  | .eqv χ => .eqv χ
  | .pi d c => .pi d c
  | .piEqv d c χ =>
      .pi (.trans (.eqToLe (.symm (.dom χ))) d)
        (.trans (c.subst (CoSubst.selfCast (.eqToLe (.symm (.dom χ))))) (.eqToLe (.cod χ.weaken (.var .here))))

def Acc.run : Acc s → Form s → Option (Acc s)
  | a, .nil => some a
  | a, .cons A F => (a.step A).bind (Acc.run · F)

/-- The head of a function form: `id`, `eqv φ` or `pi d (z. c)`. -/
def collapse (F : Form s) : Option (AppHead s) := (Acc.run .start F).map Acc.head

/-! ## The application view, as the machine's parameter -/

/-- `σ ⊢ P ⇓ (lam (z : S₀) t₀, h)` (rule `AV`): over the context of the typed store, `P` is typed at
a function type, its path view there is a function view, its stored casts normalize to the closure
`lam (z : S₀) t₀` with a form, and the form collapses to the head `h`.  The typing conjunct is
repair 2 of the refutation. -/
def appView : AppView := fun {s} σ P S₀ t₀ h =>
  ∃ (Γ : Ctx s) (S : Ty s) (T : Ty (s,x)) (v : Value s) (F : Form s) (X : Ty s) (W : View s) (F' : Form s),
    Store.Typed σ Γ ∧ PathCo.HasType Γ P (.pi S T) ∧ PV σ Γ P (.pi S T) (.fn v F) ∧ NormV σ Γ P.path v X W ∧
    View.applyForm F P.path W = .fn (.lam S₀ t₀) F' ∧ collapse F' = some h

/-! ## The relations are functions of the evidence (repair 1)

The tree's typing is functional, read off the checker's completeness.  With the premises of `LE-Pi`
on `Hnf.pi`, every type index of `Hnf`, `HnfM`, `HnfS` and `PV` is fixed by the evidence, by a
telescope position or by an annotation, and so is every output.  The proofs are the refuter's
(`notes-pdot-c0/scratch-refute/R3_Repair.lean:263-536`) over the merged relations. -/

theorem LeCo.HasType.fun_idx {Γ : Ctx s} (h₁ : LeCo.HasType Γ e S T) (h₂ : LeCo.HasType Γ e S' T') :
    S = S' ∧ T = T' := by
  have a := synthLe_complete h₁
  rw [synthLe_complete h₂] at a
  cases a
  exact ⟨rfl, rfl⟩

theorem EqCo.HasType.fun_idx {Γ : Ctx s} (h₁ : EqCo.HasType Γ φ S T) (h₂ : EqCo.HasType Γ φ S' T') :
    S = S' ∧ T = T' := by
  have a := synthEq_complete h₁
  rw [synthEq_complete h₂] at a
  cases a
  exact ⟨rfl, rfl⟩

theorem Value.HasType.fun_idx {Γ : Ctx s} (h₁ : Value.HasType Γ v T) (h₂ : Value.HasType Γ v T') : T = T' := by
  have a := synthValue_complete h₁
  rw [synthValue_complete h₂] at a
  cases a
  rfl

theorem PathCo.HasType.fun_idx {Γ : Ctx s} (h₁ : PathCo.HasType Γ P T) (h₂ : PathCo.HasType Γ P T') : T = T' := by
  have a := synthPath_complete h₁
  rw [synthPath_complete h₂] at a
  cases a
  rfl

theorem Telescope.At.fun_idx {Tel : Telescope s} (h₁ : Tel.At i pr) (h₂ : Tel.At i pr') : pr = pr' := by
  have a := Telescope.get?_iff.2 h₁
  rw [Telescope.get?_iff.2 h₂] at a
  cases a
  rfl

theorem Ty.weaken_inj {T T' : Ty s} (h : T.weaken = T'.weaken) : T = T' := by
  have a : T.weaken.unweaken = some T := Ty.unweaken_iff.2 rfl
  have b : T'.weaken.unweaken = some T' := Ty.unweaken_iff.2 rfl
  rw [h, b] at a
  cases a
  rfl

/-- A typed store has one context. -/
theorem Store.Typed.ctx_unique : ∀ {σ : Store s} {Γ Γ' : Ctx s}, Store.Typed σ Γ → Store.Typed σ Γ' → Γ = Γ'
  | _, _, _, .nil, h => by cases h; rfl
  | _, _, _, .lam h₀ hv, h => by
      cases h with
      | lam h₀' hv' =>
          cases Store.Typed.ctx_unique h₀ h₀'
          cases Value.HasType.fun_idx hv hv'
          rfl
  | _, _, _, .obj h₀ _, h => by
      cases h with
      | obj h₀' _ =>
          cases Store.Typed.ctx_unique h₀ h₀'
          rfl

/-! Constructor injections over the indexed families. -/

theorem Ty.mu_inj {Tel Tel' : Telescope (s,x)} (h : Ty.mu Tel = Ty.mu Tel') : Tel = Tel' := by cases h; rfl
theorem Pr.is_inj {T T' : Ty s} (h : Pr.is T = Pr.is T') : T = T' := by cases h; rfl
theorem Pr.le_inj {S T S' T' : Ty s} (h : Pr.le S T = Pr.le S' T') : S = S' ∧ T = T' := by cases h; exact ⟨rfl, rfl⟩
theorem Pr.fld_inj {a a' : Label} {T T' : Ty s} (h : Pr.fld a T = Pr.fld a' T') : a = a' ∧ T = T' := by
  cases h; exact ⟨rfl, rfl⟩
theorem Pr.alias_inj {q q' : Path s} (h : Pr.alias q = Pr.alias q') : q = q' := by cases h; rfl
theorem View.obj_inj {V V' : VEntries s} (h : View.obj V = View.obj V') : V = V' := by cases h; rfl
theorem View.fn_inj {v v' : Value s} {F F' : Form s} (h : View.fn v F = View.fn v' F') : v = v' ∧ F = F' := by
  cases h; exact ⟨rfl, rfl⟩
theorem VEntry.le_inj {F F' : Form s} (h : VEntry.le F = VEntry.le F') : F = F' := by cases h; rfl
theorem VEntry.fld_inj {a a' : Label} {W W' : View s} (h : VEntry.fld a W = VEntry.fld a' W') : a = a' ∧ W = W' := by
  cases h; exact ⟨rfl, rfl⟩
theorem Value.lam_inj {S S' : Ty s} {t t' : Tm (s,x)} (h : Value.lam S t = Value.lam S' t') : S = S' ∧ t = t' := by
  cases h; exact ⟨rfl, rfl⟩

section Det
variable {σ : Store s} {Γ : Ctx s}

mutual
theorem Hnf.idx : Hnf σ Γ e S T F → ∀ {S' T' F'}, Hnf σ Γ e S' T' F' → S = S' ∧ T = T'
  | .refl, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | .trans h₁ h₂, _, _, _, h => by
      cases h with
      | trans h₁' h₂' =>
          obtain ⟨e₁, e₂⟩ := Hnf.idx h₁ h₁'
          subst e₂
          exact ⟨e₁, (Hnf.idx h₂ h₂').2⟩
  | .top, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | .bot, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | .eqToLe hφ, _, _, _, h => by
      cases h with
      | eqToLe hφ' => exact EqCo.HasType.fun_idx hφ hφ'
  | .pi he hf, _, _, _, h => by
      cases h with
      | pi he' hf' =>
          obtain ⟨e₁, e₂⟩ := LeCo.HasType.fun_idx he he'
          subst e₁; subst e₂
          obtain ⟨e₃, e₄⟩ := LeCo.HasType.fun_idx hf hf'
          subst e₃; subst e₄
          exact ⟨rfl, rfl⟩
  | .obj hm, _, _, _, h => by
      cases h with
      | obj hm' => rw [HnfM.idx hm hm']; exact ⟨rfl, rfl⟩
  | .pair h₁ h₂, _, _, _, h => by
      cases h with
      | pair h₁' h₂' => exact ⟨(Hnf.idx h₁ h₁').1, rfl⟩
  | .bound hi, _, _, _, h => by
      cases h with
      | bound hi' =>
          rw [Ty.weaken_inj (Pr.is_inj (Telescope.At.fun_idx hi hi'))]
          exact ⟨rfl, rfl⟩
  | .intoBnd h₁, _, _, _, h => by
      cases h with
      | intoBnd h₁' =>
          obtain ⟨e₁, e₂⟩ := Hnf.idx h₁ h₁'
          subst e₁; subst e₂
          exact ⟨rfl, rfl⟩
  | .member _ he hi _ _, _, _, _, h => by
      cases h with
      | member _ he' hi' _ _ =>
          have e₁ := Ty.mu_inj (Hnf.idx he he').2
          subst e₁
          obtain ⟨e₂, e₃⟩ := Pr.le_inj (Telescope.At.fun_idx hi hi')
          subst e₂; subst e₃
          exact ⟨rfl, rfl⟩
  | .seal h₁, _, _, _, h => by
      cases h with
      | «seal» h₁' => rw [h₁] at h₁'; exact ⟨Option.some.inj h₁', rfl⟩
theorem HnfM.idx : HnfM σ Γ src m Tel Es → ∀ {Tel' Es'}, HnfM σ Γ src m Tel' Es' → Tel = Tel'
  | .nil, _, _, h => by cases h; rfl
  | .le hm hj hpre hpost, _, _, h => by
      cases h with
      | le hm' hj' hpre' hpost' =>
          obtain ⟨eX, eY⟩ := Pr.le_inj (Telescope.At.fun_idx hj hj')
          subst eX; subst eY
          rw [HnfM.idx hm hm', HnfS.idx_pre hpre hpre' rfl, HnfS.idx_post hpost hpost' rfl]
  | .fld hm hj hsd, _, _, h => by
      cases h with
      | fld hm' hj' hsd' =>
          obtain ⟨ea, eX⟩ := Pr.fld_inj (Telescope.At.fun_idx hj hj')
          subst ea; subst eX
          rw [HnfM.idx hm hm', HnfS.idx_post hsd hsd' rfl]
  | .alias hm hj, _, _, h => by
      cases h with
      | alias hm' hj' =>
          have eq := Pr.alias_inj (Telescope.At.fun_idx hj hj')
          subst eq
          rw [HnfM.idx hm hm']
  | .is hm he, _, _, h => by
      cases h with
      | is hm' he' => rw [HnfM.idx hm hm', (Hnf.idx he he').2]
theorem HnfS.idx_pre : HnfS σ Γ sd S X sd₁ → ∀ {S' X' sd₂}, HnfS σ Γ sd S' X' sd₂ → X = X' → S = S'
  | .none, _, _, _, h, eX => by cases h; exact eX
  | .some h₁, _, _, _, h, eX => by
      cases h with
      | some h₁' =>
          have eY := Ty.weaken_inj eX
          subst eY
          rw [(Hnf.idx h₁ h₁').1]
  | .bot, _, _, _, h, _ => by cases h; rfl
  | .top, _, _, _, h, _ => by cases h; rfl
theorem HnfS.idx_post : HnfS σ Γ sd Y T sd₁ → ∀ {Y' T' sd₂}, HnfS σ Γ sd Y' T' sd₂ → Y = Y' → T = T'
  | .none, _, _, _, h, eY => by cases h; exact eY
  | .some h₁, _, _, _, h, eY => by
      cases h with
      | some h₁' =>
          have eX := Ty.weaken_inj eY
          subst eX
          rw [(Hnf.idx h₁ h₁').2]
  | .bot, _, _, _, h, _ => by cases h; rfl
  | .top, _, _, _, h, _ => by cases h; rfl
theorem PV.idx : PV σ Γ P T W → ∀ {T' W'}, PV σ Γ P T' W' → T = T'
  | .var h, _, _, h' => by cases h'; rename_i h''; exact h.symm.trans h''
  | .sel hP hi _, _, _, h => by
      cases h with
      | sel hP' hi' _ =>
          have e := Ty.mu_inj (PV.idx hP hP')
          subst e
          rw [(Pr.fld_inj (Telescope.At.fun_idx hi hi')).2]
  | .cast _ he, _, _, h => by
      cases h with
      | cast _ he' => exact (Hnf.idx he he').2
  | .alias hQ, _, _, h => by
      cases h with
      | alias hQ' => exact PV.idx hQ hQ'
  | .sngl, _, _, h => by cases h; rfl
  | .fldI hQ, _, _, h => by
      cases h with
      | fldI hQ' => rw [PV.idx hQ hQ']
  | .unfold hP, _, _, h => by
      cases h with
      | unfold hP' =>
          rw [Ty.mu_inj (PV.idx hP hP')]
  | .fold _, _, _, h => by cases h; rfl
  | .both _ _, _, _, h => by cases h; rfl
end

mutual
theorem Hnf.det : Hnf σ Γ e S T F → ∀ {S' T' F'}, Hnf σ Γ e S' T' F' → F = F'
  | .refl, _, _, _, h => by cases h; rfl
  | .trans h₁ h₂, _, _, _, h => by
      cases h with
      | trans h₁' h₂' => rw [Hnf.det h₁ h₁', Hnf.det h₂ h₂']
  | .top, _, _, _, h => by cases h; rfl
  | .bot, _, _, _, h => by cases h; rfl
  | .eqToLe _, _, _, _, h => by cases h; rfl
  | .pi _ _, _, _, _, h => by cases h; rfl
  | .obj hm, _, _, _, h => by
      cases h with
      | obj hm' => rw [HnfM.det hm hm']
  | .pair h₁ h₂, _, _, _, h => by
      cases h with
      | pair h₁' h₂' => rw [Hnf.det h₁ h₁', Hnf.det h₂ h₂']
  | .bound _, _, _, _, h => by cases h; rfl
  | .intoBnd h₁, _, _, _, h => by
      cases h with
      | intoBnd h₁' => rw [Hnf.det h₁ h₁']
  | .member hP he _ hV hg, _, _, _, h => by
      cases h with
      | member hP' he' _ hV' hg' =>
          rw [PV.det hP hP', Hnf.det he he', hV'] at hV
          have e := View.obj_inj hV
          subst e
          rw [hg'] at hg
          exact (VEntry.le_inj (Option.some.inj hg)).symm
  | .seal _, _, _, _, h => by cases h; rfl
theorem HnfM.det : HnfM σ Γ src m Tel Es → ∀ {Tel' Es'}, HnfM σ Γ src m Tel' Es' → Es = Es'
  | .nil, _, _, h => by cases h; rfl
  | .le hm _ hpre hpost, _, _, h => by
      cases h with
      | le hm' _ hpre' hpost' => rw [HnfM.det hm hm', HnfS.det hpre hpre', HnfS.det hpost hpost']
  | .fld hm _ hsd, _, _, h => by
      cases h with
      | fld hm' _ hsd' => rw [HnfM.det hm hm', HnfS.det hsd hsd']
  | .alias hm _, _, _, h => by
      cases h with
      | alias hm' _ => rw [HnfM.det hm hm']
  | .is hm he, _, _, h => by
      cases h with
      | is hm' he' => rw [HnfM.det hm hm', Hnf.det he he']
theorem HnfS.det : HnfS σ Γ sd X Y sd₁ → ∀ {X' Y' sd₂}, HnfS σ Γ sd X' Y' sd₂ → sd₁ = sd₂
  | .none, _, _, _, h => by cases h; rfl
  | .some h₁, _, _, _, h => by
      cases h with
      | some h₁' => rw [Hnf.det h₁ h₁']
  | .bot, _, _, _, h => by cases h; rfl
  | .top, _, _, _, h => by cases h; rfl
theorem PV.det : PV σ Γ P T W → ∀ {T' W'}, PV σ Γ P T' W' → W = W'
  | .var _, _, _, h => by cases h; rfl
  | .sel hP _ hg, _, _, h => by
      cases h with
      | sel hP' _ hg' =>
          have e := View.obj_inj (PV.det hP hP')
          subst e
          rw [hg'] at hg
          exact ((VEntry.fld_inj (Option.some.inj hg)).2).symm
  | .cast hP he, _, _, h => by
      cases h with
      | cast hP' he' => rw [PV.det hP hP', Hnf.det he he']
  | .alias hQ, _, _, h => by
      cases h with
      | alias hQ' => rw [PV.det hQ hQ', PV.idx hQ hQ']
  | .sngl, _, _, h => by cases h; rfl
  | .fldI hQ, _, _, h => by
      cases h with
      | fldI hQ' => rw [PV.det hQ hQ']
  | .unfold hP, _, _, h => by
      cases h with
      | unfold hP' => exact PV.det hP hP'
  | .fold hP, _, _, h => by
      cases h with
      | fold hP' => exact PV.det hP hP'
  | .both hP hQ, _, _, h => by
      cases h with
      | both hP' hQ' =>
          rw [View.obj_inj (PV.det hP hP'), View.obj_inj (PV.det hQ hQ')]
end

theorem NormV.det {r : Path s} : NormV σ Γ r v X W → ∀ {X' W'}, NormV σ Γ r v X' W' → W = W'
  | .lam _, _, _, h => by cases h; rfl
  | .cast hN hH, _, _, h => by
      cases h with
      | cast hN' hH' => rw [NormV.det hN hN', Hnf.det hH hH']

end Det

/-! ## The application view is deterministic (repair 2) -/

/-- `AppView.Det`, which the tree's `Step.det` asks (`Machine.lean:80`). -/
theorem appView_det : AppView.Det appView := by
  intro s σ P S₀ S₀' t₀ t₀' h h' ⟨Γ, S, T, v, F, X, W, F', hσ, _, hPV, hN, hA, hc⟩
    ⟨Γ₂, S₂, T₂, v₂, F₂, X₂, W₂, F₂', hσ₂, _, hPV₂, hN₂, hA₂, hc₂⟩
  cases Store.Typed.ctx_unique hσ hσ₂
  obtain ⟨ev, eF⟩ := View.fn_inj (PV.det hPV hPV₂)
  subst ev; subst eF
  cases NormV.det hN hN₂
  rw [hA₂] at hA
  obtain ⟨el, eF'⟩ := View.fn_inj hA
  obtain ⟨eS, et⟩ := Value.lam_inj el
  subst eS; subst et; subst eF'
  rw [hc₂] at hc
  exact ⟨rfl, rfl, (Option.some.inj hc).symm⟩

end Nominal.FCn

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The computable versions

`Store.ctx` builds the context of a store by `ST-Nil`, `ST-Lam` and `ST-Obj`.  `hnf`, `hnfM`,
`hnfSPre`, `hnfSPost`, `pview` and `normV` read the rules of `Hnf`, `HnfM`, `HnfS`, `PV` and `NormV`
left to right, and each computes the indices of its relation with its output, as the checker's
`synth*` functions do.  A side fixes one index from the other (`HS-None` relates `X` to `X`), so a side
has two functions, as `synthPre` and `synthPost`.  `appViewOf` computes the application view `AV`.
Every function is structural on the evidence.  Each graph lemma holds with no typing hypothesis:
`X_sound` reads the relation off a computation and `X_complete` computes a derivation. -/

/-- The context of a store, by `ST-Nil`, `ST-Lam` and `ST-Obj`. -/
def Store.ctx : Store s → Option (Ctx s)
  | .nil => some .nil                                                             -- ST-Nil
  | .cons σ v =>
      match Store.ctx σ, v with
      | some Γ, .lam S t =>                                                       -- ST-Lam, z of t
          match synthValue Γ (.lam S t) with
          | some T => some (Γ.cons (.opaque T))
          | none => none
      | some Γ, .obj Tel ds =>                                                    -- ST-Obj, z of ds, w of Tel
          if synthValue Γ (.obj Tel ds) = some (.mu Tel) then some (Γ.cons (.transparent (.mu Tel) ds.block))
          else none
      | some _, .cast _ _ => none                                                 -- no rule stores a cast
      | none, _ => none

mutual
/-- `hnf σ Γ e = some (S, T, F)` when `σ ⊢ e ⇓ F : S ≤ T`. -/
def hnf (σ : Store s) (Γ : Ctx s) : LeCo s → Option (Ty s × Ty s × Form s)
  | .refl T => some (T, T, .nil)                                                  -- HN-Refl
  | .trans e f =>                                                                 -- HN-Trans
      match hnf σ Γ e, hnf σ Γ f with
      | some (S, M, F), some (M', T, G) => if M = M' then some (S, T, F.append G) else none
      | _, _ => none
  | .top T => some (T, .top, .single .top)                                        -- HN-Top
  | .bot T => some (.bot, T, .single .bot)                                        -- HN-Bot
  | .eqToLe φ =>                                                                  -- HN-Eq
      match synthEq Γ φ with
      | some (S, T) => some (S, T, .single (.eqv φ))
      | none => none
  | .pi e f =>                                                                    -- HN-Pi, z of f
      match synthLe Γ e with
      | some (S₂, S₁) =>
          match synthLe (Γ.cons (.opaque S₂)) f with
          | some (T₁, T₂) => some (.pi S₁ T₁, .pi S₂ T₂, .single (.pi e f))
          | none => none
      | none => none
  | .obj Tel m =>                                                                 -- HN-Obj, w of Tel
      match hnfM σ Γ Tel m with
      | some (Tel', Es) => some (.mu Tel, .mu Tel', .single (.obj Es))
      | none => none
  | .pair Tel Tel' e f =>                                                         -- HN-Pair, w of Tel Tel'
      match hnf σ Γ e, hnf σ Γ f with
      | some (S, T, F), some (S', T', G) =>
          if S' = S ∧ T = .mu Tel ∧ T' = .mu Tel' then some (S, .mu (Tel ++ Tel'), .single (.pair F G)) else none
      | _, _ => none
  | .bound Tel i =>                                                               -- HN-Bound, w of Tel
      match Tel.get? i with
      | some (.is T') =>
          match T'.unweaken with
          | some T => some (.mu Tel, T, .single (.bnd i))
          | none => none
      | _ => none
  | .intoBnd e =>                                                                 -- HN-IntoBnd
      match hnf σ Γ e with
      | some (S, T, F) => some (S, .mu (.cons .nil (.is T.weaken)), .single (.into F))
      | none => none
  | .member P e i =>                                                              -- HN-Member
      match pview σ Γ P, hnf σ Γ e with
      | some (S, W), some (S', .mu Tel, F) =>
          if S = S' then
            match Tel.get? i, View.applyForm F P.path W with
            | some (.le S₁ T₁), .obj V =>
                match V.get i with
                | some (.le G) => some (S₁.substPath P.path, T₁.substPath P.path, G)
                | _ => none
            | _, _ => none
          else none
      | _, _ => none
  | .seal p C =>                                                                  -- HN-Seal₁
      match Γ.clsAt p C with
      | some U => some (U, .sel p C, .single (.eqv (.symm (.defP p C))))
      | none => none
/-- `hnfM σ Γ src m = some (Tel, Es)` when `σ ⊢ m ⇓ₘ Es : src ⇒ Tel`. -/
def hnfM (σ : Store s) (Γ : Ctx s) (src : Telescope (s,x)) : Morphism s → Option (Telescope (s,x) × Entries s)
  | .nil => some (.nil, .nil)                                                     -- HM-Nil
  | .le m pre j post =>                                                           -- HM-Le
      match hnfM σ Γ src m, src.get? j with
      | some (Tel, Es), some (.le X Y) =>
          match hnfSPre σ Γ pre X, hnfSPost σ Γ post Y with
          | some (S, pre'), some (T, post') => some (.cons Tel (.le S T), .cons Es (.le pre' j post'))
          | _, _ => none
      | _, _ => none
  | .fld m j sd =>                                                                -- HM-Fld
      match hnfM σ Γ src m, src.get? j with
      | some (Tel, Es), some (.fld a X) =>
          match hnfSPost σ Γ sd X with
          | some (T, sd') => some (.cons Tel (.fld a T), .cons Es (.fld j sd'))
          | none => none
      | _, _ => none
  | .alias m j =>                                                                 -- HM-Alias
      match hnfM σ Γ src m, src.get? j with
      | some (Tel, Es), some (.alias q) => some (.cons Tel (.alias q), .cons Es (.alias j))
      | _, _ => none
  | .is m e =>                                                                    -- HM-Is
      match hnfM σ Γ src m, hnf σ Γ e with
      | some (Tel, Es), some (S, T, F) =>
          if S = .mu src then some (.cons Tel (.is T.weaken), .cons Es (.is F)) else none
      | _, _ => none
/-- `hnfSPre σ Γ sd X = some (S, sd')` when `σ ⊢ sd ⇓ˢ sd' : S ≤ X`. -/
def hnfSPre (σ : Store s) (Γ : Ctx s) : Side s → Ty (s,x) → Option (Ty (s,x) × SideF s)
  | .none, X => some (X, .none)                                                   -- HS-None
  | .some e, X =>                                                                 -- HS-Some
      match hnf σ Γ e with
      | some (S, T, F) => if T.weaken = X then some (S.weaken, .some F) else none
      | none => none
  | .bot X', X => if X' = X then some (.bot, .bot) else none                      -- HS-Bot
  | .top X', X => if X = .top then some (X', .top) else none                      -- HS-Top
/-- `hnfSPost σ Γ sd Y = some (T, sd')` when `σ ⊢ sd ⇓ˢ sd' : Y ≤ T`. -/
def hnfSPost (σ : Store s) (Γ : Ctx s) : Side s → Ty (s,x) → Option (Ty (s,x) × SideF s)
  | .none, Y => some (Y, .none)                                                   -- HS-None
  | .some e, Y =>                                                                 -- HS-Some
      match hnf σ Γ e with
      | some (S, T, F) => if S.weaken = Y then some (T.weaken, .some F) else none
      | none => none
  | .bot X', Y => if Y = .bot then some (X', .bot) else none                      -- HS-Bot
  | .top X', Y => if X' = Y then some (.top, .top) else none                      -- HS-Top
/-- `pview σ Γ P = some (T, W)` when `σ ⊢ P ⇓ₚ W : T`. -/
def pview (σ : Store s) (Γ : Ctx s) : PathCo s → Option (Ty s × View s)
  | .var x => some (Γ.ty x, varView σ x)                                          -- PV-Var
  | .sel P a i =>                                                                 -- PV-Sel
      match pview σ Γ P with
      | some (.mu Tel, .obj V) =>
          match Tel.get? i, V.get i with
          | some (.fld a' T), some (.fld a'' W) =>
              if a' = a ∧ a'' = a then some (T.substPath P.path, W) else none
          | _, _ => none
      | _ => none
  | .cast P e =>                                                                  -- PV-Cast
      match pview σ Γ P, hnf σ Γ e with
      | some (S, W), some (S', T, F) => if S = S' then some (T, View.applyForm F P.path W) else none
      | _, _ => none
  | .alias P₀ π Q =>                                                              -- PV-Alias
      match pview σ Γ Q with
      | some (T, W) => some (T, View.repath Γ W T π Q.path P₀.path)
      | none => none
  | .sngl _ q _ => some (Ty.sngl q, .obj (.cons .nil .alias))                     -- PV-Sngl
  | .fldI _ a Q =>                                                                -- PV-FldI
      match pview σ Γ Q with
      | some (T, W) => some (.mu (.cons .nil (.fld a T.weaken)), .obj (.cons .nil (.fld a W)))
      | none => none
  | .fold Tel P =>                                                                -- PV-Fold, w of Tel
      match pview σ Γ P with
      | some (T, W) => if T = .mu (Tel.substPath P.path).weaken then some (.mu Tel, W) else none
      | none => none
  | .unfold P =>                                                                  -- PV-Unfold
      match pview σ Γ P with
      | some (.mu Tel, W) => some (.mu (Tel.substPath P.path).weaken, W)
      | _ => none
  | .both Tel Tel' P Q =>                                                         -- PV-Both, w of Tel Tel'
      match pview σ Γ P, pview σ Γ Q with
      | some (T, .obj V), some (T', .obj V') =>
          if T = .mu Tel ∧ T' = .mu Tel' then some (.mu (Tel ++ Tel'), .obj (V.append V')) else none
      | _, _ => none
end

/-- `normV σ Γ r v = some (X, W)` when `σ ⊢[r] v ⇓ᵥ W : X`. -/
def normV (σ : Store s) (Γ : Ctx s) (r : Path s) : Value s → Option (Ty s × View s)
  | .lam S₀ t₀ =>                                                                 -- NV-Lam, z of t₀
      match synthTm (Γ.cons (.opaque S₀)) t₀ with
      | some T₀ => some (.pi S₀ T₀, .fn (.lam S₀ t₀) .nil)
      | none => none
  | .cast v e =>                                                                  -- NV-Cast
      match normV σ Γ r v, hnf σ Γ e with
      | some (X, W), some (X', Y, G) => if X = X' then some (Y, View.applyForm G r W) else none
      | _, _ => none
  | .obj _ _ => none                                                              -- no rule at a literal

/-- The application view, computed: the closure and the head of `AV`. -/
def appViewOf (σ : Store s) (P : PathCo s) : Option (Ty s × Tm (s,x) × AppHead s) :=
  match Store.ctx σ with
  | none => none
  | some Γ =>
      match synthPath Γ P, pview σ Γ P with
      | some (.pi S T), some (U, .fn v F) =>
          if U = .pi S T then
            match normV σ Γ P.path v with
            | some (_, W) =>
                match View.applyForm F P.path W with
                | .fn (.lam S₀ t₀) F' => (collapse F').map (fun h => (S₀, t₀, h))
                | _ => none
            | none => none
          else none
      | _, _ => none

section Graph
variable {σ : Store s} {Γ : Ctx s}

mutual
theorem hnf_sound : ∀ (e : LeCo s) {S T : Ty s} {F : Form s}, hnf σ Γ e = some (S, T, F) → Hnf σ Γ e S T F
  | .refl _, _, _, _, h => by
      simp only [hnf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .refl
  | .trans e f, _, _, _, h => by
      cases h₁ : hnf σ Γ e with
      | none => simp [hnf, h₁] at h
      | some r₁ =>
          obtain ⟨S₁, M, F₁⟩ := r₁
          cases h₂ : hnf σ Γ f with
          | none => simp [hnf, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨M', T₁, G⟩ := r₂
              simp only [hnf, h₁, h₂] at h
              split at h
              · rename_i hM
                subst hM
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .trans (hnf_sound e h₁) (hnf_sound f h₂)
              · cases h
  | .top _, _, _, _, h => by
      simp only [hnf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .top
  | .bot _, _, _, _, h => by
      simp only [hnf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .bot
  | .eqToLe φ, _, _, _, h => by
      cases h₁ : synthEq Γ φ with
      | none => simp [hnf, h₁] at h
      | some r =>
          obtain ⟨S₁, T₁⟩ := r
          simp only [hnf, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .eqToLe (synthEq_sound h₁)
  | .pi e f, _, _, _, h => by
      cases h₁ : synthLe Γ e with
      | none => simp [hnf, h₁] at h
      | some r =>
          obtain ⟨S₂, S₁⟩ := r
          cases h₂ : synthLe (Γ.cons (.opaque S₂)) f with
          | none => simp [hnf, h₁, h₂] at h
          | some r' =>
              obtain ⟨T₁, T₂⟩ := r'
              simp only [hnf, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact .pi (synthLe_sound h₁) (synthLe_sound h₂)
  | .obj Tel m, _, _, _, h => by
      cases h₁ : hnfM σ Γ Tel m with
      | none => simp [hnf, h₁] at h
      | some r =>
          obtain ⟨Tel', Es⟩ := r
          simp only [hnf, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .obj (hnfM_sound Tel m h₁)
  | .pair Tel Tel' e f, _, _, _, h => by
      cases h₁ : hnf σ Γ e with
      | none => simp [hnf, h₁] at h
      | some r₁ =>
          obtain ⟨S₁, T₁, F₁⟩ := r₁
          cases h₂ : hnf σ Γ f with
          | none => simp [hnf, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨S₂, T₂, G⟩ := r₂
              simp only [hnf, h₁, h₂] at h
              split at h
              · rename_i hc
                obtain ⟨rfl, rfl, rfl⟩ := hc
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .pair (hnf_sound e h₁) (hnf_sound f h₂)
              · cases h
  | .bound Tel i, _, _, _, h => by
      cases h₁ : Tel.get? i with
      | none => simp [hnf, h₁] at h
      | some pr =>
          cases pr with
          | is T' =>
              cases h₂ : T'.unweaken with
              | none => simp [hnf, h₁, h₂] at h
              | some T₁ =>
                  simp only [hnf, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  have e := Ty.unweaken_iff.1 h₂
                  subst e
                  exact .bound (Telescope.get?_iff.1 h₁)
          | le _ _ => simp [hnf, h₁] at h
          | fld _ _ => simp [hnf, h₁] at h
          | alias _ => simp [hnf, h₁] at h
  | .intoBnd e, _, _, _, h => by
      cases h₁ : hnf σ Γ e with
      | none => simp [hnf, h₁] at h
      | some r =>
          obtain ⟨S₁, T₁, F₁⟩ := r
          simp only [hnf, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .intoBnd (hnf_sound e h₁)
  | .member P e i, _, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [hnf, h₁] at h
      | some r₁ =>
          obtain ⟨S₁, W⟩ := r₁
          cases h₂ : hnf σ Γ e with
          | none => simp [hnf, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨S₂, M, F₁⟩ := r₂
              cases M with
              | mu Tel =>
                  simp only [hnf, h₁, h₂] at h
                  split at h
                  · rename_i hS
                    subst hS
                    split at h
                    · rename_i S' T' V hg hV
                      split at h
                      · rename_i G hG
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact .member (pview_sound P h₁) (hnf_sound e h₂) (Telescope.get?_iff.1 hg) hV hG
                      · cases h
                    · cases h
                  · cases h
              | bot => simp [hnf, h₁, h₂] at h
              | sel _ _ => simp [hnf, h₁, h₂] at h
              | pi _ _ => simp [hnf, h₁, h₂] at h
  | .seal p C, _, _, _, h => by
      cases h₁ : Γ.clsAt p C with
      | none => simp [hnf, h₁] at h
      | some U =>
          simp only [hnf, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .seal h₁
theorem hnfM_sound (src : Telescope (s,x)) : ∀ (m : Morphism s) {Tel : Telescope (s,x)} {Es : Entries s},
    hnfM σ Γ src m = some (Tel, Es) → HnfM σ Γ src m Tel Es
  | .nil, _, _, h => by
      simp only [hnfM, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .nil
  | .le m pre j post, _, _, h => by
      cases h₁ : hnfM σ Γ src m with
      | none => simp [hnfM, h₁] at h
      | some r =>
          obtain ⟨Tel, Es⟩ := r
          cases hj : src.get? j with
          | none => simp [hnfM, h₁, hj] at h
          | some pr =>
              cases pr with
              | le X Y =>
                  cases h₂ : hnfSPre σ Γ pre X with
                  | none => simp [hnfM, h₁, hj, h₂] at h
                  | some r₂ =>
                      obtain ⟨S, pre'⟩ := r₂
                      cases h₃ : hnfSPost σ Γ post Y with
                      | none => simp [hnfM, h₁, hj, h₂, h₃] at h
                      | some r₃ =>
                          obtain ⟨T, post'⟩ := r₃
                          simp only [hnfM, h₁, hj, h₂, h₃, Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, rfl⟩ := h
                          exact .le (hnfM_sound src m h₁) (Telescope.get?_iff.1 hj) (hnfSPre_sound pre h₂)
                            (hnfSPost_sound post h₃)
              | fld _ _ => simp [hnfM, h₁, hj] at h
              | alias _ => simp [hnfM, h₁, hj] at h
              | is _ => simp [hnfM, h₁, hj] at h
  | .fld m j sd, _, _, h => by
      cases h₁ : hnfM σ Γ src m with
      | none => simp [hnfM, h₁] at h
      | some r =>
          obtain ⟨Tel, Es⟩ := r
          cases hj : src.get? j with
          | none => simp [hnfM, h₁, hj] at h
          | some pr =>
              cases pr with
              | fld a X =>
                  cases h₂ : hnfSPost σ Γ sd X with
                  | none => simp [hnfM, h₁, hj, h₂] at h
                  | some r₂ =>
                      obtain ⟨T, sd'⟩ := r₂
                      simp only [hnfM, h₁, hj, h₂, Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact .fld (hnfM_sound src m h₁) (Telescope.get?_iff.1 hj) (hnfSPost_sound sd h₂)
              | le _ _ => simp [hnfM, h₁, hj] at h
              | alias _ => simp [hnfM, h₁, hj] at h
              | is _ => simp [hnfM, h₁, hj] at h
  | .alias m j, _, _, h => by
      cases h₁ : hnfM σ Γ src m with
      | none => simp [hnfM, h₁] at h
      | some r =>
          obtain ⟨Tel, Es⟩ := r
          cases hj : src.get? j with
          | none => simp [hnfM, h₁, hj] at h
          | some pr =>
              cases pr with
              | alias q =>
                  simp only [hnfM, h₁, hj, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact .alias (hnfM_sound src m h₁) (Telescope.get?_iff.1 hj)
              | le _ _ => simp [hnfM, h₁, hj] at h
              | fld _ _ => simp [hnfM, h₁, hj] at h
              | is _ => simp [hnfM, h₁, hj] at h
  | .is m e, _, _, h => by
      cases h₁ : hnfM σ Γ src m with
      | none => simp [hnfM, h₁] at h
      | some r =>
          obtain ⟨Tel, Es⟩ := r
          cases h₂ : hnf σ Γ e with
          | none => simp [hnfM, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨S, T, F⟩ := r₂
              simp only [hnfM, h₁, h₂] at h
              split at h
              · rename_i hS
                subst hS
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .is (hnfM_sound src m h₁) (hnf_sound e h₂)
              · cases h
theorem hnfSPre_sound : ∀ (sd : Side s) {X S : Ty (s,x)} {sd' : SideF s},
    hnfSPre σ Γ sd X = some (S, sd') → HnfS σ Γ sd S X sd'
  | .none, _, _, _, h => by
      simp only [hnfSPre, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .none
  | .some e, _, _, _, h => by
      cases h₁ : hnf σ Γ e with
      | none => simp [hnfSPre, h₁] at h
      | some r =>
          obtain ⟨S, T, F⟩ := r
          simp only [hnfSPre, h₁] at h
          split at h
          · rename_i hT
            subst hT
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .some (hnf_sound e h₁)
          · cases h
  | .bot _, _, _, _, h => by
      simp only [hnfSPre] at h
      split at h
      · rename_i hX
        subst hX
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .bot
      · cases h
  | .top _, _, _, _, h => by
      simp only [hnfSPre] at h
      split at h
      · rename_i hX
        subst hX
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .top
      · cases h
theorem hnfSPost_sound : ∀ (sd : Side s) {Y T : Ty (s,x)} {sd' : SideF s},
    hnfSPost σ Γ sd Y = some (T, sd') → HnfS σ Γ sd Y T sd'
  | .none, _, _, _, h => by
      simp only [hnfSPost, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .none
  | .some e, _, _, _, h => by
      cases h₁ : hnf σ Γ e with
      | none => simp [hnfSPost, h₁] at h
      | some r =>
          obtain ⟨S, T, F⟩ := r
          simp only [hnfSPost, h₁] at h
          split at h
          · rename_i hS
            subst hS
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .some (hnf_sound e h₁)
          · cases h
  | .bot _, _, _, _, h => by
      simp only [hnfSPost] at h
      split at h
      · rename_i hY
        subst hY
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .bot
      · cases h
  | .top _, _, _, _, h => by
      simp only [hnfSPost] at h
      split at h
      · rename_i hY
        subst hY
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .top
      · cases h
theorem pview_sound : ∀ (P : PathCo s) {T : Ty s} {W : View s}, pview σ Γ P = some (T, W) → PV σ Γ P T W
  | .var x, _, _, h => by
      simp only [pview, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .var rfl
  | .sel P a i, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T₁, W₁⟩ := r
          cases T₁ with
          | mu Tel =>
              cases W₁ with
              | obj V =>
                  simp only [pview, h₁] at h
                  split at h
                  · rename_i a' T a'' W hg hv
                    split at h
                    · rename_i ha
                      obtain ⟨rfl, rfl⟩ := ha
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact .sel (pview_sound P h₁) (Telescope.get?_iff.1 hg) hv
                    · cases h
                  · cases h
              | fn _ _ => simp [pview, h₁] at h
              | none => simp [pview, h₁] at h
          | bot => simp [pview, h₁] at h
          | sel _ _ => simp [pview, h₁] at h
          | pi _ _ => simp [pview, h₁] at h
  | .cast P e, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨S, W₁⟩ := r
          cases h₂ : hnf σ Γ e with
          | none => simp [pview, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨S', T, F⟩ := r₂
              simp only [pview, h₁, h₂] at h
              split at h
              · rename_i hS
                subst hS
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .cast (pview_sound P h₁) (hnf_sound e h₂)
              · cases h
  | .alias P₀ π Q, _, _, h => by
      cases h₁ : pview σ Γ Q with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T, W₁⟩ := r
          simp only [pview, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .alias (pview_sound Q h₁)
  | .sngl _ _ _, _, _, h => by
      simp only [pview, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .sngl
  | .fldI _ _ Q, _, _, h => by
      cases h₁ : pview σ Γ Q with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T, W₁⟩ := r
          simp only [pview, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .fldI (pview_sound Q h₁)
  | .fold Tel P, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T, W₁⟩ := r
          simp only [pview, h₁] at h
          split at h
          · rename_i hT
            subst hT
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .fold (pview_sound P h₁)
          · cases h
  | .unfold P, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T, W₁⟩ := r
          cases T with
          | mu Tel =>
              simp only [pview, h₁, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .unfold (pview_sound P h₁)
          | bot => simp [pview, h₁] at h
          | sel _ _ => simp [pview, h₁] at h
          | pi _ _ => simp [pview, h₁] at h
  | .both Tel Tel' P Q, _, _, h => by
      cases h₁ : pview σ Γ P with
      | none => simp [pview, h₁] at h
      | some r =>
          obtain ⟨T, W₁⟩ := r
          cases h₂ : pview σ Γ Q with
          | none => simp [pview, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨T', W₂⟩ := r₂
              cases W₁ with
              | obj V =>
                  cases W₂ with
                  | obj V' =>
                      simp only [pview, h₁, h₂] at h
                      split at h
                      · rename_i hc
                        obtain ⟨rfl, rfl⟩ := hc
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact .both (pview_sound P h₁) (pview_sound Q h₂)
                      · cases h
                  | fn _ _ => simp [pview, h₁, h₂] at h
                  | none => simp [pview, h₁, h₂] at h
              | fn _ _ => simp [pview, h₁, h₂] at h
              | none => simp [pview, h₁, h₂] at h
end

mutual
theorem hnf_complete : Hnf σ Γ e S T F → hnf σ Γ e = some (S, T, F)
  | .refl => rfl
  | .trans h₁ h₂ => by simp [hnf, hnf_complete h₁, hnf_complete h₂]
  | .top => rfl
  | .bot => rfl
  | .eqToLe hφ => by simp [hnf, synthEq_complete hφ]
  | .pi he hf => by simp [hnf, synthLe_complete he, synthLe_complete hf]
  | .obj hm => by simp [hnf, hnfM_complete hm]
  | .pair h₁ h₂ => by simp [hnf, hnf_complete h₁, hnf_complete h₂]
  | .bound hi => by simp [hnf, Telescope.get?_iff.2 hi, Ty.unweaken_iff.2 rfl]
  | .intoBnd h => by simp [hnf, hnf_complete h]
  | .member hP he hi hV hg => by
      simp [hnf, pview_complete hP, hnf_complete he, Telescope.get?_iff.2 hi, hV, hg]
  | .seal h => by simp [hnf, h]
theorem hnfM_complete : HnfM σ Γ src m Tel Es → hnfM σ Γ src m = some (Tel, Es)
  | .nil => rfl
  | .le hm hj hpre hpost => by
      simp [hnfM, hnfM_complete hm, Telescope.get?_iff.2 hj, hnfSPre_complete hpre, hnfSPost_complete hpost]
  | .fld hm hj hsd => by simp [hnfM, hnfM_complete hm, Telescope.get?_iff.2 hj, hnfSPost_complete hsd]
  | .alias hm hj => by simp [hnfM, hnfM_complete hm, Telescope.get?_iff.2 hj]
  | .is hm he => by simp [hnfM, hnfM_complete hm, hnf_complete he]
theorem hnfSPre_complete : HnfS σ Γ sd X Y sd' → hnfSPre σ Γ sd Y = some (X, sd')
  | .none => rfl
  | .some h => by simp [hnfSPre, hnf_complete h]
  | .bot => by simp [hnfSPre]
  | .top => by simp [hnfSPre]
theorem hnfSPost_complete : HnfS σ Γ sd X Y sd' → hnfSPost σ Γ sd X = some (Y, sd')
  | .none => rfl
  | .some h => by simp [hnfSPost, hnf_complete h]
  | .bot => by simp [hnfSPost]
  | .top => by simp [hnfSPost]
theorem pview_complete : PV σ Γ P T W → pview σ Γ P = some (T, W)
  | .var h => by simp [pview, h]
  | .sel hP hi hg => by simp [pview, pview_complete hP, Telescope.get?_iff.2 hi, hg]
  | .cast hP he => by simp [pview, pview_complete hP, hnf_complete he]
  | .alias hQ => by simp [pview, pview_complete hQ]
  | .sngl => rfl
  | .fldI hQ => by simp [pview, pview_complete hQ]
  | .unfold hP => by simp [pview, pview_complete hP]
  | .fold hP => by simp [pview, pview_complete hP]
  | .both hP hQ => by simp [pview, pview_complete hP, pview_complete hQ]
end

theorem normV_sound {r : Path s} : ∀ (v : Value s) {X : Ty s} {W : View s},
    normV σ Γ r v = some (X, W) → NormV σ Γ r v X W
  | .lam S₀ t₀, _, _, h => by
      cases h₁ : synthTm (Γ.cons (.opaque S₀)) t₀ with
      | none => simp [normV, h₁] at h
      | some T₀ =>
          simp only [normV, h₁, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .lam (synthTm_sound h₁)
  | .cast v e, _, _, h => by
      cases h₁ : normV σ Γ r v with
      | none => simp [normV, h₁] at h
      | some r₁ =>
          obtain ⟨X, W⟩ := r₁
          cases h₂ : hnf σ Γ e with
          | none => simp [normV, h₁, h₂] at h
          | some r₂ =>
              obtain ⟨X', Y, G⟩ := r₂
              simp only [normV, h₁, h₂] at h
              split at h
              · rename_i hX
                subst hX
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .cast (normV_sound v h₁) (hnf_sound e h₂)
              · cases h
  | .obj _ _, _, _, h => by simp [normV] at h

theorem normV_complete {r : Path s} : NormV σ Γ r v X W → normV σ Γ r v = some (X, W)
  | .lam h => by simp [normV, synthTm_complete h]
  | .cast hN hH => by simp [normV, normV_complete hN, hnf_complete hH]

end Graph

theorem Store.ctx_sound : ∀ {σ : Store s} {Γ : Ctx s}, Store.ctx σ = some Γ → Store.Typed σ Γ
  | .nil, _, h => by
      simp only [Store.ctx, Option.some.injEq] at h
      subst h
      exact .nil
  | .cons σ v, _, h => by
      cases h₁ : Store.ctx σ with
      | none => simp [Store.ctx, h₁] at h
      | some Γ₀ =>
          have hσ := Store.ctx_sound h₁
          cases v with
          | lam S t =>
              cases h₂ : synthValue Γ₀ (.lam S t) with
              | none => simp [Store.ctx, h₁, h₂] at h
              | some T =>
                  simp only [Store.ctx, h₁, h₂, Option.some.injEq] at h
                  subst h
                  have hv := synthValue_sound h₂
                  cases h₃ : synthTm (Γ₀.cons (.opaque S)) t with
                  | none => simp [synthValue, h₃] at h₂
                  | some T₀ =>
                      simp only [synthValue, h₃, Option.some.injEq] at h₂
                      subst h₂
                      exact .lam hσ hv
          | obj Tel ds =>
              simp only [Store.ctx, h₁] at h
              split at h
              · rename_i h₂
                simp only [Option.some.injEq] at h
                subst h
                exact .obj hσ (synthValue_sound h₂)
              · cases h
          | cast _ _ => simp [Store.ctx, h₁] at h

theorem Store.ctx_complete : ∀ {σ : Store s} {Γ : Ctx s}, Store.Typed σ Γ → Store.ctx σ = some Γ
  | _, _, .nil => rfl
  | _, _, .lam hσ hv => by simp [Store.ctx, Store.ctx_complete hσ, synthValue_complete hv]
  | _, _, .obj hσ hv => by simp [Store.ctx, Store.ctx_complete hσ, synthValue_complete hv]

theorem Store.ctx_iff {σ : Store s} {Γ : Ctx s} : Store.ctx σ = some Γ ↔ Store.Typed σ Γ :=
  ⟨Store.ctx_sound, Store.ctx_complete⟩

theorem appViewOf_iff {σ : Store s} {P : PathCo s} {S₀ : Ty s} {t₀ : Tm (s,x)} {h : AppHead s} :
    appViewOf σ P = some (S₀, t₀, h) ↔ appView σ P S₀ t₀ h := by
  constructor
  · intro e
    cases h₁ : Store.ctx σ with
    | none => simp [appViewOf, h₁] at e
    | some Γ =>
        have hσ := Store.ctx_sound h₁
        cases h₂ : synthPath Γ P with
        | none => simp [appViewOf, h₁, h₂] at e
        | some U₀ =>
            cases U₀ with
            | pi S T =>
                cases h₃ : pview σ Γ P with
                | none => simp [appViewOf, h₁, h₂, h₃] at e
                | some r =>
                    obtain ⟨U, W₀⟩ := r
                    cases W₀ with
                    | fn v F =>
                        simp only [appViewOf, h₁, h₂, h₃] at e
                        split at e
                        · rename_i hU
                          subst hU
                          cases h₄ : normV σ Γ P.path v with
                          | none => simp [h₄] at e
                          | some r₄ =>
                              obtain ⟨X, W⟩ := r₄
                              simp only [h₄] at e
                              split at e
                              · rename_i S₁ t₁ F' hA
                                cases h₅ : collapse F' with
                                | none => simp [h₅] at e
                                | some hd =>
                                    simp only [h₅, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
                                    obtain ⟨rfl, rfl, rfl⟩ := e
                                    exact ⟨Γ, S, T, v, F, X, W, F', hσ, synthPath_sound h₂, pview_sound P h₃,
                                      normV_sound v h₄, hA, h₅⟩
                              · cases e
                        · cases e
                    | obj _ => simp [appViewOf, h₁, h₂, h₃] at e
                    | none => simp [appViewOf, h₁, h₂, h₃] at e
            | bot => simp [appViewOf, h₁, h₂] at e
            | sel _ _ => simp [appViewOf, h₁, h₂] at e
            | mu _ => simp [appViewOf, h₁, h₂] at e
  · intro ⟨Γ, S, T, v, F, X, W, F', hσ, hP, hPV, hN, hA, hc⟩
    simp [appViewOf, Store.ctx_complete hσ, synthPath_complete hP, pview_complete hPV, normV_complete hN, hA, hc]

end Nominal.FCn

