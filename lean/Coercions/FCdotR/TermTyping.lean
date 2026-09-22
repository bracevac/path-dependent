import Coercions.FCdotR.StoreTyping
import Coercions.Oopsla16.Examples

/-!
# Typing of FCdotR atoms, terms and definitions

`Typing` types the two evidence sorts and `StoreTyping` ties the store typing
to the store; this module types the three *term* sorts of `Syntax`, so that a
statement about safety becomes expressible at all.  The judgments are

```text
Γ ⊢ₐ a : T        Γ ⊢ t : T        Γ ⊢d ds : T
```

one mutual block, `Type`-valued as everywhere in this development, indexed by
the same `Store σ σ`, `StoreTy σ` and `Ctx σ s` as `LeTy`/`VcTy`.  They are
`Oopsla16.HasType` and `Oopsla16.DmsHasType` rule for rule, with the three
differences the target makes explicit:

* **Subsumption is a syntax node.**  `T_Sub` becomes `AtomTy.cast` at an atom
  and `TmTy.cast` at a term; there is no subsumption rule.
* **Application is in normal form.**  `T_App` and `T_AppVar` are the one rule
  `TmTy.app`, whose operands are atoms and whose result is `U.substVr b.root`.
  The non-dependent `T_App` is the derived rule `TmTy.appWeaken`, because
  `U.weaken.substVr v` is `U` (`Oopsla16.Ty.substVr_weaken`).
* **`let` exists**, as the binding form A-normalisation needs.  It is not a
  source rule; its result type is a weakening, so the bound variable does not
  escape.

The block is *separate* from `LeTy`/`VcTy` and depends on it in one direction
only.  That is the structural fact the whole design rests on: FCdotR's
evidence contains no atoms, so atoms may contain evidence.

`AtomTy.varConc` reads a location's type off `StoreTy` rather than re-deriving
it; `StoreTyping.Store.Honest.vary` is what says that is the reference's
`T_Vary` and not a new power.

The last result here is the target's reading of the reference's
`hastp_to_htpy` (`dot_soundness.v:249`): at the **empty local scope** an atom
is rooted at a location, and its typing collapses into observation evidence
about that location.  It is stated only at `s = []`, where `BVar [] .var` is
uninhabited; a version at `s ≠ []` would be exactly the packing power that
`Oopsla16/PackingCounterexample` refutes, since `AtomTy.pack` is available at
either zone while `VcTy.vcPack` is not.

The last section types an object literal whose method returns a value of a
self-referential type member — the `FunctionField` example of
`Oopsla16/Examples.lean`, at the exact member bounds `D_Typ` forces.

What this module does **not** contain: any operational semantics, any
substitution or renaming lemma for these judgments, and any elaboration from
`Oopsla16`.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Ctx Store Subst renameNil renameUpTo)

/-! ## The judgments -/

mutual

/-- `Γ ⊢ₐ a : T`, the image of `Oopsla16.HasType` at a variable: `T_Varz`,
`T_Vary`, `T_Sub`, `T_VarPack` and `T_VarUnpack`, each with its coercion made
into a node. -/
inductive AtomTy : {σ s : Sig} → Store σ σ → StoreTy σ → Ctx σ s → Atom σ s →
    Ty σ s → Type where
  /-- `T_Varz`, `dot.v:227-230`. -/
  | varAbs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {x : BVar s .var} :
      AtomTy G W Γ (.var (.abs x)) (Γ.lookup x)
  /-- `T_Vary`, `dot.v:220-226`, read off the store typing instead of off a
  re-typing of the stored literal.  `StoreTyping.Store.Honest` is what ties the
  two together. -/
  | varConc {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {l : BVar σ .var} :
      AtomTy G W Γ (.var (.conc l)) ((tyOf W l).rename renameNil)
  /-- `T_Sub` at a variable. -/
  | cast {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {a : Atom σ s} {e : Le σ s} {S T : Ty σ s} :
      AtomTy G W Γ a S → LeTy G W Γ e S T → AtomTy G W Γ (.cast a e) T
  /-- `T_VarPack`, `dot.v:231-235`, at a subject of **either** zone.  The
  subject is the atom's root, which casts and packs do not move. -/
  | pack {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {a : Atom σ s} {T : Ty σ (s,x)} :
      AtomTy G W Γ a (T.substVr a.root) → AtomTy G W Γ (.pack T a) (.TBind T)
  /-- `T_VarUnpack`, `dot.v:236-240`. -/
  | unpack {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {a : Atom σ s} {T : Ty σ (s,x)} :
      AtomTy G W Γ a (.TBind T) → AtomTy G W Γ (.unpack T a) (T.substVr a.root)

/-- `Γ ⊢ t : T`, the image of `Oopsla16.HasType` at a compound term. -/
inductive TmTy : {σ s : Sig} → Store σ σ → StoreTy σ → Ctx σ s → Tm σ s →
    Ty σ s → Type where
  /-- An atom is a term. -/
  | atom {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {a : Atom σ s} {T : Ty σ s} :
      AtomTy G W Γ a T → TmTy G W Γ (.atom a) T
  /-- `T_Obj`, `dot.v:241-245`: the definitions are typed under the *opened*
  self type, which is why `Ctx.cons` admits an entry mentioning its own
  binder. -/
  | new {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      (T : Ty σ (s,x)) {ds : Defs σ (s,x)} :
      DefsTy G W (Γ.cons T) ds T → TmTy G W Γ (.new T ds) (.TBind T)
  /-- `T_AppVar`, `dot.v:251-256`.  Both operands are atoms, so the dependent
  form is the only one needed; `appWeaken` below is `T_App`. -/
  | app {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {a b : Atom σ s} {l : Lb} {S : Ty σ s} {U : Ty σ (s,x)} :
      AtomTy G W Γ a (.TFun l S U) → AtomTy G W Γ b S →
      TmTy G W Γ (.app a l b) (U.substVr b.root)
  /-- Sequencing, the binding form A-normalisation needs.  The result type is a
  weakening, so the bound variable does not escape. -/
  | «let» {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {t : Tm σ s} {u : Tm σ (s,x)} {S T : Ty σ s} :
      TmTy G W Γ t S → TmTy G W (Γ.cons S.weaken) u T.weaken →
      TmTy G W Γ (.let t u) T
  /-- `T_Sub`, `dot.v:257-262`. -/
  | cast {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {t : Tm σ s} {e : Le σ s} {S T : Ty σ s} :
      TmTy G W Γ t S → LeTy G W Γ e S T → TmTy G W Γ (.cast t e) T

/-- `Γ ⊢d ds : T`, the image of `Oopsla16.DmsHasType`: a definition list has a
right-nested intersection whose labels are the positions in the list. -/
inductive DefsTy : {σ s : Sig} → Store σ σ → StoreTy σ → Ctx σ s → Defs σ s →
    Ty σ s → Type where
  /-- `D_Nil`, `dot.v:264-265`. -/
  | dnil {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s} :
      DefsTy G W Γ .dnil .TTop
  /-- `D_Typ`, `dot.v:266-271`: a type member is **exact**, and its label is
  the length of the remaining list. -/
  | dty {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {T : Ty σ s} {ds : Defs σ s} {TS : Ty σ s} :
      DefsTy G W Γ ds TS →
      DefsTy G W Γ (.dty T ds) (.TAnd (.TTyp ds.length T T) TS)
  /-- `D_Fun`, `dot.v:272-284`.  The parameter does not mention itself, hence
  the weakening; the reference's two `EqSome` premises disappear because
  FCdotR's `Defs.dfun` carries both annotations outright. -/
  | dfun {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
      {S : Ty σ s} {U : Ty σ (s,x)} {t : Tm σ (s,x)} {ds : Defs σ s}
      {TS : Ty σ s} :
      DefsTy G W Γ ds TS → TmTy G W (Γ.cons S.weaken) t U →
      DefsTy G W Γ (.dfun S U t ds) (.TAnd (.TFun ds.length S U) TS)

end

/-! ## Derived rules -/

/-- `T_App`, `dot.v:246-250`: invocation whose result does not mention the
parameter.  The reference needs a rule of its own because its argument is an
arbitrary term; here the argument is an atom and the codomain is a weakening,
so the rule is `app` composed with `Ty.substVr_weaken`. -/
def TmTy.appWeaken {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {a b : Atom σ s} {l : Lb} {S U : Ty σ s}
    (ha : AtomTy G W Γ a (.TFun l S U.weaken)) (hb : AtomTy G W Γ b S) :
    TmTy G W Γ (.app a l b) U := by
  rw [← Ty.substVr_weaken U b.root]
  exact TmTy.app ha hb

/-! ## Atoms at the empty local scope

At `s = []` there is no abstract variable, so every atom is rooted at a store
location, and its typing is an *observation* of that location.  This is the
reference's `hastp_to_htpy` (`dot_soundness.v:249`), and the restriction to
`s = []` is exactly why the packing rule the reference omits from `htp` cannot
sneak back in through `AtomTy.pack`. -/

/-- A variable of the empty local scope is a location: `BVar [] .var` is
uninhabited, so the abstract zone is empty there. -/
def locOf {σ : Sig} : Vr σ [] → BVar σ .var
  | .conc l => l
  | .abs x => nomatch x

/-- And it is that location. -/
@[simp] theorem conc_locOf {σ : Sig} : (p : Vr σ []) → Vr.conc (locOf p) = p
  | .conc _ => rfl
  | .abs x => nomatch x

/-- The location an atom of empty local scope is rooted at.  It goes through
`Atom.root` rather than recursing again, so that it reduces on a constructor: a
direct recursion over the mutual block `Atom`/`Tm`/`Defs` compiles by
well-founded recursion, and `(cast a e).rootLoc = a.rootLoc` would then not be
definitional. -/
abbrev Atom.rootLoc {σ : Sig} (a : Atom σ []) : BVar σ .var := locOf a.root

/-- `rootLoc` is the root. -/
theorem Atom.root_eq_rootLoc {σ : Sig} (a : Atom σ []) :
    a.root = .conc a.rootLoc := (conc_locOf a.root).symm

/-- **An atom's typing is an observation of its root.**  A closed atom of type
`T` rooted at `ℓ` gives `ℓ` that same type, as observation evidence — which is
what `selL`/`selR` at a concrete subject consume, and what a machine needs in
order to read a member off the receiver of an application.

The evidence is produced, not merely asserted, so the result is a function on
derivations: `cast` becomes `vcSub` (its inclusion is already checked in the
empty context, which is `ctxAt Γ (conc ℓ)`), `pack` becomes `vcPack` (legal
here, because the subject is a location), and `unpack` becomes `vcUnfold` (the
subject's self is the location itself).

Stated only at `s = []`; see the module header. -/
def AtomTy.toVc {σ : Sig} {G : Store σ σ} {W : StoreTy σ} :
    {a : Atom σ []} → {T : Ty σ []} → AtomTy G W Ctx.nil a T →
    (v : Vc σ []) × VcTy G W Ctx.nil (.conc a.rootLoc) v T
  | _, _, .varConc (l := l) =>
      ⟨.vcLoc l, by rw [Ty.rename_renameNil_nil]; exact VcTy.vcLoc⟩
  | _, _, .cast (a := a) (S := S) (e := e) ha he =>
      let ⟨v, hv⟩ := ha.toVc
      ⟨.vcSub S e v, VcTy.vcSub (Γ := Ctx.nil) (p := .conc a.rootLoc) S hv he⟩
  | _, _, .pack (a := a) (T := T) ha =>
      let ⟨v, hv⟩ := ha.toVc
      ⟨.vcPack T v, VcTy.vcPack (by rw [Atom.root_eq_rootLoc a] at hv; exact hv)⟩
  | _, _, .unpack (a := a) (T := T) ha =>
      let ⟨v, hv⟩ := ha.toVc
      ⟨.vcUnfold T v, by rw [Atom.root_eq_rootLoc a]; exact VcTy.vcUnfold hv⟩

/-! ## An object literal at a self-referential type

`Oopsla16/Examples.lean`'s `FunctionField` derives `μz.S(z) ≤ μz.T(z)` for

```text
S(z) = {A : ⊥ .. z.B} ∧ ({B : ⊥ .. ⊤} ∧ {f : ∀(_ : ⊤) z.A})
```

but exhibits no object of that type.  Here is one, as an FCdotR term.

Two things are worth reading off it.  First, `DefsTy.dty` makes a type member
**exact** (`D_Typ`, `dot.v:266-271`), so a literal cannot be given `S(z)`
outright: its exact type is `Sexact`, with `A = z.B` and `B = ⊤` and a trailing
`⊤` from `D_Nil`, and `S(z)` is reached by widening — under the self, so the
widening is a `bindx` premise.  Second, the method body has to produce a value
of `z.A`, a member of the self it is being defined in, and it does so by
casting its parameter through two `selR`s whose subject is the self of the
enclosing `bindx`.  That is exactly the step `FCdot/ReceiverCounterexample`
shows the previous target could not take.

Each stage is a pair of the evidence or term and its derivation, so that the
syntax is inferred from the typing rather than written twice. -/

namespace FunctionFieldObject

open Oopsla16.Examples.FunctionField (A B f Sbody)

/-- The empty store. -/
abbrev G : Store ([] : Sig) [] := .nil

/-- Its literal typing: there are no locations to type. -/
def W : StoreTy [] := fun l => nomatch l

/-- The self, seen from under the method's parameter. -/
abbrev z' : Vr [] ([],x,x) := .abs (.there .here)

/-- `z.B`, at the self's own scope. -/
abbrev zB : Ty [] ([],x) := .TSel (.abs .here) B

/-- The method member `{f : ∀(_ : ⊤) z.A}`, which is `S(z)`'s verbatim. -/
abbrev fM : Ty [] ([],x) := .TFun f .TTop (.TSel z' A)

/-- The literal's **exact** type. -/
abbrev Sexact : Ty [] ([],x) :=
  .TAnd (.TTyp A zB zB) (.TAnd (.TTyp B .TTop .TTop) (.TAnd fM .TTop))

/-- `S(z)` is `Sexact` with both lower bounds dropped and the trailing `⊤`
forgotten. -/
example : Sbody = .TAnd (.TTyp A .TBot zB) (.TAnd (.TTyp B .TBot .TTop) fM) := rfl

/-- The context the definitions are typed in: the self at its exact type. -/
abbrev Gz : Ctx [] ([],x) := Ctx.nil.cons Sexact

/-- The context the method body is typed in. -/
abbrev Gp : Ctx [] ([],x,x) := Gz.cons (Ty.TTop (σ := []) (s := ([],x))).weaken

/-- `{A : z.B .. z.B}` is the first conjunct of the exact type. -/
def aConj : Conjunct Sexact (.TTyp A zB zB) := .here
/-- `{B : ⊤ .. ⊤}` is the second. -/
def bConj : Conjunct Sexact (.TTyp B .TTop .TTop) := .there .here
/-- The method member is the third. -/
def fConj : Conjunct Sexact fM := .there (.there .here)

/-- `z : {B : ⊤ .. ⊤}`, observed from under the parameter.  The subject's
prefix is `Gz`, which the parameter does not touch — that is why the
observation is scoped where it is. -/
def bObs : (v : Vc [] (scopeAt z')) × VcTy G W Gp z' v (.TTyp B .TTop .TTop) :=
  ⟨_, VcTy.vcSub (Γ := Gp) (p := z') Sexact VcTy.vcVar bConj.typed⟩

/-- `z : {A : z.B .. ⊤}`, the shape `selR` consumes. -/
def aObs : (v : Vc [] (scopeAt z')) × VcTy G W Gp z' v (.TTyp A zB .TTop) :=
  ⟨_, VcTy.vcSub (Γ := Gp) (p := z') Sexact VcTy.vcVar
        (.trans (.TTyp A zB zB) aConj.typed (.dtyp (.refl zB) (.top zB)))⟩

/-- `⊤ ≤ z.B`, by `selR` at the self's `B` member. -/
def leB : (e : Le [] ([],x,x)) × LeTy G W Gp e .TTop (.TSel z' B) :=
  ⟨_, LeTy.selR (p := z') (a := B) (S := .TTop) bObs.2⟩

/-- `z.B ≤ z.A`, by `selR` at the self's `A` member, whose lower bound is
`z.B`.  The subject of both steps is the self of the enclosing `bindx`. -/
def leA : (e : Le [] ([],x,x)) × LeTy G W Gp e (.TSel z' B) (.TSel z' A) :=
  ⟨_, LeTy.selR (p := z') (a := A) (S := zB) aObs.2⟩

/-- The method body: the parameter, cast up to `z.B` and then to `z.A`. -/
def body : (t : Tm [] ([],x,x)) × TmTy G W Gp t (.TSel z' A) :=
  ⟨_, .atom (.cast (.cast (AtomTy.varAbs (x := .here)) leB.2) leA.2)⟩

/-- The three definitions: `A = z.B` at label `2`, `B = ⊤` at label `1`, and
the method at label `0`.  The labels are the lengths of the tails. -/
def defs : (ds : Defs [] ([],x)) × DefsTy G W Gz ds Sexact :=
  ⟨_, DefsTy.dty (T := zB) (DefsTy.dty (T := .TTop) (.dfun .dnil body.2))⟩

/-- The literal, at its exact recursive type. -/
def literal : (t : Tm [] []) × TmTy G W Ctx.nil t (.TBind Sexact) :=
  ⟨_, .new Sexact defs.2⟩

/-- `Sexact ≤ S(z)`, under the self: both lower bounds drop to `⊥` and the
trailing `⊤` is forgotten. -/
def widen : (e : Le [] ([],x)) × LeTy G W Gz e Sexact Sbody :=
  ⟨_, LeTy.andI _ _
        (.trans (.TTyp A zB zB) aConj.typed (.dtyp (.bot zB) (.refl zB)))
        (LeTy.andI _ _
          (.trans (.TTyp B .TTop .TTop) bConj.typed
            (.dtyp (.bot .TTop) (.refl .TTop)))
          fConj.typed)⟩

/-- **The object literal at `μz. S(z)`**, the left endpoint of
`Oopsla16.Examples.FunctionField.recursive` and of
`FCdotR.Examples.recursive_typed`.  Composing the cast below with that
evidence gives a closed term of `μz. T(z)`. -/
def literalAtSbody : (t : Tm [] []) × TmTy G W Ctx.nil t (.TBind Sbody) :=
  ⟨_, .cast literal.2 (LeTy.bindx Sexact Sbody widen.2)⟩

end FunctionFieldObject

end FCdotR
