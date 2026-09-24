import Coercions.FCdotR.Correspondence

/-!
# Elaboration of every `Oopsla16` typing, and type safety of `Oopsla16`

`Elaboration.elabHasType` elaborates a source typing only on the fragment
`TmFrag`: variable operands at every application, both annotations on every
method.  This module drops both restrictions.  Every `Oopsla16.HasType`
derivation, at any store, store typing, context and scope, becomes a typed
FCdotR term that corresponds to the source term in the sense of
`Correspondence.Corr`, and every `DmsHasType` derivation becomes a typed
definition list that corresponds in the sense of `DmsCorr`.  That inhabits
`Correspondence.ElabSpecGen`, hence `ElabSpec`, the one hypothesis
`Correspondence.oopsla16_safety` took.

## The two rules the fragment excluded

* **General application is A-normalised.**  The target applies atoms and has
  `let`; the source applies arbitrary terms.
  * `T_App` binds both operands:
    `let x1 = t1' in let x2 = t2'↑ in x1 l x2`.  The argument's elaboration is
    weakened under the first binder by the typed substitution theorem
    (`TmTy.substEv` at `MonoSyn.EvA.weaken`).  Its correspondence is kept by
    `Corr.substEv`.  The result `T2` does not mention the parameter, so both
    `let`s have a weakened result type, as `TmTy.let` demands.
  * `T_AppVar` binds **only the receiver**: `let x1 = t1' in x1 l v'↑`, where
    `v'` is the argument's atom, weakened by `AtomTy.weakenVar`.  Binding the
    argument would make the result type `T2{x2}` mention a `let`-bound
    variable, which `TmTy.let` forbids.  Keeping it an atom rooted at `v`
    makes the body's type `(T2{v})↑`, a weakening, by `Ty.substVr_subst`.
  * The two shapes are `Corr.anf_app` and `Corr.anf_recv`.  The receiver is
    bound even when it is already a variable.  The correspondence accepts that,
    and the simulation (`Correspondence.sim_spec`) runs the extra `let` as an
    administrative step.
* **An unannotated method takes its types from `D_Fun`.**  `Defs.dfun`
  requires a domain and a codomain.  The elaboration uses the `T11` and `T12`
  that `D_Fun`'s premises check, whatever the source's optional annotations
  are.  `DmsCorr` ignores annotations on both sides, so nothing about them has
  to be proved.

The other rules are as in `Elaboration`.  `T_Vary`, `T_Varz`, `T_VarPack` and
`T_VarUnpack` become an atom by `elabAtom`, rooted at the source's variable;
`T_Vary` lands on the atom `loc ℓ T`, typed by `AtomTy.varConcAny`.  The
argument of `T_AppVar` becomes an atom the same way, its `T_Sub` steps turning
into atom casts.  `T_Obj` becomes `new`, and `T_Sub` at any other position
becomes a term-level `cast`.  The correspondence is carried as a field of the
result (`TmElab.corr`, `DefsElabC.corr`) and built clause by clause, so it
never has to be read back off the definition.

## What follows

* `elabSpecGen : ElabSpecGen` and `elabSpec : ElabSpec`, with no hypothesis.
* `oopsla16Safety_holds : Oopsla16Safety` and `oopsla16_safety'`: no
  configuration reachable from a closed source term typed over the empty
  store is stuck.  Both are `Correspondence.transport` at `elabSpec` and
  `sim_spec`, and take **no hypothesis**.
* `oopsla16_progress`, the positive form, in the shape of
  `DotMNF.dot_safety`: every such configuration is an answer or takes a
  source step.  It is proved constructively.  A target state stuck at an
  invocation contradicts `MethodInversion.safety'`, and every other focused
  target state gives the source step directly.
* These supersede `Correspondence.elabSpec_frag` and
  `oopsla16_safety_frag`.  Both are kept, as is the fragment elaboration
  `Elaboration.elabHasType` with its on-the-nose erasure
  (`ElaborationErasure`).

## What this module does not contain

* No erasure equation for the full elaboration.  A `let` erases to an object
  encoding (`Erasure.letEncode`), so `Tm.erase` of an A-normalised term is not
  its source term.  The correspondence `Corr` replaces that equation here.
* No claim that elaboration is unique, or that it agrees with
  `Elaboration.elabHasType` on the fragment.  It does not agree syntactically,
  because it binds every receiver with `let`.
* No source-side metatheory: no source preservation and no source canonical
  forms.  All typing reasoning is the target's.
* No use of classical logic.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst Grows HasType DmsHasType Stp)

/-! ## What an elaboration produces -/

/-- **An elaborated term**: a target term, its typing at the source's type, and
its correspondence with the source term. -/
structure TmElab {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (t : Oopsla16.Tm σ s) (T : Ty σ s) : Type where
  /-- The target term. -/
  tm : Tm σ s
  /-- It has the source's type. -/
  typed : TmTy G W Γ tm T
  /-- It computes what the source term computes. -/
  corr : Corr t tm

/-- **An elaborated definition list**: a target list, its typing at the
source's type, and its correspondence with the source list.  Unlike
`Elaboration.DefsElab` it needs no length field, because `DmsCorr.length`
derives the length from the correspondence (`DefsElabC.length`). -/
structure DefsElabC {σ s : Sig} (G : Store σ σ) (W : StoreTy σ) (Γ : Ctx σ s)
    (ds : Dms σ s) (T : Ty σ s) : Type where
  /-- The target list. -/
  defs : Defs σ s
  /-- It has the source's type. -/
  typed : DefsTy G W Γ defs T
  /-- It corresponds to the source's list member by member. -/
  corr : DmsCorr ds defs

/-- An elaborated list has as many members as its source, so the positional
labels agree. -/
theorem DefsElabC.length {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {ds : Dms σ s} {T : Ty σ s} (r : DefsElabC G W Γ ds T) : r.defs.length = ds.length :=
  (DmsCorr.length r.defs r.corr).symm

/-- An elaborated atom is an elaborated term: it is typed as a term, and it
corresponds to the variable it is rooted at. -/
def TmElab.ofAtom {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {p : Vr σ s} {T : Ty σ s} (r : AtomElab G W Γ p T) : TmElab G W Γ (.tvar p) T :=
  ⟨.atom r.atom, .atom r.typed, Corr.var_of_root r.root⟩

/-! ## The `let`-bound variables

An A-normalised application refers to its bound operands by the newest one or
two abstract variables.  Their types are read off the context, and the
context's entries are weakenings. -/

/-- Weakening a method type whose codomain is itself a weakening gives a
method type whose codomain is a double weakening.  This is the bookkeeping
`T_App`'s receiver needs under two binders. -/
theorem Ty.weaken_fun_weaken {σ s : Sig} (l : Lb) (S U : Ty σ s) :
    (Ty.TFun l S U.weaken).weaken = .TFun l S.weaken U.weaken.weaken := by
  show Ty.TFun l S.weaken (U.weaken.subst (Subst.ofRename (Rename.succ (k := .var))).lift)
      = _
  rw [Ty.weaken_subst_lift]

/-- The same, weakened twice: the receiver's type as the second-newest of two
`let`-bound variables sees it. -/
theorem Ty.weaken_weaken_fun_weaken {σ s : Sig} (l : Lb) (S U : Ty σ s) :
    (Ty.TFun l S U.weaken).weaken.weaken = .TFun l S.weaken.weaken U.weaken.weaken.weaken := by
  rw [Ty.weaken_fun_weaken, Ty.weaken_fun_weaken]

/-- The newest variable has the newest hypothesis' type. -/
def AtomTy.bound {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) : AtomTy G W (Γ.cons S) (.var (.abs .here)) S := by
  have h : AtomTy G W (Γ.cons S) (.var (.abs .here)) ((Γ.cons S).lookup .here) := .varAbs
  rw [Ctx.lookup_cons_here] at h
  exact h

/-- The second-newest variable has the second-newest hypothesis' type,
weakened past the newest. -/
def AtomTy.boundOuter {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (S : Ty σ (s,x)) (S' : Ty σ ((s,x),x)) :
    AtomTy G W ((Γ.cons S).cons S') (.var (.abs (.there .here))) S.weaken := by
  have h : AtomTy G W ((Γ.cons S).cons S') (.var (.abs (.there .here)))
      (((Γ.cons S).cons S').lookup (.there .here)) := .varAbs
  rw [Ctx.lookup_cons_there, Ctx.lookup_cons_here] at h
  exact h

/-! ## The two application rules -/

/-- **`T_App`, A-normalised**: from elaborations of the receiver at
`{l : T1 → T2↑}` and of the argument at `T1`,
`let x1 = t1' in let x2 = t2'↑ in x1 l x2` at `T2`.

The argument is weakened under `x1` by `TmTy.substEv` at
`MonoSyn.EvA.weaken`.  That re-chooses its evidence, so its correspondence is
moved along by `Corr.substEv`, which reads only the skeleton.  Both `let`s
return a weakening, which is what `TmTy.let` needs: the inner one returns
`T2↑` at the scope of `x1`, the outer one `T2`. -/
def TmElab.app {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {t1 t2 : Oopsla16.Tm σ s} {l : Lb} {T1 T2 : Ty σ s}
    (r1 : TmElab G W Γ t1 (.TFun l T1 T2.weaken)) (r2 : TmElab G W Γ t2 T1) :
    TmElab G W Γ (.tapp t1 l t2) T2 :=
  let S : Ty σ s := .TFun l T1 T2.weaken
  let E := MonoSyn.EvA.weaken (G := G) (W := W) (Γ := Γ) S.weaken
  let d2 := TmTy.substEv r2.typed E
  let a : Atom σ ((s,x),x) := .var (.abs (.there .here))
  let b : Atom σ ((s,x),x) := .var (.abs .here)
  have ha : AtomTy G W ((Γ.cons S.weaken).cons T1.weaken.weaken) a
      (.TFun l T1.weaken.weaken T2.weaken.weaken.weaken) :=
    Ty.weaken_weaken_fun_weaken l T1 T2 ▸
      AtomTy.boundOuter (G := G) (W := W) (Γ := Γ) S.weaken T1.weaken.weaken
  have hb : AtomTy G W ((Γ.cons S.weaken).cons T1.weaken.weaken) b T1.weaken.weaken :=
    AtomTy.bound T1.weaken.weaken
  ⟨.let r1.tm (.let d2.1 (.app a l b)),
    .let r1.typed (.let d2.2 (TmTy.appWeaken ha hb)),
    Corr.anf_app l r1.corr (Corr.substEv r2.corr r2.typed E) rfl rfl⟩

/-- **`T_AppVar`, A-normalised at the receiver only**: from an elaboration of
the receiver at `{l : T1 → T2}` and an atom for the argument `v` at `T1`,
`let x1 = t1' in x1 l v'↑` at `T2{v}`.

The argument stays an atom rooted at `v`, weakened under `x1` by
`AtomTy.weakenVar`.  So `TmTy.app` types the body at `(T2⇑){v↑}`, which is
`(T2{v})↑` by `Ty.substVr_subst`: a weakening, as `TmTy.let` demands.  Binding
the argument instead would type the body at `T2{x2}`, which mentions a
`let`-bound variable and is not a weakening. -/
def TmElab.appVar {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {t1 : Oopsla16.Tm σ s} {v : Vr σ s} {l : Lb} {T1 : Ty σ s} {T2 : Ty σ (s,x)}
    (r1 : TmElab G W Γ t1 (.TFun l T1 T2)) (r2 : AtomElab G W Γ v T1) :
    TmElab G W Γ (.tapp t1 l (.tvar v)) (T2.substVr v) :=
  let S : Ty σ s := .TFun l T1 T2
  let bw := AtomTy.weakenVar S.weaken r2.typed
  let a : Atom σ (s,x) := .var (.abs .here)
  have ha : AtomTy G W (Γ.cons S.weaken) a
      (.TFun l T1.weaken (T2.subst (Subst.ofRename (Rename.succ (k := .var))).lift)) :=
    AtomTy.bound S.weaken
  have hroot : bw.atom.root = v.weaken := bw.root.trans (congrArg Vr.weaken r2.root)
  have hty : (T2.subst (Subst.ofRename (Rename.succ (k := .var))).lift).substVr bw.atom.root
      = (T2.substVr v).weaken := by
    rw [hroot, Vr.weaken_eq_subst_succ]
    exact (Ty.substVr_subst T2 v _).symm
  ⟨.let r1.tm (.app a l bw.atom),
    .let r1.typed (hty ▸ TmTy.app ha bw.deriv),
    Corr.anf_recv l r1.corr rfl hroot⟩

/-! ## The elaboration -/

mutual

/-- **Every source term typing elaborates to a typed, corresponding target
term.**  One clause per rule of `HasType`, all 8 of them, at an arbitrary
store typing `W`, with **no hypothesis** and no restriction on the term.

`T_App` and `T_AppVar` are A-normalised (`TmElab.app`, `TmElab.appVar`).  The
four rules that conclude only at a variable go through `elabAtom`.  `T_Obj` is
`new` at the source's self type, and `T_Sub` is a term-level `cast`. -/
def elabTm {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} :
    {t : Oopsla16.Tm σ s} → {T : Ty σ s} → HasType G Γ t T → TmElab G W Γ t T
  | _, _, .T_Vary hds heq => .ofAtom (elabAtom W (.T_Vary hds heq))
  | _, _, .T_Varz => .ofAtom (elabAtom W .T_Varz)
  | _, _, .T_VarPack h => .ofAtom (elabAtom W (.T_VarPack h))
  | _, _, .T_VarUnpack h => .ofAtom (elabAtom W (.T_VarUnpack h))
  | _, _, .T_Obj (T := T) hds =>
      let r := elabDefs W hds
      ⟨.new T r.defs, .new T r.typed, Corr.obj T r.corr⟩
  | _, _, .T_App h1 h2 => TmElab.app (elabTm W h1) (elabTm W h2)
  | _, _, .T_AppVar h1 h2 => TmElab.appVar (elabTm W h1) (elabAtom W h2)
  | _, _, .T_Sub h hs =>
      let r := elabTm W h
      let e := elabStp W hs
      ⟨.cast r.tm e.1, .cast r.typed e.2, Corr.cast e.1 r.corr⟩

/-- **Every source definition-list typing elaborates to a typed,
corresponding target list.**  `D_Nil`, `D_Typ` and `D_Fun`, with **no
restriction on annotations**.  A method is elaborated at the domain `T11` and
codomain `T12` that `D_Fun` checks, and the source's optional annotations
play no part.  The positional label is moved along by `DefsElabC.length`. -/
def elabDefs {σ s : Sig} {G : Store σ σ} (W : StoreTy σ) {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → DmsHasType G Γ ds T → DefsElabC G W Γ ds T
  | _, _, .D_Nil => ⟨.dnil, .dnil, DmsCorr.dnil⟩
  | _, _, .D_Typ (T11 := T11) hds =>
      let r := elabDefs W hds
      ⟨.dty T11 r.defs, by rw [← r.length]; exact .dty r.typed, DmsCorr.dty T11 r.corr⟩
  | _, _, .D_Fun (OT11 := o1) (OT12 := o2) (T11 := T11) (T12 := T12) hds hb _ _ =>
      let r := elabDefs W hds
      let rb := elabTm W hb
      ⟨.dfun T11 T12 rb.tm r.defs, by rw [← r.length]; exact .dfun r.typed rb.typed,
        DmsCorr.dfun o1 o2 T11 T12 rb.corr r.corr⟩

end

/-! ## The specification, inhabited -/

/-- **`ElabSpecGen` holds**: the compositional elaboration obligation of
`Correspondence`, by `elabTm`.  No hypothesis. -/
def elabSpecGen : ElabSpecGen := @fun _ _ _ W _ _ _ h =>
  let r := elabTm W h
  ⟨r.tm, r.typed, ⟨r.corr⟩⟩

/-- **`ElabSpec` holds**: every closed source typing over the empty store
yields a closed typed target term whose initial state is related to the
source's initial configuration.  No hypothesis.  This supersedes
`Correspondence.elabSpec_frag`, which is the same statement restricted to
`TmFrag`. -/
theorem elabSpec : ElabSpec := elabSpecGen.toElabSpec

/-- **Type safety of `Oopsla16`, as the proposition `Oopsla16Safety`.**  It
is `Correspondence.transport` at `elabSpec` and `sim_spec`, and takes no
hypothesis. -/
theorem oopsla16Safety_holds : Oopsla16Safety := transport elabSpec sim_spec

/-- **Type safety of `Oopsla16`'s own machine, with no hypothesis**: no
configuration reachable from a closed source term typed over the empty store is
stuck.  This is `Correspondence.oopsla16_safety` without its hypothesis
`hE : ElabSpec`, which `elabSpec` discharges.  It supersedes
`Correspondence.oopsla16_safety_frag`, which needs the term in `TmFrag`. -/
theorem oopsla16_safety' {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) {σ : Sig} {g : Grows [] σ} {G' : Store σ σ}
    {t' : Oopsla16.Tm σ []} (run : Oopsla16.Steps g Store.nil t G' t') : ¬ SrcStuck G' t' :=
  oopsla16_safety elabSpec ht run

/-- **Progress along every run of `Oopsla16`, in positive form, with no
hypothesis.**  Every configuration reachable from a closed source term typed
over the empty store is an answer or takes a source step.  This is the shape of
`DotMNF.dot_safety`.

The proof is constructive.  The source run is simulated from the elaborated
state (`Rel.steps`), and the related target state is normalised to a focus
(`normalize`).  A final focus makes the source an answer (`Rel.final`).  An
allocation, or an invocation of a label the receiver defines, makes the source
step (`Rel.new_steps`, `Rel.app_steps`).  An invocation of an undefined label
would be a stuck target state reachable from a typed closed term, which
`MethodInversion.safety'` rules out. -/
theorem oopsla16_progress {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) {σ : Sig} {g : Grows [] σ} {G' : Store σ σ}
    {t' : Oopsla16.Tm σ []} (run : Oopsla16.Steps g Store.nil t G' t') :
    t'.IsAnswer ∨ ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
      Oopsla16.Step g' G' t' G'' t'' := by
  have r := elabTm emptyStoreTy ht
  obtain ⟨⟨Gt, K, d⟩, h1, hr1⟩ := Rel.steps sim_step (Rel.init r.corr) run
  obtain ⟨⟨Gt1, K1, d1⟩, h2, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G' t' hr1
  rcases hfoc with hfin | ⟨T0, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact Or.inl (hr.final hfin)
  · simp only at hd
    subst hd
    obtain ⟨G'', t'', hs⟩ := Rel.new_steps hr
    exact Or.inr ⟨_, _, G'', t'', hs⟩
  · simp only at hd
    subst hd
    cases hf : (Gt1.lookup (Vr.loc a.root)).fun? l with
    | none => exact absurd (State.stuck_app hf) (safety' r.typed (Steps.trans h1 h2))
    | some p =>
        obtain ⟨S, U, body⟩ := p
        obtain ⟨t'', hs⟩ := Rel.app_steps hr hf
        exact Or.inr ⟨_, _, G', t'', hs⟩


/-! ## A worked instance outside the fragment

A closed program that `TmFrag` excludes twice over: both of its applications
have a non-variable receiver, and both of its methods are Curry-style, with
no annotation at all.

```text
id   = new { def 0(y) = y }                 -- self type  {0 : ⊤ → ⊤} ∧ ⊤
call = new { def 0(y) = id 0 y }            -- T_AppVar, receiver an object
prog = call 0 id                            -- T_App, both operands objects
```

The elaboration binds both operands of `T_App`, binds only the receiver of
`T_AppVar`, and gives each method the types `D_Fun` checked (`⊤` and `⊤`).
The skeleton equation is checked by `rfl`, with `Elaboration.elabAtom`
unsealed: it is compiled by well-founded recursion, hence irreducible by
default. -/

namespace CurryCall

/-- The self type of both objects: one method `{0 : ⊤ → ⊤}` and the trailing
`⊤` of `D_Nil`.  Generic in the enclosing scope. -/
abbrev Tid {s : Sig} : Ty [] (s,x) := .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- The identity literal, Curry-style: `{ def 0(y) = y }`. -/
abbrev Did {s : Sig} : Dms [] (s,x) := .dcons (.dfun none none (.tvar (.abs .here))) .dnil

/-- The identity literal at its self type. -/
def dId {s : Sig} {Γ : Ctx [] s} : DmsHasType Store.nil (Γ.cons Tid) Did Tid :=
  .D_Fun (T11 := .TTop) (T12 := .TTop) .D_Nil (.T_Sub .T_Varz .stp_top) (Or.inl rfl) (Or.inl rfl)

/-- The identity object, by `T_Obj`. -/
def idObj {s : Sig} {Γ : Ctx [] s} : HasType Store.nil Γ (.tobj Did) (.TBind Tid) := .T_Obj dId

/-- Forgetting the self: `μz. Tid ≤ {0 : ⊤ → ⊤}`, by `stp_bind1`. -/
def forget {s : Sig} {Γ : Ctx [] s} : Stp Store.nil Γ (.TBind Tid) (.TFun 0 .TTop .TTop) :=
  .stp_bind1 (.stp_and11 (.stp_fun .stp_top .stp_top))

/-- The identity object at its method type. -/
def idFun {s : Sig} {Γ : Ctx [] s} : HasType Store.nil Γ (.tobj Did) (.TFun 0 .TTop .TTop) :=
  .T_Sub idObj forget

/-- The caller literal, Curry-style: `{ def 0(y) = id 0 y }`.  Its body is a
`T_AppVar` whose receiver is an object literal. -/
abbrev Dcall : Dms [] ([],x) :=
  .dcons (.dfun none none (.tapp (.tobj Did) 0 (.tvar (.abs .here)))) .dnil

/-- The caller literal at its self type. -/
def dCall : DmsHasType Store.nil (Ctx.nil.cons Tid) Dcall Tid :=
  .D_Fun (T11 := .TTop) (T12 := .TTop) .D_Nil (.T_AppVar idFun (.T_Sub .T_Varz .stp_top))
    (Or.inl rfl) (Or.inl rfl)

/-- The program: the caller invoked on the identity. -/
abbrev prog : Oopsla16.Tm [] [] := .tapp (.tobj Dcall) 0 (.tobj Did)

/-- The program is typed at `⊤`, by `T_App`. -/
def progTy : HasType Store.nil Ctx.nil prog .TTop :=
  .T_App (T2 := .TTop) (.T_Sub (.T_Obj dCall) forget) (.T_Sub idObj .stp_top)

/-- The program is outside the fragment `Elaboration.elabHasType` handles. -/
theorem not_frag : TmFrag prog → False := fun f => nomatch f

/-- The identity literal as the elaboration produces it, up to evidence: the
method is annotated `⊤ → ⊤`, the types `D_Fun` checked. -/
abbrev idLit {s : Sig} : Tm [] s :=
  .new Tid (.dfun .TTop .TTop (.atom (.var (.abs .here))) .dnil)

unseal elabAtom in
/-- **The elaborated program, up to evidence.**  At the top, `T_App` binds
both operands.  In the caller's body, `T_AppVar` binds only the receiver, and
the argument is the parameter, weakened past the binder. -/
example : (elabTm emptyStoreTy progTy).tm.skel =
    .let (.new Tid (.dfun .TTop .TTop
        (.let idLit (.app (.var (.abs .here)) 0 (.var (.abs (.there .here))))) .dnil))
      (.let idLit (.app (.var (.abs (.there .here))) 0 (.var (.abs .here)))) := rfl

/-- The program's source run never gets stuck, by `oopsla16_safety'`. -/
theorem prog_safe {σ : Sig} {g : Grows [] σ} {G' : Store σ σ} {t' : Oopsla16.Tm σ []}
    (run : Oopsla16.Steps g Store.nil prog G' t') : ¬ SrcStuck G' t' :=
  oopsla16_safety' progTy run

end CurryCall

end FCdotR
