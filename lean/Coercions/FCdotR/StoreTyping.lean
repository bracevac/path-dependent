import Coercions.FCdotR.Typing
import Coercions.Oopsla16.SubstLemmas
import Coercions.Oopsla16.PackingCounterexample

/-!
# Store typing: tying `StoreTy` to the store it describes

`Typing` carries the type of each stored literal as a bare function
`StoreTy σ := (l : BVar σ .var) → Ty σ ([],x)`, so that `tyOf` is data and its
stability under allocation is that function's extension rather than a
derivation's.  Nothing there says the function tells the truth, and until it
does, `VcTy.vcLoc` — and with it every concrete `selL`/`selR` — is a licence to
invent types for locations.  This module supplies the missing invariant.

```text
Store.Honest G W  ≔  for every ℓ there is a literal ds with
                     ⊢d ds : W ℓ   under the self  W ℓ,  and  ds[ℓ/z] = G(ℓ)
```

That is `T_Vary`'s two premises (`dot.v:220-226`) lifted out of the rule and
made an invariant of the pair `(G, W)`.  Three things follow, and they are what
the module proves.

* **`AtomTy.varConc` is `T_Vary`.**  `Store.Honest.vary` produces the source
  derivation the target's rule asserts, so reading a location's type off `W`
  is not a new power.
* **`W` agrees with what `defL`/`defR` read.**  `DmsHasType` only ever concludes
  at a right-nested intersection — `TAnd (TTyp ..) (TAnd .. TTop)` — and
  `D_Typ` makes a type member *exact*.  So if the stored literal defines `a` to
  be `TX`, which is the premise of `LeTy.defL`/`LeTy.defR`, then `tyOf W ℓ`
  has `{a : TX .. TX}` as a conjunct (`Store.Honest.member`), and the
  observation `selL`/`selR` want is derivable (`Store.Honest.obs`).  The shape
  is named, as data, by `Conjunct`.
* **Honesty survives allocation.**  `Store.Honest.alloc` mirrors `ST_Obj`
  (`Semantics.lean`), extending `W` by one entry.

The last one needs a fact the reference never has to state: its concrete
identifiers are absolute positions and are therefore "invariant under context
extension" (`dot.v:21-22`), whereas here a store weakening is a real renaming.
So the second half of this module proves that **the four source judgments are
stable under a store renaming that transports lookups** (`StoreMap`), which is
the intrinsic-scoping cost of `dot.v:21-22` and is reused by every later
preservation argument.

**The other location rule needs none of this.**  `VcTy.vcLocAny` (and
`AtomTy.varConcAny`) observes a location at any self type whose instance
matches the stored literal (`Typing.LitMatch`), with no store invariant.  A
match asks a method member for the stored method's two annotations, so the
section *Annotated literals* defines `Dms.Annotated` (every method of a list
carries both annotations) and `Store.Annotated` (every stored literal is
annotated).  The section *Matching a stored literal* shows that a pair of
`T_Vary` premises gives the match exactly when the stored literal is annotated
(`varyLitMatch`, and the converse `varyLitMatch_annotated`), and that a stored
method lacking an annotation matches no method member
(`LitMatch.no_unannotated_method`).  `varyMember`, `varyMethod` and `varyObs`
are the witness-level versions of `Store.Honest.member`, `Store.Honest.method`
and `Store.Honest.obs` (`member` and `method` are `varyMember` and
`varyMethod` at the honesty witness), and `Store.Honest.vcLoc_of_vcLocAny`
says that over an honest store `vcLoc` is `vcLocAny` at the recorded type
wherever the stored literal is annotated, and only there
(`Store.Honest.not_vcLocAny_tyOf`).  `Store.Honest.member` and
`Store.Honest.method` are also what `Admissibility` needs to show that over an
honest store the location rules derive nothing the source cannot.  The
section *A substitution's store part* moves the match along a substitution
(`LitMatch.subst`), which is what the `vcLocAny` and `AtomTy.varConcAny`
clauses of the two substitution theorems use.

The module closes with `Store.Honest` instantiated at the two-object store of
`Oopsla16/PackingCounterexample`, so that the invariant is known to be
inhabited by something with cross-referencing entries and positional labels.

What this module does **not** contain: any typing of the target's own terms
(that is `TermTyping`), any operational semantics for FCdotR, and any
completeness claim — `Store.Honest` is an invariant a machine maintains, not a
characterisation of the stores `Typing` admits.  It is the invariant of a
*source* store.  The FCdotR machine's own store is kept honest by a different
invariant, `Preservation.MachineStore.Honest`, which types the stored target
literals instead; `Preservation` says why the two differ and proves how they
are connected (`Store.Honest.toMachine`).
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst HasType DmsHasType Stp Htp EqSome
  renameNil renameUpTo varUpTo scopeUpTo)

/-! ## Conjuncts

`DmsHasType` concludes at a right-nested intersection whose conjuncts are the
members, in order (`dot.v:263-282`).  `Conjunct T M` names one of them.  It is
`Type`-valued, like every judgment here, because its payoff is *evidence*:
`Conjunct.ev` is the `andE1`/`andE2` chain that projects the member out. -/

/-- `T` is a right-nested intersection one of whose conjuncts is `M`. -/
inductive Conjunct {σ s : Sig} : Ty σ s → Ty σ s → Type where
  /-- The member is the head conjunct. -/
  | here {T1 T2 : Ty σ s} : Conjunct (.TAnd T1 T2) T1
  /-- The member is further along the spine. -/
  | there {T1 T2 M : Ty σ s} : Conjunct T2 M → Conjunct (.TAnd T1 T2) M

/-- The inclusion a conjunct *is*: a chain of `andE2` ending in an `andE1`. -/
def Conjunct.ev {σ s : Sig} {T M : Ty σ s} : Conjunct T M → Le σ s
  | .here (T1 := T1) (T2 := T2) => .andE1 T2 (.refl T1)
  | .there (T1 := T1) h => .andE2 T1 h.ev

/-- And that chain is typed: an intersection is included in each conjunct. -/
def Conjunct.typed {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {T M : Ty σ s} : (h : Conjunct T M) → LeTy G W Γ h.ev T M
  | .here => .andE1 _ (.refl _)
  | .there h => .andE2 _ h.typed

/-- Conjuncts survive substitution, because `TAnd` is a plain congruence. -/
def Conjunct.subst {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    {T M : Ty σ1 s1} → Conjunct T M → Conjunct (T.subst θ) (M.subst θ)
  | _, _, .here => .here
  | _, _, .there h => .there (Conjunct.subst θ h)

/-- **A definition list's type declares each of its type members, exactly.**
`D_Typ` (`dot.v:266-271`) gives a type member the bounds `T11..T11`, so reading
the member at label `a` off the definitions and reading it off the type agree.
This is the shape statement the module header promises. -/
def DmsHasType.conjunct {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → DmsHasType G Γ ds T → {a : Lb} →
    {TX : Ty σ s} → ds.get? a = some (.dty TX) → Conjunct T (.TTyp a TX TX)
  | _, _, .D_Nil, _, _, hg => by simp [Dms.get?] at hg
  | _, _, .D_Typ (ds := ds) (T11 := T11) hds, a, TX, hg => by
      have hg' : (if a = ds.length then some (Dm.dty T11) else ds.get? a)
          = some (.dty TX) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'
        have hT : T11 = TX := by simpa using hg'
        subst hT
        subst h
        exact .here
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunct hds hg')
  | _, _, .D_Fun (ds := ds) (OT11 := OT11) (OT12 := OT12) (t12 := t12) hds _ _ _,
      a, TX, hg => by
      have hg' : (if a = ds.length then some (Dm.dfun OT11 OT12 t12) else ds.get? a)
          = some (.dty TX) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'; simp at hg'
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunct hds hg')

/-- A member found by `Dms.get?` has a label below the length of the list.
Labels are positional, so this is what separates the head member of a list from
the members of its tail. -/
theorem dmsTyp_label_lt {σ s : Sig} : (ds : Dms σ s) → {a : Lb} → {d : Dm σ s} →
    ds.get? a = some d → a < ds.length
  | .dnil, _, _, h => by simp [Dms.get?] at h
  | .dcons d0 ds, a, d, h => by
      show a < ds.length + 1
      by_cases hc : a = ds.length
      · rw [hc]; exact Nat.lt_succ_self _
      · have h' : (if a = ds.length then some d0 else ds.get? a) = some d := h
        rw [if_neg hc] at h'
        exact Nat.lt_succ_of_lt (dmsTyp_label_lt ds h')

/-- The head of a definition list is found at the label its tail's length
names. -/
theorem dms_get?_head {σ s : Sig} (d : Dm σ s) (ds : Dms σ s) :
    (Dms.dcons d ds).get? ds.length = some d := by
  show (if ds.length = ds.length then some d else ds.get? ds.length) = some d
  rw [if_pos rfl]

/-- A member of the tail is a member of the whole list, at the same label:
positional labels (`dmsTyp_label_lt`) keep the tail's labels below the
head's. -/
theorem dms_get?_tail {σ s : Sig} (d0 : Dm σ s) {ds : Dms σ s} {a : Lb} {d : Dm σ s}
    (h : ds.get? a = some d) : (Dms.dcons d0 ds).get? a = some d := by
  show (if a = ds.length then some d0 else ds.get? a) = some d
  rw [if_neg (Nat.ne_of_lt (dmsTyp_label_lt ds h))]
  exact h

/-- An optional annotation's agreement with a checked type survives a map;
this is what `D_Fun`'s two `EqSome` premises need under a store renaming
(`DmsHasType.renameStore`, `dot.v:216`). -/
theorem eqSome_map {α β : Type} (f : α → β) {o : Option α} {a : α}
    (h : EqSome o a) : EqSome (o.map f) (f a) := by
  cases h with
  | inl h => exact Or.inl (by rw [h]; rfl)
  | inr h => exact Or.inr (by rw [h]; rfl)

/-- An annotation that is present, and agrees with a checked type by
`EqSome` (`dot.v:216`), is that type. -/
theorem eqSome_of_isSome {α : Type} {o : Option α} {a : α} (h : EqSome o a)
    (hs : o.isSome) : o = some a := by
  cases h with
  | inl h => rw [h] at hs; cases hs
  | inr h => exact h

/-- **A definition list's type declares each of its annotated methods at the
annotations.**  `D_Fun` (`dot.v:272-282`) relates a method's optional
annotations to the types it checks by `EqSome`, so a method stored as
`dfun (some S) (some U) t` at label `a` appears in the list's type as the
conjunct `{a : S → U}`, whatever the body's typing.  The method counterpart of
`DmsHasType.conjunct`. -/
def DmsHasType.conjunctFun {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} :
    {ds : Dms σ s} → {T : Ty σ s} → DmsHasType G Γ ds T → {a : Lb} →
    {S : Ty σ s} → {U : Ty σ (s,x)} → {t : Oopsla16.Tm σ (s,x)} →
    ds.get? a = some (.dfun (some S) (some U) t) → Conjunct T (.TFun a S U)
  | _, _, .D_Nil, _, _, _, _, hg => by simp [Dms.get?] at hg
  | _, _, .D_Typ (ds := ds) (T11 := T11) hds, a, S, U, t, hg => by
      have hg' : (if a = ds.length then some (Dm.dty T11) else ds.get? a)
          = some (.dfun (some S) (some U) t) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'; simp at hg'
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunctFun hds hg')
  | _, _, .D_Fun (ds := ds) (OT11 := OT11) (OT12 := OT12) (T11 := T11) (T12 := T12)
      (t12 := t12) hds _ e1 e2, a, S, U, t, hg => by
      have hg' : (if a = ds.length then some (Dm.dfun OT11 OT12 t12) else ds.get? a)
          = some (.dfun (some S) (some U) t) := hg
      by_cases h : a = ds.length
      · rw [if_pos h] at hg'
        simp only [Option.some.injEq, Dm.dfun.injEq] at hg'
        obtain ⟨rfl, rfl, -⟩ := hg'
        have h1 : T11 = S := by
          cases e1 with
          | inl e => cases e
          | inr e => exact (Option.some.inj e).symm
        have h2 : T12 = U := by
          cases e2 with
          | inl e => cases e
          | inr e => exact (Option.some.inj e).symm
        subst h h1 h2
        exact .here
      · rw [if_neg h] at hg'
        exact .there (DmsHasType.conjunctFun hds hg')

/-! ## Annotated literals

A method of the source may leave out either annotation (`dot.v:48`), and
`D_Fun` relates the annotations to the types it checks by `EqSome`
(`dot.v:216`): an absent annotation agrees with every type.  The location
rules' premise `Typing.LitMatch` asks a method member for the stored
annotations themselves, so a `T_Vary` typing reaches the location rules only at
a location whose methods carry both (`varyLitMatch_iff` below).
`Dms.Annotated` says that of a
definition list, and `Store.Annotated` of every literal in a store; the
elaboration of `T_Vary` takes the latter.  Both are decidable.  Substitution
neither adds nor removes an annotation (`Dms.annotated_subst`), so a `T_Vary`
witness is annotated exactly when the literal it instantiates to is.

These are written prefix, `Dms.Annotated ds` and `Store.Annotated G`: dot
notation on an `Oopsla16` definition list or store would look for the name in
`Oopsla16`. -/

/-- A member definition **carries its annotations**: a type member has none to
carry, and a method must have both its parameter annotation and its result
annotation (Church style). -/
def Dm.Annotated {σ s : Sig} : Dm σ s → Prop
  | .dty _ => True
  | .dfun OS OU _ => OS.isSome ∧ OU.isSome

/-- **Every method of a definition list carries both annotations.** -/
def Dms.Annotated {σ s : Sig} : Dms σ s → Prop
  | .dnil => True
  | .dcons d ds => Dm.Annotated d ∧ Dms.Annotated ds

/-- Whether a member carries its annotations is decidable. -/
instance Dm.Annotated.decidable {σ s : Sig} : (d : Dm σ s) → Decidable (Dm.Annotated d)
  | .dty _ => isTrue trivial
  | .dfun OS OU _ => inferInstanceAs (Decidable (OS.isSome ∧ OU.isSome))

/-- Whether a definition list is annotated is decidable. -/
instance Dms.Annotated.decidable {σ s : Sig} :
    (ds : Dms σ s) → Decidable (Dms.Annotated ds)
  | .dnil => isTrue trivial
  | .dcons d ds =>
      have := Dms.Annotated.decidable ds
      inferInstanceAs (Decidable (Dm.Annotated d ∧ Dms.Annotated ds))

/-- The head of an annotated list is annotated. -/
theorem Dms.Annotated.head {σ s : Sig} {d : Dm σ s} {ds : Dms σ s}
    (h : Dms.Annotated (.dcons d ds)) : Dm.Annotated d := h.1

/-- The tail of an annotated list is annotated. -/
theorem Dms.Annotated.tail {σ s : Sig} {d : Dm σ s} {ds : Dms σ s}
    (h : Dms.Annotated (.dcons d ds)) : Dms.Annotated ds := h.2

/-- A substitution keeps a member's annotations and adds none. -/
theorem Dm.annotated_subst {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (d : Dm σ1 s1) → (Dm.Annotated (d.subst θ) ↔ Dm.Annotated d)
  | .dty _ => Iff.rfl
  | .dfun OS OU t => by
      show (OS.map (fun T => T.subst θ)).isSome ∧ (OU.map (fun T => T.subst θ.lift)).isSome
        ↔ OS.isSome ∧ OU.isSome
      rw [Option.isSome_map, Option.isSome_map]

/-- A substitution keeps a definition list's annotations and adds none. -/
theorem Dms.annotated_subst {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (ds : Dms σ1 s1) → (Dms.Annotated (ds.subst θ) ↔ Dms.Annotated ds)
  | .dnil => Iff.rfl
  | .dcons d ds => by
      show Dm.Annotated (d.subst θ) ∧ Dms.Annotated (ds.subst θ)
        ↔ Dm.Annotated d ∧ Dms.Annotated ds
      rw [Dm.annotated_subst θ d, Dms.annotated_subst θ ds]

/-- **Every stored literal is annotated**: at every location of the store (or
store fragment), every method carries both annotations.  This is the
hypothesis under which the elaboration of `T_Vary` goes through
(`Elaboration.elabAtom`, `ElaborationFull.elabTm`).  It is a class, so that the
elaboration finds it at the empty store (`Store.Annotated.nil`) without being
told; a store of the honest-store theorems supplies it by
`Elaboration.Store.Honest.annotated`. -/
class Store.Annotated {σ σ' : Sig} (G : Store σ σ') : Prop where
  /-- The literal at each location is annotated. -/
  ann : ∀ l : BVar σ' .var, Dms.Annotated (G.lookup l)

/-- **The empty store is annotated**: it has no location. -/
instance Store.Annotated.nil {σ : Sig} : Store.Annotated (Store.nil : Store σ []) :=
  ⟨fun l => nomatch l⟩

/-- One more location, holding an annotated literal. -/
theorem Store.Annotated.cons {σ σ' : Sig} {G : Store σ σ'} {d : Dms σ []}
    (hG : Store.Annotated G) (hd : Dms.Annotated d) : Store.Annotated (G.cons d) :=
  ⟨fun | .here => hd | .there l => hG.ann l⟩

/-- A store with one more location is annotated exactly when the old store and
the new literal are. -/
theorem Store.annotated_cons_iff {σ σ' : Sig} {G : Store σ σ'} {d : Dms σ []} :
    Store.Annotated (G.cons d) ↔ Store.Annotated G ∧ Dms.Annotated d :=
  ⟨fun h => ⟨⟨fun l => h.ann (.there l)⟩, h.ann .here⟩, fun h => h.1.cons h.2⟩

/-- Whether a store is annotated is decidable, one location at a time. -/
instance Store.Annotated.decidable {σ : Sig} :
    {σ' : Sig} → (G : Store σ σ') → Decidable (Store.Annotated G)
  | _, .nil => isTrue Store.Annotated.nil
  | _, .cons G _ =>
      have := Store.Annotated.decidable G
      decidable_of_iff _ Store.annotated_cons_iff.symm

/-! ## Matching a stored literal

`Typing.LitMatch` is the premise of the two location rules.  A source `T_Vary`
derives it **when the stored literal is annotated**: a literal typed at `T`
under its own self, instantiating to what `ℓ` stores, has `T[ℓ]` matching the
stored literal, because `D_Typ` makes each type member exact and `D_Fun`'s
`EqSome` premises make each present annotation the checked type.  An absent
annotation leaves `EqSome` satisfied by any type, and then the match fails,
since it asks for the stored annotation itself (`varyLitMatch_annotated`).
`D_Fun`'s typing of the method body is never needed, which is why a match does
not give a `T_Vary` typing back: the match holds at types no `T_Vary` gives,
such as `⊤` at a location holding a nonempty literal. -/

/-- **An annotated typed definition list's type matches the list**, under any
substitution `θ` into the empty scope and relative to any lookup `g` that finds
every member of the list, substituted.  Positional labels (`dms_get?_head`,
`dms_get?_tail`) are what let the tail of the list keep the same lookup.  At a
method, `D_Fun`'s `EqSome` premises and the list's annotations give the stored
annotations as the checked types (`eqSome_of_isSome`); the method body's typing
is not used. -/
def dmsLitMatch {σ s1 : Sig} {G : Store σ σ} {Γ : Ctx σ s1} (θ : Subst σ s1 σ [])
    (g : Lb → Option (Dm σ [])) :
    {ds : Dms σ s1} → {T : Ty σ s1} → DmsHasType G Γ ds T → Dms.Annotated ds →
    (∀ a d, ds.get? a = some d → g a = some (d.subst θ)) → LitMatch g (T.subst θ)
  | _, _, .D_Nil, _, _ => .top
  | _, _, .D_Typ (ds := ds) (T11 := T11) hds, ha, hg =>
      .typ (hg ds.length (.dty T11) (dms_get?_head _ ds))
        (dmsLitMatch θ g hds ha.tail (fun a d h => hg a d (dms_get?_tail _ h)))
  | _, _, .D_Fun (ds := ds) (OT11 := OT11) (OT12 := OT12) (T11 := T11) (T12 := T12)
      (t12 := t12) hds _ e1 e2, ha, hg =>
      .fn (t := t12.subst θ.lift) (by
          have h := hg ds.length (.dfun OT11 OT12 t12) (dms_get?_head _ ds)
          rw [eqSome_of_isSome e1 ha.head.1, eqSome_of_isSome e2 ha.head.2] at h
          exact h)
        (dmsLitMatch θ g hds ha.tail (fun a d h => hg a d (dms_get?_tail _ h)))

/-- **A pair of `T_Vary` premises gives the location rules' premise, when the
stored literal is annotated**: a literal typed at `T` under its own self,
instantiating to what `ℓ` stores, has `T[ℓ]` matching the stored literal as
soon as every method stored at `ℓ` carries both annotations.  So every type a
source `T_Vary` gives such a location, `VcTy.vcLocAny` and
`AtomTy.varConcAny` give it too; this is what the elaboration of `T_Vary` uses.
No store invariant is needed.

The annotation hypothesis cannot be dropped: `varyLitMatch_annotated` is the
converse. -/
def varyLitMatch {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) (ha : Dms.Annotated (G.lookup l)) :
    LitMatch (G.lookup l).get? (T.substVr (.conc l)) :=
  dmsLitMatch (Subst.one (.conc l)) _ hd
    ((Dms.annotated_subst (Subst.one (.conc l)) ds).mp
      (by rw [show ds.subst (Subst.one (.conc l)) = G.lookup l from hs]; exact ha))
    (fun a d h => by rw [← hs, Dms.get?_subst, h]; rfl)

/-- **A method member of a matched type is a method stored with both
annotations, at the member's two types.**  Only `LitMatch.fn` concludes at an
intersection headed by a method member, and its premise is that stored method;
`LitMatch.typ` hands the question down the spine, and `⊤` has no conjunct.  The
source-store counterpart of `Preservation.LitMatch.method`, which reads the
same fact in a machine store. -/
theorem LitMatch.storedMethod {σ : Sig} {g : Lb → Option (Dm σ [])} :
    {B : Ty σ []} → LitMatch g B → {b : Lb} → {S : Ty σ []} → {U : Ty σ ([],x)} →
    Conjunct B (.TFun b S U) → ∃ t, g b = some (.dfun (some S) (some U) t)
  | _, .top, _, _, _, c => nomatch c
  | _, .typ _ r, _, _, _, c => by
      cases c with
      | there c => exact LitMatch.storedMethod r c
  | _, .fn (t := t) hg r, _, _, _, c => by
      cases c with
      | here => exact ⟨t, hg⟩
      | there c => exact LitMatch.storedMethod r c

/-- **A stored method lacking an annotation matches no method member.**  If the
literal defines at label `b` a member that does not carry its annotations
(`Dm.Annotated`), no type with a method member at `b`, anywhere along its
spine, matches the literal (`LitMatch.storedMethod`). -/
theorem LitMatch.no_unannotated_method {σ : Sig} {g : Lb → Option (Dm σ [])} {b : Lb}
    {d : Dm σ []} (hg : g b = some d) (hd : ¬ Dm.Annotated d) {B : Ty σ []}
    (m : LitMatch g B) {S : Ty σ []} {U : Ty σ ([],x)} (c : Conjunct B (.TFun b S U)) :
    False := by
  obtain ⟨t, ht⟩ := m.storedMethod c
  rw [hg] at ht
  cases ht
  exact hd (show (some S).isSome ∧ (some U).isSome from ⟨rfl, rfl⟩)

/-- **The converse of `dmsLitMatch`: a typed definition list whose type
matches is annotated.**  Under the same substitution `θ` and lookup `g`, if
`T[θ]` matches, every method of the list carries both annotations.  At a
method, `LitMatch.fn` finds the stored method with both annotations, and that
stored method is the list's own method substituted, which carries the same
annotations (`Dm.annotated_subst`).  Nothing about the method body is used. -/
theorem dmsLitMatch_annotated {σ s1 : Sig} {G : Store σ σ} {Γ : Ctx σ s1}
    (θ : Subst σ s1 σ []) (g : Lb → Option (Dm σ [])) :
    {ds : Dms σ s1} → {T : Ty σ s1} → DmsHasType G Γ ds T →
    (∀ a d, ds.get? a = some d → g a = some (d.subst θ)) → LitMatch g (T.subst θ) →
    Dms.Annotated ds
  | _, _, .D_Nil, _, _ => trivial
  | _, _, .D_Typ hds, hg, m => by
      cases m with
      | typ _ r =>
          exact And.intro trivial
            (dmsLitMatch_annotated θ g hds (fun a d h => hg a d (dms_get?_tail _ h)) r)
  | _, _, .D_Fun (ds := ds) (OT11 := OT11) (OT12 := OT12) (t12 := t12) hds _ _ _, hg, m => by
      cases m with
      | fn hf r =>
          refine And.intro ?_
            (dmsLitMatch_annotated θ g hds (fun a d h => hg a d (dms_get?_tail _ h)) r)
          have h := hg ds.length (.dfun OT11 OT12 t12) (dms_get?_head _ ds)
          rw [hf] at h
          have ha : Dm.Annotated ((Dm.dfun OT11 OT12 t12).subst θ) := by
            rw [← Option.some.inj h]
            exact show (some _).isSome ∧ (some _).isSome from ⟨rfl, rfl⟩
          exact (Dm.annotated_subst θ _).mp ha

/-- **`varyLitMatch`'s annotation hypothesis cannot be dropped.**  If a pair of
`T_Vary` premises at `ℓ` has `T[ℓ]` matching the literal stored at `ℓ`, that
literal is annotated (`dmsLitMatch_annotated`).  So at a location holding a
method without both annotations, no type a source `T_Vary` gives the location
matches, and the location rules `VcTy.vcLocAny` and `AtomTy.varConcAny` give
it none of them (`Admissibility.vcLocAny_not_vary`,
`Admissibility.varConcAny_not_vary`). -/
theorem varyLitMatch_annotated {σ : Sig} {G : Store σ σ} {l : BVar σ .var}
    {T : Ty σ ([],x)} {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l)
    (m : LitMatch (G.lookup l).get? (T.substVr (.conc l))) : Dms.Annotated (G.lookup l) := by
  have ha := dmsLitMatch_annotated (Subst.one (.conc l)) _ hd
    (fun a d h => by rw [← hs, Dms.get?_subst, h]; rfl) m
  rw [← hs]
  exact (Dms.annotated_subst (Subst.one (.conc l)) ds).mpr ha

/-- **A pair of `T_Vary` premises gives the match exactly when the stored
literal is annotated**: `varyLitMatch` and `varyLitMatch_annotated`. -/
theorem varyLitMatch_iff {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) :
    Nonempty (LitMatch (G.lookup l).get? (T.substVr (.conc l))) ↔
      Dms.Annotated (G.lookup l) :=
  ⟨fun ⟨m⟩ => varyLitMatch_annotated hd hs m, fun ha => ⟨varyLitMatch hd hs ha⟩⟩

/-! ## Honest stores -/

/-- What honesty asks at one location: the store typing's entry is a type the
stored literal really has under its own self, and instantiating that self by
the location gives what the store holds.  These are exactly `T_Vary`'s two
premises (`dot.v:220-226`). -/
structure HonestAt {σ : Sig} (G : Store σ σ) (W : StoreTy σ) (l : BVar σ .var) :
    Type where
  /-- The literal, before its self is instantiated. -/
  defs : Dms σ ([],x)
  /-- It has the recorded type, under that type as its self assumption. -/
  typed : DmsHasType G (Ctx.nil.cons (W l)) defs (W l)
  /-- Instantiating the self by the location gives the stored literal. -/
  stored : defs.substVr (.conc l) = G.lookup l

/-- An honest store: every location's literal really has the type the store
typing records for it.  The reference has no such predicate — `venv` is
unconstrained (`dot.v:69`) and `T_Vary` re-derives the literal's type at every
use — which is exactly why `StoreTy` needs one here. -/
structure Store.Honest {σ : Sig} (G : Store σ σ) (W : StoreTy σ) : Type where
  /-- The witness at each location. -/
  at' : (l : BVar σ .var) → HonestAt G W l

/-- **`AtomTy.varConc` is the reference's `T_Vary`.**  Over an honest store the
type the target reads off `W` is one the source assigns to the location, so
indexing by a function rather than by a derivation costs nothing. -/
def Store.Honest.vary {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (h : Store.Honest G W) (l : BVar σ .var) :
    HasType G Γ (.tvar (.conc l)) ((tyOf W l).rename renameNil) :=
  .T_Vary (h.at' l).typed (h.at' l).stored

/-- **A `T_Vary` witness agrees with what `defL`/`defR` read.**  If a literal
`ds` has type `T` under its own self and instantiates to what `ℓ` stores — the
two premises of `T_Vary` — and the stored literal defines the type member `a`
to be `TX`, then `T` instantiated at `ℓ` has `{a : TX .. TX}` among its
conjuncts.  `D_Typ` makes the member exact whatever type the witness picks, so
this needs no store invariant; `Store.Honest.member` is its instance at the
recorded type.  A type that merely matches the stored literal (`LitMatch`) need
not have the conjunct, since it may leave members out. -/
def varyMember {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    Conjunct (T.substVr (.conc l)) (.TTyp a TX TX) := by
  have hg2 : (ds.substVr (.conc l)).get? a = some (.dty TX) := by
    rw [hs]; exact hg
  rw [Dms.get?_subst] at hg2
  cases hget : ds.get? a with
  | none => rw [hget] at hg2; simp at hg2
  | some d =>
      rw [hget] at hg2
      cases d with
      | dfun _ _ _ => simp [Dm.subst] at hg2
      | dty TX0 =>
          have hTX : TX0.substVr (.conc l) = TX := by
            simp only [Option.map_some, Dm.subst] at hg2
            injection hg2 with e
            injection e
          have hc := Conjunct.subst (Subst.one (Vr.conc l))
            (DmsHasType.conjunct hd hget)
          simp only [Ty.subst] at hc
          rw [show Ty.subst TX0 (Subst.one (Vr.conc l)) = TX from hTX] at hc
          exact hc

/-- **A `T_Vary` witness declares each annotated stored method at its
annotations.**  If a literal `ds` has type `T` under its own self and
instantiates to what `ℓ` stores — the two premises of `T_Vary` — and the
stored literal has at label `a` a method stored as `dfun (some S) (some U) t`,
then `T` instantiated at `ℓ` has `{a : S → U}` among its conjuncts.  The
witness's method at `a` carries the two annotations that instantiate to `S` and
`U`, and `D_Fun`'s `EqSome` premises make them the types it checked
(`DmsHasType.conjunctFun`).  The method counterpart of `varyMember`, again with
no store invariant; `Store.Honest.method` is its instance at the recorded
type. -/
def varyMethod {σ : Sig} {G : Store σ σ} {l : BVar σ .var} {T : Ty σ ([],x)}
    {ds : Dms σ ([],x)} (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) {a : Lb} {S : Ty σ []}
    {U : Ty σ ([],x)} {t : Oopsla16.Tm σ ([],x)}
    (hg : (G.lookup l).get? a = some (.dfun (some S) (some U) t)) :
    Conjunct (T.substVr (.conc l)) (.TFun a S U) := by
  have hg2 : (ds.substVr (.conc l)).get? a = some (.dfun (some S) (some U) t) := by
    rw [hs]; exact hg
  rw [Dms.get?_subst] at hg2
  cases hget : ds.get? a with
  | none => rw [hget] at hg2; simp at hg2
  | some d =>
      rw [hget] at hg2
      cases d with
      | dty _ => simp [Dm.subst] at hg2
      | dfun OS0 OU0 t0 =>
          cases OS0 with
          | none => simp [Dm.subst] at hg2
          | some S0 =>
              cases OU0 with
              | none => simp [Dm.subst] at hg2
              | some U0 =>
                  simp only [Option.map_some, Dm.subst, Option.some.injEq,
                    Dm.dfun.injEq] at hg2
                  obtain ⟨hS, hU, -⟩ := hg2
                  have hc := Conjunct.subst (Subst.one (Vr.conc l))
                    (DmsHasType.conjunctFun hd hget)
                  simp only [Ty.subst] at hc
                  rw [hS, hU] at hc
                  exact hc

/-- **The store typing agrees with what `defL`/`defR` read.**  If the literal
stored at `ℓ` defines the type member `a` to be `TX` — the premise of
`LeTy.defL` and `LeTy.defR`, and the reference's `stp_strong_sel1/2`
(`dot.v:305-314`) — then `tyOf W ℓ` has `{a : TX .. TX}` among its conjuncts.
The instance of `varyMember` at the honesty witness. -/
def Store.Honest.member {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    Conjunct (tyOf W l) (.TTyp a TX TX) :=
  varyMember (h.at' l).typed (h.at' l).stored hg

/-- **The store typing declares each annotated stored method at its
annotations.**  If the literal stored at `ℓ` has at label `a` a method stored
as `dfun (some S) (some U) t` — what the method case of `Typing.LitMatch`
finds — then `tyOf W ℓ` has `{a : S → U}` among its conjuncts.  The instance of
`varyMethod` at the honesty witness, and the method counterpart of
`Store.Honest.member`. -/
def Store.Honest.method {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (l : BVar σ .var) {a : Lb} {S : Ty σ []}
    {U : Ty σ ([],x)} {t : Oopsla16.Tm σ ([],x)}
    (hg : (G.lookup l).get? a = some (.dfun (some S) (some U) t)) :
    Conjunct (tyOf W l) (.TFun a S U) :=
  varyMethod (h.at' l).typed (h.at' l).stored hg

/-- The observation of a location that `selL`/`selR` consume, built from the
definition `defL`/`defR` read.  Over an honest store the two ways of resolving
a concrete type selection therefore agree, which is the easy half of the
`obs_conc_admissible` question `PLAN.md` leaves open. -/
def Store.Honest.obs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    (h : Store.Honest G W) (l : BVar σ .var) {a : Lb} {TX : Ty σ []}
    (hg : (G.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G W Γ (.conc l) v (.TTyp a TX TX) :=
  let c := h.member l hg
  ⟨.vcSub (tyOf W l) c.ev (.vcLoc l),
    VcTy.vcSub (Γ := Γ) (p := .conc l) (tyOf W l) VcTy.vcLoc c.typed⟩

/-- The observation `selL`/`selR` consume, built through a `T_Vary` witness
rather than through the store typing: `vcLocAny` at the witness's self type
(its premise by `varyLitMatch`, which needs the stored literal annotated),
widened to the member by `varyMember`.  The `vcLocAny` counterpart of
`Store.Honest.obs`, with no honesty hypothesis. -/
def varyObs {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} {T : Ty σ ([],x)} {ds : Dms σ ([],x)}
    (hd : DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) (ha : Dms.Annotated (G.lookup l))
    {a : Lb} {TX : Ty σ []} (hg : (G.lookup l).get? a = some (.dty TX)) :
    (v : Vc σ []) × VcTy G W Γ (.conc l) v (.TTyp a TX TX) :=
  let c := varyMember hd hs hg
  ⟨.vcSub (T.substVr (.conc l)) c.ev (.vcLocAny l T),
    VcTy.vcSub (Γ := Γ) (p := .conc l) (T.substVr (.conc l))
      (VcTy.vcLocAny (varyLitMatch hd hs ha)) c.typed⟩

/-- **Over an honest store `vcLoc` is an instance of `vcLocAny` wherever the
stored literal is annotated.**  The honesty witness at `ℓ` is a pair of
`T_Vary` premises at the recorded type `W ℓ`, so with the literal stored at `ℓ`
annotated `varyLitMatch` gives the match at `(W ℓ).substVr (conc ℓ)`, which is
`tyOf W ℓ` by definition, and `VcTy.vcLocAny` at `W ℓ` observes `ℓ` at exactly
the type `VcTy.vcLoc` reads off `W`.

The annotation hypothesis is needed: at a location holding a method without
both annotations `vcLoc` is an instance of `vcLocAny` at no self type
(`Store.Honest.not_vcLocAny_tyOf`).  What `vcLocAny` adds is the observation
at *other* types that match the literal; over an honest store each of them is
a source typing of `ℓ` (`Admissibility.Store.Honest.litMatch_hasType`). -/
def Store.Honest.vcLoc_of_vcLocAny {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : Store.Honest G W) (l : BVar σ .var)
    (ha : Dms.Annotated (G.lookup l)) :
    VcTy G W Γ (.conc l) (.vcLocAny l (W l)) (tyOf W l) :=
  .vcLocAny (varyLitMatch (h.at' l).typed (h.at' l).stored ha)

/-- **Over an honest store the recorded type matches the stored literal
exactly when that literal is annotated.**  The honesty witness at `ℓ` is a
pair of `T_Vary` premises at `W ℓ`, and `tyOf W ℓ` is `(W ℓ).substVr (conc ℓ)`,
so this is `varyLitMatch_iff` at the witness. -/
theorem Store.Honest.litMatch_tyOf_iff {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (l : BVar σ .var) :
    Nonempty (LitMatch (G.lookup l).get? (tyOf W l)) ↔ Dms.Annotated (G.lookup l) :=
  varyLitMatch_iff (h.at' l).typed (h.at' l).stored

/-- **At a location whose stored literal is not annotated, `vcLoc` is an
instance of `vcLocAny` at no self type**: over an honest store no node
`vcLocAny ℓ T` observes `ℓ` at the recorded type `tyOf W ℓ`, because its one
rule would need `tyOf W ℓ` to match the stored literal
(`Store.Honest.litMatch_tyOf_iff`). -/
theorem Store.Honest.not_vcLocAny_tyOf {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : Store.Honest G W) {l : BVar σ .var}
    (hna : ¬ Dms.Annotated (G.lookup l)) (T : Ty σ ([],x))
    (d : VcTy G W Γ (.conc l) (.vcLocAny l T) (tyOf W l)) : False := by
  have key : ∀ {U : Ty σ []}, VcTy G W Γ (.conc l) (.vcLocAny l T) U →
      U = tyOf W l → False := by
    intro U d' hU
    cases d' with
    | vcLocAny hm => exact hna ((h.litMatch_tyOf_iff l).mp ⟨hU ▸ hm⟩)
  exact key d rfl

/-! ## Store renaming

The reference's concrete identifiers are absolute positions, "invariant under
context extension" (`dot.v:21-22`), so allocation costs it nothing.  Here a
store weakening is a real renaming of the store scope, and the four judgments
have to be shown stable under it.  The local scope is a separate index and is
never touched, so `scopeUpTo` is unchanged throughout and no scope transport
appears; the only content is that a renamed store's lookups are the renamed
lookups.

`Ctx.renameStore` and the three lemmas about it live here rather than in
`Oopsla16.Context`, so they are written prefix: dot notation would look for
them in `Oopsla16`. -/

/-- Rename every context entry's store scope. -/
def Ctx.renameStore {σ1 σ2 : Sig} :
    {s : Sig} → Ctx σ1 s → Rename σ1 σ2 → Ctx σ2 s
  | _, .nil, _ => .nil
  | _, .cons Γ T, ρ => .cons (Ctx.renameStore Γ ρ) (T.renameStore ρ)

/-- Reading a hypothesis in its own prefix commutes with a store renaming. -/
theorem Ctx.lookupAt_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (Γ : Ctx σ1 s) → (y : BVar s .var) →
    (Ctx.renameStore Γ ρ).lookupAt y = (Γ.lookupAt y).renameStore ρ
  | _, .cons _ _, .here => rfl
  | _, .cons Γ _, .there y => Ctx.lookupAt_renameStore ρ Γ y

/-- Reading a hypothesis commutes with a store renaming. -/
theorem Ctx.lookup_renameStore {σ1 σ2 s : Sig} (ρ : Rename σ1 σ2) (Γ : Ctx σ1 s)
    (y : BVar s .var) :
    (Ctx.renameStore Γ ρ).lookup y = (Γ.lookup y).renameStore ρ := by
  show ((Ctx.renameStore Γ ρ).lookupAt y).rename (renameUpTo y)
      = ((Γ.lookupAt y).rename (renameUpTo y)).renameStore ρ
  rw [Ctx.lookupAt_renameStore ρ Γ y]
  exact (Ty.renameStore_rename (Γ.lookupAt y) (renameUpTo y) ρ).symm

/-- Truncating at a variable commutes with a store renaming. -/
theorem Ctx.upTo_renameStore {σ1 σ2 : Sig} (ρ : Rename σ1 σ2) :
    {s : Sig} → (Γ : Ctx σ1 s) → (y : BVar s .var) →
    (Ctx.renameStore Γ ρ).upTo y = Ctx.renameStore (Γ.upTo y) ρ
  | _, .cons _ _, .here => rfl
  | _, .cons Γ _, .there y => Ctx.upTo_renameStore ρ Γ y

/-- Extending by a hypothesis that does not mention itself — the parameter of
`stp_fun`, `D_Fun`, `stp_bind1` — commutes with a store renaming.  Stated
separately because the weakening has to be pushed past the renaming. -/
theorem Ctx.renameStore_consWeaken {σ1 σ2 s : Sig} (Γ : Ctx σ1 s) (T : Ty σ1 s)
    (ρ : Rename σ1 σ2) :
    Ctx.renameStore (Γ.cons T.weaken) ρ
      = (Ctx.renameStore Γ ρ).cons ((T.renameStore ρ).weaken) := by
  show (Ctx.renameStore Γ ρ).cons (T.weaken.renameStore ρ) = _
  rw [Ty.renameStore_weaken]

/-- A renaming of the store scope that transports every lookup.  Allocation is
the instance `StoreMap.alloc`. -/
structure StoreMap {σ1 σ2 : Sig} (G1 : Store σ1 σ1) (G2 : Store σ2 σ2) : Type where
  /-- The renaming of locations. -/
  ren : Rename σ1 σ2
  /-- It carries each stored literal to the one at the image location. -/
  lookup : ∀ l : BVar σ1 .var, (G1.lookup l).renameStore ren = G2.lookup (ren.var l)

mutual

/-- `has_type` is stable under a store renaming. -/
def HasType.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {t : Oopsla16.Tm σ1 s} → {T : Ty σ1 s} →
    HasType G1 Γ t T →
    HasType G2 (Ctx.renameStore Γ m.ren) (t.renameStore m.ren) (T.renameStore m.ren)
  | _, _, _, _, .T_Vary (x := y) (ds := ds) (T := T) hd hs => by
      have hs' : (ds.renameStore m.ren).substVr
          ((Vr.conc y).subst (Subst.ofStore m.ren)) = G2.lookup (m.ren.var y) := by
        rw [← Dms.renameStore_substVr, hs]
        exact m.lookup y
      rw [Ty.renameStore_rename, Ty.renameStore_substVr]
      exact .T_Vary (DmsHasType.renameStore m hd) hs'
  | _, _, _, _, .T_Varz => by
      rw [← Ctx.lookup_renameStore]
      exact .T_Varz
  | _, _, _, _, .T_VarPack h => by
      have h' := HasType.renameStore m h
      rw [Ty.renameStore_substVr] at h'
      simp only [Ty.renameStore_TBind]
      exact .T_VarPack h'
  | _, _, _, _, .T_VarUnpack h => by
      have h' := HasType.renameStore m h
      simp only [Ty.renameStore_TBind] at h'
      rw [Ty.renameStore_substVr]
      exact .T_VarUnpack h'
  | _, _, _, _, .T_Obj hd => by
      simp only [Ty.renameStore_TBind, Oopsla16.Tm.renameStore_tobj]
      exact .T_Obj (DmsHasType.renameStore m hd)
  | _, _, _, _, .T_App h1 h2 => by
      have h1' := HasType.renameStore m h1
      simp only [Ty.renameStore_TFun] at h1'
      rw [Ty.renameStore_weaken] at h1'
      exact .T_App h1' (HasType.renameStore m h2)
  | _, _, _, _, .T_AppVar h1 h2 => by
      have h1' := HasType.renameStore m h1
      simp only [Ty.renameStore_TFun] at h1'
      rw [Ty.renameStore_substVr]
      exact .T_AppVar h1' (HasType.renameStore m h2)
  | _, _, _, _, .T_Sub h hs =>
      .T_Sub (HasType.renameStore m h) (Stp.renameStore m hs)

/-- `dms_has_type` is stable under a store renaming.  The positional labels
survive because substitution preserves length (`Dms.length_subst`). -/
def DmsHasType.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {ds : Dms σ1 s} → {T : Ty σ1 s} →
    DmsHasType G1 Γ ds T →
    DmsHasType G2 (Ctx.renameStore Γ m.ren) (ds.renameStore m.ren)
      (T.renameStore m.ren)
  | _, _, _, _, .D_Nil => .D_Nil
  | _, _, _, _, .D_Typ (ds := ds) hd => by
      simp only [Ty.renameStore_TAnd, Ty.renameStore_TTyp,
        Dms.renameStore_dcons, Dm.renameStore_dty]
      rw [← Dms.length_subst ds (Subst.ofStore m.ren)]
      exact .D_Typ (DmsHasType.renameStore m hd)
  | _, _, _, _, .D_Fun (ds := ds) hd ht e1 e2 => by
      have ht' := HasType.renameStore m ht
      rw [Ctx.renameStore_consWeaken] at ht'
      simp only [Ty.renameStore_TAnd, Ty.renameStore_TFun,
        Dms.renameStore_dcons, Dm.renameStore_dfun]
      rw [← Dms.length_subst ds (Subst.ofStore m.ren)]
      exact .D_Fun (DmsHasType.renameStore m hd) ht'
        (eqSome_map _ e1) (eqSome_map _ e2)

/-- `stp` is stable under a store renaming.  The two concrete-selection rules
are the only ones that consult the store, and they consult it through
`Dms.get?`, which commutes with substitution. -/
def Stp.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {T1 T2 : Ty σ1 s} → Stp G1 Γ T1 T2 →
    Stp G2 (Ctx.renameStore Γ m.ren) (T1.renameStore m.ren) (T2.renameStore m.ren)
  | _, _, _, _, .stp_bot => .stp_bot
  | _, _, _, _, .stp_top => .stp_top
  | _, _, _, _, .stp_fun h1 h2 => by
      have h2' := Stp.renameStore m h2
      rw [Ctx.renameStore_consWeaken] at h2'
      simp only [Ty.renameStore_TFun]
      exact .stp_fun (Stp.renameStore m h1) h2'
  | _, _, _, _, .stp_typ h1 h2 => by
      simp only [Ty.renameStore_TTyp]
      exact .stp_typ (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_strong_sel1 (x := y) (l := a) (TX := TX) hg h => by
      have hg' : (G2.lookup (m.ren.var y)).get? a
          = some (.dty (TX.renameStore m.ren)) := by
        rw [← m.lookup y, Dms.get?_subst, hg]; rfl
      simp only [Ty.renameStore_TSel]
      rw [Ty.renameStore_rename]
      exact .stp_strong_sel1 hg' (Stp.renameStore m h)
  | _, _, _, _, .stp_strong_sel2 (x := y) (l := a) (TX := TX) hg h => by
      have hg' : (G2.lookup (m.ren.var y)).get? a
          = some (.dty (TX.renameStore m.ren)) := by
        rw [← m.lookup y, Dms.get?_subst, hg]; rfl
      simp only [Ty.renameStore_TSel]
      rw [Ty.renameStore_rename]
      exact .stp_strong_sel2 hg' (Stp.renameStore m h)
  | _, _, _, _, .stp_sel1 h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TTyp, Ty.renameStore_TBot,
        Ty.renameStore_TSel] at h' ⊢
      rw [Ty.renameStore_rename]
      exact .stp_sel1 h'
  | _, _, _, _, .stp_sel2 h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TTyp, Ty.renameStore_TTop,
        Ty.renameStore_TSel] at h' ⊢
      rw [Ty.renameStore_rename]
      exact .stp_sel2 h'
  | _, _, _, _, .stp_selx => .stp_selx
  | _, _, _, _, .stp_bind1 h => by
      have h' := Stp.renameStore m h
      rw [Ty.renameStore_weaken] at h'
      simp only [Ty.renameStore_TBind]
      exact .stp_bind1 h'
  | _, _, _, _, .stp_bindx h => by
      simp only [Ty.renameStore_TBind]
      exact .stp_bindx (Stp.renameStore m h)
  | _, _, _, _, .stp_and11 h => by
      simp only [Ty.renameStore_TAnd]; exact .stp_and11 (Stp.renameStore m h)
  | _, _, _, _, .stp_and12 h => by
      simp only [Ty.renameStore_TAnd]; exact .stp_and12 (Stp.renameStore m h)
  | _, _, _, _, .stp_and2 h1 h2 => by
      simp only [Ty.renameStore_TAnd]
      exact .stp_and2 (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_or21 h => by
      simp only [Ty.renameStore_TOr]; exact .stp_or21 (Stp.renameStore m h)
  | _, _, _, _, .stp_or22 h => by
      simp only [Ty.renameStore_TOr]; exact .stp_or22 (Stp.renameStore m h)
  | _, _, _, _, .stp_or1 h1 h2 => by
      simp only [Ty.renameStore_TOr]
      exact .stp_or1 (Stp.renameStore m h1) (Stp.renameStore m h2)
  | _, _, _, _, .stp_trans h1 h2 =>
      .stp_trans (Stp.renameStore m h1) (Stp.renameStore m h2)

/-- `htp` is stable under a store renaming.  The subject and its prefix scope
are untouched, so this is the one judgment where nothing has to be said. -/
def Htp.renameStore {σ1 σ2 : Sig} {G1 : Store σ1 σ1} {G2 : Store σ2 σ2}
    (m : StoreMap G1 G2) :
    {s : Sig} → {Γ : Ctx σ1 s} → {y : BVar s .var} → {T : Ty σ1 (scopeUpTo y)} →
    Htp G1 Γ y T → Htp G2 (Ctx.renameStore Γ m.ren) y (T.renameStore m.ren)
  | _, _, _, _, .htp_var => by
      rw [← Ctx.lookupAt_renameStore]
      exact .htp_var
  | _, _, _, _, .htp_unpack h => by
      have h' := Htp.renameStore m h
      simp only [Ty.renameStore_TBind] at h'
      rw [Ty.renameStore_substVr]
      exact .htp_unpack h'
  | _, _, _, _, .htp_sub h hs => by
      have hs' := Stp.renameStore m hs
      rw [← Ctx.upTo_renameStore] at hs'
      exact .htp_sub (Htp.renameStore m h) hs'

end

/-! ## A substitution's store part

`Subst.conc` maps locations to locations (`Oopsla16.Structural`): the reference
never substitutes for a concrete variable.  So the store part of *any*
substitution is a renaming of the store scope, and on the empty local scope,
where a stored literal lives, a substitution *is* that renaming.  That is what
moves the location rules' premise along a substitution.  `LitMatch` reads the
stored literal only through `Dms.get?`, so the store agreement of
`SubstTyping.MonoSyn.Ev`, read at one label (`defs_get?`), carries it
(`LitMatch.subst`), and `varyTy` is the equation on the type the rules report.
Those three are what the `vcLocAny` and `AtomTy.varConcAny` clauses of the two
substitution theorems consume.

Written prefix rather than as `Subst.storeRen`, for the reason
`Ctx.renameStore` above gives: dot notation on an `Oopsla16.Subst` would look
for the name in `Oopsla16`. -/

/-- The store part of a substitution, read as a renaming of the store scope. -/
def storeRen {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) : Rename σ1 σ2 where
  var := fun {k} => match k with | .var => θ.conc

/-- On the empty local scope a substitution *is* its store renaming: there is
no local variable left for the two to differ at. -/
theorem atNil_eq_ofStore {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    Subst.atNil θ = Subst.ofStore (s := []) (storeRen θ) :=
  Subst.ext (fun _ => rfl) (fun y => nomatch y)

/-- The same one binder in, which is where a stored literal and its self type
live. -/
theorem atNil_lift_eq_ofStore {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (Subst.atNil θ).lift = Subst.ofStore (s := ([],x)) (storeRen θ) := by
  rw [atNil_eq_ofStore, Subst.lift_ofStore]

/-- **The store agreement, read at one label.**  If the image store holds at
the image of `ℓ` the literal at `ℓ`, substituted — the sense of
`SubstTyping.MonoSyn.Ev`'s `defs` field, taken here as a bare hypothesis so
that this sits below `SubstTyping` in the import order — then every member it
has there is the member at `ℓ`, substituted. -/
theorem defs_get? {σ1 σ2 s1 s2 : Sig} {G : Store σ1 σ1} {G' : Store σ2 σ2}
    (θ : Subst σ1 s1 σ2 s2) {l : BVar σ1 .var}
    (h : G'.lookup (θ.conc l) = (G.lookup l).subst (Subst.atNil θ)) (a : Lb) :
    (G'.lookup (θ.conc l)).get? a
      = ((G.lookup l).get? a).map (fun d => d.subst (Subst.atNil θ)) := by
  rw [h, Dms.get?_subst]

/-- **A match survives a substitution of the empty local scope**, relative to
two member lookups that agree up to it.  Each member moves by `Dm.subst`,
which maps a present annotation to a present annotation.  The substitution
theorems use it at `Subst.atNil θ`, with `defs_get?` for the lookups. -/
def LitMatch.subst {σ1 σ2 : Sig} (θ : Subst σ1 [] σ2 [])
    {g : Lb → Option (Dm σ1 [])} {g' : Lb → Option (Dm σ2 [])}
    (hg : ∀ a, g' a = (g a).map (fun d => d.subst θ)) :
    {B : Ty σ1 []} → LitMatch g B → LitMatch g' (B.subst θ)
  | _, .top => .top
  | _, .typ (b := b) h r => .typ (by rw [hg b, h]; rfl) (LitMatch.subst θ hg r)
  | _, .fn (b := b) (t := t) h r =>
      .fn (t := t.subst θ.lift) (by rw [hg b, h]; rfl) (LitMatch.subst θ hg r)

/-- **The type a location rule reports, moved along a substitution.**
Substituting `T[ℓ]`, the type `VcTy.vcLocAny` and `AtomTy.varConcAny` report
at `ℓ` for the self type `T`, is instantiating the renamed self type at the
image location.  This is the equation the `vcLocAny`/`varConcAny` clauses of
the two substitution theorems close with. -/
theorem varyTy {σ1 σ2 s1 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) (l : BVar σ1 .var)
    (T : Ty σ1 ([],x)) :
    (T.substVr (.conc l)).subst (Subst.atNil θ)
      = (T.renameStore (storeRen θ)).substVr (.conc (θ.conc l)) := by
  rw [atNil_eq_ofStore]
  exact Ty.renameStore_substVr T (.conc l) (storeRen θ)

/-! ## Allocation

`ST_Obj` (`Semantics.lean`, `dot.v:199-200`) allocates one location and
substitutes it for the literal's self.  Honesty is preserved by extending `W`
with the literal's type, weakened. -/

/-- Allocating one location is a store map: every old lookup is weakened. -/
def StoreMap.alloc {σ : Sig} (G : Store σ σ) (d : Dms (σ,x) []) :
    StoreMap G (G.weakenStore.cons d) where
  ren := Rename.succ
  lookup := fun l => (Store.lookup_renameStore G Rename.succ l).symm

/-- The store typing extended by one newly allocated location. -/
def StoreTy.alloc {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x)) : StoreTy (σ,x)
  | .here => TD.weakenStore
  | .there l => (W l).weakenStore

/-- At the newly allocated location the recorded type is the literal's type,
weakened, with its self instantiated there. -/
theorem tyOf_alloc_here {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x)) :
    tyOf (StoreTy.alloc W TD) .here = TD.weakenStore.substVr (.conc .here) := rfl

/-- At an old location the recorded type is the old one, weakened.  This is the
`tys` field of a store-weakening hypothesis structure, and the target machine's
honesty invariant (`Preservation.MachineStore.Honest.alloc`) consumes it. -/
theorem tyOf_alloc_there {σ : Sig} (W : StoreTy σ) (TD : Ty σ ([],x))
    (l : BVar σ .var) :
    tyOf (StoreTy.alloc W TD) (.there l) = (tyOf W l).weakenStore := by
  show ((W l).weakenStore).substVr (.conc (.there l))
      = ((W l).substVr (.conc l)).renameStore Rename.succ
  rw [Ty.renameStore_substVr]
  rfl

/-- **Honesty is preserved by allocation.**  The statement mirrors
`Step.ST_Obj`: from a literal that is well typed under its own self over the
old store, the store `G` extended with that literal at its own new location is
honest at `W` extended with the literal's type.  Both halves go through
`DmsHasType.renameStore`, which is where the reference's `dot.v:21-22` is
being paid for. -/
def Store.Honest.alloc {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) {D : Dms σ ([],x)} {TD : Ty σ ([],x)}
    (hd : DmsHasType G (Ctx.nil.cons TD) D TD) :
    Store.Honest (G.weakenStore.cons (D.weakenStore.substVr (.conc .here)))
      (StoreTy.alloc W TD) where
  at' := fun
    | .here =>
        { defs := D.weakenStore
          typed := DmsHasType.renameStore (StoreMap.alloc G _) hd
          stored := rfl }
    | .there l =>
        { defs := (h.at' l).defs.weakenStore
          typed := DmsHasType.renameStore (StoreMap.alloc G _) (h.at' l).typed
          stored := by
            show ((h.at' l).defs.renameStore Rename.succ).substVr
                ((Vr.conc l).subst (Subst.ofStore Rename.succ)) = _
            rw [← Dms.renameStore_substVr, (h.at' l).stored]
            exact (Store.lookup_renameStore G Rename.succ l).symm }

/-! ## An honest store

`Oopsla16.PackingCounterexample` builds a two-object store over which the
reference calculus is well behaved — its unsoundness needs the *extra* rule
`htp_pack`, not the store.  So it is the natural test that `Store.Honest` is
inhabited by something non-trivial: two locations, whose definitions mention
the older one, and whose labels are positional. -/

namespace TwoObjectStore

open Oopsla16.PackingCounterexample
  (A B C D S2 p q Bbody Cbody pDefs qDefs G)

/-- The store typing of the two-object store.  Each entry is the right-nested
intersection `D_Typ` produces: `p` has `C` at label `1` and `B` at label `0`,
`q` has `A` at label `0`, every bound exact, and each spine ends in `⊤`. -/
def W : StoreTy S2
  | .here => .TAnd (.TTyp A D D) .TTop
  | .there .here =>
      .TAnd (.TTyp C Cbody Cbody) (.TAnd (.TTyp B Bbody Bbody) .TTop)

/-- The two-object store is honest at `W`.  Both `stored` obligations are
`rfl`: the stored literals mention no abstract variable, so instantiating the
self changes nothing. -/
def honest : Store.Honest G W where
  at' := fun
    | .here =>
        { defs := qDefs, typed := .D_Typ .D_Nil, stored := rfl }
    | .there .here =>
        { defs := pDefs, typed := .D_Typ (.D_Typ .D_Nil), stored := rfl }

/-- The two-object store is annotated: it stores type members only.  An
instance, so that the elaboration of a typing over this store finds it. -/
instance annotated : Store.Annotated G := by decide

/-- The member lemma fires on it: `p`'s definition of `B`, which `defL`/`defR`
read off the store, is the bounds `tyOf W p` declares. -/
example : Conjunct (tyOf W p) (.TTyp B Bbody Bbody) := honest.member p rfl

/-- And `q`'s definition of `A`. -/
example : Conjunct (tyOf W q) (.TTyp A D D) := honest.member q rfl

/-- So the observation a concrete `selL`/`selR` consumes is available. -/
example :
    (v : Vc S2 []) × VcTy G W (Ctx.nil (σ := S2)) (.conc p) v (.TTyp C Cbody Cbody) :=
  honest.obs p rfl

/-- Allocating a third object — the empty one — keeps the store honest. -/
example :
    Store.Honest ((G.weakenStore).cons ((Dms.dnil (σ := S2) (s := ([],x))).weakenStore.substVr
      (.conc .here))) (StoreTy.alloc W .TTop) :=
  honest.alloc (D := .dnil) (TD := .TTop) .D_Nil

end TwoObjectStore

end FCdotR
