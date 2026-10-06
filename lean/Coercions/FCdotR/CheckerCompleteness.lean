import Coercions.FCdotR.Checker

/-!
# Completeness of the FCdotR checker

`Checker` gives kernels that return the derivation they validated, so
soundness is extraction.  This module proves the converse, in the strong form
`FCdot/CheckerCompleteness.lean` states it: every derivation is accepted, and
the kernel returns **that derivation**, with the outputs it assigns.

```text
LeTy.complete  : (h : LeTy G W Γ e S T) → synthLeCore G W Γ e = some ⟨S, T, h⟩
VcTy.complete  : (h : VcTy G W Γ p v T) → synthVcCore G W Γ p v = some ⟨T, h⟩
```

and likewise for atoms, terms and definition lists.  In FCdot the derivation
is a proposition, so such an equation is about the outputs only.  Here
derivations are `Type`-valued data, and the equation is about the derivation
too.  It holds because the kernel rebuilds the derivation from the same
pieces: the node fixes the rule, by induction the recursive calls return the
premises' own derivations, and the remaining premises are propositions or a
`LitMatch`, which has at most one inhabitant (`LitMatch.instSubsingleton`).  So
every judgment has at most one derivation (`LeTy.unique`, …, and the
`Subsingleton` instances).

No acceptance predicate is needed.  The typing rules at a location are the
rules of their own nodes (`Vc.vcLoc`, `Vc.vcLocAny`, `Atom.var (conc ℓ)`,
`Atom.loc`), and their premise is decided by `litMatchB`, so completeness is
unconditional and the checking modes are decision procedures:
`checkLe_iff`, `checkVc_iff`, `checkAtom_iff`, `checkTm_iff`, `checkDefs_iff`,
each against `Nonempty` of the judgment.

## The equation lemmas of the observation kernel

`synthVcCore` matches on the observation and, for the nodes that fix a zone,
on the subject.  Lean compiles that match with the subject as a discriminant,
so its equation lemmas are stated at `Vr.abs` and at `Vr.conc` separately,
even for `vcUnfold` and `vcSub`, which do not look at the zone.  The two
completeness cases for those nodes therefore split on the subject after taking
the induction hypotheses.
-/

namespace FCdotR

open FCdot (Sig BVar)
open Oopsla16 (Vr Ty Lb Ctx Store renameNil)

/-! ## Kernel plumbing

The helpers of `Checker`, evaluated at the data a derivation supplies. -/

section Plumbing
variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ}

/-- `leDefL` at a stored type member and a premise starting there. -/
theorem leDefL_eq {s : Sig} {Γ : Ctx σ s} {l : BVar σ .var} {a : Lb} {e : Le σ []}
    {TX T2 : Ty σ []} (hg : (G.lookup l).get? a = some (.dty TX))
    (he : LeTy G W .nil e TX T2) :
    leDefL (Γ := Γ) l a he = some ⟨.TSel (.conc l) a, T2.rename renameNil, .defL hg he⟩ := by
  simp [leDefL, witness?_eq_some hg]

/-- `leDefR` at a stored type member and a premise ending there. -/
theorem leDefR_eq {s : Sig} {Γ : Ctx σ s} {l : BVar σ .var} {a : Lb} {e : Le σ []}
    {T1 TX : Ty σ []} (hg : (G.lookup l).get? a = some (.dty TX))
    (he : LeTy G W .nil e T1 TX) :
    leDefR (Γ := Γ) l a he = some ⟨T1.rename renameNil, .TSel (.conc l) a, .defR hg he⟩ := by
  simp [leDefR, witness?_eq_some hg]

/-- `leSelL` at an observation reporting `{a : ⊥ .. U}`. -/
theorem leSelL_eq {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)} {a : Lb}
    {U : Ty σ (scopeAt p)} (hv : VcTy G W Γ p v (.TTyp a .TBot U)) :
    leSelL a hv = some ⟨.TSel p a, U.rename (renameAt p), .selL hv⟩ := by
  simp [leSelL]

/-- `leSelR` at an observation reporting `{a : S .. ⊤}`. -/
theorem leSelR_eq {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)} {a : Lb}
    {S : Ty σ (scopeAt p)} (hv : VcTy G W Γ p v (.TTyp a S .TTop)) :
    leSelR a hv = some ⟨S.rename (renameAt p), .TSel p a, .selR hv⟩ := by
  simp [leSelR]

/-- `tmApp` at a receiver of method type and an argument at its domain. -/
theorem tmApp_eq {s : Sig} {Γ : Ctx σ s} {a b : Atom σ s} {l : Lb} {S : Ty σ s}
    {U : Ty σ (s,x)} (ha : AtomTy G W Γ a (.TFun l S U)) (hb : AtomTy G W Γ b S) :
    tmApp l ha hb = some ⟨U.substVr b.root, .app ha hb⟩ := by
  simp [tmApp]

end Plumbing

/-! ## Completeness for evidence

One mutual recursion on the derivation.  Each case evaluates the kernel at the
node with the induction hypotheses and the plumbing lemmas. -/

section Evidence
variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ}

mutual

/-- **The inclusion kernel returns every inclusion derivation**, at its
endpoints. -/
theorem LeTy.complete : ∀ {s : Sig} {Γ : Ctx σ s} {e : Le σ s} {S T : Ty σ s}
    (h : LeTy G W Γ e S T), synthLeCore G W Γ e = some ⟨S, T, h⟩
  | _, _, _, _, _, .refl _ => by simp [synthLeCore]
  | _, _, _, _, _, .top _ => by simp [synthLeCore]
  | _, _, _, _, _, .bot _ => by simp [synthLeCore]
  | _, _, _, _, _, .trans _ he hf => by
      simp [synthLeCore, LeTy.complete he, LeTy.complete hf]
  | _, _, _, _, _, .dtyp he hf => by
      simp [synthLeCore, LeTy.complete he, LeTy.complete hf]
  | _, _, _, _, _, .dfun he hf => by
      simp [synthLeCore, LeTy.complete he, LeTy.complete hf]
  | _, _, _, _, _, .andI _ _ he hf => by
      simp [synthLeCore, LeTy.complete he, LeTy.complete hf]
  | _, _, _, _, _, .andE1 _ he => by simp [synthLeCore, LeTy.complete he]
  | _, _, _, _, _, .andE2 _ he => by simp [synthLeCore, LeTy.complete he]
  | _, _, _, _, _, .orI1 _ he => by simp [synthLeCore, LeTy.complete he]
  | _, _, _, _, _, .orI2 _ he => by simp [synthLeCore, LeTy.complete he]
  | _, _, _, _, _, .orE _ _ he hf => by
      simp [synthLeCore, LeTy.complete he, LeTy.complete hf]
  | _, _, _, _, _, .defL hg he => by
      simp [synthLeCore, LeTy.complete he, leDefL_eq hg he]
  | _, _, _, _, _, .defR hg he => by
      simp [synthLeCore, LeTy.complete he, leDefR_eq hg he]
  | _, _, _, _, _, .selL hv => by
      simp [synthLeCore, VcTy.complete hv, leSelL_eq hv]
  | _, _, _, _, _, .selR hv => by
      simp [synthLeCore, VcTy.complete hv, leSelR_eq hv]
  | _, _, _, _, _, .bindx _ _ he => by
      simp [synthLeCore, LeTy.complete he]
  | _, _, _, _, _, .muDrop _ => by simp [synthLeCore]

/-- **The observation kernel returns every observation derivation**, at the
type it reports. -/
theorem VcTy.complete {s : Sig} {Γ : Ctx σ s} {p : Vr σ s} {v : Vc σ (scopeAt p)}
    {T : Ty σ (scopeAt p)} (h : VcTy G W Γ p v T) :
    synthVcCore G W Γ p v = some ⟨T, h⟩ :=
  match h with
  | .vcVar (x := x) => by simp [synthVcCore]
  | .vcLoc (l := l) => by simp [synthVcCore]
  | .vcLocAny (l := l) h0 => by
      simp [synthVcCore, litMatchB_complete h0]
      exact Subsingleton.elim _ _
  | .vcPack (l := l) hv => by simp [synthVcCore, VcTy.complete hv]
  | .vcUnfold hv => by
      have ih := VcTy.complete hv
      cases p <;> simp [synthVcCore, ih]
  | .vcSub _ hv he => by
      have ih1 := VcTy.complete hv
      have ih2 := LeTy.complete he
      cases p <;> simp [synthVcCore, ih1, ih2]

end

end Evidence

/-! ## Completeness for atoms, terms and definition lists -/

section Terms
variable {σ : Sig} {G : Store σ σ} {W : StoreTy σ}

/-- **The atom kernel returns every atom derivation**, at its type. -/
theorem AtomTy.complete : ∀ {s : Sig} {Γ : Ctx σ s} {a : Atom σ s} {T : Ty σ s}
    (h : AtomTy G W Γ a T), synthAtomCore G W Γ a = some ⟨T, h⟩
  | _, _, _, _, .varAbs => by simp [synthAtomCore]
  | _, _, _, _, .varConc => by simp [synthAtomCore]
  | _, _, _, _, .varConcAny h0 => by
      simp [synthAtomCore, litMatchB_complete h0]
      exact Subsingleton.elim _ _
  | _, _, _, _, .cast ha he => by
      simp [synthAtomCore, AtomTy.complete ha, LeTy.complete he]
  | _, _, _, _, .pack ha => by simp [synthAtomCore, AtomTy.complete ha]
  | _, _, _, _, .unpack ha => by simp [synthAtomCore, AtomTy.complete ha]

mutual

/-- **The term kernel returns every term derivation**, at its type. -/
theorem TmTy.complete : ∀ {s : Sig} {Γ : Ctx σ s} {t : Tm σ s} {T : Ty σ s}
    (h : TmTy G W Γ t T), synthTmCore G W Γ t = some ⟨T, h⟩
  | _, _, _, _, .atom ha => by simp [synthTmCore, AtomTy.complete ha]
  | _, _, _, _, .new _ hd => by simp [synthTmCore, DefsTy.complete hd]
  | _, _, _, _, .app ha hb => by
      simp [synthTmCore, AtomTy.complete ha, AtomTy.complete hb, tmApp_eq ha hb]
  | _, _, _, _, .let ht hu => by
      simp [synthTmCore, TmTy.complete ht, TmTy.complete hu, Ty.strengthenW?_weaken]
  | _, _, _, _, .cast ht he => by
      simp [synthTmCore, TmTy.complete ht, LeTy.complete he]

/-- **The definition-list kernel returns every definition-list derivation**,
at its type. -/
theorem DefsTy.complete : ∀ {s : Sig} {Γ : Ctx σ s} {ds : Defs σ s} {T : Ty σ s}
    (h : DefsTy G W Γ ds T), synthDefsCore G W Γ ds = some ⟨T, h⟩
  | _, _, _, _, .dnil => by simp [synthDefsCore]
  | _, _, _, _, .dty hd => by simp [synthDefsCore, DefsTy.complete hd]
  | _, _, _, _, .dfun hd ht => by
      simp [synthDefsCore, DefsTy.complete hd, TmTy.complete ht]

end

end Terms

/-! ## Derivations are unique

Two derivations of one judgment are both what the kernel returns, so they are
equal. -/

section Unique
variable {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}

/-- An inclusion judgment has at most one derivation. -/
theorem LeTy.unique {e : Le σ s} {S T : Ty σ s} (h h' : LeTy G W Γ e S T) : h = h' := by
  have := (LeTy.complete h).symm.trans (LeTy.complete h')
  simpa using this

/-- An observation judgment has at most one derivation. -/
theorem VcTy.unique {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (h h' : VcTy G W Γ p v T) : h = h' := by
  have := (VcTy.complete h).symm.trans (VcTy.complete h')
  simpa using this

/-- An atom judgment has at most one derivation. -/
theorem AtomTy.unique {a : Atom σ s} {T : Ty σ s} (h h' : AtomTy G W Γ a T) : h = h' := by
  have := (AtomTy.complete h).symm.trans (AtomTy.complete h')
  simpa using this

/-- A term judgment has at most one derivation. -/
theorem TmTy.unique {t : Tm σ s} {T : Ty σ s} (h h' : TmTy G W Γ t T) : h = h' := by
  have := (TmTy.complete h).symm.trans (TmTy.complete h')
  simpa using this

/-- A definition-list judgment has at most one derivation. -/
theorem DefsTy.unique {ds : Defs σ s} {T : Ty σ s} (h h' : DefsTy G W Γ ds T) : h = h' := by
  have := (DefsTy.complete h).symm.trans (DefsTy.complete h')
  simpa using this

/-- Inclusion derivations form a subsingleton. -/
instance LeTy.instSubsingleton {e : Le σ s} {S T : Ty σ s} :
    Subsingleton (LeTy G W Γ e S T) := ⟨LeTy.unique⟩

/-- Observation derivations form a subsingleton. -/
instance VcTy.instSubsingleton {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)} :
    Subsingleton (VcTy G W Γ p v T) := ⟨VcTy.unique⟩

/-- Atom derivations form a subsingleton. -/
instance AtomTy.instSubsingleton {a : Atom σ s} {T : Ty σ s} :
    Subsingleton (AtomTy G W Γ a T) := ⟨AtomTy.unique⟩

/-- Term derivations form a subsingleton. -/
instance TmTy.instSubsingleton {t : Tm σ s} {T : Ty σ s} :
    Subsingleton (TmTy G W Γ t T) := ⟨TmTy.unique⟩

/-- Definition-list derivations form a subsingleton. -/
instance DefsTy.instSubsingleton {ds : Defs σ s} {T : Ty σ s} :
    Subsingleton (DefsTy G W Γ ds T) := ⟨DefsTy.unique⟩

end Unique

/-! ## Public interface

Soundness lives in `Checker`; here it is paired with completeness into
decision procedures.  The judgments are `Type`-valued, so each `iff` is stated
against `Nonempty` of the judgment. -/

section Public
variable {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}

/-- **Every inclusion derivation is synthesised**, at its endpoints. -/
theorem synthLe_complete {e : Le σ s} {S T : Ty σ s} (h : LeTy G W Γ e S T) :
    synthLe G W Γ e = some (S, T) := by
  simp [synthLe, LeTy.complete h]

/-- Synthesis decides inclusion typing. -/
theorem synthLe_iff {e : Le σ s} {S T : Ty σ s} :
    synthLe G W Γ e = some (S, T) ↔ Nonempty (LeTy G W Γ e S T) :=
  ⟨fun h => ⟨synthLe_sound h⟩, fun ⟨h⟩ => synthLe_complete h⟩

/-- Every inclusion derivation is accepted at its endpoints. -/
theorem checkLe_complete {e : Le σ s} {S T : Ty σ s} (h : LeTy G W Γ e S T) :
    checkLe G W Γ e S T = true :=
  decide_eq_true (synthLe_complete h)

/-- **The inclusion check decides inclusion typing.** -/
theorem checkLe_iff {e : Le σ s} {S T : Ty σ s} :
    checkLe G W Γ e S T = true ↔ Nonempty (LeTy G W Γ e S T) :=
  ⟨fun h => ⟨checkLe_sound h⟩, fun ⟨h⟩ => checkLe_complete h⟩

/-- A rejected inclusion has no derivation at those endpoints. -/
theorem checkLe_eq_false_iff {e : Le σ s} {S T : Ty σ s} :
    checkLe G W Γ e S T = false ↔ ¬ Nonempty (LeTy G W Γ e S T) := by
  rw [← checkLe_iff]; simp

/-- **Every observation derivation is synthesised**, at its type. -/
theorem synthVc_complete {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (h : VcTy G W Γ p v T) : synthVc G W Γ p v = some T := by
  simp [synthVc, VcTy.complete h]

/-- Synthesis decides observation typing. -/
theorem synthVc_iff {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)} :
    synthVc G W Γ p v = some T ↔ Nonempty (VcTy G W Γ p v T) :=
  ⟨fun h => ⟨synthVc_sound h⟩, fun ⟨h⟩ => synthVc_complete h⟩

/-- Every observation derivation is accepted at its type. -/
theorem checkVc_complete {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)}
    (h : VcTy G W Γ p v T) : checkVc G W Γ p v T = true :=
  decide_eq_true (synthVc_complete h)

/-- **The observation check decides observation typing.** -/
theorem checkVc_iff {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)} :
    checkVc G W Γ p v T = true ↔ Nonempty (VcTy G W Γ p v T) :=
  ⟨fun h => ⟨checkVc_sound h⟩, fun ⟨h⟩ => checkVc_complete h⟩

/-- A rejected observation has no derivation at that type. -/
theorem checkVc_eq_false_iff {p : Vr σ s} {v : Vc σ (scopeAt p)} {T : Ty σ (scopeAt p)} :
    checkVc G W Γ p v T = false ↔ ¬ Nonempty (VcTy G W Γ p v T) := by
  rw [← checkVc_iff]; simp

/-- **Every atom derivation is synthesised**, at its type. -/
theorem synthAtom_complete {a : Atom σ s} {T : Ty σ s} (h : AtomTy G W Γ a T) :
    synthAtom G W Γ a = some T := by
  simp [synthAtom, AtomTy.complete h]

/-- Synthesis decides atom typing. -/
theorem synthAtom_iff {a : Atom σ s} {T : Ty σ s} :
    synthAtom G W Γ a = some T ↔ Nonempty (AtomTy G W Γ a T) :=
  ⟨fun h => ⟨synthAtom_sound h⟩, fun ⟨h⟩ => synthAtom_complete h⟩

/-- Every atom derivation is accepted at its type. -/
theorem checkAtom_complete {a : Atom σ s} {T : Ty σ s} (h : AtomTy G W Γ a T) :
    checkAtom G W Γ a T = true :=
  decide_eq_true (synthAtom_complete h)

/-- **The atom check decides atom typing.** -/
theorem checkAtom_iff {a : Atom σ s} {T : Ty σ s} :
    checkAtom G W Γ a T = true ↔ Nonempty (AtomTy G W Γ a T) :=
  ⟨fun h => ⟨checkAtom_sound h⟩, fun ⟨h⟩ => checkAtom_complete h⟩

/-- A rejected atom has no derivation at that type. -/
theorem checkAtom_eq_false_iff {a : Atom σ s} {T : Ty σ s} :
    checkAtom G W Γ a T = false ↔ ¬ Nonempty (AtomTy G W Γ a T) := by
  rw [← checkAtom_iff]; simp

/-- **Every term derivation is synthesised**, at its type. -/
theorem synthTm_complete {t : Tm σ s} {T : Ty σ s} (h : TmTy G W Γ t T) :
    synthTm G W Γ t = some T := by
  simp [synthTm, TmTy.complete h]

/-- Synthesis decides term typing. -/
theorem synthTm_iff {t : Tm σ s} {T : Ty σ s} :
    synthTm G W Γ t = some T ↔ Nonempty (TmTy G W Γ t T) :=
  ⟨fun h => ⟨synthTm_sound h⟩, fun ⟨h⟩ => synthTm_complete h⟩

/-- Every term derivation is accepted at its type. -/
theorem checkTm_complete {t : Tm σ s} {T : Ty σ s} (h : TmTy G W Γ t T) :
    checkTm G W Γ t T = true :=
  decide_eq_true (synthTm_complete h)

/-- **The term check decides term typing.** -/
theorem checkTm_iff {t : Tm σ s} {T : Ty σ s} :
    checkTm G W Γ t T = true ↔ Nonempty (TmTy G W Γ t T) :=
  ⟨fun h => ⟨checkTm_sound h⟩, fun ⟨h⟩ => checkTm_complete h⟩

/-- A rejected term has no derivation at that type. -/
theorem checkTm_eq_false_iff {t : Tm σ s} {T : Ty σ s} :
    checkTm G W Γ t T = false ↔ ¬ Nonempty (TmTy G W Γ t T) := by
  rw [← checkTm_iff]; simp

/-- **Every definition-list derivation is synthesised**, at its type. -/
theorem synthDefs_complete {ds : Defs σ s} {T : Ty σ s} (h : DefsTy G W Γ ds T) :
    synthDefs G W Γ ds = some T := by
  simp [synthDefs, DefsTy.complete h]

/-- Synthesis decides definition-list typing. -/
theorem synthDefs_iff {ds : Defs σ s} {T : Ty σ s} :
    synthDefs G W Γ ds = some T ↔ Nonempty (DefsTy G W Γ ds T) :=
  ⟨fun h => ⟨synthDefs_sound h⟩, fun ⟨h⟩ => synthDefs_complete h⟩

/-- Every definition-list derivation is accepted at its type. -/
theorem checkDefs_complete {ds : Defs σ s} {T : Ty σ s} (h : DefsTy G W Γ ds T) :
    checkDefs G W Γ ds T = true :=
  decide_eq_true (synthDefs_complete h)

/-- **The definition-list check decides definition-list typing.** -/
theorem checkDefs_iff {ds : Defs σ s} {T : Ty σ s} :
    checkDefs G W Γ ds T = true ↔ Nonempty (DefsTy G W Γ ds T) :=
  ⟨fun h => ⟨checkDefs_sound h⟩, fun ⟨h⟩ => checkDefs_complete h⟩

/-- A rejected definition list has no derivation at that type. -/
theorem checkDefs_eq_false_iff {ds : Defs σ s} {T : Ty σ s} :
    checkDefs G W Γ ds T = false ↔ ¬ Nonempty (DefsTy G W Γ ds T) := by
  rw [← checkDefs_iff]; simp

end Public

/-! ## Determinism

Synthesis is a function, so each judgment's outputs are fixed by its inputs:
the endpoints of an inclusion, and the type of an observation, an atom, a term
or a definition list. -/

section Determinism
variable {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}

/-- An inclusion's endpoints are determined by the evidence. -/
theorem LeTy.endpoints_unique {e : Le σ s} {S T S' T' : Ty σ s}
    (h : LeTy G W Γ e S T) (h' : LeTy G W Γ e S' T') : S = S' ∧ T = T' := by
  have := (synthLe_complete h).symm.trans (synthLe_complete h')
  simpa using this

/-- An observation's type is determined by the evidence and its subject. -/
theorem VcTy.type_unique {p : Vr σ s} {v : Vc σ (scopeAt p)} {T T' : Ty σ (scopeAt p)}
    (h : VcTy G W Γ p v T) (h' : VcTy G W Γ p v T') : T = T' := by
  have := (synthVc_complete h).symm.trans (synthVc_complete h')
  simpa using this

/-- An atom's type is determined by the atom. -/
theorem AtomTy.type_unique {a : Atom σ s} {T T' : Ty σ s}
    (h : AtomTy G W Γ a T) (h' : AtomTy G W Γ a T') : T = T' := by
  have := (synthAtom_complete h).symm.trans (synthAtom_complete h')
  simpa using this

/-- A term's type is determined by the term. -/
theorem TmTy.type_unique {t : Tm σ s} {T T' : Ty σ s}
    (h : TmTy G W Γ t T) (h' : TmTy G W Γ t T') : T = T' := by
  have := (synthTm_complete h).symm.trans (synthTm_complete h')
  simpa using this

/-- A definition list's type is determined by the list. -/
theorem DefsTy.type_unique {ds : Defs σ s} {T T' : Ty σ s}
    (h : DefsTy G W Γ ds T) (h' : DefsTy G W Γ ds T') : T = T' := by
  have := (synthDefs_complete h).symm.trans (synthDefs_complete h')
  simpa using this

end Determinism

end FCdotR
