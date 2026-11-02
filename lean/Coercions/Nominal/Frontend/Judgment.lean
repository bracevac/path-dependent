import Coercions.Nominal.Frontend.Ann
import Coercions.Nominal.Frontend.Decide
import Coercions.Nominal.Frontend.Sub

/-!
# The annotated judgment

The judgment `AHasTy` of the pDOT front end over the annotated terms `ATm`.
This is plan XI (`plan-11-pdot-frontends.md`), its part "The annotated
judgment (D-14)" and the "Reuse" row `Judgment`.  There is no model in the
Paths front end.  Substitution follows `Nominal/Source/Binding.lean` and the
rules follow `Nominal/Source/Typing.lean`.

- `AHasTy`, `ADefTy` and `ADefsTy` are one mutual block of `Type`-valued
  families.  There is one rule per former of `ATm`, `ADef` and `ADefs`, and
  one rule `asub` for subtyping.  A `let` with a written type binds at that
  type (`aletS`), and a `let` without one binds at the type of its right side
  (`aletN`).  The rule `adnew` types the opened definitions, as `ty_def_new`
  does.
- `AHasTy.erase` gives the `Nominal.Source` derivation of the erased term, and
  `ADefTy.erase` and `ADefsTy.erase` do so for definitions.  The cast of
  `adnew` crosses `ADefs.erase_substPath`.
- `ATm.size` counts the constructors of `ATm`, `ADef` and `ADefs`.  It is the
  index of the typer, and substitution keeps it (`ATm.size_subst`).

Plan XII N3 g1 adds the class definition.  `ATm.subst` substitutes in the tag
of a `let`, `ADef.subst`, `ADef.erase_subst`, `ADef.size` and
`ADef.size_subst` gain their `.cls` arms, `adnew` reads `tightC`, and the rule
`adcls` types `{class C = T}` at `{C : ⊥..T}` when `T.clsBody`.  The two erase
to `ty_def_new` and `ty_def_cls`, which replaces N2's placeholder line.

Plan XII N3 g4 (P8) adds the certificates of D-17 as predicates over the
annotated judgment, not as fields of its constructors, so `AHasTy` keeps its
indices.  `AHasTy.NomAt K tg st d` asks `NomPath` at every `apath` and `NomSub`
at every `asub`, `AHasTy.SealsAt tg st d` asks every seal at a tagged variable
and every `asub` seal-free, and `d.Nom K` and `d.SealsTagged` are the two at the
empty tags.  `CHasTy`, `CDefsTy` and `CDefTy` carry a derivation with both, and
the smart constructors build them rule by rule.

Plan XII N3 g5 adds the antitone lemmas: `NomSub`, `NomPath` and `NomAt` at
more class labels give them at fewer (`AHasTy.NomAt.mono`), so the certificate
of a run at `K ++ ks` is one at `K` (`AHasTy.Nom.of_append`).

Nothing here is metatheory.  Every recursive definition is structural, so it
reduces in the kernel and `decide +kernel` runs it.
-/

namespace NominalFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Tm Val Def Defs Rhs Ctx HasTy DefTy DefsTy Sub)

/-! ## Substitution on annotated terms -/

mutual
/-- Substitution of paths in an annotated term.  A written type of a `let` is
substituted, and the body under a binder by `σ.lift`. -/
def ATm.subst : {s₁ s₂ : Sig} → ATm s₁ → PathSubst s₁ s₂ → ATm s₂
  | _, _, .path p, σ => .path (p.subst σ)
  | _, _, .app p q, σ => .app (p.subst σ) (q.subst σ)
  | _, _, .lam S t, σ => .lam (S.subst σ) (t.subst σ.lift)
  | _, _, .new T ds, σ => .new (T.subst σ.lift) (ds.subst σ.lift)
  | _, _, .«let» g W t u, σ => .«let» (g.subst σ) (W.map (·.subst σ)) (t.subst σ) (u.subst σ.lift)
termination_by structural _ _ t => t
/-- Substitution of paths in an annotated definition. -/
def ADef.subst : {s₁ s₂ : Sig} → ADef s₁ → PathSubst s₁ s₂ → ADef s₂
  | _, _, .typ A T, σ => .typ A (T.subst σ)
  | _, _, .path a p, σ => .path a (p.subst σ)
  | _, _, .lam a S t, σ => .lam a (S.subst σ) (t.subst σ.lift)
  | _, _, .new a T ds, σ => .new a (T.subst σ.lift) (ds.subst σ.lift)
  | _, _, .cls C T, σ => .cls C (T.subst σ)
termination_by structural _ _ d => d
/-- Substitution of paths in annotated definitions. -/
def ADefs.subst : {s₁ s₂ : Sig} → ADefs s₁ → PathSubst s₁ s₂ → ADefs s₂
  | _, _, .nil, _ => .nil
  | _, _, .cons ds d, σ => .cons (ds.subst σ) (d.subst σ)
termination_by structural _ _ ds => ds
end

/-- The path `p` for the newest variable of an annotated term. -/
def ATm.substPath (t : ATm (s,x)) (p : Path s) : ATm s := t.subst (PathSubst.one p)
/-- The path `p` for the newest variable of an annotated definition. -/
def ADef.substPath (d : ADef (s,x)) (p : Path s) : ADef s := d.subst (PathSubst.one p)
/-- The path `p` for the newest variable of annotated definitions. -/
def ADefs.substPath (ds : ADefs (s,x)) (p : Path s) : ADefs s := ds.subst (PathSubst.one p)

mutual
/-- Erasure commutes with substitution. -/
theorem ATm.erase_subst : ∀ {s₁ s₂ : Sig} (t : ATm s₁) (σ : PathSubst s₁ s₂),
    (t.subst σ).erase = t.erase.subst σ
  | _, _, .path p, σ => by simp only [ATm.subst, ATm.erase, Tm.subst]
  | _, _, .app p q, σ => by simp only [ATm.subst, ATm.erase, Tm.subst]
  | _, _, .lam S t, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, Val.subst, ATm.erase_subst t σ.lift]
  | _, _, .new T ds, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, Val.subst, ADefs.erase_subst ds σ.lift]
  | _, _, .«let» g W t u, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, ATm.erase_subst t σ, ATm.erase_subst u σ.lift]
/-- Erasure of a definition commutes with substitution. -/
theorem ADef.erase_subst : ∀ {s₁ s₂ : Sig} (d : ADef s₁) (σ : PathSubst s₁ s₂),
    (d.subst σ).erase = d.erase.subst σ
  | _, _, .typ A T, σ => by simp only [ADef.subst, ADef.erase, Def.subst]
  | _, _, .path a p, σ => by simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst]
  | _, _, .lam a S t, σ => by
      simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst, Val.subst, ATm.erase_subst t σ.lift]
  | _, _, .new a T ds, σ => by
      simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst, Val.subst, ADefs.erase_subst ds σ.lift]
  | _, _, .cls C T, σ => by simp only [ADef.subst, ADef.erase, Def.subst]
/-- Erasure of definitions commutes with substitution. -/
theorem ADefs.erase_subst : ∀ {s₁ s₂ : Sig} (ds : ADefs s₁) (σ : PathSubst s₁ s₂),
    (ds.subst σ).erase = ds.erase.subst σ
  | _, _, .nil, σ => by simp only [ADefs.subst, ADefs.erase, Defs.subst]
  | _, _, .cons ds d, σ => by
      simp only [ADefs.subst, ADefs.erase, Defs.subst, ADefs.erase_subst ds σ, ADef.erase_subst d σ]
end

/-- Erasure of definitions commutes with opening at a path. -/
theorem ADefs.erase_substPath (ds : ADefs (s,x)) (p : Path s) :
    (ds.substPath p).erase = ds.erase.substPath p :=
  ADefs.erase_subst ds (PathSubst.one p)

/-- Erasure commutes with opening at a path. -/
theorem ATm.erase_substPath (t : ATm (s,x)) (p : Path s) :
    (t.substPath p).erase = t.erase.substPath p :=
  ATm.erase_subst t (PathSubst.one p)

/-! ## The judgment and its erasure -/

mutual
/-- The annotated judgment, one rule per former of `ATm` and the rule `asub`. -/
inductive AHasTy : Ctx s → ATm s → Ty s → Type where
  | apath : HasTy Γ (.path p) T → AHasTy Γ (.path p) T
  | aapp : HasTy Γ (.app p q) T → AHasTy Γ (.app p q) T
  | alam : AHasTy (Γ.cons S) t U → AHasTy Γ (.lam S t) (.all S U)
  | anew : ADefsTy (Γ.consSelf T) (.var .here) ds T → AHasTy Γ (.new T ds) (.mu T)
  | aletN : AHasTy Γ t T → AHasTy (Γ.cons T) u U.weaken → AHasTy Γ (.«let» g none t u) U
  | aletS : AHasTy Γ t W → AHasTy (Γ.cons W) u U.weaken → AHasTy Γ (.«let» g (some W) t u) U
  | asub : AHasTy Γ a T → Sub Γ T U → AHasTy Γ a U
/-- The annotated judgment of a definition at the receiver `r`. -/
inductive ADefTy : Ctx s → Path s → ADef s → Dec s → Type where
  | adtyp : ADefTy Γ r (.typ A T) (.typ A T T)
  | adpath : HasTy Γ (.path q) T → ADefTy Γ r (.path b q) (.trm b (.sngl q))
  | adlam : AHasTy Γ (.lam S t) (.all U V) → ADefTy Γ r (.lam b S t) (.trm b (.all U V))
  | adnew : (Ty.mu T).tightC = true →
      ADefsTy Γ (r.sel b) (ds.substPath (r.sel b)) (T.substPath (r.sel b)) →
      ADefTy Γ r (.new b T ds) (.trm b (.mu T))
  | adcls : T.clsBody = true → ADefTy Γ r (.cls C T) (.typ C .bot T)
/-- The annotated judgment of definitions at the receiver `r`. -/
inductive ADefsTy : Ctx s → Path s → ADefs s → Ty s → Type where
  | adone : ADefTy Γ r d D → ADefsTy Γ r (.cons .nil d) (.rcd D)
  | adcons : ADefsTy Γ r ds T → ADefTy Γ r d D → ds.erase.hasnt d.erase.label →
      ADefsTy Γ r (.cons ds d) (.and T (.rcd D))
end

mutual
/-- The `Nominal.Source` derivation of the erased term. -/
def AHasTy.erase : {s : Sig} → {Γ : Ctx s} → {a : ATm s} → {T : Ty s} →
    AHasTy Γ a T → HasTy Γ a.erase T
  | _, _, _, _, .apath d => d
  | _, _, _, _, .aapp d => d
  | _, _, _, _, .alam d => .ty_all_intro d.erase
  | _, _, _, _, .anew d => .ty_new_intro d.erase
  | _, _, _, _, .aletN d₁ d₂ => .ty_let d₁.erase d₂.erase
  | _, _, _, _, .aletS d₁ d₂ => .ty_let d₁.erase d₂.erase
  | _, _, _, _, .asub d e => .ty_sub d.erase e
termination_by structural _ _ _ _ d => d
/-- The `Nominal.Source` derivation of the erased definition. -/
def ADefTy.erase : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {d : ADef s} → {D : Dec s} →
    ADefTy Γ r d D → DefTy Γ r d.erase D
  | _, _, _, _, _, .adtyp => .ty_def_typ
  | _, _, _, _, _, .adpath d => .ty_def_path d
  | _, _, _, _, _, .adlam d => .ty_def_all d.erase
  | _, _, _, _, _, .adnew (ds := ds) (r := r) (b := b) h d =>
      .ty_def_new h (ADefs.erase_substPath ds (r.sel b) ▸ d.erase)
  | _, _, _, _, _, .adcls h => .ty_def_cls h
termination_by structural _ _ _ _ _ d => d
/-- The `Nominal.Source` derivation of the erased definitions. -/
def ADefsTy.erase : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} →
    ADefsTy Γ r ds T → DefsTy Γ r ds.erase T
  | _, _, _, _, _, .adone d => .ty_defs_one d.erase
  | _, _, _, _, _, .adcons d₁ d₂ h => .ty_defs_cons d₁.erase d₂.erase h
termination_by structural _ _ _ _ _ d => d
end

/-! ## The certificates (plan XII D-17)

The predicates over the annotated judgment, structural over the mutual family,
one clause per constructor, the tags extended at each binder by `push`.  A
lambda's binder is untagged.  A `let`'s bound term is typed at the self tag
`g.self`, which only `anew` reads, and its body under `push g.self`.  A
literal's definitions are typed under `push st`.  The certified structures
`CHasTy`, `CDefsTy`, `CDefTy` carry a derivation with both predicates. -/

section Certificates

open NominalFrontend.Core (SubAns)
open Nominal.Source (IsView)

mutual
/-- `NomAt K tg st d`: `NomPath` at every `apath` and `NomSub` at every `asub` of `d`, under the tags `tg`, with
`st` the self tag of a literal (plan XII D-17).  The tags are extended at each binder by `push`. -/
def AHasTy.NomAt (K : List Label) : {s : Sig} → Tags s → Option (Path s × Label) → {Γ : Ctx s} → {a : ATm s} →
    {T : Ty s} → AHasTy Γ a T → Prop
  | _, tg, _, _, _, _, .apath (Γ := Γ) (p := p) (T := T) _ => NomPath K tg Γ p T
  | _, _, _, _, _, _, .aapp _ => True
  | _, tg, _, _, _, _, .alam d => AHasTy.NomAt K (tg.push none) none d
  | _, tg, st, _, _, _, .anew d => ADefsTy.NomAt K (tg.push st) d
  | _, tg, _, _, _, _, .aletN (g := g) d₁ d₂ => AHasTy.NomAt K tg g.self d₁ ∧ AHasTy.NomAt K (tg.push g.self) none d₂
  | _, tg, _, _, _, _, .aletS (g := g) d₁ d₂ => AHasTy.NomAt K tg g.self d₁ ∧ AHasTy.NomAt K (tg.push g.self) none d₂
  | _, tg, st, _, _, _, .asub (Γ := Γ) (T := T) (U := U) d _ => NomSub K Γ T U ∧ AHasTy.NomAt K tg st d
termination_by structural _ _ _ _ _ _ d => d
/-- `NomAt` of a definition's derivation: the class definition and the type and path definitions ask nothing. -/
def ADefTy.NomAt (K : List Label) : {s : Sig} → Tags s → {Γ : Ctx s} → {r : Path s} → {d : ADef s} → {D : Dec s} →
    ADefTy Γ r d D → Prop
  | _, _, _, _, _, _, .adtyp => True
  | _, _, _, _, _, _, .adpath _ => True
  | _, tg, _, _, _, _, .adlam d => AHasTy.NomAt K tg none d
  | _, tg, _, _, _, _, .adnew _ d => ADefsTy.NomAt K tg d
  | _, _, _, _, _, _, .adcls _ => True
termination_by structural _ _ _ _ _ _ d => d
/-- `NomAt` of the definitions' derivation, definition by definition. -/
def ADefsTy.NomAt (K : List Label) : {s : Sig} → Tags s → {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} →
    ADefsTy Γ r ds T → Prop
  | _, tg, _, _, _, _, .adone d => ADefTy.NomAt K tg d
  | _, tg, _, _, _, _, .adcons d₁ d₂ _ => ADefsTy.NomAt K tg d₁ ∧ ADefTy.NomAt K tg d₂
termination_by structural _ _ _ _ _ _ d => d
end

mutual
/-- `SealsAt tg st d`: every seal of the erased derivations of `d` sits at a variable tagged in `tg`, and every
`asub` is seal-free (plan XII D-17). -/
def AHasTy.SealsAt : {s : Sig} → Tags s → Option (Path s × Label) → {Γ : Ctx s} → {a : ATm s} → {T : Ty s} →
    AHasTy Γ a T → Prop
  | _, tg, _, _, _, _, .apath d => HasTy.SealsAt tg d
  | _, tg, _, _, _, _, .aapp d => HasTy.SealsAt tg d
  | _, tg, _, _, _, _, .alam d => AHasTy.SealsAt (tg.push none) none d
  | _, tg, st, _, _, _, .anew d => ADefsTy.SealsAt (tg.push st) d
  | _, tg, _, _, _, _, .aletN (g := g) d₁ d₂ => AHasTy.SealsAt tg g.self d₁ ∧ AHasTy.SealsAt (tg.push g.self) none d₂
  | _, tg, _, _, _, _, .aletS (g := g) d₁ d₂ => AHasTy.SealsAt tg g.self d₁ ∧ AHasTy.SealsAt (tg.push g.self) none d₂
  | _, tg, st, _, _, _, .asub d e => AHasTy.SealsAt tg st d ∧ Sub.SealFree e
termination_by structural _ _ _ _ _ _ d => d
/-- `SealsAt` of a definition's derivation. -/
def ADefTy.SealsAt : {s : Sig} → Tags s → {Γ : Ctx s} → {r : Path s} → {d : ADef s} → {D : Dec s} →
    ADefTy Γ r d D → Prop
  | _, _, _, _, _, _, .adtyp => True
  | _, tg, _, _, _, _, .adpath d => HasTy.SealsAt tg d
  | _, tg, _, _, _, _, .adlam d => AHasTy.SealsAt tg none d
  | _, tg, _, _, _, _, .adnew _ d => ADefsTy.SealsAt tg d
  | _, _, _, _, _, _, .adcls _ => True
termination_by structural _ _ _ _ _ _ d => d
/-- `SealsAt` of the definitions' derivation, definition by definition. -/
def ADefsTy.SealsAt : {s : Sig} → Tags s → {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} →
    ADefsTy Γ r ds T → Prop
  | _, tg, _, _, _, _, .adone d => ADefTy.SealsAt tg d
  | _, tg, _, _, _, _, .adcons d₁ d₂ _ => ADefsTy.SealsAt tg d₁ ∧ ADefTy.SealsAt tg d₂
termination_by structural _ _ _ _ _ _ d => d
end

/-- `d.Nom K`: the certificate at the empty tags (plan XII Head, NOM-A). -/
def AHasTy.Nom {s : Sig} {Γ : Ctx s} {e : ATm s} {T : Ty s} (d : AHasTy Γ e T) (K : List Label) : Prop := AHasTy.NomAt K [] none d
/-- `d.SealsTagged`: `SealsAt` at the empty tags (plan XII Head). -/
def AHasTy.SealsTagged {s : Sig} {Γ : Ctx s} {e : ATm s} {T : Ty s} (d : AHasTy Γ e T) : Prop := AHasTy.SealsAt [] none d

/-- A path's annotated derivation carries its `SealsAt` to the erased derivation. -/
theorem AHasTy.sealsAt_erase {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s} :
    ∀ {p : Path s} {T : Ty s} (d : AHasTy Γ (.path p) T), AHasTy.SealsAt tg st d → HasTy.SealsAt tg d.erase
  | _, _, .apath _, h => h
  | _, _, .asub d _, h => ⟨AHasTy.sealsAt_erase d h.1, .inl h.2⟩

/-- An annotated derivation with its certificates (plan XII D-17). -/
structure CHasTy (K : List Label) (tg : Tags s) (st : Option (Path s × Label)) (Γ : Ctx s) (a : ATm s) (T : Ty s) where
  d : AHasTy Γ a T
  nom : AHasTy.NomAt K tg st d
  ss : AHasTy.SealsAt tg st d
/-- Annotated definitions with their certificates. -/
structure CDefsTy (K : List Label) (tg : Tags s) (Γ : Ctx s) (r : Path s) (ds : ADefs s) (T : Ty s) where
  d : ADefsTy Γ r ds T
  nom : ADefsTy.NomAt K tg d
  ss : ADefsTy.SealsAt tg d
/-- An annotated definition with its certificates. -/
structure CDefTy (K : List Label) (tg : Tags s) (Γ : Ctx s) (r : Path s) (e : ADef s) (D : Dec s) where
  d : ADefTy Γ r e D
  nom : ADefTy.NomAt K tg d
  ss : ADefTy.SealsAt tg d

section Smart
variable {K : List Label} {s : Sig} {tg : Tags s} {st : Option (Path s × Label)} {Γ : Ctx s}
/-- `asub` with the certificate of the subtyping answer. -/
def CHasTy.asub {a : ATm s} {T U : Ty s} (c : CHasTy K tg st Γ a T) (e : SubAns K Γ T U) : CHasTy K tg st Γ a U :=
  ⟨.asub c.d e.d, ⟨e.nom, c.nom⟩, ⟨c.ss, e.sf⟩⟩
/-- `alam`, the body under an untagged binder. -/
def CHasTy.alam {S : Ty s} {t : ATm (s,x)} {U : Ty (s,x)} (c : CHasTy K (tg.push none) none (Γ.cons S) t U) :
    CHasTy K tg st Γ (.lam S t) (.all S U) := ⟨.alam c.d, c.nom, c.ss⟩
/-- `aletN`: the bound term at the self tag `g.self`, the body under `push g.self`. -/
def CHasTy.aletN {g : LetTag s} {t : ATm s} {u : ATm (s,x)} {T U : Ty s}
    (c₁ : CHasTy K tg g.self Γ t T) (c₂ : CHasTy K (tg.push g.self) none (Γ.cons T) u U.weaken) :
    CHasTy K tg st Γ (.«let» g none t u) U := ⟨.aletN c₁.d c₂.d, ⟨c₁.nom, c₂.nom⟩, ⟨c₁.ss, c₂.ss⟩⟩
/-- `aletS`: as `aletN`, at the written type. -/
def CHasTy.aletS {g : LetTag s} {t : ATm s} {u : ATm (s,x)} {W U : Ty s}
    (c₁ : CHasTy K tg g.self Γ t W) (c₂ : CHasTy K (tg.push g.self) none (Γ.cons W) u U.weaken) :
    CHasTy K tg st Γ (.«let» g (some W) t u) U := ⟨.aletS c₁.d c₂.d, ⟨c₁.nom, c₂.nom⟩, ⟨c₁.ss, c₂.ss⟩⟩
end Smart

/-- The elaborator's `let` at no tag: a tag with no self tag keeps the tags empty. -/
def CHasTy.aletN0 {K : List Label} {s : Sig} {Γ : Ctx s} {g : LetTag s} {t : ATm s} {u : ATm (s,x)} {T U : Ty s}
    (hg : g.self = none) (c₁ : CHasTy K [] none Γ t T) (c₂ : CHasTy K [] none (Γ.cons T) u U.weaken) :
    CHasTy K [] none Γ (.«let» g none t u) U :=
  ⟨.aletN c₁.d c₂.d, by simp only [AHasTy.NomAt, hg]; exact ⟨c₁.nom, c₂.nom⟩,
    by simp only [AHasTy.SealsAt, hg]; exact ⟨c₁.ss, c₂.ss⟩⟩
/-- The elaborator's typed `let` at no tag. -/
def CHasTy.aletS0 {K : List Label} {s : Sig} {Γ : Ctx s} {g : LetTag s} {t : ATm s} {u : ATm (s,x)} {W U : Ty s}
    (hg : g.self = none) (c₁ : CHasTy K [] none Γ t W) (c₂ : CHasTy K [] none (Γ.cons W) u U.weaken) :
    CHasTy K [] none Γ (.«let» g (some W) t u) U :=
  ⟨.aletS c₁.d c₂.d, by simp only [AHasTy.NomAt, hg]; exact ⟨c₁.nom, c₂.nom⟩,
    by simp only [AHasTy.SealsAt, hg]; exact ⟨c₁.ss, c₂.ss⟩⟩
/-- The elaborator's lambda at no tag. -/
def CHasTy.alam0 {K : List Label} {s : Sig} {Γ : Ctx s} {S : Ty s} {t : ATm (s,x)} {U : Ty (s,x)}
    (c : CHasTy K [] none (Γ.cons S) t U) : CHasTy K [] none Γ (.lam S t) (.all S U) := ⟨.alam c.d, c.nom, c.ss⟩

end Certificates

/-! ## The certificates are antitone in the class labels (plan XII N3, finding G-5) -/

/-- `NomSub` is antitone in the class labels. -/
theorem NomSub.mono {K K' : List Label} (hK : ∀ C, C ∈ K → C ∈ K') {s : Sig} {Γ : Ctx s} {S T : Ty s}
    (h : NomSub K' Γ S T) : NomSub K Γ S T :=
  fun p C hT hC => h p C hT (hK C hC)
/-- `NomPath` is antitone in the class labels. -/
theorem NomPath.mono {K K' : List Label} (hK : ∀ C, C ∈ K → C ∈ K') {s : Sig} {tg : Tags s} {Γ : Ctx s}
    {q : Path s} {T : Ty s} (h : NomPath K' tg Γ q T) : NomPath K tg Γ q T :=
  fun p C hT hC => h p C hT (hK C hC)
mutual
/-- `NomAt` is antitone in the class labels: a certificate at more labels is one at fewer. -/
theorem AHasTy.NomAt.mono {K K' : List Label} (hK : ∀ C, C ∈ K → C ∈ K') : {s : Sig} → (tg : Tags s) →
    (st : Option (Path s × Label)) → {Γ : Ctx s} → {a : ATm s} → {T : Ty s} → (d : AHasTy Γ a T) →
    AHasTy.NomAt K' tg st d → AHasTy.NomAt K tg st d
  | _, _, _, _, _, _, .apath _, h => NomPath.mono hK h
  | _, _, _, _, _, _, .aapp _, h => h
  | _, tg, _, _, _, _, .alam d, h => AHasTy.NomAt.mono hK (tg.push none) none d h
  | _, tg, st, _, _, _, .anew d, h => ADefsTy.NomAt.mono hK (tg.push st) d h
  | _, tg, _, _, _, _, .aletN (g := g) d₁ d₂, h =>
      ⟨AHasTy.NomAt.mono hK tg g.self d₁ h.1, AHasTy.NomAt.mono hK (tg.push g.self) none d₂ h.2⟩
  | _, tg, _, _, _, _, .aletS (g := g) d₁ d₂, h =>
      ⟨AHasTy.NomAt.mono hK tg g.self d₁ h.1, AHasTy.NomAt.mono hK (tg.push g.self) none d₂ h.2⟩
  | _, tg, st, _, _, _, .asub d _, h => ⟨NomSub.mono hK h.1, AHasTy.NomAt.mono hK tg st d h.2⟩
/-- The same for a definition's derivation. -/
theorem ADefTy.NomAt.mono {K K' : List Label} (hK : ∀ C, C ∈ K → C ∈ K') : {s : Sig} → (tg : Tags s) →
    {Γ : Ctx s} → {r : Path s} → {e : ADef s} → {D : Dec s} → (d : ADefTy Γ r e D) →
    ADefTy.NomAt K' tg d → ADefTy.NomAt K tg d
  | _, _, _, _, _, _, .adtyp, h => h
  | _, _, _, _, _, _, .adpath _, h => h
  | _, tg, _, _, _, _, .adlam d, h => AHasTy.NomAt.mono hK tg none d h
  | _, tg, _, _, _, _, .adnew _ d, h => ADefsTy.NomAt.mono hK tg d h
  | _, _, _, _, _, _, .adcls _, h => h
/-- The same for the definitions' derivation. -/
theorem ADefsTy.NomAt.mono {K K' : List Label} (hK : ∀ C, C ∈ K → C ∈ K') : {s : Sig} → (tg : Tags s) →
    {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} → (d : ADefsTy Γ r ds T) →
    ADefsTy.NomAt K' tg d → ADefsTy.NomAt K tg d
  | _, tg, _, _, _, _, .adone d, h => ADefTy.NomAt.mono hK tg d h
  | _, tg, _, _, _, _, .adcons d₁ d₂ _, h => ⟨ADefsTy.NomAt.mono hK tg d₁ h.1, ADefTy.NomAt.mono hK tg d₂ h.2⟩
end
/-- With `compileE` running at `b.classes ++ ks`, the Head's `c.ann.Nom b.classes` follows from the stronger one. -/
theorem AHasTy.Nom.of_append {s : Sig} {Γ : Ctx s} {e : ATm s} {T : Ty s} (d : AHasTy Γ e T) (K ks : List Label)
    (h : d.Nom (K ++ ks)) : d.Nom K :=
  AHasTy.NomAt.mono (fun _ hC => List.mem_append_left ks hC) [] none d h

/-! ## The size, the typer's index -/

mutual
/-- The number of constructors of `ATm`, `ADef` and `ADefs` in a term. -/
def ATm.size : {s : Sig} → ATm s → Nat
  | _, .path _ => 1
  | _, .app _ _ => 1
  | _, .lam _ t => t.size + 1
  | _, .new _ ds => ds.size + 1
  | _, .«let» _ _ t u => t.size + u.size + 1
termination_by structural _ t => t
/-- The number of constructors in a definition. -/
def ADef.size : {s : Sig} → ADef s → Nat
  | _, .typ _ _ => 1
  | _, .path _ _ => 1
  | _, .lam _ _ t => t.size + 1
  | _, .new _ _ ds => ds.size + 1
  | _, .cls _ _ => 1
termination_by structural _ d => d
/-- The number of constructors in definitions. -/
def ADefs.size : {s : Sig} → ADefs s → Nat
  | _, .nil => 1
  | _, .cons ds d => ds.size + d.size + 1
termination_by structural _ ds => ds
end

mutual
/-- Substitution keeps the size. -/
theorem ATm.size_subst : ∀ {s₁ s₂ : Sig} (t : ATm s₁) (σ : PathSubst s₁ s₂), (t.subst σ).size = t.size
  | _, _, .path _, _ => rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .lam _ t, σ => by simp only [ATm.subst, ATm.size, ATm.size_subst t σ.lift]
  | _, _, .new _ ds, σ => by simp only [ATm.subst, ATm.size, ADefs.size_subst ds σ.lift]
  | _, _, .«let» _ _ t u, σ => by simp only [ATm.subst, ATm.size, ATm.size_subst t σ, ATm.size_subst u σ.lift]
/-- Substitution keeps the size of a definition. -/
theorem ADef.size_subst : ∀ {s₁ s₂ : Sig} (d : ADef s₁) (σ : PathSubst s₁ s₂), (d.subst σ).size = d.size
  | _, _, .typ _ _, _ => rfl
  | _, _, .path _ _, _ => rfl
  | _, _, .lam _ _ t, σ => by simp only [ADef.subst, ADef.size, ATm.size_subst t σ.lift]
  | _, _, .new _ _ ds, σ => by simp only [ADef.subst, ADef.size, ADefs.size_subst ds σ.lift]
  | _, _, .cls _ _, _ => rfl
/-- Substitution keeps the size of definitions. -/
theorem ADefs.size_subst : ∀ {s₁ s₂ : Sig} (ds : ADefs s₁) (σ : PathSubst s₁ s₂), (ds.subst σ).size = ds.size
  | _, _, .nil, _ => rfl
  | _, _, .cons ds d, σ => by simp only [ADefs.subst, ADefs.size, ADefs.size_subst ds σ, ADef.size_subst d σ]
end

/-! ## Tests

E13 through the judgment, a nested literal through `adnew`, two definitions
through `adcons` with `hasnt` decided, an ascription through `aletS` and
`asub`, the erasures, two sizes. -/

section Tests

open Nominal.Source (e13_T e13_a) in
/-- E13 through the judgment, closed. -/
def e13A : ATm [] := .new e13_T (.cons .nil (.path e13_a (.sel (.var .here) e13_a)))

open Nominal.Source (e13_T e13_a) in
/-- The derivation of E13 at its type. -/
def E13A_d : AHasTy .nil e13A (.mu e13_T) :=
  .anew (.adone (.adpath (.ty_new_elim (.ty_var rfl))))

example : e13A.erase = .val Nominal.Source.e13_lit := by decide

/-- A type label of the tests. -/
abbrev jA : Label := .typ 0
/-- A term label of the tests. -/
abbrev jb : Label := .trm 0
/-- A second term label of the tests. -/
abbrev jc : Label := .trm 1

/-- `ν(x : {b : μ(y. {A : ⊤..⊤})}) {b = ν(y : {A : ⊤..⊤}) {A = ⊤}}`. -/
def nestA : ATm [] :=
  .new (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top)))))
    (.cons .nil (.new jb (.rcd (.typ jA .top .top)) (.cons .nil (.typ jA .top))))

/-- The nested literal through `adnew`. -/
def nestA_d : AHasTy .nil nestA (.mu (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top)))))) :=
  .anew (.adone (.adnew rfl (.adone .adtyp)))

example : Nonempty (HasTy .nil nestA.erase (.mu (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top))))))) :=
  ⟨nestA_d.erase⟩

/-- `ν(x : {A : ⊤..⊤} ∧ {c : x.type}) {A = ⊤, c = x}`. -/
def twoA : ATm [] :=
  .new (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))
    (.cons (.cons .nil (.typ jA .top)) (.path jc (.var .here)))

/-- Two definitions through `adcons`, with `hasnt` decided. -/
def twoA_d : AHasTy .nil twoA (.mu (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))) :=
  .anew (.adcons (.adone .adtyp) (.adpath (.ty_var rfl)) (by decide))

example : twoA.erase = .val (.new (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))
    (.cons (.cons .nil (.typ jA .top)) (.trm jc (.defp (.var .here))))) := by decide

/-- `let y : ⊤ = λ(z : ⊤). z in y`, through `aletS` and `asub`. -/
def letA : ATm [] := .«let» .asc (some .top) (.lam .top (.path (.var .here))) (.path (.var .here))
/-- The ascription at `⊤`. -/
def letA_d : AHasTy .nil letA .top :=
  .aletS (.asub (.alam (.apath (.ty_var rfl))) .subtyp_top) (.apath (.ty_var rfl))

example : letA.erase = .lett (.val (.lam .top (.path (.var .here)))) (.path (.var .here)) := by decide
example : nestA.size = 7 := by decide
example : (ADefs.substPath (.cons .nil (.typ jA (.sel (.var .here) jA))) (.var .here : Path ([],x))).size = 3 := by decide

end Tests

end NominalFrontend
