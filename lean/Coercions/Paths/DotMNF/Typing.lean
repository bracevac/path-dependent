import Coercions.Paths.DotMNF.Syntax

namespace Paths

/-!
# DOT-MNF typing

Subtyping, path typing, term typing and definition typing, as four mutually
inductive families.  They live in `Type`, not in `Prop`: the translation of
Plan III §8 is a function on derivations and therefore needs `Type`-valued
elimination.

Path typing is pDOT's `Γ ⊢ p : T`.  It carries `T-Var`, `Rec-I`, `Rec-E` and
`And-I` at a path, and it carries the singleton rules.  The four base rules at a
variable are term typing's: `HasTy.var`, `HasTy.recI`, `HasTy.recE` and
`HasTy.andI` are constructors with the base's statements (P2 g0, decision 28).
Term typing reads path typing at two places only.  The bridge `HasTy.sngl` types
a variable at a singleton, and `HasTy.projP` projects a field out of a receiver
typed as a path.  `HasTy.toPathTy` maps every term typing at a variable to a
path typing.

P2 g0 restricts four P0 rules (P2.0).  The subtyping rules `repl` and `replSym`
are removed (decision 29), and `Ty.ReplOne` stays unused.  `HasTy.letSngl` is a derived
`let` over a field declared at a singleton (decision 23).  `DefsTy.trmLam` and
`DefsTy.trmSngl` are derived forms at a plain field, so `DefsTy.trmObj` is the
only rule that declares a stable field (decision 27).

Well-formedness appears only as a premise of the two rules that introduce a
type out of thin air: the domain annotation of a lambda and the result type
of a `let`.  Everything else is derived from those, so no side predicate on
derivations is needed.

One deviation from the surface presentation of §3.4: `{}-I` is stated as

```text
Γ, x : μ(x. T) ⊢ d : T   ⟹   Γ ⊢ ν(x. d) : μ(x. T)
```

rather than with the *opened* self type `T^x` as the binding for `x`.  With
intrinsic scoping a context entry lives in the signature *before* its own
binder, so `T^x` cannot be an entry.  The two are interderivable, since
`Rec-I` and `Rec-E` convert between `x : μ(x. T)` and `x : T^x`, and the
shape chosen here is the one that matches `FCdot.Ctx` binder for binder.

The fragment of §3.2 is enforced in the rules that need it (plan §13 items
8 and 9): `Rec-I` and `Rec-E` carry `Ty.Decl` premises for the bodies they
open and close, as does `Wf.mu`.  Intersections are *not* restricted:
`And₁`, `And₂`, `And` and `And-I` apply to arbitrary operands, since a
non-declaration operand `B` translates to the one-proposition telescope
`[⊑ ⟦B⟧]` — the self-bound proposition of `FCdot` (plan §13 item 9).  The
declaration shapes are still the only bodies a `μ` may bind, because a bound
proposition never mentions the self.  `{}-I` no longer restricts aliasing
among the definitions: the
target's alias-tolerant resolution (`FCdot.Ctx.resolve`) admits same-block
aliases and cycles (a cyclic alias resolves to `⊤`), so the self-alias
restriction that used to accompany `Defs.Distinct` here is gone.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Contexts -/

/-- A context is a list of types, newest binder first.  A binder introduced
by an object literal remembers the literal's definitions (`consSelf`); its
type is `μ(x. T)` like any other binder, and `lookup` does not distinguish
the two.  The translation of Plan III §8 does: such a binder is typed at the
literal's precise type in the target. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Ty s → Ctx (s,x)
  | consSelf : Ctx s → Defs (s,x) → Ty (s,x) → Ctx (s,x)

/-- The type of a variable, weakened into the current scope. -/
def Ctx.lookup : Ctx s → BVar s .var → Ty s
  | .cons _ T, .here => T.weaken
  | .cons Γ _, .there y => (Γ.lookup y).weaken
  | .consSelf _ _ T, .here => (Ty.mu T).weaken
  | .consSelf Γ _ _, .there y => (Γ.lookup y).weaken

/-! ## Path replacement

pDOT's `repl_typ` (`Definitions.v:895-906`), the relation pDOT's two
singleton subtyping rules carry.  `Ty.ReplOne p q T T'` says that `T'` is `T`
with exactly one occurrence of `p`, as a path prefix, rewritten to `q`.  P2 g0
removes those two rules, `repl` and `replSym` of `Sub` (decision 29), and the
relation and its decision procedure stay unused, as the place a later stage
would reinstate replacement. -/

/-- Rewrite the prefix `p` of a path to `q`.  The answer is `none` when `p`
is not a prefix.  A path has at most one prefix of a given depth, so the
answer is unique, and it is pDOT's step from `p •• bs` to `q •• bs`. -/
def Path.replPrefix (p q : Path s) : Path s → Option (Path s)
  | .var x => if Path.var x = p then some q else none
  | .sel r a =>
      if Path.sel r a = p then some q
      else (Path.replPrefix p q r).map (Path.sel · a)

/-- One occurrence of `p`, as a path prefix, rewritten to `q`.  One leaf per
path-shaped former and one congruence per former, so exactly one occurrence
changes.  The two binder cases weaken the two paths, which is what pDOT's
opening does on the nameless side. -/
inductive Ty.ReplOne : {s : Sig} → Path s → Path s → Ty s → Ty s → Prop where
  | sel : Path.replPrefix p q r = some r' → Ty.ReplOne p q (.sel r A) (.sel r' A)
  | sngl : Path.replPrefix p q r = some r' → Ty.ReplOne p q (.sngl r) (.sngl r')
  | typL : Ty.ReplOne p q S S' → Ty.ReplOne p q (.typ A S T) (.typ A S' T)
  | typR : Ty.ReplOne p q T T' → Ty.ReplOne p q (.typ A S T) (.typ A S T')
  | fld : Ty.ReplOne p q T T' → Ty.ReplOne p q (.fld a T) (.fld a T')
  | vfld : Ty.ReplOne p q T T' → Ty.ReplOne p q (.vfld a T) (.vfld a T')
  | mu : Ty.ReplOne p.weaken q.weaken T T' → Ty.ReplOne p q (.mu T) (.mu T')
  | allL : Ty.ReplOne p q S S' → Ty.ReplOne p q (.all S T) (.all S' T)
  | allR : Ty.ReplOne p.weaken q.weaken T T' → Ty.ReplOne p q (.all S T) (.all S T')
  | andL : Ty.ReplOne p q S S' → Ty.ReplOne p q (.and S T) (.and S' T)
  | andR : Ty.ReplOne p q T T' → Ty.ReplOne p q (.and S T) (.and S T')

/-- The decision procedure for `Ty.ReplOne` (`Ty.isReplOne_iff`).  It is the
recursion of the relation itself, with the two disjunctions that say which
operand of a binary former carries the occurrence. -/
def Ty.isReplOne : {s : Sig} → Path s → Path s → Ty s → Ty s → Bool
  | _, p, q, .sel r A, .sel r' A' => decide (A = A') && decide (Path.replPrefix p q r = some r')
  | _, p, q, .sngl r, .sngl r' => decide (Path.replPrefix p q r = some r')
  | _, p, q, .typ A S T, .typ A' S' T' =>
      decide (A = A') &&
        ((Ty.isReplOne p q S S' && decide (T = T')) ||
          (decide (S = S') && Ty.isReplOne p q T T'))
  | _, p, q, .fld a T, .fld a' T' => decide (a = a') && Ty.isReplOne p q T T'
  | _, p, q, .vfld a T, .vfld a' T' => decide (a = a') && Ty.isReplOne p q T T'
  | _, p, q, .mu T, .mu T' => Ty.isReplOne p.weaken q.weaken T T'
  | _, p, q, .all S T, .all S' T' =>
      (Ty.isReplOne p q S S' && decide (T = T')) ||
        (decide (S = S') && Ty.isReplOne p.weaken q.weaken T T')
  | _, p, q, .and S T, .and S' T' =>
      (Ty.isReplOne p q S S' && decide (T = T')) ||
        (decide (S = S') && Ty.isReplOne p q T T')
  | _, _, _, _, _ => false

theorem Ty.isReplOne_iff : ∀ {s : Sig} (p q : Path s) (T T' : Ty s),
    Ty.isReplOne p q T T' = true ↔ Ty.ReplOne p q T T'
  | _, _, _, .top, T' => by
      cases T' <;> exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | _, _, _, .bot, T' => by
      cases T' <;> exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | _, p, q, .sel r A, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i r' A'
      simp only [Ty.isReplOne, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, h⟩
        exact .sel h
      · intro h
        cases h
        exact ⟨rfl, by assumption⟩
  | _, p, q, .sngl r, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i r'
      simp only [Ty.isReplOne, decide_eq_true_eq]
      constructor
      · intro h
        exact .sngl h
      · intro h
        cases h
        assumption
  | _, p, q, .typ A S T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i A' S' T'
      simp only [Ty.isReplOne, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isReplOne_iff p q S S', Ty.isReplOne_iff p q T T']
      constructor
      · rintro ⟨rfl, (⟨h, rfl⟩ | ⟨rfl, h⟩)⟩
        · exact .typL h
        · exact .typR h
      · intro h
        cases h with
        | typL h => exact ⟨rfl, .inl ⟨h, rfl⟩⟩
        | typR h => exact ⟨rfl, .inr ⟨rfl, h⟩⟩
  | _, p, q, .fld a T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i a' T'
      simp only [Ty.isReplOne, Bool.and_eq_true, decide_eq_true_eq, Ty.isReplOne_iff p q T T']
      constructor
      · rintro ⟨rfl, h⟩
        exact .fld h
      · intro h
        cases h with
        | fld h => exact ⟨rfl, h⟩
  | _, p, q, .vfld a T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i a' T'
      simp only [Ty.isReplOne, Bool.and_eq_true, decide_eq_true_eq, Ty.isReplOne_iff p q T T']
      constructor
      · rintro ⟨rfl, h⟩
        exact .vfld h
      · intro h
        cases h with
        | vfld h => exact ⟨rfl, h⟩
  | _, p, q, .mu T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i T'
      simp only [Ty.isReplOne, Ty.isReplOne_iff p.weaken q.weaken T T']
      constructor
      · intro h
        exact .mu h
      · intro h
        cases h with
        | mu h => exact h
  | _, p, q, .all S T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i S' T'
      simp only [Ty.isReplOne, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isReplOne_iff p q S S', Ty.isReplOne_iff p.weaken q.weaken T T']
      constructor
      · rintro (⟨h, rfl⟩ | ⟨rfl, h⟩)
        · exact .allL h
        · exact .allR h
      · intro h
        cases h with
        | allL h => exact .inl ⟨h, rfl⟩
        | allR h => exact .inr ⟨rfl, h⟩
  | _, p, q, .and S T, T0 => by
      cases T0 <;> first
        | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
        | skip
      rename_i S' T'
      simp only [Ty.isReplOne, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        Ty.isReplOne_iff p q S S', Ty.isReplOne_iff p q T T']
      constructor
      · rintro (⟨h, rfl⟩ | ⟨rfl, h⟩)
        · exact .andL h
        · exact .andR h
      · intro h
        cases h with
        | andL h => exact .inl ⟨h, rfl⟩
        | andR h => exact .inr ⟨rfl, h⟩

instance Ty.ReplOne.instDecidable {s : Sig} (p q : Path s) (T T' : Ty s) :
    Decidable (Ty.ReplOne p q T T') :=
  decidable_of_iff _ (Ty.isReplOne_iff p q T T')

/-! ## The judgments -/

mutual

/-- Subtyping.  No `Rec` rule: recursion is `Rec-I`/`Rec-E` on paths. -/
inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | top : Sub Γ T .top
  | bot : Sub Γ .bot T
  | refl : Sub Γ T T
  | trans : Sub Γ S M → Sub Γ M T → Sub Γ S T
  | and1 : Sub Γ (.and S T) S
  | and2 : Sub Γ (.and S T) T
  | and : Sub Γ S T → Sub Γ S U → Sub Γ S (.and T U)
  | fld : Sub Γ T U → Sub Γ (.fld a T) (.fld a U)
  /-- `Fld`, for stable fields. -/
  | vfld : Sub Γ T U → Sub Γ (.vfld a T) (.vfld a U)
  /-- A stable member is a member.  There is no converse. -/
  | vfldToFld : Sub Γ (.vfld a T) (.fld a T)
  | typ : Sub Γ S2 S1 → Sub Γ T1 T2 → Sub Γ (.typ A S1 T1) (.typ A S2 T2)
  /-- `Sel-<:`, pDOT `subtyp_sel1` (`Definitions.v:908-919`), receiver
  widened to a path. -/
  | selUpper : PathTy Γ p (.typ A S T) → Sub Γ (.sel p A) T
  /-- `<:-Sel`, pDOT `subtyp_sel2`. -/
  | selLower : PathTy Γ p (.typ A S T) → Sub Γ S (.sel p A)
  | all : Sub Γ S2 S1 → Sub (Γ.cons S2) T1 T2 → Sub Γ (.all S1 T1) (.all S2 T2)
  /-- `Typ-Abs`, the abstract view of a declaration (`SubDecl` below).  It is
  gDOT's `D-Typ-Abs` (`gdot-fulltext.txt:706-708`) moved out of definition
  typing and into subtyping between `μ` types.  The move is what pays for the
  self being in scope: the rule is used through `PathTy.sub` or `HasTy.sub`,
  at a point where the self is about to be instantiated at a path. -/
  | mu : SubDecl Γ D D' → Ty.Decl D → Ty.Decl D' → Sub Γ (.mu D) (.mu D')
  -- P2 g0 (decision 29): `repl` and `replSym` are removed.

/-- Path typing.  pDOT's `Γ ⊢ p : T` for the fragment plan V §4 keeps. -/
inductive PathTy : {s : Sig} → Ctx s → Path s → Ty s → Type where
  | var : PathTy Γ (.var x) (Γ.lookup x)
  /-- `Fld-E`, pDOT `ty_new_elim` (`Definitions.v:688-691`), restricted to
  stable fields.  The premise is Fact 2's answer and it replaces pDOT's
  `tight_bounds`. -/
  | sel : PathTy Γ p (.vfld a T) → PathTy Γ (.sel p a) T
  /-- `Rec-I` at a path, pDOT `ty_rec_intro` (`Definitions.v:735-746`). -/
  | recI : PathTy Γ p (T.substPath p) → Ty.Decl T → PathTy Γ p (.mu T)
  /-- `Rec-E` at a path, pDOT `ty_rec_elim`. -/
  | recE : PathTy Γ p (.mu T) → Ty.Decl T → PathTy Γ p (T.substPath p)
  /-- `And-I` at a path. -/
  | andI : PathTy Γ p T → PathTy Γ p U → PathTy Γ p (.and T U)
  | sub : PathTy Γ p T → Sub Γ T U → PathTy Γ p U
  /-- `P-Sngl-Refl`, gDOT Fig. 6 (`gdot-fulltext.txt:687`). -/
  | snglRefl : PathTy Γ p T → PathTy Γ p (.sngl p)
  /-- `Sngl-Trans`, pDOT `ty_sngl` (`Definitions.v:718-721`). -/
  | snglTrans : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ p T
  /-- `P-Sngl-Sym`, gDOT (`gdot-fulltext.txt:691,730`).  Stated, not derived:
  the four-rule derivation gDOT gives needs `Sngl-<:-Self`, which this line
  does not have. -/
  | snglSym : PathTy Γ p (.sngl q) → PathTy Γ q T → PathTy Γ q (.sngl p)
  /-- `P-Sngl-Inv`, gDOT (`gdot-fulltext.txt:689`).  The aliased path is well
  typed. -/
  | snglInv : PathTy Γ p (.sngl q) → PathTy Γ q .top
  /-- `ty_path_elim` (`Definitions.v:726-730`): an alias is inherited by a
  stable field. -/
  | snglSel :
      PathTy Γ p (.sngl q) → PathTy Γ p (.vfld a T) →
      PathTy Γ (.sel p a) (.sngl (.sel q a))

/-- Term typing. -/
inductive HasTy : {s : Sig} → Ctx s → Tm s → Ty s → Type where
  /-- `T-Var`, the base's rule (decision 28). -/
  | var : HasTy Γ (.path x) (Γ.lookup x)
  /-- `Rec-I`, the base's rule. -/
  | recI : HasTy Γ (.path x) (T.substVar x) → Ty.Decl T → HasTy Γ (.path x) (.mu T)
  /-- `Rec-E`, the base's rule. -/
  | recE : HasTy Γ (.path x) (.mu T) → Ty.Decl T → HasTy Γ (.path x) (T.substVar x)
  /-- `And-I`, the base's rule. -/
  | andI : HasTy Γ (.path x) T → HasTy Γ (.path x) U → HasTy Γ (.path x) (.and T U)
  /-- The bridge from path typing, at a singleton only (decision 28). -/
  | sngl : PathTy Γ (.var x) (.sngl q) → HasTy Γ (.path x) (.sngl q)
  /-- `All-I`. -/
  | lam : HasTy (Γ.cons S) t T → Ty.Wf S → HasTy Γ (.val (.lam S t)) (.all S T)
  /-- `All-E`. -/
  | app :
      HasTy Γ (.path x) (.all S T) →
      HasTy Γ (.path y) S →
      HasTy Γ (.app x y) (T.substVar y)
  /-- `{}-I`.  The self binder remembers the definitions. -/
  | obj :
      DefsTy (Γ.consSelf d T) d T →
      Defs.Distinct d →
      HasTy Γ (.val (.obj d)) (.mu T)
  /-- `{}-E`. -/
  | proj : HasTy Γ (.path x) (.fld a T) → HasTy Γ (.proj x a) T
  /-- `{}-E` with the receiver typed as a path (decision 28). -/
  | projP : PathTy Γ (.var x) (.fld a T) → HasTy Γ (.proj x a) T
  | «let» :
      HasTy Γ t T →
      HasTy (Γ.cons T) u U.weaken →
      Ty.Wf U →
      HasTy Γ (.let t u) U
  -- P2 g0 (decision 23): `letSngl` is a derived form below.
  | sub : HasTy Γ t T → Sub Γ T U → HasTy Γ t U

/-- Definition typing. -/
inductive DefsTy : {s : Sig} → Ctx s → Defs s → Ty s → Type where
  /-- Exact, as in the base: a type definition declares equal bounds. -/
  | typ : DefsTy Γ (.typ A T) (.typ A T T)
  | trm : HasTy Γ t T → DefsTy Γ (.trm a t) (.fld a T)
  /-- A field whose body is an object literal is stable, and its declared
  type is the literal's own type.  pDOT's `ty_def_new`
  (`Definitions.v:793-799`) minus `tight T`.  The conclusion is exact: if a
  value field could be declared at a subsumed type, the block built from the
  stored value and the block built from the declaration type would disagree. -/
  | trmObj :
      DefsTy (Γ.consSelf d' T') d' T' → Defs.Distinct d' →
      DefsTy Γ (.trm a (.val (.obj d'))) (.vfld a (.mu T'))
  -- P2 g0 (decision 27): `trmLam` and `trmSngl` are derived forms below.
  | and : DefsTy Γ d1 T1 → DefsTy Γ d2 T2 → DefsTy Γ (.and d1 d2) (.and T1 T2)

/-- The self-free steps a declared bound may take.  The source image of
`FCdot.Side`.  `refl`, `bot` and `top` may mention the self, `closed` may
not, so every side of a template stays closed. -/
inductive SelfFree : {s : Sig} → Ctx s → Ty (s,x) → Ty (s,x) → Type where
  | refl : SelfFree Γ X X
  | bot : SelfFree Γ .bot X
  | top : SelfFree Γ X .top
  | closed : Sub Γ X Y → SelfFree Γ X.weaken Y.weaken

/-- The abstract view of a declaration body, proposition by proposition.
Each rule reads one member off the left body through a declaration reader and
widens it by self-free steps. -/
inductive SubDecl : {s : Sig} → Ctx s → Ty (s,x) → Ty (s,x) → Type where
  | top : SubDecl Γ D .top
  | typ :
      D.lookupTypDecl A = some (S1, T1) → SelfFree Γ S2 S1 → SelfFree Γ T1 T2 →
      SubDecl Γ D (.typ A S2 T2)
  | fld :
      D.lookupFldDecl a = some T1 → SelfFree Γ T1 T2 →
      SubDecl Γ D (.fld a T2)
  | vfld :
      D.lookupVfldDecl a = some T1 → SelfFree Γ T1 T2 →
      SubDecl Γ D (.vfld a T2)
  | vfldToFld :
      D.lookupVfldDecl a = some T1 → SelfFree Γ T1 T2 →
      SubDecl Γ D (.fld a T2)
  | and : SubDecl Γ D D1 → SubDecl Γ D D2 → SubDecl Γ D (.and D1 D2)

end

/-! ## Reflection, and the derived forms of P2 g0 -/

/-- A term derivation at a path term is a path derivation. -/
def HasTy.toPathTy : {s : Sig} → {Γ : Ctx s} → {x : BVar s .var} → {T : Ty s} →
    HasTy Γ (.path x) T → PathTy Γ (.var x) T
  | _, _, _, _, .var => .var
  | _, _, _, _, .recI d hd => .recI (by rw [Ty.substPath_var]; exact d.toPathTy) hd
  | _, _, _, _, .recE d hd => by rw [← Ty.substPath_var]; exact .recE d.toPathTy hd
  | _, _, _, _, .andI d e => .andI d.toPathTy e.toPathTy
  | _, _, _, _, .sngl d => d
  | _, _, _, _, .sub d h => .sub d.toPathTy h

/-- `let y = x.a in u` over a field declared at a singleton (decision 23),
derived from `HasTy.let` and `HasTy.projP`. -/
def HasTy.letSngl {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} {q : Path s}
    {u : Tm (s,x)} {U : Ty s} (hx : PathTy Γ (.var x) (.fld a (.sngl q)))
    (hu : HasTy (Γ.cons (.sngl q)) u U.weaken) (hU : Ty.Wf U) :
    HasTy Γ (.let (.proj x a) u) U :=
  .let (.projP hx) hu hU

/-- Decision 23's premise, a field declared stable, is an instance. -/
def HasTy.letSnglVal {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} {q : Path s}
    {u : Tm (s,x)} {U : Ty s} (hx : PathTy Γ (.var x) (.vfld a (.sngl q)))
    (hu : HasTy (Γ.cons (.sngl q)) u U.weaken) (hU : Ty.Wf U) :
    HasTy Γ (.let (.proj x a) u) U :=
  HasTy.letSngl (.sub hx .vfldToFld) hu hU

/-- `D-Path-Sngl`, derived at a plain field (decision 27). -/
def DefsTy.trmSngl {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty s} {a : Label}
    (h : PathTy Γ (.var y) T) :
    DefsTy Γ (.trm a (.path y)) (.fld a (.sngl (.var y))) :=
  .trm (.sngl (.snglRefl h))

/-- A lambda field, derived at a plain field (decision 27). -/
def DefsTy.trmLam {s : Sig} {Γ : Ctx s} {S T : Ty s} {t : Tm (s,x)} {a : Label}
    (h : HasTy Γ (.val (.lam S t)) T) :
    DefsTy Γ (.trm a (.val (.lam S t))) (.fld a T) :=
  .trm h

/-! ## Exactness of a literal's declared type

The two theorems that replace pDOT's `tight_bounds`.  The first says that
`{}-I` never introduces an abstract type member, the second reads the shapes a
stable field can have off the declaration type.  After P2 g0 `trmObj` is the
only rule that declares a stable field, and `DefsTy.vfld_exact_obj` states the
one shape left.

`DefsTy` is a member of a mutual block, so the `induction` tactic is not
available on it and every proof below recurses through the equation compiler
on the derivation itself. -/

/-- Read a successful `Option.or` as one of its two sides.  Every reader of a
declaration and of a definition list descends an intersection this way, so
this is the only case split the proofs below need. -/
theorem Option.or_eq_some_cases {α : Type _} {x y : Option α} {z : α}
    (h : x.or y = some z) : x = some z ∨ (x = none ∧ y = some z) := by
  cases x with
  | some _ => exact .inl h
  | none => exact .inr ⟨rfl, h⟩

/-- A definition list of one term member answers about it.  It is what the
stable-field rule `trmObj` needs to turn a declared label into a definition. -/
theorem Defs.lookupTrm_trm_self {s : Sig} (a : Label) (t : Tm s) :
    (Defs.trm a t).lookupTrm a = some t := by
  rw [Defs.lookupTrm, if_pos rfl]

/-- The declared type of a literal is exact on type members: `{}-I` never
introduces an abstract member, so no derivation inside a literal uses an
abstract bound of its own self. -/
theorem DefsTy.typ_exact : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → ∀ {A : Label} {S U : Ty s}, T.lookupTypDecl A = some (S, U) → S = U
  | _, _, _, _, .typ, _, _, _, hA => by
      rw [Ty.lookupTypDecl] at hA
      split at hA
      · simp only [Option.some.injEq, Prod.mk.injEq] at hA
        exact hA.1.symm.trans hA.2
      · exact absurd hA (by simp)
  | _, _, _, _, .trm _, _, _, _, hA => by simp [Ty.lookupTypDecl] at hA
  | _, _, _, _, .trmObj _ _, _, _, _, hA => by simp [Ty.lookupTypDecl] at hA
  | _, _, _, _, .and h1 h2, _, _, _, hA => by
      rw [Ty.lookupTypDecl] at hA
      rcases Option.or_eq_some_cases hA with h | ⟨_, h⟩
      · exact h2.typ_exact h
      · exact h1.typ_exact h

/-- A stable member of the declaration type is defined at that label. -/
theorem DefsTy.mem_labels_of_lookupVfldDecl : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → ∀ {a : Label} {U : Ty s}, T.lookupVfldDecl a = some U → a ∈ d.labels
  | _, _, _, _, .typ, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trm _, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trmObj _ _, _, _, hU => by
      rw [Ty.lookupVfldDecl] at hU
      split at hU
      · subst_vars; simp [Defs.labels]
      · exact absurd hU (by simp)
  | _, _, _, _, .and h1 h2, _, _, hU => by
      rw [Ty.lookupVfldDecl] at hU
      rcases Option.or_eq_some_cases hU with h | ⟨_, h⟩
      · exact List.mem_append_right _ (h2.mem_labels_of_lookupVfldDecl h)
      · exact List.mem_append_left _ (h1.mem_labels_of_lookupVfldDecl h)

/-- A label the definitions do not define has no term member. -/
theorem Defs.lookupTrm_eq_none : ∀ {s : Sig} {d : Defs s} {a : Label},
    a ∉ d.labels → d.lookupTrm a = none
  | _, .typ _ _, _, _ => rfl
  | _, .trm _ _, _, ha => by
      rw [Defs.lookupTrm]
      split
      · subst_vars; exact absurd (by simp [Defs.labels]) ha
      · rfl
  | _, .and _ _, _, ha => by
      simp only [Defs.labels, List.mem_append, not_or] at ha
      rw [Defs.lookupTrm, Defs.lookupTrm_eq_none ha.2, Defs.lookupTrm_eq_none ha.1]
      rfl

/-- Exactness of a stable field: the three shapes a `∋ᵛ` field could have at
P0, read off the declaration type.  The statement is P0's.  After P2 g0 only
`trmObj` declares a stable field (decision 27), so the second and third
disjuncts are no longer inhabited, and `DefsTy.vfld_exact_obj` states the first
alone.

The `Defs.Distinct d` premise is not in P0.8, and it is not optional.  Without
it the right conjunct of the definitions may define the label with a
computation body while the left conjunct declares it stable, and then the
reader of the type and the reader of the definitions answer about two
different definitions.  The counterexample to the unpremised statement is
`p0-g3-counterexample.lean`.  Every use of this theorem has the premise:
`HasTy.obj` carries `Defs.Distinct` beside the `DefsTy` derivation. -/
theorem DefsTy.vfld_exact : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Defs.Distinct d → ∀ {a : Label} {U : Ty s},
    T.lookupVfldDecl a = some U →
    (∃ d' T', U = .mu T' ∧ d.lookupTrm a = some (.val (.obj d')) ∧
        Nonempty (DefsTy (Γ.consSelf d' T') d' T'))
    ∨ (∃ y, U = .sngl (.var y)) ∨ (∃ S t, d.lookupTrm a = some (.val (.lam S t)))
  | _, _, _, _, .typ, _, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trm _, _, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trmObj hd' _, _, _, _, hU => by
      rw [Ty.lookupVfldDecl] at hU
      split at hU
      · subst_vars
        simp only [Option.some.injEq] at hU
        exact .inl ⟨_, _, hU.symm, Defs.lookupTrm_trm_self _ _, ⟨hd'⟩⟩
      · exact absurd hU (by simp)
  | _, _, _, _, .and h1 h2, hd, a, _, hU => by
      cases hd with
      | and hd1 hd2 hdis =>
      rw [Ty.lookupVfldDecl] at hU
      rcases Option.or_eq_some_cases hU with h | ⟨_, h⟩
      · rcases h2.vfld_exact hd2 h with
          ⟨d', T', rfl, he, hn⟩ | ⟨y, rfl⟩ | ⟨S0, t0, he⟩
        · exact .inl ⟨d', T', rfl, by rw [Defs.lookupTrm, he]; rfl, hn⟩
        · exact .inr (.inl ⟨y, rfl⟩)
        · exact .inr (.inr ⟨S0, t0, by rw [Defs.lookupTrm, he]; rfl⟩)
      · have hnone : _ = none :=
          Defs.lookupTrm_eq_none (hdis a (h1.mem_labels_of_lookupVfldDecl h))
        rcases h1.vfld_exact hd1 h with
          ⟨d', T', rfl, he, hn⟩ | ⟨y, rfl⟩ | ⟨S0, t0, he⟩
        · exact .inl ⟨d', T', rfl, by rw [Defs.lookupTrm, hnone, Option.none_or, he], hn⟩
        · exact .inr (.inl ⟨y, rfl⟩)
        · exact .inr (.inr ⟨S0, t0, by rw [Defs.lookupTrm, hnone, Option.none_or, he]⟩)

/-- T10 in its sharp form (P2 g0): a stable field of a literal holds an object
literal, since `trmObj` is the only rule that declares one. -/
theorem DefsTy.vfld_exact_obj : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Defs.Distinct d → ∀ {a : Label} {U : Ty s},
    T.lookupVfldDecl a = some U →
    ∃ d' T', U = .mu T' ∧ d.lookupTrm a = some (.val (.obj d')) ∧
        Nonempty (DefsTy (Γ.consSelf d' T') d' T')
  | _, _, _, _, .typ, _, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trm _, _, _, _, hU => by simp [Ty.lookupVfldDecl] at hU
  | _, _, _, _, .trmObj hd' _, _, _, _, hU => by
      rw [Ty.lookupVfldDecl] at hU
      split at hU
      · subst_vars
        simp only [Option.some.injEq] at hU
        exact ⟨_, _, hU.symm, Defs.lookupTrm_trm_self _ _, ⟨hd'⟩⟩
      · exact absurd hU (by simp)
  | _, _, _, _, .and h1 h2, hd, a, _, hU => by
      cases hd with
      | and hd1 hd2 hdis =>
      rw [Ty.lookupVfldDecl] at hU
      rcases Option.or_eq_some_cases hU with h | ⟨_, h⟩
      · obtain ⟨d', T', rfl, he, hn⟩ := h2.vfld_exact_obj hd2 h
        exact ⟨d', T', rfl, by rw [Defs.lookupTrm, he]; rfl, hn⟩
      · have hnone : _ = none :=
          Defs.lookupTrm_eq_none (hdis a (h1.mem_labels_of_lookupVfldDecl h))
        obtain ⟨d', T', rfl, he, hn⟩ := h1.vfld_exact_obj hd1 h
        exact ⟨d', T', rfl, by rw [Defs.lookupTrm, hnone, Option.none_or, he], hn⟩

end DotMNF

end Paths
