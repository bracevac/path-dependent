import LambdaPHistory.StructuralHeadReflection

/-!
Possible concrete heads for structural subtyping.

The source `Tau.MayHead` interpretation follows the unique source
classification of a path.  Structural checking is intentionally not
functional, and raw runtime equality may relate a classified path to an
opaque one.  The singleton constructors below therefore retain a *latent
classifier*: the singleton path need only be related to a path which checks
at the type supplying the possible head.  This is enough to make runtime
conversion preserve possible heads without requiring `RuntimePathValid`.

One observation-sized semantic premise remains.  If two related paths are
both classified, every possible head supplied by one classification must be
admitted by the other.  Under that premise, structural subtyping preserves
possible heads through primitive transitivity, singleton rules, abstract
bounds, and conversion.  The final theorems derive pair/function reflection
from this premise and `Store.StructTy`.
-/

namespace LambdaPHistory

/-! ## Latent-classifier possible heads -/

/-- Concrete observations made by the evaluator.  Pair observations retain
the label and the kind of the stored definition. -/
inductive Ty.StructHead : Type where
| arrow : Ty.StructHead
| pair (a : Name) (k : Kind) : Ty.StructHead
deriving DecidableEq

/-- A generalized type may admit a concrete runtime head.

For a singleton `{p}`, `q` is a latent classifier: `p` and `q` are related,
and the classification of `q` supplies the possible head.  This formulation
continues to assign heads to `{p}` when conversion makes `p` opaque. -/
inductive Tau.StructPossibleHead
    (Gamma : Ctx n) (R : Path n -> Path n -> Prop) :
    Tau n k -> Ty.StructHead -> Prop where
| top : Tau.StructPossibleHead Gamma R (Tau.ty Ty.Top) h
| arrow :
    Tau.StructPossibleHead Gamma R (Tau.ty (Ty.Fun S T)) .arrow
| pair_val {d : Tau (n + 1) .star} :
    Tau.StructPossibleHead Gamma R
      (Tau.ty (Ty.Pair S a d)) (.pair a .star)
| pair_type {d : Tau (n + 1) .iota} :
    Tau.StructPossibleHead Gamma R
      (Tau.ty (Ty.Pair S a d)) (.pair a .iota)
| single_ty :
    R p q ->
    Path.StructCheck Gamma R q (Tau.ty T) ->
    Tau.StructPossibleHead Gamma R (Tau.ty T) h ->
    Tau.StructPossibleHead Gamma R (Tau.ty (Ty.Single p)) h
| single_intv :
    R p q ->
    Path.StructCheck Gamma R q (Tau.intv L U) ->
    Tau.StructPossibleHead Gamma R (Tau.ty U) h ->
    Tau.StructPossibleHead Gamma R (Tau.ty (Ty.Single p)) h
| interval :
    Tau.StructPossibleHead Gamma R (Tau.ty U) h ->
    Tau.StructPossibleHead Gamma R (Tau.intv L U) h

/-! ## Conversion closure -/

/-- Replacing related paths in an ordinary type template preserves possible
heads.  Only an outer singleton observes the replacement; all other outer
constructors determine their concrete head independently of their fields. -/
private theorem Tau.StructPossibleHead.open_ty
    {n : Nat} {Gamma : Ctx n}
    {R : Path n -> Path n -> Prop} {p q : Path n}
    {h : Ty.StructHead}
    (hR : Path.IsEquivCongr R) (hpq : R p q)
    (T : LambdaPHistory.Ty (n + 1)) :
    Tau.StructPossibleHead Gamma R (Tau.ty (T.open p)) h ->
      Tau.StructPossibleHead Gamma R (Tau.ty (T.open q)) h := by
  cases T with
  | Top =>
      intro hh
      cases hh
      exact .top
  | Bot =>
      intro hh
      cases hh
  | Fun S U =>
      intro hh
      cases hh
      exact .arrow
  | @Pair k S a d =>
      intro hh
      cases hh with
      | pair_val => exact .pair_val
      | pair_type => exact .pair_type
  | Single r =>
      intro hh
      have hr : R (r.open p) (r.open q) := hR.open_context hpq r
      cases hh with
      | single_ty hrel hcheck hhead =>
          exact .single_ty (hR.trans (hR.symm hr) hrel) hcheck hhead
      | single_intv hrel hcheck hhead =>
          exact .single_intv (hR.trans (hR.symm hr) hrel) hcheck hhead

/-- Generalized-type replacement closure, including intervals whose upper
bound is a singleton mentioning the replaced path. -/
theorem Tau.StructPossibleHead.open
    {n : Nat} {Gamma : Ctx n}
    {R : Path n -> Path n -> Prop} {p q : Path n}
    {k : Kind} {h : Ty.StructHead}
    (hR : Path.IsEquivCongr R) (hpq : R p q)
    (d : Tau (n + 1) k) :
    Tau.StructPossibleHead Gamma R (d.open p) h ->
      Tau.StructPossibleHead Gamma R (d.open q) h := by
  cases d with
  | ty T => exact Tau.StructPossibleHead.open_ty hR hpq T
  | intv L U =>
      intro hh
      cases hh with
      | interval hU =>
          exact .interval (Tau.StructPossibleHead.open_ty hR hpq U hU)

/-- Structural conversion preserves possible concrete heads in both
directions.  The latent classifier is what makes the `replace` case valid
without transporting a complete path-checking derivation. -/
theorem Tau.StructConv.possibleHead_iff
    (hconv : Tau.StructConv R d1 d2)
    (hR : Path.IsEquivCongr R) :
    Tau.StructPossibleHead Gamma R d1 h <->
      Tau.StructPossibleHead Gamma R d2 h := by
  induction hconv with
  | refl => rfl
  | symm hconv ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | replace template hpq =>
      exact ⟨
        fun hh => Tau.StructPossibleHead.open hR hpq template hh,
        fun hh => Tau.StructPossibleHead.open hR (hR.symm hpq) template hh⟩

/-! ## The exact residual coherence property -/

/-- Head coherence for classifications of runtime-related paths.

This is strictly weaker than `RuntimePathValid`: it assumes that both paths
already have classifications and transports only one of the three concrete
observations (`arrow`, term-member pair, or type-member pair). -/
def Path.RelatedCheckHeadCoherent
    (Gamma : Ctx n) (R : Path n -> Path n -> Prop) : Prop :=
  forall {p q : Path n} {k1 k2 : Kind}
      {d1 : Tau n k1} {d2 : Tau n k2} {h : Ty.StructHead},
    R p q ->
    Path.StructCheck Gamma R p d1 ->
    Path.StructCheck Gamma R q d2 ->
    Tau.StructPossibleHead Gamma R d2 h ->
    Tau.StructPossibleHead Gamma R d1 h

private abbrev CheckPossibleMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Gamma R p d) : Prop := True

private abbrev SubPossibleMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop :=
  Path.IsEquivCongr R ->
  Path.RelatedCheckHeadCoherent Gamma R ->
  forall {h : Ty.StructHead},
    Tau.StructPossibleHead Gamma R d1 h ->
    Tau.StructPossibleHead Gamma R d2 h

private theorem Tau.StructSub.possibleHeadAux
    (hs : Tau.StructSub Gamma R d1 d2) :
    SubPossibleMotive Gamma R d1 d2 hs := by
  induction hs using Tau.StructSub.rec
      (motive_1 := CheckPossibleMotive) with
  | var hb => trivial
  | sub hp hs ihp ihs => trivial
  | promote hp hs ihp ihs => trivial
  | fst hp ih => trivial
  | sel_r hp ih => trivial
  | sel_l hp htail hne ihp ihtail => trivial
  | refl =>
      intro hR hcoh h hh
      exact hh
  | trans h1 h2 ih1 ih2 =>
      intro hR hcoh h hh
      exact ih2 hR hcoh (ih1 hR hcoh hh)
  | conv hconv =>
      intro hR hcoh h hh
      exact (hconv.possibleHead_iff hR).mp hh
  | bot =>
      intro hR hcoh h hh
      cases hh
  | top =>
      intro hR hcoh h hh
      exact .top
  | widen hp ih =>
      intro hR hcoh h hh
      cases hh with
      | single_ty hrel hq hhead =>
          exact hcoh hrel hp hq hhead
      | single_intv hrel hq hhead =>
          exact hcoh hrel hp hq (.interval hhead)
  | symm hp ih =>
      intro hR hcoh h hh
      exact .single_ty (hR.refl _) hp hh
  | sel_hi hp hbounds ihp ihbounds =>
      intro hR hcoh h hh
      cases hh with
      | single_ty hrel hq hhead =>
          have hout := hcoh hrel hp hq hhead
          cases hout with
          | interval hU => exact hU
      | single_intv hrel hq hhead =>
          have hout := hcoh hrel hp hq (.interval hhead)
          cases hout with
          | interval hU => exact hU
  | sel_lo hp hbounds ihp ihbounds =>
      intro hR hcoh h hh
      exact .single_intv (hR.refl _) hp (ihbounds hR hcoh hh)
  | «fun» hdom hcod ihdom ihcod =>
      intro hR hcoh h hh
      cases hh
      exact .arrow
  | pair hfst hsnd ihfst ihsnd =>
      intro hR hcoh h hh
      cases hh with
      | pair_val => exact .pair_val
      | pair_type => exact .pair_type
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro hR hcoh h hh
      cases hh with
      | interval hU => exact .interval (ihhi hR hcoh hU)

/-- Structural subtyping preserves latent-classifier possible heads.

The proof covers primitive transitivity directly.  `widen` and `sel_hi` are
the only rules that use related-check coherence; `conv` uses the conversion
closure above.  The nonempty premise in `sel_lo` transports the lower head to
the upper bound before packaging it as an abstract singleton head. -/
theorem Tau.StructSub.possibleHead
    (hs : Tau.StructSub Gamma R d1 d2)
    (hR : Path.IsEquivCongr R)
    (hcoh : Path.RelatedCheckHeadCoherent Gamma R)
    (hh : Tau.StructPossibleHead Gamma R d1 h) :
    Tau.StructPossibleHead Gamma R d2 h :=
  hs.possibleHeadAux hR hcoh hh

/-! ## Conditional derivation of concrete store reflection -/

/-- Store specialization of the sole semantic residual. -/
def Store.StructHeadCoherent
    (Gamma : Ctx n) (sigma : Store n) : Prop :=
  Path.RelatedCheckHeadCoherent Gamma (Path.RuntimeEq sigma)

/-- The concrete syntax represented by a possible head. -/
def Tm.HeadShape (v : Tm n) : Ty.StructHead -> Prop
| .arrow => exists A body, v = Tm.abs A body
| .pair a k => exists (y : Fin n) (delta : Def n k),
    v = @Tm.pair n k y a delta

/-- A syntax-directed structural value type supplies its concrete possible
head together with the corresponding value constructor. -/
theorem Tm.StructPrecise.possibleHead_shape
    (hp : Tm.StructPrecise Gamma R v P) :
    exists h,
      Tau.StructPossibleHead Gamma R (Tau.ty P) h /\
      Tm.HeadShape v h := by
  cases hp with
  | abs hbody hA =>
      exact ⟨.arrow, .arrow, ⟨_, _, rfl⟩⟩
  | pair hy hz =>
      exact ⟨.pair _ .star, .pair_val, ⟨_, .val _, rfl⟩⟩
  | tpair hy hT =>
      exact ⟨.pair _ .iota, .pair_type, ⟨_, .type _, rfl⟩⟩

/-- Under related-check head coherence, a structurally typed store reflects
every concrete function observation at a variable. -/
theorem Store.StructTy.functionCheckReflection_of_headCoherent
    (hstore : Store.StructTy Gamma sigma)
    (hcoh : Store.StructHeadCoherent Gamma sigma) :
    Store.FunctionCheckReflection Gamma sigma := by
  intro x S U hfun
  obtain ⟨v, X, P, hbind, hctx, hpublic, hprecise, hsub⟩ :=
    hstore.lookup_exists x
  have hX : Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (.var x) (Tau.ty X) := .var hctx
  obtain ⟨head, hPhead, hshape⟩ := hprecise.possibleHead_shape
  have hXhead := hsub.possibleHead
    (Path.RuntimeEq.isEquivCongr sigma) hcoh hPhead
  have hout := hcoh (Path.RuntimeEq.refl (p := Path.var x))
    hfun hX hXhead
  cases hout
  simp only [Tm.HeadShape] at hshape
  obtain ⟨A, body, hv⟩ := hshape
  subst v
  exact ⟨A, body, hbind⟩

/-- The same premise reflects pair label and member kind. -/
theorem Store.StructTy.pairCheckReflection_of_headCoherent
    (hstore : Store.StructTy Gamma sigma)
    (hcoh : Store.StructHeadCoherent Gamma sigma) :
    Store.PairCheckReflection Gamma sigma := by
  intro x S a k d hpair
  obtain ⟨v, X, P, hbind, hctx, hpublic, hprecise, hsub⟩ :=
    hstore.lookup_exists x
  have hX : Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (.var x) (Tau.ty X) := .var hctx
  obtain ⟨head, hPhead, hshape⟩ := hprecise.possibleHead_shape
  have hXhead := hsub.possibleHead
    (Path.RuntimeEq.isEquivCongr sigma) hcoh hPhead
  have hout := hcoh (Path.RuntimeEq.refl (p := Path.var x))
    hpair hX hXhead
  have hhead : head = .pair a k := by
    cases hout <;> rfl
  subst head
  simp only [Tm.HeadShape] at hshape
  obtain ⟨y, delta, hv⟩ := hshape
  subst v
  exact ⟨y, delta, hbind⟩

theorem Store.StructTy.headCheckReflection_of_headCoherent
    (hstore : Store.StructTy Gamma sigma)
    (hcoh : Store.StructHeadCoherent Gamma sigma) :
    Store.HeadCheckReflection Gamma sigma :=
  ⟨hstore.functionCheckReflection_of_headCoherent hcoh,
    hstore.pairCheckReflection_of_headCoherent hcoh⟩

/-!
`Store.StructHeadCoherent` is now the only unproved store-semantic fact in
this argument.  It does not transport arbitrary types or construct a missing
classification: both related paths must already check, and only a concrete
head is transported.  Proving it allocation-by-allocation requires the
usual possible-types interpretation of stored type definitions and their
nonempty bounds; the structural conversion, singleton, and transitivity
parts no longer contribute additional obligations.
-/

end LambdaPHistory
