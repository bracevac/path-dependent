import LambdaP.Repaired.StoreRefinement
import LambdaP.Repaired.Canonical
import LambdaP.Repaired.PathProgress
import LambdaP.Repaired.RuntimeConversion

/-!
Progress for paths in a publicly typed, refined store.

The syntax-directed proof for `Store.PreciseTy` uses the fact that the type
found in the context is exactly the introduction type of the stored value.
For `Store.RefinedTy`, a resolved composite path need not have the same source
type as the variable to which it reduces.  The single missing fact is recorded
below as `Path.PairTransport`: when such a path has a static pair type, the
cell it reaches really contains a pair of the same label *and member kind*.
The contract retains no hidden precise type and requires no full subtype
derivation to the static pair: reduction inspects only this outer shape.
-/

namespace LambdaP.Repaired

/-- A pair head admitted by a generalized type, retaining both pieces of
information erased by `Tau.MayHead.pair`: the label and the kind of the
dependent member. -/
inductive Tau.MayPairHead (Γ : Ctx n) : Tau n k -> Name -> Kind -> Prop where
| top : Tau.MayPairHead Γ (Tau.ty Ty.Top) a k'
| pair {k' : Kind} {d : Tau (n + 1) k'} :
    Tau.MayPairHead Γ (Tau.ty (Ty.Pair S a d)) a k'
| single_ty :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.MayPairHead Γ (Tau.ty T) a k' ->
    Tau.MayPairHead Γ (Tau.ty (Ty.Single p)) a k'
| tsel :
    Path.Ty Γ (p.sel A) (Tau.intv L U) ->
    Tau.MayPairHead Γ (Tau.ty U) a k' ->
    Tau.MayPairHead Γ (Tau.ty (Ty.TSel p A)) a k'
| interval :
    Tau.MayPairHead Γ (Tau.ty U) a k' ->
    Tau.MayPairHead Γ (Tau.intv L U) a k'

/-- Source subtyping preserves the label and member kind of every admitted
pair head. -/
theorem Tau.Sub.mayPairHead
    (hs : Tau.Sub Γ d₁ d₂)
    (hh : Tau.MayPairHead Γ d₁ a k') : Tau.MayPairHead Γ d₂ a k' := by
  induction hs with
  | refl => exact hh
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hh)
  | bot => cases hh
  | top => exact Tau.MayPairHead.top
  | widen hp =>
      cases hh with
      | single_ty hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | symm hp => exact Tau.MayPairHead.single_ty hp hh
  | sel_hi hp _ _ =>
      cases hh with
      | tsel hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | sel_lo hp _ ih =>
      exact Tau.MayPairHead.tsel hp (ih hh)
  | «fun» _ _ _ _ =>
      cases hh
  | pair_fst _ _ =>
      cases hh
      exact Tau.MayPairHead.pair
  | pair_single_member _ _ _ _ _ =>
      cases hh
      exact Tau.MayPairHead.pair
  | bounds _ _ _ _ ih _ =>
      cases hh with
      | interval hh => exact Tau.MayPairHead.interval (ih hh)

/-- A possible head for the first component of a pair-shaped type.  This is
the first projection of the `Tau.MayHead` interpretation; `Top` forgets the
observation, while singleton and interval cases follow their usual upper
bounds. -/
inductive Tau.MayFstHead (Γ : Ctx n) : Tau n k -> Ty.Head -> Prop where
| top : Tau.MayFstHead Γ (Tau.ty Ty.Top) h
| pair :
    Tau.MayHead Γ (Tau.ty S) h ->
    Tau.MayFstHead Γ (Tau.ty (Ty.Pair S a d)) h
| single_ty :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.MayFstHead Γ (Tau.ty T) h ->
    Tau.MayFstHead Γ (Tau.ty (Ty.Single p)) h
| tsel :
    Path.Ty Γ (p.sel A) (Tau.intv L U) ->
    Tau.MayFstHead Γ (Tau.ty U) h ->
    Tau.MayFstHead Γ (Tau.ty (Ty.TSel p A)) h
| interval :
    Tau.MayFstHead Γ (Tau.ty U) h ->
    Tau.MayFstHead Γ (Tau.intv L U) h

/-- Source subtyping preserves first-component head observations. -/
theorem Tau.Sub.mayFstHead
    (hs : Tau.Sub Γ d₁ d₂)
    (hh : Tau.MayFstHead Γ d₁ h) : Tau.MayFstHead Γ d₂ h := by
  induction hs with
  | refl => exact hh
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hh)
  | bot => cases hh
  | top => exact Tau.MayFstHead.top
  | widen hp =>
      cases hh with
      | single_ty hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | symm hp => exact Tau.MayFstHead.single_ty hp hh
  | sel_hi hp _ _ =>
      cases hh with
      | tsel hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | sel_lo hp _ ih =>
      exact Tau.MayFstHead.tsel hp (ih hh)
  | «fun» _ _ _ _ => cases hh
  | pair_fst hfst ihfst =>
      cases hh with
      | pair hh => exact Tau.MayFstHead.pair (hfst.mayHead hh)
  | pair_single_member _ _ _ _ _ =>
      cases hh with
      | pair hh => exact Tau.MayFstHead.pair hh
  | bounds _ _ _ _ ih _ =>
      cases hh with
      | interval hh => exact Tau.MayFstHead.interval (ih hh)

/-- In particular, subtyping between concrete pairs transports every
possible head of the first component. -/
theorem Tau.Sub.pair_fst_head
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Pair S a d₁))
      (Tau.ty (Ty.Pair U b d₂)))
    (hh : Tau.MayHead Γ (Tau.ty S) h) :
    Tau.MayHead Γ (Tau.ty U) h := by
  have hout : Tau.MayFstHead Γ (Tau.ty (Ty.Pair U b d₂)) h :=
    hs.mayFstHead (Tau.MayFstHead.pair hh)
  cases hout with
  | pair hh => exact hh

/-- Label-and-kind refinement of `MayFstHead`, used when the first component
is itself inspected as a pair. -/
inductive Tau.MayFstPairHead (Γ : Ctx n) :
    Tau n k -> Name -> Kind -> Prop where
| top : Tau.MayFstPairHead Γ (Tau.ty Ty.Top) a k'
| pair :
    Tau.MayPairHead Γ (Tau.ty S) a' k' ->
    Tau.MayFstPairHead Γ (Tau.ty (Ty.Pair S a d)) a' k'
| single_ty :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.MayFstPairHead Γ (Tau.ty T) a k' ->
    Tau.MayFstPairHead Γ (Tau.ty (Ty.Single p)) a k'
| tsel :
    Path.Ty Γ (p.sel A) (Tau.intv L U) ->
    Tau.MayFstPairHead Γ (Tau.ty U) a k' ->
    Tau.MayFstPairHead Γ (Tau.ty (Ty.TSel p A)) a k'
| interval :
    Tau.MayFstPairHead Γ (Tau.ty U) a k' ->
    Tau.MayFstPairHead Γ (Tau.intv L U) a k'

/-- Source subtyping also preserves the label and member kind observed one
first projection below a pair. -/
theorem Tau.Sub.mayFstPairHead
    (hs : Tau.Sub Γ d₁ d₂)
    (hh : Tau.MayFstPairHead Γ d₁ a k') :
    Tau.MayFstPairHead Γ d₂ a k' := by
  induction hs with
  | refl => exact hh
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hh)
  | bot => cases hh
  | top => exact Tau.MayFstPairHead.top
  | widen hp =>
      cases hh with
      | single_ty hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | symm hp => exact Tau.MayFstPairHead.single_ty hp hh
  | sel_hi hp _ _ =>
      cases hh with
      | tsel hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | sel_lo hp _ ih =>
      exact Tau.MayFstPairHead.tsel hp (ih hh)
  | «fun» _ _ _ _ => cases hh
  | pair_fst hfst ihfst =>
      cases hh with
      | pair hh => exact Tau.MayFstPairHead.pair (hfst.mayPairHead hh)
  | pair_single_member _ _ _ _ _ =>
      cases hh with
      | pair hh => exact Tau.MayFstPairHead.pair hh
  | bounds _ _ _ _ ih _ =>
      cases hh with
      | interval hh => exact Tau.MayFstPairHead.interval (ih hh)

theorem Tau.Sub.pair_fst_pairHead
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Pair S a d₁))
      (Tau.ty (Ty.Pair U b d₂)))
    (hh : Tau.MayPairHead Γ (Tau.ty S) c k') :
    Tau.MayPairHead Γ (Tau.ty U) c k' := by
  have hout :
      Tau.MayFstPairHead Γ (Tau.ty (Ty.Pair U b d₂)) c k' :=
    hs.mayFstPairHead (Tau.MayFstPairHead.pair hh)
  cases hout with
  | pair hh => exact hh

/-- Subtyping between concrete pair types preserves the kind of their
dependent component, even through primitive transitivity. -/
theorem Tau.Sub.pair_kind
    {k₁ k₂ : Kind} {d₁ : Tau (n + 1) k₁} {d₂ : Tau (n + 1) k₂}
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Pair S a d₁))
      (Tau.ty (Ty.Pair U b d₂))) : k₁ = k₂ := by
  have hh : Tau.MayPairHead Γ (Tau.ty (Ty.Pair U b d₂)) a k₁ :=
    hs.mayPairHead Tau.MayPairHead.pair
  cases hh
  rfl

/-- Canonical pair shape with the member kind retained. -/
theorem Tm.PreciseTy.pair_canonical_kind
    {n : Nat} {Γ : Ctx n} {v : Tm n} {P S : LambdaP.Repaired.Ty n}
    {a : Name} {k : Kind} {d : Tau (n + 1) k}
    (hp : Tm.PreciseTy Γ v P)
    (hs : Tau.Sub Γ (Tau.ty P) (Tau.ty (Ty.Pair S a d))) :
    ∃ (y : Fin n) (δ : Def n k), v = @Tm.pair n k y a δ := by
  cases hp with
  | abs ht hwf => exact (Tau.Sub.fun_not_pair hs).elim
  | pair hy hz =>
      have hlabel := Tau.Sub.pair_label hs
      have hkind := Tau.Sub.pair_kind hs
      subst a
      cases hkind
      exact ⟨_, .val _, rfl⟩
  | tpair hy hwf =>
      have hlabel := Tau.Sub.pair_label hs
      have hkind := Tau.Sub.pair_kind hs
      subst a
      cases hkind
      exact ⟨_, .type _, rfl⟩

/-- The pair-shape transport needed at projection and selection sites.

The `Def` witness has the same kind as the static second component.  This is
all projection and selection progress inspect. -/
def Path.PairTransport (Γ : Ctx n) (σ : Store n) : Prop :=
  ∀ {p : Path n} {x : Fin n} {S : LambdaP.Repaired.Ty n} {a : Name}
      {k : Kind} {d : Tau (n + 1) k},
    Path.reduce p σ x ->
    Path.Ty Γ p (Tau.ty (Ty.Pair S a d)) ->
    ∃ (y : Fin n) (δ : Def n k),
      Store.Binds σ x (Tm.pair y a δ)

/-- Exact stores satisfy pair transport: lookup preservation identifies the
destination context entry with the source pair type, after which precise
value inversion is immediate. -/
theorem Store.PreciseTy.pairTransport
    (hσ : Store.PreciseTy Γ σ) : Path.PairTransport Γ σ := by
  intro p x S a k d hr hp
  rcases Path.lookup_type_shape hσ hr.toLookup hp with hbind | heq
  · obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hbind
    cases hprecise with
    | pair hy hz =>
        exact ⟨_, .val _, hv⟩
    | tpair hy hwf =>
        exact ⟨_, .type _, hv⟩
  · cases heq

/-- An exact store is a refined public store whose public and precise types
coincide. -/
theorem Store.PreciseTy.toRefined (hσ : Store.PreciseTy Γ σ) :
    Store.RefinedTy Γ σ := by
  induction hσ with
  | empty => exact .empty
  | val hσ hv vv ih =>
      exact .val ih hv hv.toTy .refl vv

private def Path.RefinedLookupable
    (σ : Store n) (p : Path n) (d : Tau n k) : Prop :=
  match d with
  | .ty _ => ∃ x, Path.reduce p σ x
  | .intv _ _ => True

private theorem Path.refinedLookupable_fst
    (hpair : Path.PairTransport Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.RefinedLookupable σ p (Tau.ty (Ty.Pair S a d))) :
    Path.RefinedLookupable σ p.fst (Tau.ty S) := by
  obtain ⟨x, hx⟩ := ih
  obtain ⟨y, δ, hbind⟩ := hpair hx hp
  exact ⟨y, .fst hx hbind⟩

private theorem Path.refinedLookupable_sel_r
    (hpair : Path.PairTransport Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.RefinedLookupable σ p (Tau.ty (Ty.Pair S a d))) :
    Path.RefinedLookupable σ (p.sel a) (d.open p.fst) := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, δ, hbind⟩ := hpair hx hp
      cases δ with
      | val z => exact ⟨z, .sel_hit hx hbind⟩
  | intv L U =>
      trivial

private theorem Path.refinedLookupable_sel_l
    (hpair : Path.PairTransport Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S b d')))
    (htail : Path.Ty Γ (p.fst.sel a) d)
    (hne : a ≠ b)
    (ihp : Path.RefinedLookupable σ p (Tau.ty (Ty.Pair S b d')))
    (ihtail : Path.RefinedLookupable σ (p.fst.sel a) d) :
    Path.RefinedLookupable σ (p.sel a) d := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ihp
      obtain ⟨z, hz⟩ := ihtail
      obtain ⟨y, δ, hbind⟩ := hpair hx hp
      have hfst : Path.reduce p.fst σ y := .fst hx hbind
      have heq : Path.RuntimeEq σ p.fst (Path.var y) :=
        .coresolve hfst .var
      have hselEq :
          Path.RuntimeEq σ (p.fst.sel a) ((Path.var y).sel a) := by
        simpa [Path.open, Path.subst] using
          (Path.RuntimeEq.congr heq
            ((Path.var (0 : Fin (_ + 1))).sel a))
      have htail' : Path.reduce ((Path.var y).sel a) σ z :=
        (hselEq.reduce_iff z).mp hz
      exact ⟨z, .sel_miss hx hbind hne htail'⟩
  | intv L U =>
      trivial

private theorem Path.refinedLookupable
    (hσ : Store.RefinedTy Γ σ)
    (hpair : Path.PairTransport Γ σ)
    (hp : Path.Ty Γ p d) : Path.RefinedLookupable σ p d := by
  induction hp with
  | var hb =>
      exact ⟨_, .var⟩
  | fst hp ih =>
      exact Path.refinedLookupable_fst hpair hp (ih hσ hpair)
  | sel_r hp ih =>
      exact Path.refinedLookupable_sel_r hpair hp (ih hσ hpair)
  | sel_l hp htail hne ihp ihtail =>
      exact Path.refinedLookupable_sel_l hpair hp htail hne
        (ihp hσ hpair) (ihtail hσ hpair)

/-- General refined-store path totality, factored through the exact
pair-component transport obligation exposed by the direct induction. -/
theorem Path.reduce_progress_refined_of_pairTransport
    (hσ : Store.RefinedTy Γ σ)
    (hpair : Path.PairTransport Γ σ)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    ∃ x, Path.reduce p σ x :=
  Path.refinedLookupable hσ hpair hp

/-- The factored proof specializes back to the existing exact-store theorem,
confirming that `PairTransport` is precisely the extra public-store input. -/
theorem Path.reduce_progress_precise_via_pairTransport
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    ∃ x, Path.reduce p σ x :=
  Path.reduce_progress_refined_of_pairTransport
    hσ.toRefined hσ.pairTransport hp

/-- Refined stores discharge the complete shape/label/kind contract for a
variable path. -/
theorem Store.RefinedTy.variable_pair_transport
    {n : Nat} {Γ : Ctx n} {σ : Store n} {x : Fin n}
    {S : LambdaP.Repaired.Ty n} {a : Name} {k : Kind}
    {d : Tau (n + 1) k}
    (hσ : Store.RefinedTy Γ σ)
    (hp : Path.Ty Γ (Path.var x) (Tau.ty (Ty.Pair S a d))) :
    ∃ (y : Fin n) (δ : Def n k),
      Store.Binds σ x (@Tm.pair n k y a δ) := by
  cases hp with
  | var hbind =>
      obtain ⟨v, P, hv, hprecise, _, hsub⟩ := hσ.of_ctx_binds hbind
      obtain ⟨y, δ, rfl⟩ := hprecise.pair_canonical_kind hsub
      exact ⟨y, δ, hv⟩

/-!
### Dependent-member boundary

`mayFstHead` and `mayFstPairHead` show that ordinary source subtyping loses
no elimination information about a pair's first component.  Member
covariance is now confined to `Tau.Sub.pair_single_member`: its first
component is `{p}`, and the rule records both the scoped member comparison
and the ambient comparison after opening at `p`.  The separate
`pair_fst` rule cannot change the member.  Consequently the source relation
does not need a generic theorem transporting dependent subtyping across an
arbitrary change of first component.  At runtime, co-resolution is used only
to convert the recorded opening at `p` to the concrete stored first value.
-/

end LambdaP.Repaired
