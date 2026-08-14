import LambdaP.Progress
import LambdaP.StructuralApplicationBoundary
import LambdaP.StructuralRefinedProgress

/-!
Progress for the fully structural machine invariant.

The proof is factored through two observation-sized store properties.  Pair
reflection is exactly the property already isolated by structural path
progress: a variable checked at a concrete pair type names a stored pair of
the same label and member kind.  Function reflection says only that a stored
value at a variable checked at a concrete function type is an abstraction.
No typing information about the abstraction is repeated here; preservation
uses the separate `Store.StructAppCompatibility` contract.
-/

namespace LambdaP

/-! ## Structural path totality from pair reflection -/

/-- Lookupability is required only for ordinary types.  Type-member paths
are checked at intervals but never occur as machine terms. -/
private def Path.StructLookupable
    (sigma : Store n) (p : Path n) (d : Tau n k) : Prop :=
  match d with
  | .ty _ => exists x, Path.reduce p sigma x
  | .intv _ _ => True

private abbrev Tau.StructSubLookupableMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop := True

private theorem Path.structLookupable
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {p : Path n} {d : Tau n k}
    (hreflect : Store.PairCheckReflection Gamma sigma)
    (hp : Path.StructCheck Gamma R p d) :
    R = Path.RuntimeEq sigma -> Path.StructLookupable sigma p d := by
  induction hp using Path.StructCheck.rec
      (motive_2 := Tau.StructSubLookupableMotive) with
  | var hb => intro hR; exact ⟨_, .var⟩
  | @sub n Gamma R p k d1 d2 hp hs ih ihs =>
      intro hR
      cases d1 <;> cases d2
      · exact ih hreflect hR
      · trivial
  | promote hp hs ih ihs => intro hR; exact ih hreflect hR
  | @fst n Gamma R p S a k d hp ih =>
      intro hR
      obtain ⟨x, hx⟩ := ih hreflect hR
      have hp' : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
          (Tau.ty (Ty.Pair S a d)) := by simpa only [hR] using hp
      obtain ⟨y, delta, hbind⟩ := hreflect (hp'.reduce_to_var hx)
      exact ⟨y, .fst hx hbind⟩
  | @sel_r n Gamma R p S a k d hp ih =>
      intro hR
      cases d with
      | ty D =>
          obtain ⟨x, hx⟩ := ih hreflect hR
          have hp' : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
              (Tau.ty (Ty.Pair S a (Tau.ty D))) := by
            simpa only [hR] using hp
          obtain ⟨y, delta, hbind⟩ := hreflect (hp'.reduce_to_var hx)
          cases delta with
          | val z => exact ⟨z, .sel_hit hx hbind⟩
      | intv L U => trivial
  | @sel_l n Gamma R p S b k' d' a k d hp htail hne ihp ihtail =>
      intro hR
      cases d with
      | ty D =>
          obtain ⟨x, hx⟩ := ihp hreflect hR
          obtain ⟨z, hz⟩ := ihtail hreflect hR
          have hp' : Path.StructCheck Gamma (Path.RuntimeEq sigma) p
              (Tau.ty (Ty.Pair S b d')) := by simpa only [hR] using hp
          obtain ⟨y, delta, hbind⟩ := hreflect (hp'.reduce_to_var hx)
          have hfst : Path.reduce p.fst sigma y := .fst hx hbind
          have heq : Path.RuntimeEq sigma p.fst (Path.var y) :=
            .coresolve hfst .var
          have hselEq :
              Path.RuntimeEq sigma (p.fst.sel a) ((Path.var y).sel a) := by
            simpa [Path.open, Path.subst] using
              (Path.RuntimeEq.congr heq
                ((Path.var (0 : Fin (_ + 1))).sel a))
          have htail' : Path.reduce ((Path.var y).sel a) sigma z :=
            (hselEq.reduce_iff z).mp hz
          exact ⟨z, .sel_miss hx hbind hne htail'⟩
      | intv L U => trivial
  | refl => trivial
  | trans h1 h2 ih1 ih2 => trivial
  | conv hconv => trivial
  | bot => trivial
  | top => trivial
  | widen hp ih => trivial
  | symm hp ih => trivial
  | sel_hi hp hbounds ihp ihbounds => trivial
  | sel_lo hp hbounds ihp ihbounds => trivial
  | «fun» hdom hcod ihdom ihcod => trivial
  | pair_fst hfst ihfst => trivial
  | pair_single_member hp hsnd hopen ihp ihsnd ihopen => trivial
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty => trivial

/-- Every structurally checked term-level path resolves when pair-shaped
checks at resolved locations are reflected by the store. -/
theorem Path.reduce_progress_structural
    (hreflect : Store.PairCheckReflection Gamma sigma)
    (hp : Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty T)) :
    exists x, Path.reduce p sigma x :=
  Path.structLookupable hreflect hp rfl

/-! ## Minimal store observations -/

/-- Function-shape reflection at an occupied location.  The equality is the
least evidence needed to construct the machine's application step. -/
def Store.FunCheckReflection (Gamma : Ctx n) (sigma : Store n) : Prop :=
  forall {x : Fin n} {S : LambdaP.Ty n}
      {U : LambdaP.Ty (n + 1)} {v : Tm n},
    Store.Binds sigma x v ->
    Path.StructCheck Gamma (Path.RuntimeEq sigma) (.var x)
      (Tau.ty (Ty.Fun S U)) ->
    exists A body, v = Tm.abs A body

/-- The complete store-facing contract needed by progress. -/
structure Store.StructOperational
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  pairReflect : Store.PairCheckReflection Gamma sigma
  funReflect : Store.FunCheckReflection Gamma sigma

/-! ## Full conditional progress -/

/-- A structural path-term derivation supplies the path classification used
by operational totality. -/
private theorem Tm.StructCheck.resolve_path
    (hops : Store.StructOperational Gamma sigma)
    (h : Tm.StructCheck Gamma (Path.RuntimeEq sigma) (Tm.path p) T) :
    exists x, Path.reduce p sigma x := by
  cases h.path_inversion rfl with
  | intro U hp hsub hwf =>
      exact Path.reduce_progress_structural hops.pairReflect hp

/-- A structurally typed machine state is final or can step, assuming only
pair and function shape reflection for its current store. -/
theorem State.StructTy.progress
    (hops : Store.StructOperational Gamma sigma)
    (h : State.StructTy Gamma ⟨sigma, k, t⟩ T) :
    State.Progress ⟨sigma, k, t⟩ := by
  cases h with
  | ok hstore hcont hterm =>
      cases t with
      | path p =>
          cases p with
          | var x =>
              cases k with
              | nil =>
                  obtain ⟨v, hbind, hv⟩ := hstore.lookup_value x
                  exact .final (.is_var hbind)
              | cons frame rest =>
                  cases frame with
                  | «let» body => exact .step .rename
          | fst p =>
              obtain ⟨x, hx⟩ := hterm.resolve_path hops
              exact .step (.path hx (by intro hvar; cases hvar))
          | sel p a =>
              obtain ⟨x, hx⟩ := hterm.resolve_path hops
              exact .step (.path hx (by intro hvar; cases hvar))
      | abs A body =>
          cases k with
          | nil => exact .final (.is_val .abs)
          | cons frame rest =>
              cases frame with
              | «let» body' => exact .step (.lift .abs)
      | pair y a delta =>
          cases k with
          | nil => exact .final (.is_val .pair)
          | cons frame rest =>
              cases frame with
              | «let» body => exact .step (.lift .pair)
      | app p q =>
          obtain ⟨S, U, hfun, harg, post⟩ := hterm.app_inversion
          obtain ⟨x, hp⟩ := hfun.resolve_path hops
          obtain ⟨y, hq⟩ := harg.resolve_path hops
          cases hfun.path_inversion rfl with
          | intro P hpath hsingle hwf =>
              have hfunAtP : Path.StructCheck Gamma
                  (Path.RuntimeEq sigma) p (Tau.ty (Ty.Fun S U)) :=
                hpath.promote hsingle
              have hfunAtX : Path.StructCheck Gamma
                  (Path.RuntimeEq sigma) (.var x)
                  (Tau.ty (Ty.Fun S U)) :=
                hfunAtP.reduce_to_var hp
              obtain ⟨v, hbind, hv⟩ := hstore.lookup_value x
              obtain ⟨A, body, rfl⟩ := hops.funReflect hbind hfunAtX
              exact .step (.app hp hq hbind)
      | «let» s body => exact .step .let_push
      | typed u A => exact .step .ascribe

end LambdaP
