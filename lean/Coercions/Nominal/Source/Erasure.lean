import Coercions.PDot.Runtime
import Coercions.Nominal.Source.Reduction
import Coercions.Nominal.Source.Programs

/-!
# The erasure of the source into the runtime

The erasure of pDOT into the untyped runtime `PDot.Runtime`, as Part R of plan X states it
(`plan-10-pdot.md:311-342`).  Types are dropped.  A top-level literal `ν(z : T) ds` erases to a runtime
literal `ν(z) ds'`.  A literal nested in a field has no self binder in the runtime.  It erases to a
`nest`, and its self is the path of the field, so a nested literal is addressed by its path from the
enclosing top-level self.

* `Tm.erase`, `Val.erase`, `Defs.addr` and `Rhs.eraseField` are one structural recursion on the
  source's syntax.  `Defs.addr r ds` erases the definitions of a literal whose self is the path `r`.
  `Rhs.eraseField rhs p` erases a field's right side at the field's path `p`.  A nested literal's
  definitions are erased at their own self `.here` and then opened at `p`, so the recursion stays
  structural.  The plan's equation for a nested literal is the theorem `Defs.addr_new`.
* A type definition erases to `drop`.  `addr r (ds ▹ {A = T})` is `(addr r ds).drop A`, which
  removes every definition at `A`.  So a type definition at a term label shadows an older field in
  the runtime as it does in the source.  The plan's equation `addr r ds` holds when `ds.hasnt A`
  (`Defs.addr_typ_of_hasnt`), which `ty_defs_cons` asks of every typed literal.
* `eraseAt p r` erases a right side that lookup reached at the path `p`.  At a variable it is the
  stored value.  Below a variable it is the field at its path, a nested literal as a `nest`.
* The lockstep theorems of R.3.  `erase_lookup` and `erase_lookup_reflect` relate one lookup step
  of the source and of the runtime.  `erase_step` and `erase_reflect` do the same for reduction, and
  `erase_reflect` holds for every configuration, typed or not.  `erase_normForm` and
  `erase_pathSafe` carry normal forms and safe paths back to the source.
* E5's erased program runs to `path o.incr.decr` by `decide +kernel` (`E5_runFuel`), and E12's
  lookup runs on the erased store (`E12_runtime`).  The regressions `rk_*` check the risk of the
  plan at `red_let_tgt` under a store extension, and `ts_*` check the shadowing of a field by a
  type definition at the same label.

Binders are named in comments only.  `(s,x)` adds one variable, and `.here` is the newest variable of
a signature.  Inside this namespace the runtime's names are written `PDot.Runtime.Tm`, `PDot.Runtime.LStep`
and so on.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Erasure (plan R.2) -/

/-- The right side of a field definition, `none` at a type definition. -/
def Def.rhs? : Def s → Option (Rhs s)
  | .typ _ _ => none
  | .trm _ r => some r
  | .cls _ _ => none

mutual
/-- `erase t`.  Types are dropped. -/
def Tm.erase : Tm s → PDot.Runtime.Tm s
  | .val v => .val v.erase                            -- erase (val v) = val (eraseV v)
  | .app q p => .app q p                              -- erase (app q p) = app q p
  | .lett t u => .lett t.erase u.erase                -- erase (let z = t in u) = let z = erase t in erase u
  | .path p => .path p                                -- erase (path p) = path p
/-- `eraseV v`. -/
def Val.erase : Val s → PDot.Runtime.Val s
  | .new _ ds => .new (Defs.addr (.var .here) ds)     -- eraseV ν(z : T) ds = ν(z) (addr z ds)
  | .lam _ t => .lam t.erase                          -- eraseV λ(z : T) t = λ(z) erase t
/-- `addr r ds`: the definitions of a literal whose self is the path `r`. -/
def Defs.addr (r : Path s) : Defs s → PDot.Runtime.Defs s
  -- addr r [] = []
  | .nil => .nil
  -- addr r (ds ▹ {A = T}) = (addr r ds).drop A
  | .cons ds (.typ A _) => (Defs.addr r ds).drop A
  -- addr r (ds ▹ {a = rhs}) = addr r ds ▹ (a = rhs erased at r.a)
  | .cons ds (.trm a rhs) => .cons (Defs.addr r ds) a (rhs.eraseField (r.sel a))
  -- addr r (ds ▹ {class C = T}) = (addr r ds).drop C
  | .cons ds (.cls C _) => (Defs.addr r ds).drop C
/-- The erasure of a field's right side, at the field's path `p`. -/
def Rhs.eraseField : Rhs s → Path s → PDot.Runtime.Rhs s
  -- defp q ↦ defp q
  | .defp q, _ => .defp q
  -- defv λ(z : T) t ↦ defv λ(z) erase t
  | .defv (.lam _ t), _ => .defv (.lam t.erase)
  -- defv ν(w : T') ds ↦ nest (addr w ds), w := p
  | .defv (.new _ ds), p => .nest ((Defs.addr (.var .here) ds).substPath p)
end

/-- `eraseAt p r`: a right side reached by lookup at the path `p`. -/
def eraseAt : Path s → Rhs s → PDot.Runtime.Rhs s
  | .var _, .defp q => .defp q                        -- eraseAt x (defp q) = defp q
  | .var _, .defv v => .defv v.erase                  -- eraseAt x (defv v) = defv (eraseV v), the stored value
  | .sel p a, r => r.eraseField (p.sel a)             -- eraseAt p.a r, a nested literal at its path

/-- The erasure of a store, value by value. -/
def Store.erase : Store s → PDot.Runtime.Store s
  | .nil => .nil                                      -- [] ↦ []
  | .cons γ v => .cons γ.erase v.erase                -- γ, x ↦ v  ↦  erase γ, x ↦ eraseV v

/-- The erasure of a configuration, at the same signature. -/
def Conf.erase (c : Conf) : PDot.Runtime.Conf := ⟨c.s, c.store.erase, c.tm.erase⟩

/-! ## Erasure against substitution -/

mutual
theorem Tm.erase_subst : ∀ (t : Tm s₁) (σ : PathSubst s₁ s₂), (t.subst σ).erase = t.erase.subst σ
  | .val v, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, Val.erase_subst v σ]
  | .app q p, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst]
  | .lett t u, σ => by
      simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst, Tm.erase_subst t σ, Tm.erase_subst u σ.lift]
  | .path p, σ => by simp only [Tm.subst, Tm.erase, PDot.Runtime.Tm.subst]
theorem Val.erase_subst : ∀ (v : Val s₁) (σ : PathSubst s₁ s₂), (v.subst σ).erase = v.erase.subst σ
  | .new T ds, σ => by
      simp only [Val.subst, Val.erase, PDot.Runtime.Val.subst, Defs.addr_subst (.var .here) ds σ.lift]
      rfl
  | .lam T t, σ => by simp only [Val.subst, Val.erase, PDot.Runtime.Val.subst, Tm.erase_subst t σ.lift]
theorem Defs.addr_subst : ∀ (r : Path s₁) (ds : Defs s₁) (σ : PathSubst s₁ s₂),
    (Defs.addr r ds).subst σ = Defs.addr (r.subst σ) (ds.subst σ)
  | _, .nil, _ => rfl
  | r, .cons ds (.typ A T), σ => by
      simp only [Defs.addr, Defs.subst, Def.subst, PDot.Runtime.Defs.drop_subst, Defs.addr_subst r ds σ]
  | r, .cons ds (.trm a rhs), σ => by
      simp only [Defs.addr, Defs.subst, Def.subst, PDot.Runtime.Defs.subst, Defs.addr_subst r ds σ,
        Rhs.eraseField_subst rhs (r.sel a) σ]
      rfl
  | r, .cons ds (.cls C T), σ => by
      simp only [Defs.addr, Defs.subst, Def.subst, PDot.Runtime.Defs.drop_subst, Defs.addr_subst r ds σ]
theorem Rhs.eraseField_subst : ∀ (r : Rhs s₁) (p : Path s₁) (σ : PathSubst s₁ s₂),
    (r.eraseField p).subst σ = (r.subst σ).eraseField (p.subst σ)
  | .defp q, _, _ => rfl
  | .defv (.lam T t), _, σ => by
      simp only [Rhs.eraseField, Rhs.subst, Val.subst, PDot.Runtime.Rhs.subst, PDot.Runtime.Val.subst,
        Tm.erase_subst t σ.lift]
  | .defv (.new T ds), p, σ => by
      simp only [Rhs.eraseField, Rhs.subst, Val.subst, PDot.Runtime.Rhs.subst,
        PDot.Runtime.Defs.substPath_subst, Defs.addr_subst (.var .here) ds σ.lift]
      rfl
end

/-- Erasure commutes with renaming.  This is the lemma of the plan's risk at `red_let_tgt`. -/
theorem Tm.erase_rename (t : Tm s₁) (ρ : Rename s₁ s₂) : (t.rename ρ).erase = t.erase.rename ρ := by
  rw [← Tm.subst_ofRename, Tm.erase_subst, PDot.Runtime.Tm.subst_ofRename]

theorem Val.erase_rename (v : Val s₁) (ρ : Rename s₁ s₂) : (v.rename ρ).erase = v.erase.rename ρ := by
  rw [← Val.subst_ofRename, Val.erase_subst, PDot.Runtime.Val.subst_ofRename]

theorem Tm.erase_substPath (t : Tm (s,x)) (p : Path s) :
    (t.substPath p).erase = t.erase.substPath p :=
  Tm.erase_subst t _

theorem Store.erase_get : ∀ (γ : Store s) (x : BVar s .var), γ.erase.get x = (γ.get x).erase
  | .cons γ v, .here => by
      simp only [Store.erase, Store.get, PDot.Runtime.Store.get, Val.weaken, PDot.Runtime.Val.weaken,
        Val.erase_rename]
  | .cons γ v, .there y => by
      simp only [Store.erase, Store.get, PDot.Runtime.Store.get, Val.weaken, PDot.Runtime.Val.weaken,
        Val.erase_rename, Store.erase_get γ y]

/-! ## The plan's equations, as theorems

`addr r [] = []`, the type equation with `drop`, the equations at `defp q` and at a lambda, the two
variable cases of `eraseAt` and `eraseAt` at a lambda below a variable hold by `rfl`.  The equations
at a nested literal recurse on `ds'⟨r.a⟩`, which is no subterm, and are theorems here. -/

/-- `addr r (ds ▹ {a = defv ν(w : T') ds'}) = addr r ds ▹ (a = nest (addr (r.a) ds'⟨r.a⟩))`. -/
theorem Defs.addr_new (r : Path s) (ds : Defs s) (a : Label) (T' : Ty (s,x)) (ds' : Defs (s,x)) :
    Defs.addr r (ds.cons (.trm a (.defv (.new T' ds'))))
      = (Defs.addr r ds).cons a (.nest (Defs.addr (r.sel a) (ds'.substPath (r.sel a)))) := by
  simp only [Defs.addr, Rhs.eraseField, PDot.Runtime.Defs.substPath, Defs.substPath,
    Defs.addr_subst]
  rfl

/-- `eraseAt (p.a) (defv ν(w : T') ds') = nest (addr (p.a) ds'⟨p.a⟩)`. -/
theorem eraseAt_sel_new (p : Path s) (a : Label) (T' : Ty (s,x)) (ds' : Defs (s,x)) :
    eraseAt (p.sel a) (.defv (.new T' ds')) = .nest (Defs.addr (p.sel a) (ds'.substPath (p.sel a))) := by
  simp only [eraseAt, Rhs.eraseField, PDot.Runtime.Defs.substPath, Defs.substPath, Defs.addr_subst]
  rfl

/-- `eraseAt r (defv λ(z : T) t) = defv λ(z) erase t`. -/
theorem eraseAt_lam (p : Path s) (T : Ty s) (t : Tm (s,x)) :
    eraseAt p (.defv (.lam T t)) = .defv (.lam t.erase) := by
  cases p <;> rfl

/-- `eraseAt r (defp q) = defp q`. -/
theorem eraseAt_path (p q : Path s) : eraseAt p (.defp q) = .defp q := by
  cases p <;> rfl

/-! ## Field reads -/

theorem Defs.get_label : ∀ (ds : Defs s) {a : Label} {d : Def s}, ds.get a = some d → d.label = a
  | .nil, _, _, h => by cases h
  | .cons ds d', a, d, h => by
      simp only [Defs.get] at h
      split at h
      · rename_i e
        cases h
        exact e
      · exact Defs.get_label ds h

/-- The runtime's field read of `addr r ds` is the source's, erased at `r.a`.  At a type definition
`{A = T}` with `A = a` both sides are `none`, by `drop`. -/
theorem Defs.addr_get : ∀ (r : Path s) (ds : Defs s) (a : Label),
    (Defs.addr r ds).get a = ((ds.get a).bind Def.rhs?).map (·.eraseField (r.sel a))
  | _, .nil, _ => rfl
  | r, .cons ds (.typ A T), a => by
      simp only [Defs.addr, Defs.get, Def.label]
      by_cases h : A = a
      · subst h
        rw [if_pos rfl, PDot.Runtime.Defs.get_drop_self]
        rfl
      · rw [if_neg h, PDot.Runtime.Defs.get_drop_ne _ h, Defs.addr_get r ds a]
  | r, .cons ds (.trm b rhs), a => by
      simp only [Defs.addr, Defs.get, Def.label, PDot.Runtime.Defs.get]
      by_cases h : b = a
      · subst h
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg h, if_neg h, Defs.addr_get r ds a]
  | r, .cons ds (.cls C T), a => by
      simp only [Defs.addr, Defs.get, Def.label]
      by_cases h : C = a
      · subst h
        rw [if_pos rfl, PDot.Runtime.Defs.get_drop_self]
        rfl
      · rw [if_neg h, PDot.Runtime.Defs.get_drop_ne _ h, Defs.addr_get r ds a]

theorem Defs.addr_get_some {r : Path s} {ds : Defs s} {a : Label} {rhs : Rhs s}
    (h : ds.get a = some (.trm a rhs)) : (Defs.addr r ds).get a = some (rhs.eraseField (r.sel a)) := by
  rw [Defs.addr_get, h]
  rfl

theorem Defs.addr_get_inv {r : Path s} {ds : Defs s} {a : Label} {k : PDot.Runtime.Rhs s}
    (h : (Defs.addr r ds).get a = some k) :
    ∃ rhs, ds.get a = some (.trm a rhs) ∧ rhs.eraseField (r.sel a) = k := by
  rw [Defs.addr_get] at h
  cases hg : ds.get a with
  | none =>
      rw [hg] at h
      cases h
  | some d =>
      rw [hg] at h
      have hl := Defs.get_label ds hg
      cases d with
      | typ A T => cases h
      | trm b rhs =>
          simp only [Def.label] at hl
          subst hl
          simp only [Option.bind_some, Def.rhs?, Option.map_some, Option.some.injEq] at h
          exact ⟨rhs, rfl, h⟩
      | cls C T => cases h

/-- The plan's `addr r (ds ▹ {A = T}) = addr r ds`, when no definition of `ds` is at `A`. -/
theorem Defs.addr_typ_of_hasnt {r : Path s} {ds : Defs s} {A : Label} {T : Ty s}
    (h : ds.hasnt A) : Defs.addr r (ds.cons (.typ A T)) = Defs.addr r ds := by
  simp only [Defs.addr]
  apply PDot.Runtime.Defs.drop_of_get_none
  rw [Defs.addr_get]
  rw [Defs.hasnt] at h
  rw [h]
  rfl

/-- The plan's `addr r (ds ▹ {class C = T}) = addr r ds`, when no definition of `ds` is at `C`.  A
class definition erases as a type definition does. -/
theorem Defs.addr_cls_of_hasnt {r : Path s} {ds : Defs s} {C : Label} {T : Ty s}
    (h : ds.hasnt C) : Defs.addr r (ds.cons (.cls C T)) = Defs.addr r ds := by
  simp only [Defs.addr]
  apply PDot.Runtime.Defs.drop_of_get_none
  rw [Defs.addr_get]
  rw [Defs.hasnt] at h
  rw [h]
  rfl

namespace AddrClsTests

/-- `addr z ([] ▹ {class C = ⊤}) = []`: a class definition leaves no field. -/
example : Defs.addr (.var .here) ((Defs.nil : Defs ([],x)).cons (.cls (.typ 0) .top)) = .nil := by rfl

end AddrClsTests

/-! ## Lookup, forward and back (plan R.3) -/

theorem eraseField_substPath_sel (rhs : Rhs (s,x)) (p : Path s) (a : Label) :
    (rhs.eraseField ((Path.var .here).sel a)).substPath p = (rhs.substPath p).eraseField (p.sel a) :=
  Rhs.eraseField_subst rhs _ _

/-- `erase_lookup` with its start generalized by an equation, for the induction. -/
theorem erase_lookup_of_eq {γ : Store s} {k r : Rhs s} (h : LStep γ k r) :
    ∀ {p : Path s}, k = .defp p → PDot.Runtime.LStep γ.erase (.defp p) (eraseAt p r) := by
  induction h with
  | @lookup_var x =>
      intro p e
      cases e
      show PDot.Runtime.LStep γ.erase (.defp (.var x)) (.defv (γ.get x).erase)
      rw [← Store.erase_get]
      exact .var
  | @lookup_sel_p p q a _ ih =>
      intro p' e
      cases e
      have h1 := ih rfl
      rw [eraseAt_path] at h1
      exact .selP h1
  | @lookup_sel_v p T ds a rhs _ hg ih =>
      intro p' e
      cases e
      have ih' := ih rfl
      show PDot.Runtime.LStep γ.erase (.defp (p.sel a)) ((rhs.substPath p).eraseField (p.sel a))
      rw [← eraseField_substPath_sel]
      cases p with
      | var x => exact .selV ih' (Defs.addr_get_some hg)
      | sel p₀ b =>
          refine .selN ih' ?_
          rw [PDot.Runtime.Defs.substPath, PDot.Runtime.Defs.get_subst, Defs.addr_get_some hg]
          rfl

/-- `γ ⊢ defp p ⤳ r  ⟹  erase γ ⊢ defp p ⤳ᴿ eraseAt p r`.  At `lookup_sel_v` the runtime step is
RL-SelV below a variable and RL-SelN below a selection. -/
theorem erase_lookup {γ : Store s} {p : Path s} {r : Rhs s} (h : LStep γ (.defp p) r) :
    PDot.Runtime.LStep γ.erase (.defp p) (eraseAt p r) :=
  erase_lookup_of_eq h rfl

theorem eraseAt_eq_defp {p q : Path s} {r : Rhs s} (h : eraseAt p r = .defp q) : r = .defp q := by
  cases p with
  | var x =>
      cases r with
      | defp q' =>
          cases h
          rfl
      | defv v => cases h
  | sel p a =>
      cases r with
      | defp q' =>
          cases h
          rfl
      | defv v => cases v <;> cases h

/-- Only a variable erases a right side to a runtime literal. -/
theorem eraseAt_eq_new {p : Path s} {r : Rhs s} {ds : PDot.Runtime.Defs (s,x)}
    (h : eraseAt p r = .defv (.new ds)) :
    (∃ x, p = .var x) ∧ ∃ T ds₀, r = .defv (.new T ds₀) ∧ Defs.addr (.var .here) ds₀ = ds := by
  cases p with
  | var x =>
      cases r with
      | defp q => cases h
      | defv v =>
          cases v with
          | new T ds₀ =>
              cases h
              exact ⟨⟨x, rfl⟩, T, ds₀, rfl, rfl⟩
          | lam T t => cases h
  | sel p a =>
      cases r with
      | defp q => cases h
      | defv v => cases v <;> cases h

/-- A `nest` is the erasure of a literal below a variable. -/
theorem eraseAt_eq_nest {p : Path s} {r : Rhs s} {ds : PDot.Runtime.Defs s}
    (h : eraseAt p r = .nest ds) :
    ∃ T ds₀, r = .defv (.new T ds₀) ∧ (Defs.addr (.var .here) ds₀).substPath p = ds := by
  cases p with
  | var x =>
      cases r with
      | defp q => cases h
      | defv v => cases v <;> cases h
  | sel p a =>
      cases r with
      | defp q => cases h
      | defv v =>
          cases v with
          | new T ds₀ =>
              cases h
              exact ⟨T, ds₀, rfl, rfl⟩
          | lam T t => cases h

/-- `erase_lookup_reflect` with its start generalized by an equation, for the induction. -/
theorem erase_lookup_reflect_of_eq {γ : Store s} {k₀ k : PDot.Runtime.Rhs s}
    (h : PDot.Runtime.LStep γ.erase k₀ k) :
    ∀ {p : Path s}, k₀ = .defp p → ∃ r, LStep γ (.defp p) r ∧ eraseAt p r = k := by
  induction h with
  | @var x =>
      intro p e
      cases e
      refine ⟨.defv (γ.get x), .lookup_var, ?_⟩
      show PDot.Runtime.Rhs.defv (γ.get x).erase = _
      rw [Store.erase_get]
  | @selP p q a _ ih =>
      intro p' e
      cases e
      obtain ⟨r, hr, he⟩ := ih rfl
      cases eraseAt_eq_defp he
      exact ⟨.defp (q.sel a), .lookup_sel_p hr, rfl⟩
  | @selV p ds a k _ hg ih =>
      intro p' e
      cases e
      obtain ⟨r, hr, he⟩ := ih rfl
      obtain ⟨⟨x, rfl⟩, T, ds₀, rfl, rfl⟩ := eraseAt_eq_new he
      obtain ⟨rhs, hg', hk⟩ := Defs.addr_get_inv hg
      refine ⟨rhs.substPath (.var x), .lookup_sel_v hr hg', ?_⟩
      show (rhs.substPath (.var x)).eraseField ((Path.var x).sel a) = _
      rw [← eraseField_substPath_sel, hk]
  | @selN p ds a k _ hg ih =>
      intro p' e
      cases e
      obtain ⟨r, hr, he⟩ := ih rfl
      obtain ⟨T, ds₀, rfl, rfl⟩ := eraseAt_eq_nest he
      rw [PDot.Runtime.Defs.substPath, PDot.Runtime.Defs.get_subst] at hg
      cases hg₀ : (Defs.addr (.var .here) ds₀).get a with
      | none =>
          rw [hg₀] at hg
          cases hg
      | some k₁ =>
          rw [hg₀] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          obtain ⟨rhs, hg', hk⟩ := Defs.addr_get_inv hg₀
          refine ⟨rhs.substPath p, .lookup_sel_v hr hg', ?_⟩
          show (rhs.substPath p).eraseField (p.sel a) = _
          rw [← eraseField_substPath_sel, hk]
          rfl

/-- `erase γ ⊢ defp p ⤳ᴿ k  ⟹  ∃ r, γ ⊢ defp p ⤳ r ∧ eraseAt p r = k`. -/
theorem erase_lookup_reflect {γ : Store s} {p : Path s} {k : PDot.Runtime.Rhs s}
    (h : PDot.Runtime.LStep γ.erase (.defp p) k) : ∃ r, LStep γ (.defp p) r ∧ eraseAt p r = k :=
  erase_lookup_reflect_of_eq h rfl

/-- `erase_lookups` with its start generalized by an equation, for the induction. -/
theorem erase_lookups_of_eq {γ : Store s} {k r : Rhs s} (h : Lookups γ k r) :
    ∀ {p : Path s}, k = .defp p → ∃ q, PDot.Runtime.Lookups γ.erase (.defp p) (eraseAt q r) := by
  induction h with
  | refl =>
      intro p e
      subst e
      refine ⟨p, ?_⟩
      rw [eraseAt_path]
      exact .refl
  | @step r₀ r₁ r₂ h hs ih =>
      intro p e
      subst e
      cases r₁ with
      | defp p₁ =>
          obtain ⟨q, hq⟩ := ih rfl
          have h1 := erase_lookup h
          rw [eraseAt_path] at h1
          exact ⟨q, .step h1 hq⟩
      | defv v =>
          cases Lookups.from_val hs
          exact ⟨p, .single (erase_lookup h)⟩

/-- A lookup sequence of the source erases to one of the runtime.  `q` is the path the last step
was taken at. -/
theorem erase_lookups {γ : Store s} {p : Path s} {r : Rhs s} (h : Lookups γ (.defp p) r) :
    ∃ q, PDot.Runtime.Lookups γ.erase (.defp p) (eraseAt q r) :=
  erase_lookups_of_eq h rfl

/-- `erase_lookups_reflect` with its start generalized by an equation, for the induction. -/
theorem erase_lookups_reflect_of_eq {γ : Store s} {k₀ k : PDot.Runtime.Rhs s}
    (h : PDot.Runtime.Lookups γ.erase k₀ k) :
    ∀ {p : Path s}, k₀ = .defp p → ∃ q r, Lookups γ (.defp p) r ∧ eraseAt q r = k := by
  induction h with
  | refl =>
      intro p e
      subst e
      exact ⟨p, .defp p, .refl, eraseAt_path p p⟩
  | @step k₀ k₁ k₂ h hs ih =>
      intro p e
      subst e
      obtain ⟨r₁, hr₁, he₁⟩ := erase_lookup_reflect h
      cases r₁ with
      | defp p₁ =>
          rw [eraseAt_path] at he₁
          subst he₁
          obtain ⟨q, r, hr, he⟩ := ih rfl
          exact ⟨q, r, .step hr₁ hr, he⟩
      | defv v =>
          have hnp : k₁.isPath = false := by
            subst he₁
            cases p with
            | var x => rfl
            | sel p a => cases v <;> rfl
          have e2 := hs.of_not_path hnp
          subst e2
          exact ⟨p, .defv v, .single hr₁, he₁⟩

/-- A lookup sequence of the runtime from an erased store is the erasure of one of the source. -/
theorem erase_lookups_reflect {γ : Store s} {p : Path s} {k : PDot.Runtime.Rhs s}
    (h : PDot.Runtime.Lookups γ.erase (.defp p) k) : ∃ q r, Lookups γ (.defp p) r ∧ eraseAt q r = k :=
  erase_lookups_reflect_of_eq h rfl

/-! ## Reduction, forward and back (plan R.3) -/

/-- `c ⟼[ρ] c'  ⟹  erase c ⟼ᴿ[ρ] erase c'`. -/
theorem erase_step {c c' : Conf} {ρ : Rename c.s c'.s} (h : Red c c' ρ) :
    PDot.Runtime.Red c.erase c'.erase ρ := by
  induction h with
  | @red_app s γ q p T t hl =>
      obtain ⟨q', hq⟩ := erase_lookups hl
      rw [eraseAt_lam] at hq
      show PDot.Runtime.Red ⟨s, γ.erase, .app q p⟩ ⟨s, γ.erase, (t.substPath p).erase⟩ Rename.id
      rw [Tm.erase_substPath]
      exact .app hq
  | red_let_val => exact .letVal
  | @red_let_path s γ p t =>
      show PDot.Runtime.Red ⟨s, γ.erase, .lett (.path p) t.erase⟩ ⟨s, γ.erase, (t.substPath p).erase⟩ _
      rw [Tm.erase_substPath]
      exact .letPath
  | @red_let_tgt s γ t₀ s' γ' t₀' ρ t _ ih =>
      show PDot.Runtime.Red ⟨s, γ.erase, .lett t₀.erase t.erase⟩
        ⟨s', γ'.erase, .lett t₀'.erase (t.rename ρ.lift).erase⟩ ρ
      rw [Tm.erase_rename]
      exact .letTgt ih

theorem Tm.erase_eq_app {t : Tm s} {q p : Path s} (h : t.erase = .app q p) : t = .app q p := by
  cases t <;> simp only [Tm.erase, PDot.Runtime.Tm.app.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem Tm.erase_eq_lett {t : Tm s} {t₀ : PDot.Runtime.Tm s} {u : PDot.Runtime.Tm (s,x)}
    (h : t.erase = .lett t₀ u) : ∃ t₁ u₁, t = .lett t₁ u₁ ∧ t₁.erase = t₀ ∧ u₁.erase = u := by
  cases t <;> simp only [Tm.erase, PDot.Runtime.Tm.lett.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem Tm.erase_eq_val {t : Tm s} {v : PDot.Runtime.Val s} (h : t.erase = .val v) :
    ∃ v₁, t = .val v₁ ∧ v₁.erase = v := by
  cases t <;> simp only [Tm.erase, PDot.Runtime.Tm.val.injEq, reduceCtorEq] at h
  subst h
  exact ⟨_, rfl, rfl⟩

theorem Tm.erase_eq_path {t : Tm s} {p : Path s} (h : t.erase = .path p) : t = .path p := by
  cases t <;> simp only [Tm.erase, PDot.Runtime.Tm.path.injEq, reduceCtorEq] at h
  subst h
  rfl

/-- `erase_reflect` with the runtime configuration generalized, for the induction.  Each case
starts by reducing the projections of the runtime configuration in the types of the source store
and term. -/
theorem erase_reflect_of_eq {k₀ k : PDot.Runtime.Conf} {ρ : Rename k₀.s k.s} (h : PDot.Runtime.Red k₀ k ρ) :
    ∀ (γ : Store k₀.s) (t : Tm k₀.s), γ.erase = k₀.store → t.erase = k₀.tm →
      ∃ (γ' : Store k.s) (t' : Tm k.s), Red ⟨k₀.s, γ, t⟩ ⟨k.s, γ', t'⟩ ρ ∧
        γ'.erase = k.store ∧ t'.erase = k.tm := by
  induction h with
  | @app s γr q p t hl =>
      intro γ t₁ hγ ht
      dsimp only at γ t₁ hγ ht ⊢
      cases Tm.erase_eq_app ht
      subst hγ
      obtain ⟨q', r, hr, he⟩ := erase_lookups_reflect hl
      have : ∃ T t₂, r = .defv (.lam T t₂) ∧ t₂.erase = t := by
        cases q' with
        | var x =>
            cases r with
            | defp _ => cases he
            | defv v => cases v with
              | new _ _ => cases he
              | lam T t₂ =>
                  cases he
                  exact ⟨T, t₂, rfl, rfl⟩
        | sel q₀ b =>
            cases r with
            | defp _ => cases he
            | defv v => cases v with
              | new _ _ => cases he
              | lam T t₂ =>
                  cases he
                  exact ⟨T, t₂, rfl, rfl⟩
      obtain ⟨T, t₂, rfl, rfl⟩ := this
      exact ⟨γ, t₂.substPath p, .red_app hr, rfl, Tm.erase_substPath t₂ p⟩
  | @letVal s γr v t =>
      intro γ t₁ hγ ht
      dsimp only at γ t₁ hγ ht ⊢
      obtain ⟨t₀, u, rfl, h0, hu⟩ := Tm.erase_eq_lett ht
      obtain ⟨v₁, rfl, hv⟩ := Tm.erase_eq_val h0
      refine ⟨γ.cons v₁, u, .red_let_val, ?_, hu⟩
      show PDot.Runtime.Store.cons γ.erase v₁.erase = _
      rw [hγ, hv]
  | @letPath s γr p t =>
      intro γ t₁ hγ ht
      dsimp only at γ t₁ hγ ht ⊢
      obtain ⟨t₀, u, rfl, h0, hu⟩ := Tm.erase_eq_lett ht
      cases Tm.erase_eq_path h0
      refine ⟨γ, u.substPath p, .red_let_path, hγ, ?_⟩
      rw [Tm.erase_substPath, hu]
  | @letTgt s γr t₀r s' γr' t₀r' ρ tr _ ih =>
      intro γ t₁ hγ ht
      dsimp only at γ t₁ hγ ht ih ⊢
      obtain ⟨t₀, u, rfl, h0, hu⟩ := Tm.erase_eq_lett ht
      obtain ⟨γ', t₀', hr, hγ', ht'⟩ := ih γ t₀ hγ h0
      refine ⟨γ', .lett t₀' (u.rename ρ.lift), .red_let_tgt hr, hγ', ?_⟩
      show PDot.Runtime.Tm.lett t₀'.erase (u.rename ρ.lift).erase = _
      rw [Tm.erase_rename, ht', hu]

/-- `erase c ⟼ᴿ[ρ] k  ⟹  c ⟼[ρ] c'` with `erase c' = k`, for every configuration `c`, typed or
not.  The successor is built at `k.s`. -/
theorem erase_reflect {c : Conf} {k : PDot.Runtime.Conf} {ρ : Rename c.s k.s}
    (h : PDot.Runtime.Red c.erase k ρ) :
    ∃ (γ' : Store k.s) (t' : Tm k.s), Red c ⟨k.s, γ', t'⟩ ρ ∧ γ'.erase = k.store ∧ t'.erase = k.tm :=
  erase_reflect_of_eq h c.store c.tm rfl rfl

/-- `erase_reflect` with the renaming forgotten. -/
theorem erase_reflect_step {c : Conf} {k : PDot.Runtime.Conf} (h : PDot.Runtime.Step c.erase k) :
    ∃ c', Step c c' ∧ c'.erase = k := by
  obtain ⟨ρ, hr⟩ := h
  obtain ⟨γ', t', hr', hγ, ht⟩ := erase_reflect hr
  refine ⟨⟨k.s, γ', t'⟩, ⟨ρ, hr'⟩, ?_⟩
  cases k
  simp only [Conf.erase] at hγ ht ⊢
  rw [hγ, ht]

theorem erase_normForm (t : Tm s) : PDot.Runtime.NormForm t.erase ↔ NormForm t := by
  constructor
  · intro h
    cases t with
    | val v => exact .nf_val
    | path p => exact .nf_path
    | app q p => cases h
    | lett t u => cases h
  · intro h
    cases h with
    | nf_path => exact .path
    | nf_val => exact .val

/-- A path that is safe in the erased store is safe in the source store. -/
theorem erase_pathSafe {γ : Store s} {p : Path s} (h : PDot.Runtime.PathSafe γ.erase p) :
    PathSafe γ p := by
  intro r hr
  cases r with
  | defv v => exact .inl ⟨v, rfl⟩
  | defp q =>
      obtain ⟨q', hq⟩ := erase_lookups hr
      rw [eraseAt_path] at hq
      rcases h _ hq with ⟨v, e⟩ | ⟨ds, e⟩ | ⟨k', hk'⟩
      · cases e
      · cases e
      · obtain ⟨r', hr', _⟩ := erase_lookup_reflect hk'
        exact .inr ⟨r', hr'⟩

/-- The closure of `erase_step`. -/
theorem erase_reds {c c' : Conf} (h : Reds c c') : PDot.Runtime.Reds c.erase c'.erase := by
  induction h with
  | refl => exact .refl
  | @step c₁ c₂ c₃ h _ ih =>
      obtain ⟨ρ, hr⟩ := h
      have hs : PDot.Runtime.Step c₁.erase c₂.erase := ⟨ρ, erase_step hr⟩
      exact .step hs ih

/-! ## Acceptance: E5 and E12 on the runtime -/

/-- The end of E5's run: `x` and `o` allocated, `o.incr.decr` in focus. -/
abbrev e5Final : PDot.Runtime.Conf :=
  ⟨(([] : Sig),x),x,
   (PDot.Runtime.Store.nil.cons (Val.new sg_Tx sg_xDefs).erase).cons (Val.new sg_To sg_oDefs).erase,
   .path (((Path.var .here).sel sg_incr).sel sg_decr)⟩

/-- E5's erased program runs to `path o.incr.decr`. -/
theorem E5_runFuel : PDot.Runtime.runFuel 4 8 (Conf.erase ⟨[], .nil, sngl_t⟩) = e5Final := by
  decide +kernel

/-- The run is four steps: four steps reach `e5Final`, three do not.  `red_let_val` allocates `x`,
`red_app` reads `x.d` and opens the lambda at `x`, `red_let_tgt` over `red_let_val` allocates `o`,
and `red_let_path` substitutes `o`. -/
theorem E5_four_steps :
    PDot.Runtime.runFuel 4 4 (Conf.erase ⟨[], .nil, sngl_t⟩) = e5Final ∧
    PDot.Runtime.runFuel 4 3 (Conf.erase ⟨[], .nil, sngl_t⟩) ≠ e5Final := by
  decide +kernel

theorem E5_run : PDot.Runtime.Reds (Conf.erase ⟨[], .nil, sngl_t⟩) e5Final :=
  E5_runFuel ▸ PDot.Runtime.Reds.of_runFuel 4 8 _

/-- E12 on the erased store: `x.a.c ⤳ᴿ y.b.c ⤳ᴿ λ(z) z`. -/
theorem E12_runtime :
    PDot.Runtime.Lookups γ12.erase (.defp ((x12.sel e12_a).sel e12_c)) (.defv (.lam (.path (.var .here)))) := by
  have h : PDot.Runtime.lookStar γ12.erase 4 (.defp ((x12.sel e12_a).sel e12_c))
      = .defv (.lam (.path (.var .here))) := by decide +kernel
  exact h ▸ PDot.Runtime.Lookups.of_lookStar 4 _

/-- `y.b ⤳ᴿ nest {c = λ(z) z}`, so the second step of `E12_runtime` is RL-SelN. -/
theorem E12_runtime_nest :
    PDot.Runtime.LStep γ12.erase (.defp (y12.sel e12_b))
      (.nest (PDot.Runtime.Defs.nil.cons e12_c (.defv (.lam (.path (.var .here)))))) :=
  PDot.Runtime.LStep.of_lookPath (by decide +kernel)

/-- refute-d3 E: a nested literal reached by `lookup_sel_v` is a value with its own self in the
source and a `nest` in the runtime, so the erasure of a lookup result is indexed by its path. -/
theorem E12_nest_indexed :
    LStep γ12 (.defp (y12.sel e12_b)) (.defv vyb12) ∧
    eraseAt (y12.sel e12_b) (.defv vyb12) = .nest (PDot.Runtime.Defs.nil.cons e12_c (.defv (.lam (.path (.var .here))))) ∧
    eraseAt (y12.sel e12_b) (.defv vyb12) ≠ .defv vyb12.erase :=
  ⟨E12_yb, by decide +kernel, by decide +kernel⟩

/-- The prototype's `Joinable.locations` asks each location to look up to a value.  A nested
location looks up to a `nest`, so the runtime's form asks a right side that is no path. -/
theorem E12_nest_not_val : ¬ ∃ v, PDot.Runtime.LStep γ12.erase (.defp (y12.sel e12_b)) (.defv v) := by
  intro ⟨v, h⟩
  cases PDot.Runtime.LStep.det h E12_runtime_nest

/-! ## The risk of X1: `red_let_tgt` under a store extension

The continuation of `rkConf` mentions the nested literal's path `w.d.c`, and the nested literal's
field mentions the store variable `x`.  So its erased `nest` holds a path that the renaming
`Rename.succ.lift` moves.  The source step, its erasure and the runtime's own step agree. -/

abbrev rk_b : Label := .trm 0
abbrev rk_c : Label := .trm 1
abbrev rk_d : Label := .trm 2

/-- `ν(w : ⊤) {d = ν(v : ⊤) {c = x.b}}` under `[x]`: a nested literal whose field names the store
variable `x`.  In the inner definitions `.here` is `v`, `.there .here` is `w`, `.there (.there .here)`
is `x`. -/
abbrev rkLit : Val (([] : Sig),x) :=
  .new .top (.cons .nil (.trm rk_d (.defv (.new .top
    (.cons .nil (.trm rk_c (.defp (.sel (.var (.there (.there .here))) rk_b))))))))

/-- `⟨[x], [x ↦ ν(x){b = x}], let y = (let o = ν(o){} in o) in let w = rkLit in w.d.c⟩`. -/
abbrev rkConf : Conf :=
  ⟨(([] : Sig),x), Store.nil.cons (.new .top (.cons .nil (.trm rk_b (.defp (.var .here))))),
   .lett (.lett (.val (.new .top .nil)) (.path (.var .here)))
     (.lett (.val rkLit.weaken) (.path (((Path.var .here).sel rk_d).sel rk_c)))⟩

/-- The successor: `o` allocated, the continuation renamed by `succ.lift`. -/
abbrev rkNext : Conf :=
  ⟨((([] : Sig),x),x), (Store.nil.cons (.new .top (.cons .nil (.trm rk_b (.defp (.var .here)))))).cons (.new .top .nil),
   .lett (.path (.var .here))
     ((Tm.lett (.val rkLit.weaken) (.path (((Path.var .here).sel rk_d).sel rk_c))).rename Rename.succ.lift)⟩

/-- The source step: `red_let_tgt` over `red_let_val`, which allocates `o`. -/
theorem rk_source_step : Red rkConf rkNext Rename.succ := .red_let_tgt .red_let_val

theorem rk_erase_step : PDot.Runtime.Red rkConf.erase rkNext.erase Rename.succ := erase_step rk_source_step

/-- The runtime's own step lands on the erasure of the source's successor. -/
theorem rk_runtime_computes : PDot.Runtime.runFuel 4 1 rkConf.erase = rkNext.erase := by decide +kernel

/-! ## A type definition at a term label

The Lean syntax admits a type definition at a term label.  The source's `Defs.get` then returns the
type definition, and `lookup_sel_v` does not fire.  The erasure drops the older field, so the
runtime is stuck too.  Under the plan's equation `addr r (ds ▹ {A = T}) = addr r ds` the runtime
would step to `defp x` here. -/

abbrev ts_a : Label := .trm 0

/-- `x ↦ ν(z : ⊤) {a = z} ▹ {a = ⊤}`, the second a type definition at the term label `a`. -/
abbrev γTS : Store (([] : Sig),x) :=
  Store.nil.cons (.new .top ((Defs.nil.cons (.trm ts_a (.defp (.var .here)))).cons (.typ ts_a .top)))

theorem ts_source_stuck : ∀ r, ¬ LStep γTS (.defp ((Path.var .here).sel ts_a)) r := by
  intro r h
  cases h with
  | lookup_sel_p h' => cases h'
  | lookup_sel_v h' hg =>
      cases h'
      cases hg

/-- By inversion of the four runtime rules, not through `erase_lookup_reflect`.  The inner step
from `defp x` is RL-Var, so it ends at the stored literal, whose definitions are `[]`. -/
theorem ts_runtime_stuck : ∀ k, ¬ PDot.Runtime.LStep γTS.erase (.defp ((Path.var .here).sel ts_a)) k := by
  intro k h
  generalize hp : (PDot.Runtime.Rhs.defp ((Path.var .here).sel ts_a) : PDot.Runtime.Rhs (([] : Sig),x)) = k₀ at h
  cases h with
  | var => cases hp
  | selP h' =>
      cases hp
      cases PDot.Runtime.LStep.det h' .var
  | selV h' hg =>
      cases hp
      have e := PDot.Runtime.LStep.det h' .var
      rw [show γTS.erase.get .here = .new .nil by decide +kernel] at e
      cases e
      cases hg
  | selN h' _ =>
      cases hp
      cases PDot.Runtime.LStep.det h' .var

end Nominal.Source
