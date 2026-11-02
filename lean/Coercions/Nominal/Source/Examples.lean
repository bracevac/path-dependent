import Coercions.Nominal.Source.Model
import Coercions.Nominal.Source.Lookup

/-!
# Small examples and negative examples

The examples E9, E10, E11 and E13 of the plan, each a derivation `def` and a `Nonempty` theorem, and
the negative examples N1 to N5.

* `E9_sngl`: singleton creation and propagation (`pdot-paper/calculus.tex:121-145`).
* `E10_equiv`: the four equivalent types of a path (`calculus.tex:154-206`).
* `E11_fldI`: field introduction (`calculus.tex:212-252`).
* `E13_cyclic`, `E13_cyclic_lookup`: the cyclic object typed, and its field a cyclic path
  (`pdot-paper/overview.tex:412-420`).
* `N1_bad_bounds`: the bad-bounds literal of `pdot-paper/background.tex:355-380` has no type.
* `N2_fact2`: the literal `ν(x : {a : {A : ⊤..⊥}}) {a = x.a}` has no type.
* `N3_dangling`: the literal `ν(x : {h : (x.zz).type}) {h = x.zz}` has no type.
* `N4_no_refl_sngl`: no rule types a variable at its own singleton.
* `N5_tight`: `ty_def_new`'s premise on the opened definitions holds where `tight_bounds` of the
  annotation fails.

N1 and N2 follow from the inversions of `Derived`: a definition typing has no subsumption, so the
last declaration of the annotation is the one the last definition gives.  N3 and N4 follow from a
path model (`Model`) of the one context they need.  `M₃` and `M₄` read each type by structural
recursion on it, with a closing substitution for the selves of `μ`.

Each label is a declared constant with a name unique in `Nominal.Source`.  Binders are named in comments
only.  `.here` is the newest variable of a signature.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## E9: singleton creation and propagation (`calculus.tex:121-145`)

In the body of `let x = ν(x : {a : x.type} ∧ {b : S}) {a = x} ∧ {b = s} in …`, the context binds `x` at
`μ(z. {a : z.type} ∧ {b : S})`.  Here `S = ⊤`.  Then `x.a : x.type` by `ty_rec_elim`, subsumption with
`subtyp_and11` and `ty_new_elim`.  `x.a.b : (x.b).type` by `ty_path_elim`, and `x.a.b : S` by
`ty_sngl`. -/

/-- The field `a`. -/
abbrev e9_a : Label := .trm 0
/-- The field `b`. -/
abbrev e9_b : Label := .trm 1

/-- `{a : z.type} ∧ {b : ⊤}` over `(([], x), z)`: `z` is `.here`. -/
abbrev e9_body : Ty (([],x),x) := .and (.rcd (.trm e9_a (.sngl (.var .here)))) (.rcd (.trm e9_b .top))
/-- `[x : μ(z. {a : z.type} ∧ {b : ⊤})]`. -/
abbrev e9_G : Ctx ([],x) :=
  Ctx.nil.cons (.mu (.and (.rcd (.trm e9_a (.sngl (.var .here)))) (.rcd (.trm e9_b .top))))
/-- `x`. -/
abbrev e9_x : Path ([],x) := .var .here

-- G ⊢ x : {a : x.type} ∧ {b : ⊤}                     ty_var, ty_rec_elim
def E9_x : HasTy e9_G (.path e9_x) (e9_body.substPath e9_x) :=
  .ty_rec_elim (T := e9_body) (.ty_var rfl)
-- G ⊢ x.a : x.type                                    ty_sub by subtyp_and11, ty_new_elim
def E9_xa : HasTy e9_G (.path (e9_x.sel e9_a)) (.sngl e9_x) :=
  .ty_new_elim (.ty_sub E9_x .subtyp_and11)
-- G ⊢ x.b : ⊤                                         ty_sub by subtyp_and12, ty_new_elim
def E9_xb : HasTy e9_G (.path (e9_x.sel e9_b)) .top :=
  .ty_new_elim (.ty_sub E9_x .subtyp_and12)
-- G ⊢ x.a.b : (x.b).type                              ty_path_elim
def E9_xab : HasTy e9_G (.path ((e9_x.sel e9_a).sel e9_b)) (.sngl (e9_x.sel e9_b)) :=
  .ty_path_elim E9_xa E9_xb
-- G ⊢ x.a.b : ⊤                                       ty_sngl
def E9_xab_S : HasTy e9_G (.path ((e9_x.sel e9_a).sel e9_b)) .top :=
  .ty_sngl E9_xab E9_xb

/-- `x.a : x.type`, `x.a.b : (x.b).type` and `x.a.b : S`. -/
theorem E9_sngl :
    Nonempty (HasTy e9_G (.path (e9_x.sel e9_a)) (.sngl e9_x)) ∧
    Nonempty (HasTy e9_G (.path ((e9_x.sel e9_a).sel e9_b)) (.sngl (e9_x.sel e9_b))) ∧
    Nonempty (HasTy e9_G (.path ((e9_x.sel e9_a).sel e9_b)) .top) :=
  ⟨⟨E9_xa⟩, ⟨E9_xab⟩, ⟨E9_xab_S⟩⟩

/-! ## E10: equivalent types (`calculus.tex:154-206`)

In `[q : ⊤, p : q.type, r : {a : p.type} ∧ {b : p.type}]`, the path `r` has the four types of the
text.  Each step replaces one occurrence of `p` by `q` with `subtyp_sngl_pq`, at the right operand by
`rand2` and at the left one by `rand1`. -/

/-- The field `a`. -/
abbrev e10_a : Label := .trm 0
/-- The field `b`. -/
abbrev e10_b : Label := .trm 1

/-- `[q : ⊤, p : q.type, r : {a : p.type} ∧ {b : p.type}]`. -/
abbrev e10_G : Ctx ((([],x),x),x) :=
  ((Ctx.nil.cons .top).cons (.sngl (.var .here))).cons
    (.and (.rcd (.trm e10_a (.sngl (.var .here)))) (.rcd (.trm e10_b (.sngl (.var .here)))))
/-- `r`. -/
abbrev e10_r : Path ((([],x),x),x) := .var .here
/-- `p`. -/
abbrev e10_p : Path ((([],x),x),x) := .var (.there .here)
/-- `q`. -/
abbrev e10_q : Path ((([],x),x),x) := .var (.there (.there .here))
/-- `{a : u.type} ∧ {b : v.type}`. -/
abbrev e10_ty (u v : Path ((([],x),x),x)) : Ty ((([],x),x),x) :=
  .and (.rcd (.trm e10_a (.sngl u))) (.rcd (.trm e10_b (.sngl v)))

-- G ⊢ p : q.type                                      ty_var
def E10_p : HasTy e10_G (.path e10_p) (.sngl e10_q) := .ty_var rfl
-- G ⊢ q : ⊤                                           ty_var
def E10_q : HasTy e10_G (.path e10_q) .top := .ty_var rfl

-- p ↦ q ⊢ {a : p.type} ∧ {b : p.type} ⇝ {a : p.type} ∧ {b : q.type}      rand2
def E10_repl_pp_pq : Repl e10_p e10_q (e10_ty e10_p e10_p) (e10_ty e10_p e10_q) :=
  .rand2 (.rrcd (.rdtrm (repl_intro_sngl e10_p e10_q)))
-- p ↦ q ⊢ {a : p.type} ∧ {b : q.type} ⇝ {a : q.type} ∧ {b : q.type}      rand1
def E10_repl_pq_qq : Repl e10_p e10_q (e10_ty e10_p e10_q) (e10_ty e10_q e10_q) :=
  .rand1 (.rrcd (.rdtrm (repl_intro_sngl e10_p e10_q)))
-- p ↦ q ⊢ {a : p.type} ∧ {b : p.type} ⇝ {a : q.type} ∧ {b : p.type}      rand1
def E10_repl_pp_qp : Repl e10_p e10_q (e10_ty e10_p e10_p) (e10_ty e10_q e10_p) :=
  .rand1 (.rrcd (.rdtrm (repl_intro_sngl e10_p e10_q)))

-- G ⊢ r : {a : p.type} ∧ {b : p.type}                 ty_var
def E10_pp : HasTy e10_G (.path e10_r) (e10_ty e10_p e10_p) := .ty_var rfl
-- G ⊢ r : {a : p.type} ∧ {b : q.type}                 ty_sub by subtyp_sngl_pq at rand2
def E10_pq : HasTy e10_G (.path e10_r) (e10_ty e10_p e10_q) :=
  .ty_sub E10_pp (.subtyp_sngl_pq E10_p E10_q E10_repl_pp_pq)
-- G ⊢ r : {a : q.type} ∧ {b : q.type}                 ty_sub by subtyp_sngl_pq at rand1, after E10_pq
def E10_qq : HasTy e10_G (.path e10_r) (e10_ty e10_q e10_q) :=
  .ty_sub E10_pq (.subtyp_sngl_pq E10_p E10_q E10_repl_pq_qq)
-- G ⊢ r : {a : q.type} ∧ {b : p.type}                 ty_sub by subtyp_sngl_pq at rand1
def E10_qp : HasTy e10_G (.path e10_r) (e10_ty e10_q e10_p) :=
  .ty_sub E10_pp (.subtyp_sngl_pq E10_p E10_q E10_repl_pp_qp)

/-- The four types of `r` in the order of the text. -/
theorem E10_equiv :
    Nonempty (HasTy e10_G (.path e10_r) (e10_ty e10_p e10_p)) ∧
    Nonempty (HasTy e10_G (.path e10_r) (e10_ty e10_p e10_q)) ∧
    Nonempty (HasTy e10_G (.path e10_r) (e10_ty e10_q e10_q)) ∧
    Nonempty (HasTy e10_G (.path e10_r) (e10_ty e10_q e10_p)) :=
  ⟨⟨E10_pp⟩, ⟨E10_pq⟩, ⟨E10_qq⟩, ⟨E10_qp⟩⟩

/-! ## E11: field introduction (`calculus.tex:212-252`)

In `[q : T, p : μ(z. {a : q.type})]`, `p : {a : T}`.  `ty_rec_elim` gives `p : {a : q.type}`,
`ty_new_elim` gives `p.a : q.type`, `ty_sngl` with `q : T` gives `p.a : T`, and `ty_rcd_intro` gives
`p : {a : T}`.  The type `T` is any closed type.  It sits in the context of signature `[q, p]` as
`T↑↑`. -/

/-- The field `a`. -/
abbrev e11_a : Label := .trm 0

/-- `[q : T, p : μ(z. {a : q.type})]`. -/
abbrev e11_G (T : Ty []) : Ctx (([],x),x) :=
  (Ctx.nil.cons T).cons (.mu (.rcd (.trm e11_a (.sngl (.var (.there .here))))))
/-- `p`. -/
abbrev e11_p : Path (([],x),x) := .var .here
/-- `q`. -/
abbrev e11_q : Path (([],x),x) := .var (.there .here)

-- G ⊢ p : {a : q.type}                                ty_var, ty_rec_elim
def E11_p (T : Ty []) : HasTy (e11_G T) (.path e11_p) (.rcd (.trm e11_a (.sngl e11_q))) :=
  .ty_rec_elim (T := .rcd (.trm e11_a (.sngl (.var (.there (.there .here)))))) (.ty_var rfl)
-- G ⊢ p.a : q.type                                    ty_new_elim
def E11_pa_q (T : Ty []) : HasTy (e11_G T) (.path (e11_p.sel e11_a)) (.sngl e11_q) :=
  .ty_new_elim (E11_p T)
-- G ⊢ q : T                                           ty_var
def E11_q (T : Ty []) : HasTy (e11_G T) (.path e11_q) T.weaken.weaken := .ty_var rfl
-- G ⊢ p.a : T                                         ty_sngl
def E11_pa (T : Ty []) : HasTy (e11_G T) (.path (e11_p.sel e11_a)) T.weaken.weaken :=
  .ty_sngl (E11_pa_q T) (E11_q T)
-- G ⊢ p : {a : T}                                     ty_rcd_intro
def E11_d (T : Ty []) : HasTy (e11_G T) (.path e11_p) (.rcd (.trm e11_a T.weaken.weaken)) :=
  .ty_rcd_intro (E11_pa T)

/-- `p : {a : T}`, for every closed `T`. -/
theorem E11_fldI (T : Ty []) : Nonempty (HasTy (e11_G T) (.path e11_p) (.rcd (.trm e11_a T.weaken.weaken))) :=
  ⟨E11_d T⟩

/-! ## E13: the cyclic object (`overview.tex:412-420`)

`ν(x : {a : (x.a).type}) {a = x.a}` is typed at `μ(x. {a : (x.a).type})` in the empty context.  Its
field is typed by `ty_def_path` at its own singleton.  In the store that holds it, the path `x.a`
looks up to itself, so it is cyclic. -/

/-- The field `a`. -/
abbrev e13_a : Label := .trm 0

/-- `{a : (z.a).type}` over `([], z)`: `z` is `.here`. -/
abbrev e13_T : Ty ([],x) := .rcd (.trm e13_a (.sngl (.sel (.var .here) e13_a)))
/-- `ν(z : {a : (z.a).type}) {a = z.a}`. -/
abbrev e13_lit : Val [] := .new e13_T (.cons .nil (.trm e13_a (.defp (.sel (.var .here) e13_a))))

-- z :ˢ {a : (z.a).type} ⊢ z : {a : (z.a).type}        ty_var
-- z :ˢ {a : (z.a).type} ⊢ z.a : (z.a).type             ty_new_elim
-- z :ˢ {a : (z.a).type} ⊢[z] {a = z.a} : {a : (z.a).type}            ty_def_path
-- z :ˢ {a : (z.a).type} ⊢[z] [] ▹ {a = z.a} :: {a : (z.a).type}      ty_defs_one
-- ⊢ ν(z : {a : (z.a).type}) {a = z.a} : μ(z. {a : (z.a).type})      ty_new_intro
def E13_cyclic_d : HasTy .nil (.val e13_lit) (.mu e13_T) :=
  .ty_new_intro (.ty_defs_one (.ty_def_path (.ty_new_elim (.ty_var rfl))))

theorem E13_cyclic : Nonempty (HasTy .nil (.val e13_lit) (.mu e13_T)) := ⟨E13_cyclic_d⟩

/-- The store `x ↦ ν(z : {a : (z.a).type}) {a = z.a}`. -/
abbrev γ13 : Store ([],x) := Store.nil.cons e13_lit
/-- `x`. -/
abbrev x13 : Path ([],x) := .var .here

-- γ ⊢ x.a ⤳ x.a                                       lookup_var, lookup_sel_v
theorem E13_xa_step : LStep γ13 (.defp (x13.sel e13_a)) (.defp (x13.sel e13_a)) :=
  .sel_v .lookup_var rfl rfl

/-- `x.a` is cyclic: the constant sequence `x.a, x.a, …` is a lookup sequence. -/
theorem E13_cyclic_lookup : CyclicPath γ13 (x13.sel e13_a) :=
  ⟨fun _ => .defp (x13.sel e13_a), rfl, fun _ => E13_xa_step⟩

/-! ## N1: bad bounds (`background.tex:355-380`)

`ν(x : {a : {C : ∀(y : ⊤) ⊤ .. {c : ⊤}}} ∧ {b : {c : ⊤}}) {a = x.a} ∧ {b = λ(y : ⊤) y}`.  The last
definition is a function, which `ty_def_all` declares at a `∀`.  The annotation declares it at
`{c : ⊤}`. -/

/-- The field `a`. -/
abbrev n1_a : Label := .trm 0
/-- The field `b`. -/
abbrev n1_b : Label := .trm 1
/-- The field `c`. -/
abbrev n1_c : Label := .trm 2
/-- The type member `C`. -/
abbrev n1_C : Label := .typ 0

/-- `ν(x : {a : {C : ∀(y : ⊤) ⊤ .. {c : ⊤}}} ∧ {b : {c : ⊤}}) {a = x.a} ∧ {b = λ(y : ⊤) y}`.  In the
definitions `.here` is `x`, and in the body of the lambda `.here` is `y`. -/
abbrev badBoundsLit : Val [] :=
  .new (.and (.rcd (.trm n1_a (.rcd (.typ n1_C (.all .top .top) (.rcd (.trm n1_c .top))))))
             (.rcd (.trm n1_b (.rcd (.trm n1_c .top)))))
    (.cons (.cons .nil (.trm n1_a (.defp (.sel (.var .here) n1_a))))
      (.trm n1_b (.defv (.lam .top (.path (.var .here))))))

theorem N1_bad_bounds : ∀ U, ¬ Nonempty (HasTy .nil (.val badBoundsLit) U) := by
  intro _ ⟨h⟩
  obtain ⟨d⟩ := h.val_new_inv
  rcases DefsTy.cons_inv d with ⟨hn, _⟩ | ⟨_, _, hT, ⟨hd⟩, _⟩
  · cases hn
  · cases hT
    obtain ⟨_, _, e⟩ := DefTy.lam_decl hd
    cases e

/-! ## N2: Fact 2 (`notes-pdot-design/facts.md:1279-1285`)

`ν(x : {a : {A : ⊤..⊥}}) {a = x.a}`.  The one definition is a path, which `ty_def_path` declares at
its singleton `{a : (x.a).type}` and at nothing else.  The annotation declares it at
`{a : {A : ⊤..⊥}}`. -/

/-- The field `a`. -/
abbrev n2_a : Label := .trm 0
/-- The type member `A`. -/
abbrev n2_A : Label := .typ 0

/-- `ν(x : {a : {A : ⊤..⊥}}) {a = x.a}`.  In the definitions `.here` is `x`. -/
abbrev fact2Lit : Val [] :=
  .new (.rcd (.trm n2_a (.rcd (.typ n2_A .top .bot)))) (.cons .nil (.trm n2_a (.defp (.sel (.var .here) n2_a))))

theorem N2_fact2 : ∀ U, ¬ Nonempty (HasTy .nil (.val fact2Lit) U) := by
  intro _ ⟨h⟩
  obtain ⟨d⟩ := h.val_new_inv
  rcases DefsTy.cons_inv d with ⟨_, _, hT, ⟨hd⟩⟩ | ⟨_, _, hT, _, _⟩
  · cases hT
    cases DefTy.path_decl hd
  · cases hT

/-! ## N3: the dangling literal (`notes-pdot-design/refute-d2.md:276-300`)

`ν(x : {h : (x.zz).type}) {h = x.zz}`.  Its one definition is the path `x.zz`, and `ty_def_path` asks a
typing of `x.zz` in `G₃ = [x :ˢ {h : (x.zz).type}]`.  The model `M₃` of `G₃` holds only the paths `x`
and `x.h`, so `x.zz` has no type there.

`M₃` reads `⊤` as `{x, x.h}`, `⊥` as `∅`, `{h : T}` as `{r ∈ {x, x.h} | r.h ∈ T}`, `{a : T}` as `∅`
for `a ≠ h`, `{A : S..U}` as `{r ∈ {x, x.h} | S = ∅}`, `p.A` as `∅`, `(x.zz).type` as `{x.h}`, every
other singleton as `∅`, `∧` as `∩`, `μ(z. T)` as `{r | r ∈ T⟨z := r⟩}` and `∀` as `∅`.  The fields
`sngl`, `path_elim` and `repl` of the model hold because their premise `q ∈ U` is false at the one
path `q = x.zz` whose singleton is not empty. -/

/-- The field `h`. -/
abbrev n3_h : Label := .trm 0
/-- The field `zz`. -/
abbrev n3_zz : Label := .trm 1

/-- `x`, the self. -/
abbrev n3_x : Path ([],x) := .var .here
/-- `x.h`. -/
abbrev n3_xh : Path ([],x) := n3_x.sel n3_h
/-- `x.zz`. -/
abbrev n3_xzz : Path ([],x) := n3_x.sel n3_zz

/-- `{h : (x.zz).type}` over `([], x)`. -/
abbrev n3_T : Ty ([],x) := .rcd (.trm n3_h (.sngl n3_xzz))
/-- `G₃ = [x :ˢ {h : (x.zz).type}]`. -/
abbrev n3_G : Ctx ([],x) := Ctx.nil.consSelf n3_T

/-- `ν(x : {h : (x.zz).type}) {h = x.zz}`. -/
abbrev danglingLit : Val [] := .new n3_T (.cons .nil (.trm n3_h (.defp n3_xzz)))

mutual
/-- `M₃`'s set of a type over `s'`, with `τ` closing the variables of `s'` into `[x]`. -/
def sem₃ : Ty s' → PathSubst s' ([],x) → Path ([],x) → Prop
  | .top, _, r => r = n3_x ∨ r = n3_xh                           -- ⊤ ↦ {x, x.h}
  | .bot, _, _ => False                                           -- ⊥ ↦ ∅
  | .rcd D, τ, r => dsem₃ D τ r                                   -- {D} ↦ the set of D
  | .and T U, τ, r => sem₃ T τ r ∧ sem₃ U τ r                     -- T ∧ U ↦ T ∩ U
  | .sel _ _, _, _ => False                                       -- p.A ↦ ∅
  | .mu T, τ, r => sem₃ T (τ.nomExtend r) r                          -- μ(z. T) ↦ {r | r ∈ T⟨z := r⟩}
  | .all _ _, _, _ => False                                       -- ∀(z : S) T ↦ ∅
  | .sngl q, τ, r => q.subst τ = n3_xzz ∧ r = n3_xh               -- (x.zz).type ↦ {x.h}, q.type ↦ ∅ otherwise
/-- `M₃`'s set of a declaration. -/
def dsem₃ : Dec s' → PathSubst s' ([],x) → Path ([],x) → Prop
  -- {h : T} ↦ {r ∈ {x, x.h} | r.h ∈ T},  {a : T} ↦ ∅ for a ≠ h
  | .trm a T, τ, r => (r = n3_x ∨ r = n3_xh) ∧ a = n3_h ∧ sem₃ T τ (r.sel a)
  -- {A : S..U} ↦ {r ∈ {x, x.h} | S = ∅}
  | .typ _ S _, τ, r => (r = n3_x ∨ r = n3_xh) ∧ ∀ r', ¬ sem₃ S τ r'
end

mutual
/-- Every set of `M₃` holds only `x` and `x.h`. -/
theorem sem₃_range : ∀ (T : Ty s') (τ : PathSubst s' ([],x)) r, sem₃ T τ r → r = n3_x ∨ r = n3_xh
  | .top, _, _, h => h
  | .bot, _, _, h => h.elim
  | .rcd D, τ, r, h => dsem₃_range D τ r h
  | .and T _, τ, r, h => sem₃_range T τ r h.1
  | .sel _ _, _, _, h => h.elim
  | .mu T, _, r, h => sem₃_range T _ r h
  | .all _ _, _, _, h => h.elim
  | .sngl _, _, _, h => .inr h.2
theorem dsem₃_range : ∀ (D : Dec s') (τ : PathSubst s' ([],x)) r, dsem₃ D τ r → r = n3_x ∨ r = n3_xh
  | .trm _ _, _, _, h => h.1
  | .typ _ _ _, _, _, h => h.1
end

mutual
/-- The substitution lemma of `M₃`: reading `T` after `σ` in the closing `τ` is reading `T` in the
closing `σ` then `τ`. -/
theorem sem₃_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) r,
    sem₃ (T.subst σ) τ r ↔ sem₃ T (σ.comp τ) r
  | .top, _, _, _ => .rfl
  | .bot, _, _, _ => .rfl
  | .rcd D, σ, τ, r => dsem₃_subst D σ τ r
  | .and T U, σ, τ, r => and_congr (sem₃_subst T σ τ r) (sem₃_subst U σ τ r)
  | .sel _ _, _, _, _ => .rfl
  | .mu T, σ, τ, r => by
      show sem₃ (T.subst σ.lift) (τ.nomExtend r) r ↔ sem₃ T ((σ.comp τ).nomExtend r) r
      rw [sem₃_subst T σ.lift (τ.nomExtend r) r, PathSubst.lift_comp_extend]
  | .all _ _, _, _, _ => .rfl
  | .sngl q, σ, τ, r => by
      show (q.subst σ).subst τ = n3_xzz ∧ r = n3_xh ↔ q.subst (σ.comp τ) = n3_xzz ∧ r = n3_xh
      rw [Path.subst_subst]
theorem dsem₃_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) r,
    dsem₃ (D.subst σ) τ r ↔ dsem₃ D (σ.comp τ) r
  | .trm a T, σ, τ, r => and_congr .rfl (and_congr .rfl (sem₃_subst T σ τ (r.sel a)))
  | .typ _ S _, σ, τ, _ => and_congr .rfl (forall_congr' fun r' => not_congr (sem₃_subst S σ τ r'))
end

/-- `x.zz` is neither `x` nor `x.h`. -/
theorem n3_xzz_out : ¬ (n3_xzz = n3_x ∨ n3_xzz = n3_xh) := by decide

/-- A field selection that is `x` or `x.h` is `x.h`. -/
theorem n3_sel_out (p : Path ([],x)) (a : Label) : p.sel a = n3_x ∨ p.sel a = n3_xh → p = n3_x ∧ a = n3_h := by
  rintro (h | h)
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

/-- A path whose `M₃` singleton is not empty is `x.zz`. -/
theorem n3_sngl_root {q p : Path ([],x)} (h : sem₃ (.sngl q) (PathSubst.ofRename Rename.id) p) : q = n3_xzz := by
  have e := h.1
  rwa [Path.subst_ofRename, Path.rename_id] at e

/-- The model `M₃` of `G₃ = [x :ˢ {h : (x.zz).type}]`. -/
def M₃ : Model n3_G where
  sem T p := sem₃ T (PathSubst.ofRename Rename.id) p
  var x := by
    cases x with
    | here => exact ⟨.inl rfl, rfl, rfl, rfl⟩
    | there y => nomatch y
  fld_e _ _ _ h := h.2.2
  fld_i p a T h := by
    obtain ⟨rfl, rfl⟩ := n3_sel_out p a (sem₃_range T _ _ h)
    exact ⟨.inl rfl, rfl, h⟩
  sngl _ _ T h hq := by
    cases n3_sngl_root h
    exact (n3_xzz_out (sem₃_range T _ _ hq)).elim
  path_elim _ _ a T h hq := by
    cases n3_sngl_root h
    obtain ⟨e, -⟩ := n3_sel_out _ a (sem₃_range T _ _ hq)
    cases e
  rec_i p T h := by
    show sem₃ T ((PathSubst.ofRename Rename.id).nomExtend p) p
    rw [← PathSubst.one_comp_ofRename_id, ← sem₃_subst]
    exact h
  rec_e p T h := by
    show sem₃ (T.subst (PathSubst.one p)) _ p
    rw [sem₃_subst, PathSubst.one_comp_ofRename_id]
    exact h
  and_i _ _ _ h₁ h₂ := ⟨h₁, h₂⟩
  top T p h := sem₃_range T _ p h
  bot _ _ h := h.elim
  and1 _ _ _ h := h.1
  and2 _ _ _ h := h.2
  fld _ _ _ f _ h := ⟨h.1, h.2.1, f _ h.2.2⟩
  typ _ _ _ _ _ f _ _ h := ⟨h.1, fun r hr => h.2 r (f r hr)⟩
  repl _ _ U _ _ h hq _ _ _ := by
    cases n3_sngl_root h
    exact (n3_xzz_out (sem₃_range U _ _ hq)).elim
  sel2 _ _ _ _ h r hr := (h.2 r hr).elim
  sel1 _ _ _ _ _ _ hr := hr.elim
  all _ _ _ _ _ h := h.elim
  sealCls p C _ h _ _ := by
    rw [Ctx.selfCls_none_of_classFree (G := n3_G) (by decide) p C] at h
    cases h                                                     -- M₃: n3_G declares no class

/-- `x.zz` has no type in `G₃`. -/
theorem n3_xzz_untyped : ¬ Nonempty (HasTy n3_G (.path n3_xzz) T) :=
  fun ⟨h⟩ => n3_xzz_out (sem₃_range T _ _ (M₃.sound_path h))

theorem N3_dangling : ∀ U, ¬ Nonempty (HasTy .nil (.val danglingLit) U) := by
  intro _ ⟨h⟩
  obtain ⟨d⟩ := h.val_new_inv
  rcases DefsTy.cons_inv d with ⟨_, _, hT, ⟨hd⟩⟩ | ⟨_, _, hT, _, _⟩
  · cases hT
    obtain ⟨_, hq⟩ := DefTy.path_inv hd
    exact n3_xzz_untyped hq
  · cases hT

/-! ## N4: no reflexive singleton

In `G₄ = [x : {A : ⊤..⊤}]`, `x : x.type` has no derivation.  No rule of `ty_trm` concludes `p : p.type`
(`pdot-coq/Definitions.v:585-734`).  The model `M₄` of `G₄` reads `⊤` as `{x}`, `⊥` as `∅`,
`{A : S..U}` as `{r | r = x ∧ x ∈ U}`, `p.A` as `{x}`, every singleton as `∅`, `{a : T}` as `∅`, `∀`
as `∅`, `∧` as `∩` and `μ` as `M₃` does.  Then `x ∉ M₄.sem (x.type)`. -/

/-- `x`. -/
abbrev n4_x : Path ([],x) := .var .here

mutual
/-- `M₄`'s set of a type over `s'`, with `τ` closing the variables of `s'` into `[x]`. -/
def sem₄ : Ty s' → PathSubst s' ([],x) → Path ([],x) → Prop
  | .top, _, r => r = n4_x                                        -- ⊤ ↦ {x}
  | .bot, _, _ => False                                           -- ⊥ ↦ ∅
  | .rcd D, τ, r => dsem₄ D τ r                                   -- {D} ↦ the set of D
  | .and T U, τ, r => sem₄ T τ r ∧ sem₄ U τ r                     -- T ∧ U ↦ T ∩ U
  | .sel _ _, _, r => r = n4_x                                    -- p.A ↦ {x}
  | .mu T, τ, r => sem₄ T (τ.nomExtend r) r                          -- μ(z. T) ↦ {r | r ∈ T⟨z := r⟩}
  | .all _ _, _, _ => False                                       -- ∀(z : S) T ↦ ∅
  | .sngl _, _, _ => False                                        -- q.type ↦ ∅
/-- `M₄`'s set of a declaration. -/
def dsem₄ : Dec s' → PathSubst s' ([],x) → Path ([],x) → Prop
  | .trm _ _, _, _ => False                                       -- {a : T} ↦ ∅
  | .typ _ _ U, τ, r => r = n4_x ∧ sem₄ U τ n4_x                  -- {A : S..U} ↦ {r | r = x ∧ x ∈ U}
end

mutual
/-- Every set of `M₄` holds only `x`. -/
theorem sem₄_range : ∀ (T : Ty s') (τ : PathSubst s' ([],x)) r, sem₄ T τ r → r = n4_x
  | .top, _, _, h => h
  | .bot, _, _, h => h.elim
  | .rcd D, τ, r, h => dsem₄_range D τ r h
  | .and T _, τ, r, h => sem₄_range T τ r h.1
  | .sel _ _, _, _, h => h
  | .mu T, _, r, h => sem₄_range T _ r h
  | .all _ _, _, _, h => h.elim
  | .sngl _, _, _, h => h.elim
theorem dsem₄_range : ∀ (D : Dec s') (τ : PathSubst s' ([],x)) r, dsem₄ D τ r → r = n4_x
  | .trm _ _, _, _, h => h.elim
  | .typ _ _ _, _, _, h => h.1
end

mutual
/-- The substitution lemma of `M₄`. -/
theorem sem₄_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) r,
    sem₄ (T.subst σ) τ r ↔ sem₄ T (σ.comp τ) r
  | .top, _, _, _ => .rfl
  | .bot, _, _, _ => .rfl
  | .rcd D, σ, τ, r => dsem₄_subst D σ τ r
  | .and T U, σ, τ, r => and_congr (sem₄_subst T σ τ r) (sem₄_subst U σ τ r)
  | .sel _ _, _, _, _ => .rfl
  | .mu T, σ, τ, r => by
      show sem₄ (T.subst σ.lift) (τ.nomExtend r) r ↔ sem₄ T ((σ.comp τ).nomExtend r) r
      rw [sem₄_subst T σ.lift (τ.nomExtend r) r, PathSubst.lift_comp_extend]
  | .all _ _, _, _, _ => .rfl
  | .sngl _, _, _, _ => .rfl
theorem dsem₄_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ ([],x)) r,
    dsem₄ (D.subst σ) τ r ↔ dsem₄ D (σ.comp τ) r
  | .trm _ _, _, _, _ => .rfl
  | .typ _ _ U, σ, τ, _ => and_congr .rfl (sem₄_subst U σ τ n4_x)
end

/-- `G₄ = [x : {A : ⊤..⊤}]`, at any label `A`. -/
abbrev n4_G (A : Label) : Ctx ([],x) := Ctx.nil.cons (.rcd (.typ A .top .top))

/-- The model `M₄` of `G₄`. -/
def M₄ (A : Label) : Model (n4_G A) where
  sem T p := sem₄ T (PathSubst.ofRename Rename.id) p
  var x := by
    cases x with
    | here => exact ⟨rfl, rfl⟩
    | there y => nomatch y
  fld_e _ _ _ h := h.elim
  fld_i _ _ T h := nomatch (sem₄_range T _ _ h)
  sngl _ _ _ h _ := h.elim
  path_elim _ _ _ _ h _ := h.elim
  rec_i p T h := by
    show sem₄ T ((PathSubst.ofRename Rename.id).nomExtend p) p
    rw [← PathSubst.one_comp_ofRename_id, ← sem₄_subst]
    exact h
  rec_e p T h := by
    show sem₄ (T.subst (PathSubst.one p)) _ p
    rw [sem₄_subst, PathSubst.one_comp_ofRename_id]
    exact h
  and_i _ _ _ h₁ h₂ := ⟨h₁, h₂⟩
  top T p h := sem₄_range T _ p h
  bot _ _ h := h.elim
  and1 _ _ _ h := h.1
  and2 _ _ _ h := h.2
  fld _ _ _ _ _ h := h.elim
  typ _ _ _ _ _ _ g _ h := ⟨h.1, g _ h.2⟩
  repl _ _ _ _ _ h _ _ _ _ := h.elim
  sel2 _ _ S _ _ r hr := sem₄_range S _ r hr
  sel1 p A _ _ h r hr := by
    cases sem₄_range (.sel p A) _ r hr
    exact h.2
  all _ _ _ _ _ h := h.elim
  sealCls _ _ T _ r hr := sem₄_range T _ r hr                  -- M₄: every set is within {x}, and p.A is {x}

/-- `x : x.type` has no derivation in `[x : {A : ⊤..⊤}]`, at every label `A`. -/
theorem N4_no_refl_sngl : ¬ Nonempty (HasTy (Ctx.nil.cons (.rcd (.typ A .top .top))) (.path (.var .here)) (.sngl (.var .here))) :=
  fun ⟨h⟩ => (M₄ A).sound_path h

/-! ## N5: `tight_bounds` is independent of the opened premise (`Refute_D3_Tight.lean`)

The annotation `T = {B : ⊤..⊤} ∧ {A : (z.b).B .. w.B}` of `Repl`'s `tight_premise_independent`, with
`z` the outer self and `w` the nested one, and the definitions `ds = {B = ⊤} ▹ {A = w.B}`.  Opened at
`r = z.b`, the definitions are `{B = ⊤} ▹ {A = (z.b).B}` and the annotation is
`{B : ⊤..⊤} ∧ {A : (z.b).B .. (z.b).B}`, which `ty_defs_cons`, `ty_defs_one` and `ty_def_typ` derive.
So `ty_def_new`'s premise on the opened definitions holds while `tight_bounds` of `μ(w. T)` fails.  The
path `r` stands in the place of the rule's `r.b`. -/

/-- `{B = ⊤} ▹ {A = w.B}` over `(([], z), w)`: `w` is `.here`. -/
abbrev n5_ds : Defs (([],x),x) :=
  .cons (.cons .nil (.typ tightEx_B .top)) (.typ tightEx_A (.sel (.var .here) tightEx_B))

-- [z : ⊤] ⊢[z.b] {B = ⊤} : {B : ⊤..⊤}                                    ty_def_typ
-- [z : ⊤] ⊢[z.b] [] ▹ {B = ⊤} :: {B : ⊤..⊤}                              ty_defs_one
-- [z : ⊤] ⊢[z.b] {A = (z.b).B} : {A : (z.b).B .. (z.b).B}                ty_def_typ
-- [z : ⊤] ⊢[z.b] {B = ⊤} ▹ {A = (z.b).B} :: {B : ⊤..⊤} ∧ {A : (z.b).B .. (z.b).B}   ty_defs_cons, B ≠ A
def N5_third_premise :
    DefsTy (Ctx.nil.cons .top) tightEx_r (n5_ds.substPath tightEx_r) (tightEx_T.substPath tightEx_r) :=
  .ty_defs_cons (.ty_defs_one .ty_def_typ) .ty_def_typ rfl

theorem N5_tight : ∃ (T : Ty (([],x),x)) (ds : Defs (([],x),x)) (r : Path ([],x)),
    (Ty.mu T).tight = false ∧ Nonempty (DefsTy (Ctx.nil.cons .top) r (ds.substPath r) (T.substPath r)) :=
  ⟨tightEx_T, n5_ds, tightEx_r, by decide, ⟨N5_third_premise⟩⟩

end Nominal.Source
